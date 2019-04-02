/*
 * Copyright © 2019 University of Texas at Arlington
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package edu.uta.matrix

class Typechecker {
    import AST._

    type Environment = Map[String,Type]

    val intType = BasicType("int")
    val boolType = BasicType("bool")
    val doubleType = BasicType("double")
    val stringType = BasicType("string")

    def isCollection ( f: String ): Boolean
      = List("vector","matrix","bag","list").contains(f)

    def typeMatch ( t1: Type, t2: Type ): Boolean
      = ((t1 == AnyType() || t2 == AnyType())
         || t1 == t2
         || ((t1,t2) match {
                case (ParametricType("vector",List(ts1)),
                      ParametricType("bag",List(TupleType(List(it,ts2)))))
                  => typeMatch(ts1,ts2) && typeMatch(it,intType)
                case (ParametricType("matrix",List(ts1)),
                      ParametricType("bag",List(TupleType(List(TupleType(List(it1,it2)),ts2)))))
                  => typeMatch(ts1,ts2) && typeMatch(it1,intType) && typeMatch(it2,intType)
                case (ParametricType(n1,ts1),ParametricType(n2,ts2))
                  if n1==n2 && ts1.length == ts2.length
                  => (ts1 zip ts2).map{ case (tp1,tp2) => typeMatch(tp1,tp2) }.reduce(_&&_)
                case (TupleType(ts1),TupleType(ts2))
                  if ts1.length == ts2.length
                  => (ts1 zip ts2).map{ case (tp1,tp2) => typeMatch(tp1,tp2) }.reduce(_&&_)
                case (RecordType(cs1),RecordType(cs2))
                  if cs1.size == cs2.size
                  => (cs1 zip cs2).map{ case ((_,tp1),(_,tp2)) => typeMatch(tp1,tp2) }.reduce(_&&_)
                case (FunctionType(dt1,tt1),FunctionType(dt2,tt2))
                  => typeMatch(dt1,dt2) && typeMatch(tt1,tt2)
                case _ => false
            }))

    def bindPattern ( pat: Pattern, tp: Type, env: Environment ): Environment
      = (pat,tp) match {
          case (TuplePat(cs),TupleType(ts))
            => if (cs.length != ts.length)
                 throw new Error("Pattern "+pat+" does not match the type "+tp)
               else cs.zip(ts).foldRight(env){ case ((p,t),r) => bindPattern(p,t,r) }
          case (VarPat(v),t)
            => env+((v,t))
          case (StarPat(),_)
            => env
          case _ => throw new Error("Pattern "+pat+" does not match the type "+tp)
      }

    def typecheck ( e: Expr, globals: Environment, locals: Environment ): Type
      = e match {
          case Undefined(tp)
            => tp
          case Var(v)
            => if (globals.contains(v))
                  globals(v)
               else if (locals.contains(v))
                  locals(v)
               else throw new Error("Undeclared variable: "+v)
          case Nth(u,n)
            => typecheck(u,globals,locals) match {
                  case TupleType(cs)
                    => if (n<0 || n>=cs.length)
                          throw new Error("Tuple does not contain a "+n+" element")
                       cs(n)
                  case t => throw new Error("Tuple projection "+e+" must be over a tuple (found "+t+")")
               }
          case Project(u,a)
            => typecheck(u,globals,locals) match {
                  case RecordType(cs)
                    => if (cs.contains(a))
                         cs(a)
                       else throw new Error("Unknown record attribute: "+a)
                  case ParametricType("vector",_) if a == "length"
                    => intType
                  case ParametricType("matrix",_) if a == "rows" || a == "cols"
                    => intType
                  case t => throw new Error("Record projection "+e+" must be over a record (found "+t+")")
               }
          case VectorIndex(u,i)
            => if (typecheck(i,globals,locals) != intType)
                  throw new Error("Vector indexing "+e+" must use an integer index: "+i)
               else typecheck(u,globals,locals) match {
                  case ParametricType("vector",List(t))
                    => t
                  case t => throw new Error("Vector indexing "+e+" must be over a vector (found "+t+")")
               }
          case MatrixIndex(u,i,j)
            => if (typecheck(i,globals,locals) != intType)
                  throw new Error("Matrix indexing "+e+" must use an integer row index: "+i)
               else if (typecheck(j,globals,locals) != intType)
                  throw new Error("Matrix indexing "+e+" must use an integer column index: "+i)
               else typecheck(u,globals,locals) match {
                  case ParametricType("matrix",List(t))
                    => t
                  case t => throw new Error("Matrix indexing "+e+" must be over a matrix (found "+t+")")
               }
          case Let(p,u,b)
            => typecheck(b,globals,bindPattern(p,typecheck(u,globals,locals),locals))
          case Collection("matrix",args)
            => val tp = args.foldRight(AnyType():Type){ case (a,r)
                                        => typecheck(a,globals,locals) match {
                                               case TupleType(tps)
                                                 => tps.foldRight(r){ case (t,s)
                                                        => if (s != AnyType() && t != s)
                                                              throw new Error("Incompatible types in matrix "+e)
                                                           else t }
                                               case _ => throw new Error("Matrix elements must be tuples: "+e) } }
               ParametricType("matrix",List(tp))
          case Collection(f,args)
            if isCollection(f)
            => val tp = args.foldRight(AnyType():Type){ case (a,r)
                                        => val t = typecheck(a,globals,locals)
                                           if (r != AnyType() && t != r)
                                              throw new Error("Incompatible types in collection "+e)
                                           else t }
               ParametricType(f,List(tp))
          case Comprehension(m,h,qs)
            => var nenv = locals             // extended binding environment
               var pvs: List[String] = Nil   // pattern variables in comprehension
               for ( q <- qs ) {
                  q match {
                    case Generator(p,d)
                      => typecheck(d,globals,nenv) match {
                            case ParametricType("vector",List(t))
                              => nenv = bindPattern(p,TupleType(List(intType,t)),nenv)
                            case ParametricType("matrix",List(t))
                              => nenv = bindPattern(p,TupleType(List(TupleType(List(intType,intType)),t)),nenv)
                            case ParametricType(_,List(t))
                              => nenv = bindPattern(p,t,nenv)
                            case t => throw new Error("Expected a collection type in generator "+d+" (found "+t+")")
                         }
                         pvs = pvs ++ patvars(p)
                    case LetBinding(p,d)
                      => nenv = bindPattern(p,typecheck(d,globals,nenv),nenv)
                         pvs = pvs ++ patvars(p)
                    case Predicate(p)
                      => if (typecheck(p,globals,nenv) != boolType)
                           throw new Error("The comprehension predicate "+p+" must be a boolean")
                    case GroupByQual(p,k)
                      => val nvs = patvars(p)
                         val ktp = typecheck(k,globals,nenv)
                         // lift all pattern variables to bags
                         nenv = nenv ++ pvs.diff(nvs).map{ v => (v,ParametricType("bag",List(nenv(v)))) }.toMap
                         nenv = bindPattern(p,ktp,nenv)
                         pvs = pvs ++ nvs
                    case OrderByQual(k)
                      => typecheck(k,globals,nenv)
                  }
              }
              m match {
                case BaseMonoid("option")
                  => ParametricType("option",List(typecheck(h,globals,nenv)))
                case BaseMonoid("bag")
                  => ParametricType("bag",List(typecheck(h,globals,nenv)))
                case ParametricMonoid(f,_)
                  if isCollection(f)
                  => ParametricType(f,List(typecheck(h,globals,nenv)))
                case _ => throw new Error("The comprehension monoid "+m+" must be a collection monoid")
              }
          case Call(f,args)
            => val tps = args.map(typecheck(_,globals,locals))
               functions.filter{ case (n,ts,_) => n == f && ts.length == tps.length &&
                                                  (ts zip tps).map{ case (t1,t2) => typeMatch(t1,t2) }
                                                              .reduce(_&&_) } match {
                            case (_,_,t)::_ => t
                            case _ => throw new Error("Function "+f+" with arguments of type "
                                                      +tps+" in "+e+" has not been declared")
               }
          case IfE(p,a,b)
            => if (typecheck(p,globals,locals) != boolType)
                 throw new Error("The if-expression condition "+p+" must be a boolean")
               val tp = typecheck(a,globals,locals)
               if (!typeMatch(typecheck(b,globals,locals),tp))
                 throw new Error("Ill-typed if-expression"+e)
               tp
          case Apply(Lambda(p,b),arg)
            => typecheck(b,globals,bindPattern(p,typecheck(arg,globals,locals),locals))
          case Apply(flatMap(Lambda(p,Elem(BaseMonoid("composition"),Lambda(q,b))),u),x)
            => val xtp = typecheck(x,globals,locals)
               typecheck(u,globals,locals) match {
                  case ParametricType(f,List(utp)) if List("vector","matrix","bag","list").contains(f)
                    => typecheck(b,globals,bindPattern(q,xtp,bindPattern(p,utp,locals)))
                  case _ => throw new Error("Wrong flatMap on function composition: "+e)
               }
               xtp
          case Apply(Comprehension(BaseMonoid("composition"),Lambda(VarPat(v),b),qs),x)
            => val nv = newvar
               typecheck(Comprehension(BaseMonoid("option"),Var(nv),qs:+Generator(VarPat(nv),b)),globals,
                         locals+(v->typecheck(x,globals,locals)))
          case Apply(f,arg)
            => val tp = typecheck(arg,globals,locals)
               typecheck(f,globals,locals) match {
                  case FunctionType(dt,rt)
                    => if (typeMatch(dt,tp)) rt
                      else throw new Error("Function "+f+" cannot be applied to "+arg+" of type "+tp);
                  case _ => throw new Error("Expected a function "+f)
               }
          case Tuple(cs)
            => TupleType(cs.map{ typecheck(_,globals,locals) })
          case Record(cs)
            => RecordType(cs.map{ case (v,u) => v->typecheck(u,globals,locals) })
          case Merge(x,y)
            => val xtp = typecheck(x,globals,locals)
               val ytp = typecheck(y,globals,locals)
               if (!typeMatch(xtp,ytp))
                   throw new Error("Incompatible types in Merge: "+e+" (found "+xtp+" and "+ytp+")")
               xtp
          case Elem(BaseMonoid("vector"),x)
            => typecheck(x,globals,locals) match {
                  case TupleType(List(BasicType("int"),tp))
                    => ParametricType("vector",List(tp))
                  case _ => throw new Error("Wrong vector: "+e)
               }
          case Elem(BaseMonoid("matrix"),x)
            => typecheck(x,globals,locals) match {
                  case TupleType(List(TupleType(List(BasicType("int"),BasicType("int"))),tp))
                    => ParametricType("matrix",List(tp))
                  case _ => throw new Error("Wrong matrix: "+e)
               }
          case Elem(BaseMonoid(m),x)
            => ParametricType(m,List(typecheck(x,globals,locals)))
          case Empty(BaseMonoid(f))
            => ParametricType(f,List(AnyType()))
          case flatMap(Lambda(p,b),u)
            => typecheck(u,globals,locals) match {
                  case ParametricType("vector",List(tp))
                    => typecheck(b,globals,bindPattern(p,TupleType(List(intType,tp)),locals))
                  case ParametricType("matrix",List(tp))
                    => typecheck(b,globals,bindPattern(p,TupleType(List(TupleType(List(intType,intType)),tp)),locals))
                  case ParametricType(_,List(tp))
                    => typecheck(b,globals,bindPattern(p,tp,locals))
                  case tp => throw new Error("flatMap must be over a collection in "+e+" (found "+tp+")")
               }
          case reduce(m,u)
            => typecheck(u,globals,locals) match {
                  case ParametricType(_,List(tp))
                    => //if (!typeMatch(tp,typecheck(Call(m,List(Var("x"),Var("y"))),Map(),Map( "x" -> tp, "y" -> tp))))
                       //   throw new Error("Wrong monoid "+m+" in "+e)
                       tp
                  case tp => throw new Error("Reduction "+e+" must must be over a collection (found "+tp+")")
               }
          case StringConst(_) => stringType
          case IntConst(_) => intType
          case DoubleConst(_) => doubleType
          case BoolConst(_) => boolType
          case _ => throw new Error("Illegal expression: "+e)
      }

    def typecheck ( s: Stmt, globals: Environment, locals: Environment ): Environment
      = s match {
          case DeclareVal(v,t,e)
            => if (!typeMatch(typecheck(e,globals,locals),t))
                  throw new Error("Value "+e+" has not type "+t)
               else globals+((v,t))
          case DeclareVar(v,t,Var("null"))
            => globals+((v,t))
          case DeclareVar(v,t,e)
            => if (!typeMatch(typecheck(e,globals,locals),t))
                  throw new Error("Value "+e+" has not type "+t)
               else globals+((v,t))
          case Block(cs)
            => cs.foldLeft(globals){ case (r,c) => typecheck(c,r,locals) }
          case Assign(d,v)
            => if (!typeMatch(typecheck(d,globals,locals),typecheck(v,globals,locals)))
                  throw new Error("Incompatible source in assignment: "+s)
               else globals
          case IfS(p,x,y)
            => if (typecheck(p,globals,locals) != boolType)
                  throw new Error("The if-statement condition "+p+" must be a boolean")
               typecheck(x,globals,locals)
               typecheck(y,globals,locals)
          case ForS(v,a,b,c,u)
            => if (typecheck(a,globals,locals) != intType)
                  throw new Error("For loop "+s+" must use an integer initial value: "+a)
               else if (typecheck(b,globals,locals) != intType)
                  throw new Error("For loop "+s+" must use an integer final value: "+b)
               else if (typecheck(c,globals,locals) != intType)
                  throw new Error("For loop "+s+" must use an integer step: "+c)
               else typecheck(u,globals,locals+((v,intType)))
          case ForeachS(v,c,u)
            => typecheck(c,globals,locals) match {
                  case ParametricType(f,List(tp))
                    if isCollection(f)
                    => typecheck(u,globals,locals+((v,tp)))
                  case _ => throw new Error("Foreach statement must be over a collection: "+s)
               }
          case _ => throw new Error("Illegal statement: "+s)
    }

    val functions: List[(String,List[Type],Type)] = List(
      ("+",List(intType,intType),intType),
      ("+",List(doubleType,doubleType),doubleType),
      ("-",List(intType,intType),intType),
      ("-",List(doubleType,doubleType),doubleType),
      ("*",List(intType,intType),intType),
      ("*",List(doubleType,doubleType),doubleType),
      ("/",List(intType,intType),intType),
      ("%",List(intType,intType),intType),
      ("/",List(doubleType,doubleType),doubleType),
      ("-",List(intType),intType),
      ("-",List(doubleType),doubleType),
      ("==",List(AnyType(),AnyType()),boolType),
      ("range",List(intType,intType,intType),ParametricType("list",List(intType)))
    )

    val globalEnv: Environment = Map()
    val localEnv: Environment = Map()

    def typecheck ( e: Expr ): Type = typecheck(e,globalEnv,localEnv)

    def typecheck ( s: Stmt ) { typecheck(s,globalEnv,localEnv) }
}
