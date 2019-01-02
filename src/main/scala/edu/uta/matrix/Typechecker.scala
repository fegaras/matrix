/*
 * Copyright © 2018 University of Texas at Arlington
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

    type Environment = Map[String,Type]

    val intType = BasicType("int")
    val boolType = BasicType("bool")
    val doubleType = BasicType("double")
    val stringType = BasicType("string")

    def typeMatch ( t1: Type, t2: Type ): Boolean
      = ((t1 == AnyType() || t2 == AnyType())
         || t1 == t2
         || ((t1,t2) match {
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

    def typecheck ( e: Expr, env: Environment ): Type
      = e match {
          case Var(v)
            => if (env.contains(v)) env(v)
               else throw new Error("Undeclared variable: "+v)
          case Nth(u,n)
            => typecheck(u,env) match {
                  case TupleType(cs)
                    => if (n<0 || n>=cs.length)
                          throw new Error("Tuple does not contain a "+n+" element")
                       cs(n)
                  case t => throw new Error("Tuple projection "+e+" must be over a tuple (found "+t+")")
               }
          case Project(u,a)
            => typecheck(u,env) match {
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
            => if (typecheck(i,env) != intType)
                  throw new Error("Vector indexing "+e+" must use an integer index: "+i)
               else typecheck(u,env) match {
                  case ParametricType("vector",List(t))
                    => t
                  case t => throw new Error("Vector indexing "+e+" must be over a vector (found "+t+")")
               }
          case MatrixIndex(u,i,j)
            => if (typecheck(i,env) != intType)
                  throw new Error("Matrix indexing "+e+" must use an integer row index: "+i)
               else if (typecheck(j,env) != intType)
                  throw new Error("Matrix indexing "+e+" must use an integer column index: "+i)
               else typecheck(u,env) match {
                  case ParametricType("matrix",List(t))
                    => t
                  case t => throw new Error("Matrix indexing "+e+" must be over a matrix (found "+t+")")
               }
          case Let(p,u,b)
            => typecheck(b,bindPattern(p,typecheck(u,env),env))
          case Collection(f,args) if List("vector","matrix","bag","list").contains(f)
            => val tp = args.foldRight(AnyType():Type){ case (a,r)
                                        => val t = typecheck(a,env)
                                           if (r != AnyType() && t != r)
                                              throw new Error("Incompatible types in collection "+e)
                                           else t }
               ParametricType(f,List(tp))
          case Call(f,args)
            => val tps = args.map(typecheck(_,env))
               functions.takeWhile{ case (n,ts,_) => n == f && (ts zip tps).map{ case (t1,t2) => typeMatch(t1,t2) }.reduce(_&&_) } match {
                 case (_,_,t)::_ => t
                 case _ => throw new Error("Function "+f+" with arguments of type "+tps+" in "+e+" has not been declared")
               }
          case IfE(p,a,b)
            => if (typecheck(p,env) != boolType)
                 throw new Error("The if-expression condition "+e+" must be a boolean")
               val tp = typecheck(a,env)
               if (!typeMatch(typecheck(b,env),tp))
                 throw new Error("Ill-type if-expression"+e)
               tp
          case StringConst(_) => stringType
          case IntConst(_) => intType
          case DoubleConst(_) => doubleType
          case BoolConst(_) => boolType
          case _ => throw new Error("Illegal expresion: "+e)
      }

    def typecheck ( s: Stmt, env: Environment ): Environment
      = s match {
          case DeclareVar(v,t,Var("null"))
            => env+((v,t))
         case DeclareVar(v,t,e)
            => if (!typeMatch(typecheck(e,env),t))
                  throw new Error("Value "+e+" has not type "+t)
               else env+((v,t))
          case Block(cs)
            => cs.foldLeft(env){ case (r,c) => typecheck(c,r) }
          case Assign(d,v)
            => if (!typeMatch(typecheck(d,env),typecheck(v,env)))
                  throw new Error("Incompatible source in assignment: "+s)
               else env
          case ForS(v,a,b,c,u)
            => if (typecheck(a,env) != intType)
                  throw new Error("For loop "+s+" must use an integer initial value: "+a)
               else if (typecheck(b,env) != intType)
                  throw new Error("For loop "+s+" must use an integer final value: "+b)
               else if (typecheck(c,env) != intType)
                  throw new Error("For loop "+s+" must use an integer step: "+c)
               else typecheck(u,env+((v,intType)))
          case ForeachS(v,c,u)
            => typecheck(c,env) match {
                  case ParametricType(f,List(tp)) if List("vector","matrix","bag","list").contains(f)
                    => typecheck(u,env+((v,tp)))
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
      ("-",List(doubleType),doubleType)
    )

    val initialEnvironment: Environment = Map()

    def typecheck ( s: Stmt ) { typecheck(s,initialEnvironment) }
}
