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

object Translator extends Typechecker {
  import AST._

  val assignMonoid = BaseMonoid("assign")
  val composition = BaseMonoid("composition")
  def bag ( m: Monoid ) = ParametricMonoid("bag",m)
  //val vector = ParametricMonoid("vector",assignMonoid)
  //val matrix = ParametricMonoid("matrix",assignMonoid)
  val vector = BaseMonoid("vector")
  val matrix = BaseMonoid("matrix")

  def translate ( e: Expr, globals: Environment, locals: Environment ): Expr
    = { val state = newvar
        Lambda(VarPat(state),
          e match {
          case Var(n) if locals.contains(n)
            => Var(n)
          case Var(n)
            => Project(Var(state),n)
/*
          case VectorIndex(u,ii)
            => val i = newvar
               val v = newvar
               val ic = Apply(translate(ii,globals,locals),Var(state))
               flatMap(Lambda(TuplePat(List(VarPat(i),VarPat(v))),
                              IfE(Call("==",List(Var(i),ic)),
                                  Elem(vector,Var(v)),Empty(vector))),
                       Apply(translate(u,globals,locals),Var(state)))
          case MatrixIndex(u,ii,jj)
            => val i = newvar
               val j = newvar
               val v = newvar
               val ic = Apply(translate(ii,globals,locals),Var(state))
               val jc = Apply(translate(jj,globals,locals),Var(state))
               flatMap(Lambda(TuplePat(List(TuplePat(List(VarPat(i),VarPat(j))),
                                            VarPat(v))),
                              IfE(Call("&&",List(Call("==",List(Var(i),ic)),
                                                 Call("==",List(Var(j),jc)))),
                                  Elem(matrix,Var(v)),Empty(matrix))),
                       Apply(translate(u,globals,locals),Var(state)))
*/
          case Let(p,u,b)
            => Let(p,Apply(translate(u,globals,locals),Var(state)),
                   Apply(translate(b,globals,bindPattern(p,typecheck(u,locals++globals),locals++globals)),
                         Var(state)))
          case _ => apply(e,x => Apply(translate(x,globals,locals),Var(state)))
        }
    )}

  def update ( dest: Expr, value: Expr, state: Expr, globals: Environment, locals: Environment ): Expr
    = dest match {
        case Var(n) if locals.contains(n)
          => throw new Error("Local variable "+n+" cannot be updated")
        case Var(n)
          => Record(globals.map{ case (v,_) => v -> (if (v == n) value else Project(state,v)) })
        case Project(u,a)
          => typecheck(u,locals++globals) match {
                case RecordType(cs)
                  => update(u,Record(cs.map{ case (v,_) => v -> (if (v == a) value else Project(u,v)) }),
                            state,globals,locals)
                case t => throw new Error("Record projection "+dest+" must be over a record (found "+t+")")
             }
        case Nth(u,n)
          => typecheck(u,locals++globals) match {
                case TupleType(cs)
                  => update(u,Tuple((1 to cs.length).map( i => if (i == n) value else Nth(u,i) ).toList),
                            state,globals,locals)
                case t => throw new Error("Tuple projection "+dest+" must be over a tuple (found "+t+")")
             }
        case VectorIndex(u,i)
          => update(u,Merge(Apply(translate(u,globals,locals),state),
                            Elem(vector,Tuple(List(i,value)))),
                    state,globals,locals)
        case MatrixIndex(u,i,j)
          => update(u,Merge(Apply(translate(u,globals,locals),state),
                            Elem(matrix,Tuple(List(Tuple(List(i,j)),value)))),
                    state,globals,locals)
        case _ => throw new Error("Illegal destination: "+dest)
    }

  def translate ( s: Stmt, globals: Environment, locals: Environment ): Expr
    = { val state = newvar
        s match {
          case Assign(d,e)
            => Lambda(VarPat(state),
                      update(d,Apply(translate(e,globals,locals),Var(state)),
                             Var(state),globals,locals))
          case Block(ss)
            => val (ne,_,_) = ss.foldLeft((Lambda(VarPat(state),Var(state)),globals,locals)) {
                    case ((f,gs,ls),DeclareVal(v,t,e))
                      => val st = newvar
                         ( Lambda(VarPat(st),
                                  Let(VarPat(v),Apply(translate(e,gs,ls),Var(st)),
                                      Apply(f,Var(st)))),
                           gs, ls+((v,t)) )
                    case ((f,gs,ls),DeclareVar(v,t,Var("null")))
                      => val st = newvar
                         ( Lambda(VarPat(st),update(Var(v),Undefined(t),Apply(f,Var(st)),gs+((v,t)),ls)),
                           gs+((v,t)), ls )
                    case ((f,gs,ls),DeclareVar(v,t,e))
                      => val st = newvar
                         val nst = newvar
                         ( Lambda(VarPat(st),
                                  Let(VarPat(nst),Apply(f,Var(st)),
                                      update(Var(v),Apply(translate(e,gs,ls),Var(nst)),
                                             Var(nst),gs+((v,t)),ls))),
                           gs+((v,t)), ls )
                    case ((f,gs,ls),stmt)
                      => val st = newvar
                         ( Lambda(VarPat(st),
                                  Apply(translate(stmt,gs,ls),Apply(f,Var(st)))),
                           gs, ls )
                    }
               ne
          case ForeachS(v,e,b)
            => typecheck(e,locals++globals) match {
                  case ParametricType(_,List(tp))
                    => Lambda(VarPat(state),
                              Apply(flatMap(Lambda(VarPat(v),Elem(composition,translate(b,globals,locals+((v,tp))))),
                                            Apply(translate(e,globals,locals),Var(state))),
                                    Var(state)))
                  case _ => throw new Error("Foreach statement must be over a collection: "+s)
               }
          case ForS(v,n1,n2,n3,b)
            => Lambda(VarPat(state),
                      Apply(flatMap(Lambda(VarPat(v),Elem(composition,translate(b,globals,locals+((v,intType))))),
                                    Apply(translate(Call("gen",List(n1,n2,n3)),globals,locals),Var(state))),
                            Var(state)))
          case IfS(p,te,ee)
            => Lambda(VarPat(state),
                      IfE(Apply(translate(p,globals,locals),Var(state)),
                          Apply(translate(te,globals,locals),Var(state)),
                          Apply(translate(ee,globals,locals),Var(state))))
          case _ => throw new Error("Illegal statement: "+s)
        }
  }

  def translate ( s: Stmt ): Expr
    = Apply(translate(s,Map():Environment,Map():Environment),Record(Map()))
}
