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

  def translate ( e: Expr, env: Environment ): Expr
    = { val state = newvar
        Lambda(VarPat(state),
          e match {
          case Var(n)
            => Project(Var(state),n)
          case Nth(u,n)
            => Nth(Apply(translate(u,env),Var(state)),n)
          case Project(u,a)
            => Project(Apply(translate(u,env),Var(state)),a)
          case VectorIndex(u,ii)
            => val i = newvar
               val v = newvar
               val ic = Apply(translate(ii,env),Var(state))
               flatMap(Lambda(TuplePat(List(VarPat(i),VarPat(v))),
                              IfE(Call("==",List(Var(i),ic)),
                                  Elem(vector,Var(v)),Empty(vector))),
                       Apply(translate(u,env),Var(state)))
          case MatrixIndex(u,ii,jj)
            => val i = newvar
               val j = newvar
               val v = newvar
               val ic = Apply(translate(ii,env),Var(state))
               val jc = Apply(translate(jj,env),Var(state))
               flatMap(Lambda(TuplePat(List(TuplePat(List(VarPat(i),VarPat(j))),
                                            VarPat(v))),
                              IfE(Call("&&",List(Call("==",List(Var(i),ic)),
                                                 Call("==",List(Var(j),jc)))),
                                  Elem(matrix,Var(v)),Empty(matrix))),
                       Apply(translate(u,env),Var(state)))
          case Call(f,es)
            => Call(f,es.map(x => Apply(translate(x,env),Var(state))))
          case _ => e
        }
    )}

  def update ( dest: Expr, value: Expr, state: String, env: Environment ): Expr
    = dest match {
        case Var(n)
          => Record(env.map{ case (v,_) => v -> (if (v == n) value else Project(Var(state),v)) })
        case Project(u,a)
          => typecheck(u,env) match {
                case RecordType(cs)
                  => update(u,Record(cs.map{ case (v,_) => v -> (if (v == a) value else Project(u,v)) }),state,env)
                case t => throw new Error("Record projection "+dest+" must be over a record (found "+t+")")
             }
        case Nth(u,n)
          => typecheck(u,env) match {
                case TupleType(cs)
                  => update(u,Tuple((1 to cs.length).map( i => if (i == n) value else Nth(u,i) ).toList),state,env)
                case t => throw new Error("Tuple projection "+dest+" must be over a tuple (found "+t+")")
             }
        case VectorIndex(u,i)
          => update(u,Merge(Apply(translate(u,env),Var(state)),Elem(vector,Tuple(List(i,value)))),state,env)
        case MatrixIndex(u,i,j)
          => update(u,Merge(dest,Elem(matrix,Tuple(List(Tuple(List(i,j)),value)))),state,env)
    }

  def translate ( s: Stmt, env: Environment ): (Expr,Environment)
    = { val state = newvar
        s match {
          case DeclareVar(v,t,Var("null"))
            => (Lambda(VarPat(state),Var(state)),
                env+((v,t)))
          case DeclareVar(v,t,e)
            => (Lambda(VarPat(state),update(Var(v),Apply(translate(e,env),Var(state)),state,env+((v,t)))),
                env+((v,t)))
          case Assign(d,e)
            => (Lambda(VarPat(state),update(d,Apply(translate(e,env),Var(state)),state,env)),env)
          case Block(ss)
            => ss.foldLeft((Lambda(VarPat(state),Var(state)),env)){
                    case ((r,renv),stmt)
                      => val (e,nenv) = translate(stmt,renv)
                         val st = newvar
                         (Lambda(VarPat(st),Apply(e,Apply(r,Var(st)))),nenv) }
          case ForeachS(v,e,b)
            => typecheck(e,env) match {
                  case ParametricType(_,List(tp))
                    => val (be,nenv) = translate(b,env+((v,tp)))
                       (flatMap(Lambda(VarPat(v),Elem(composition,be)),
                                Apply(translate(e,env),Var(state))),
                        nenv)
                  case _ => throw new Error("Foreach statement must be over a collection: "+s)
               }
        }
  }

  def translate ( s: Stmt ): Expr
    = Apply(translate(s,Map():Environment)._1,Record(Map()))
}
