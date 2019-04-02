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

object Translator extends Typechecker {
  import AST._

  val composition = BaseMonoid("composition")
  val vector = BaseMonoid("vector")
  val matrix = BaseMonoid("matrix")
  val option = BaseMonoid("option")
  val bag = BaseMonoid("bag")
  def some ( x: Expr ) = Elem(option,x)

  def translate ( e: Expr, state: Expr, globals: Environment, locals: Environment ): Expr
    = DefaultTranslator.translate(e,state,globals,locals)

  def key ( d: Expr, state: Expr, globals: Environment, locals: Environment ): Expr
    = d match {
        case Var(v)
          => some(Tuple(Nil))
        case Project(u,_)
          => key(u,state,globals,locals)
        case Nth(u,_)
          => key(u,state,globals,locals)
        case VectorIndex(u,i)
          => val k = newvar
             val ii = newvar
             Comprehension(option,
                           Tuple(List(Var(k),Var(ii))),
                           List(Generator(VarPat(k),key(u,state,globals,locals)),
                                Generator(VarPat(ii),translate(i,state,globals,locals))))
        case MatrixIndex(u,i,j)
          => val k = newvar
             val ii = newvar
             val jj = newvar
             Comprehension(option,
                           Tuple(List(Var(k),Tuple(List(Var(ii),Var(jj))))),
                           List(Generator(VarPat(k),key(u,state,globals,locals)),
                                Generator(VarPat(ii),translate(i,state,globals,locals)),
                                Generator(VarPat(jj),translate(j,state,globals,locals))))
        case _ => throw new Error("Illegal destination: "+d)
      }

  def destination ( d: Expr, state: Expr, k: Expr ): Expr
    = d match {
        case Var(v)
          => val st = newvar
             Comprehension(option,
                           Project(Var(st),v),
                           List(Generator(VarPat(st),state)))
        case Project(u,_)
          => destination(u,state,k)
        case Nth(u,_)
          => destination(u,state,k)
        case VectorIndex(u,i)
          => val v = newvar
             val A = newvar
             val ii = newvar
             val ku = newvar
             val w = newvar
             Comprehension(option,
                           Var(v),
                           List(LetBinding(TuplePat(List(VarPat(ku),VarPat(w))),k),
                                Generator(VarPat(A),destination(u,state,Var(ku))),
                                Generator(TuplePat(List(VarPat(ii),VarPat(v))),
                                          Var(A)),
                                Predicate(Call("==",List(Var(ii),Var(w))))))
        case MatrixIndex(u,i,j)
          => val v = newvar
             val A = newvar
             val ii = newvar
             val jj = newvar
             val ku = newvar
             val w1 = newvar
             val w2 = newvar
             Comprehension(option,
                           Var(v),
                           List(LetBinding(TuplePat(List(VarPat(ku),TuplePat(List(VarPat(w1),VarPat(w2))))),k),
                                Generator(VarPat(A),destination(u,state,Var(ku))),
                                Generator(TuplePat(List(TuplePat(List(VarPat(ii),VarPat(jj))),VarPat(v))),
                                          Var(A)),
                                Predicate(Call("==",List(Var(ii),Var(w1)))),
                                Predicate(Call("==",List(Var(jj),Var(w2))))))
        case _ => throw new Error("Illegal destination: "+d)
      }

  def update ( dest: Expr, value: Expr, state: Expr, globals: Environment, locals: Environment ): Expr
    = dest match {
        case Var(n)
          if globals.contains(n)
          => val nv = newvar
             val st = newvar
             val k = newvar
             Comprehension(option,
                           Record(globals.map {
                               case (v,_)
                                 => v -> (if (v == n) Var(nv) else Project(Var(st),v))
                           }),
                           List(Generator(VarPat(st),state),
                                Generator(TuplePat(List(VarPat(k),VarPat(nv))),value)))
        case Var(n)
          if locals.contains(n)
          => throw new Error("Local variable "+n+" cannot be updated")
        case Var(n)
          => throw new Error("No such variable: "+n)
        case Project(u,a)
          => typecheck(u,globals,locals) match {
                case RecordType(cs)
                  => val nv = newvar
                     val k = newvar
                     update(u,
                            Comprehension(option,
                                          Tuple(List(Var(k),Record(cs.map {
                                              case (v,_)
                                                => v -> (if (v == a) Var(nv) else Project(Var(k),v))
                                          }))),
                                          List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value))),
                            state,globals,locals)
                case t => throw new Error("Record projection "+dest+" must be over a record (found "+t+")")
             }
        case Nth(u,n)
          => typecheck(u,globals,locals) match {
                case TupleType(cs)
                  => val nv = newvar
                     val k = newvar
                     update(u,
                            Comprehension(option,
                                          Tuple(List(Var(k),Tuple((1 to cs.length).map {
                                              i => if (i == n) Var(nv) else Nth(Var(k),i)
                                          }.toList))),
                                          List(Generator(TuplePat(List(VarPat(k),VarPat(nv))),value))),
                            state,globals,locals)
                case t => throw new Error("Tuple projection "+dest+" must be over a tuple (found "+t+")")
             }
        case VectorIndex(u,i)
          => val A = newvar
             val s = newvar
             val k = newvar
             val w = newvar
             val v = newvar
             update(u,Comprehension(option,
                                    Tuple(List(Var(k),Merge(Var(A),Elem(bag,Var(s))))),
                                    List(Generator(TuplePat(List(TuplePat(List(VarPat(k),VarPat(w))),
                                                                 VarPat(v))),
                                                   value),
                                         LetBinding(VarPat(s),Tuple(List(Var(w),Var(v)))),
                                         //GroupByQual(VarPat(k),Var(k)),
                                         Generator(VarPat(A),destination(u,state,Var(k))))),
                    state,globals,locals)
        case MatrixIndex(u,i,j)
          => val A = newvar
             val s = newvar
             val k = newvar
             val w1 = newvar
             val w2 = newvar
             val v = newvar
             update(u,Comprehension(option,
                                    Tuple(List(Var(k),Merge(Var(A),Elem(bag,Var(s))))),
                                    List(Generator(TuplePat(List(TuplePat(List(VarPat(k),
                                                                               TuplePat(List(VarPat(w1),VarPat(w2))))),
                                                                 VarPat(v))),
                                                   value),
                                         LetBinding(VarPat(s),Tuple(List(Tuple(List(Var(w1),Var(w2))),Var(v)))),
                                         //GroupByQual(VarPat(k),Var(k)),
                                         Generator(VarPat(A),destination(u,state,Var(k))))),
                    state,globals,locals)
        case _ => throw new Error("Illegal destination: "+dest)
    }

  def translate ( s: Stmt, state: Expr, quals: List[Qualifier], globals: Environment, locals: Environment ): Expr
    = s match {
          case Assign(d,Call(op,List(x,y)))
            if d == x && op == "+"
            => val v = newvar
               val k = newvar
               val w = newvar
               update(d,Comprehension(bag,
                                      Tuple(List(Var(k),Call(op,List(Var(w),reduce(BaseMonoid(op),Var(v)))))),
                                      quals++List(Generator(VarPat(v),translate(y,state,globals,locals)),
                                                  Generator(VarPat(k),key(d,state,globals,locals)),
                                                  GroupByQual(VarPat(k),Var(k)),
                                                  Generator(VarPat(w),destination(d,state,Var(k))))),
                      state,globals,locals)
          case Assign(d,e)
            => val v = newvar
               val k = newvar
               update(d,Comprehension(bag,
                                      Tuple(List(Var(k),Var(v))),
                                      quals++List(Generator(VarPat(v),translate(e,state,globals,locals)),
                                                  Generator(VarPat(k),key(d,state,globals,locals)))),
                      state,globals,locals)
          case Block(ss)
            => val (nstate,_,_) = ss.foldLeft(( state, globals, locals )) {
                    case ((ns,gs,ls),DeclareVal(v,t,e))
                      => ( DefaultTranslator.update(Var(v),translate(e,ns,gs,ls),ns,gs,ls),
                           gs, ls+((v,t)) )
                    case ((ns,gs,ls),DeclareVar(v,t,Var("null")))
                      => ( DefaultTranslator.update(Var(v),Elem(option,Undefined(t)),ns,gs+((v,t)),ls),
                           gs+((v,t)), ls )
                    case ((ns,gs,ls),DeclareVar(v,t,e))
                      => ( DefaultTranslator.update(Var(v),translate(e,ns,gs,ls),ns,gs+((v,t)),ls),
                           gs+((v,t)), ls )
                    case ((ns,gs,ls),stmt)
                      => ( translate(stmt,ns,quals,gs,ls),
                           gs, ls )
                    }
               nstate
          case ForeachS(v,e,b)
            => typecheck(e,globals,locals) match {
                  case ParametricType(_,List(tp))
                    => val A = newvar
                       val i = newvar
                       translate(b,state,
                                 quals++List(Generator(VarPat(A),
                                                       translate(e,state,globals,locals)),
                                             Generator(TuplePat(List(VarPat(i),VarPat(v))),Var(A))),
                                 globals,locals+((v,tp)))
                  case _ => throw new Error("Foreach statement must be over a collection: "+s)
               }
          case ForS(v,n1,n2,n3,b)
            => val nv = newvar
               translate(b,state,
                         quals++List(Generator(VarPat(nv),
                                               translate(Call("range",List(n1,n2,n3)),
                                                         state,globals,locals)),
                                     Generator(VarPat(v),Var(nv))),
                         globals,locals+((v,intType)))
          case IfS(p,te,ee)
            => val np = newvar
               val nv = newvar
               Comprehension(option,
                             Var(nv),
                             List(Generator(VarPat(np),translate(p,state,globals,locals)),
                                  Generator(VarPat(nv),
                                            IfE(Var(np),
                                                translate(te,state,quals,globals,locals),
                                                translate(ee,state,quals,globals,locals)))))
          case _ => throw new Error("Illegal statement: "+s)
    }

  def translate ( s: Stmt ): Expr
    = translate(s,some(Record(Map())),Nil,Map():Environment,Map():Environment)
}
