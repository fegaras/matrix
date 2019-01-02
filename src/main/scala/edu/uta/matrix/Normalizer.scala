/*
 * Copyright © 2017 University of Texas at Arlington
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

object Normalizer {
  import AST._

  /** rename the variables in the lambda abstraction to prevent name capture */
  def renameVars ( f: Lambda ): Lambda =
    f match {
      case Lambda(p,b)
        => val m = patvars(p).map((_,newvar))
           Lambda(m.foldLeft(p){ case (r,(from,to)) => subst(from,to,r) },
                  m.foldLeft(b){ case (r,(from,to)) => subst(from,Var(to),r) })
    }

  /** normalize ASTs */
  def normalize ( e: Expr ): Expr =
    e match {
      case Apply(Lambda(VarPat(v),b),u)
        => normalize(subst(Var(v),u,b))
      case flatMap(f,flatMap(g,x))
        => renameVars(g) match {
             case Lambda(p,b)
               => normalize(flatMap(Lambda(p,flatMap(f,b)),x))
           }
      case flatMap(Lambda(_,_),Empty(m))
        => Empty(m)
      case flatMap(Lambda(p@VarPat(v),b),Elem(_,x))
        => normalize(if (occurrences(v,b) <= 1)
                        subst(Var(v),x,b)
                     else Let(p,x,b))
      case flatMap(Lambda(p,b),Elem(_,x))
        => normalize(Let(p,x,b))
      case flatMap(f,IfE(c,e1,e2))
        => normalize(IfE(c,flatMap(f,e1),flatMap(f,e2)))
      case groupBy(Empty(m))
        => Empty(m)
      case coGroup(x,Empty(m))
        => val nv = newvar
           val kv = newvar
           normalize(flatMap(Lambda(TuplePat(List(VarPat(kv),VarPat(nv))),
                                 Elem(m,Tuple(List(Var(kv),Tuple(List(Var(nv),Empty(m))))))),
                          groupBy(x)))
      case coGroup(Empty(m),x)
        => val nv = newvar
           val kv = newvar
           normalize(flatMap(Lambda(TuplePat(List(VarPat(kv),VarPat(nv))),
                                 Elem(m,Tuple(List(Var(kv),Tuple(List(Empty(m),Var(nv))))))),
                          groupBy(x)))
      case IfE(BoolConst(true),e1,_)
        => normalize(e1)
      case IfE(BoolConst(false),_,e2)
        => normalize(e2)
      case Call(a,List(Tuple(s)))
        => val pat = """_(\d+)""".r
           a match {
             case pat(x) if x.toInt <= s.length
               => normalize(s(x.toInt-1))
             case _ => Call(a,List(Tuple(s.map(normalize))))
           }
      case Call("!",List(Call("||",List(x,y))))
        => normalize(Call("&&",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("&&",List(x,y))))
        => normalize(Call("||",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("!",List(x))))
        => normalize(x)
      case Call("!",List(Call("!=",List(x,y))))
        => normalize(Call("==",List(x,y)))
      case Call("&&",List(BoolConst(b),x))
        => if (b) normalize(x) else BoolConst(false)
      case Call("&&",List(x,BoolConst(b)))
        => if (b) normalize(x) else BoolConst(false)
      case Call("||",List(BoolConst(b),x))
        => if (b) BoolConst(true) else normalize(x)
      case Call("||",List(x,BoolConst(b)))
        => if (b) BoolConst(true) else normalize(x)
      case Nth(Tuple(es),n)
        => normalize(es(n))
      case Project(Record(es),a)
        => normalize(es(a))
      case _ => apply(e,normalize)
    }

  def normalizeAll ( e: Expr ): Expr = {
    var olde = e
    var ne = olde
    do { olde = ne
         ne = normalize(ne)
       } while (olde != ne)
    ne
  }
}
