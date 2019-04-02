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

import scala.util.parsing.input.Positional

sealed abstract class Monoid
    case class BaseMonoid ( name: String ) extends Monoid
    case class ProductMonoid ( args: List[Monoid] ) extends Monoid
    case class ParametricMonoid ( name: String, parameter: Monoid ) extends Monoid

sealed abstract class Type
    case class AnyType () extends Type
    case class BasicType ( name: String ) extends Type
    case class TupleType ( components: List[Type] ) extends Type
    case class RecordType ( components: Map[String,Type] ) extends Type
    case class ParametricType ( name: String, components: List[Type] ) extends Type
    case class FunctionType ( domain: Type, target: Type ) extends Type

sealed abstract class Pattern
    case class TuplePat ( components: List[Pattern] ) extends Pattern
    case class VarPat ( name: String ) extends Pattern
    case class StarPat () extends Pattern

sealed abstract class Qualifier
    case class Generator ( pattern: Pattern, domain: Expr ) extends Qualifier
    case class LetBinding ( pattern: Pattern, domain: Expr ) extends Qualifier
    case class Predicate ( predicate: Expr ) extends Qualifier
    case class GroupByQual ( pattern: Pattern, key: Expr ) extends Qualifier
    case class OrderByQual ( key: Expr ) extends Qualifier

sealed abstract class Expr extends Positional
    case class Undefined ( tp: Type ) extends Expr
    case class Var ( name: String ) extends Expr
    case class Nth ( tuple: Expr, num: Int ) extends Expr
    case class Project ( record: Expr, attribute: String ) extends Expr
    case class VectorIndex ( vector: Expr, index: Expr ) extends Expr
    case class MatrixIndex ( matrix: Expr, row: Expr, column: Expr ) extends Expr
    case class flatMap ( function: Lambda, input: Expr ) extends Expr
    case class groupBy ( input: Expr ) extends Expr
    case class orderBy ( input: Expr ) extends Expr
    case class coGroup ( left: Expr, right: Expr ) extends Expr
    case class cross ( left: Expr, right: Expr ) extends Expr
    case class reduce ( monoid: Monoid, input: Expr ) extends Expr
    case class repeat ( function: Lambda, init: Expr, condition: Lambda, n: Expr ) extends Expr
    case class Lambda ( pattern: Pattern, body: Expr ) extends Expr
    case class TypedLambda ( args: List[(String,Type)], body: Expr ) extends Expr
    case class Let ( pat: Pattern, value: Expr, body: Expr ) extends Expr
    case class Call ( name: String, args: List[Expr] ) extends Expr
    case class Apply ( function: Expr, arg: Expr ) extends Expr
    case class IfE ( predicate: Expr, thenp: Expr, elsep: Expr ) extends Expr
    case class Tuple ( args: List[Expr] ) extends Expr
    case class Record ( args: Map[String,Expr] ) extends Expr
    case class Collection ( kind: String, args: List[Expr] ) extends Expr
    case class Comprehension ( monoid: Monoid, head: Expr, qualifiers: List[Qualifier] ) extends Expr
    case class Empty ( m: Monoid ) extends Expr
    case class Elem ( m: Monoid, elem: Expr ) extends Expr
    case class Merge ( left: Expr, right: Expr ) extends Expr
    case class StringConst ( value: String ) extends Expr {
         override def toString: String = "StringConst(\""+value+"\")"
    }
    case class CharConst ( value: Char ) extends Expr
    case class IntConst ( value: Int ) extends Expr
    case class LongConst ( value: Long ) extends Expr
    case class DoubleConst ( value: Double ) extends Expr
    case class BoolConst ( value: Boolean ) extends Expr

sealed abstract class Stmt extends Positional
    case class DeclareVal ( varname: String, vartype: Type, value: Expr ) extends Stmt
    case class DeclareVar ( varname: String, vartype: Type, value: Expr ) extends Stmt
    case class Block ( stmts: List[Stmt] ) extends Stmt
    case class Assign ( destination: Expr, value: Expr ) extends Stmt
    case class ForS ( varname: String, from: Expr, to: Expr, step: Expr, body: Stmt ) extends Stmt
    case class ForeachS ( varname: String, domain: Expr, body: Stmt ) extends Stmt
    case class IfS ( predicate: Expr, thenp: Stmt, elsep: Stmt ) extends Stmt


object AST {

  private var count = 0

  /** return a fresh variable name */
  def newvar: String = { count = count+1; "v"+count }

  /** apply f to every pattern in p */
  def apply ( p: Pattern, f: Pattern => Pattern ): Pattern =
    p match {
      case TuplePat(ps) => TuplePat(ps.map(f(_)))
      case _ => p
    }

  def apply ( q: Qualifier, f: Expr => Expr ): Qualifier =
    q match {
      case Generator(p,e)
        => Generator(p,f(e))
      case LetBinding(p,e)
        => LetBinding(p,f(e))
      case Predicate(e)
        => Predicate(f(e))
      case GroupByQual(p,k)
        => GroupByQual(p,f(k))
      case OrderByQual(k)
        => OrderByQual(f(k))
    }

  /** apply f to every expression in e */
  def apply ( e: Expr, f: Expr => Expr ): Expr =
    e match {
      case Nth(x,n)
        => Nth(f(x),n)
      case Project(x,n)
        => Project(f(x),n)
      case VectorIndex(b,i)
        => VectorIndex(f(b),f(i))
      case MatrixIndex(b,i,j)
        => MatrixIndex(f(b),f(i),f(j))
      case flatMap(Lambda(p,b),x)
        => flatMap(Lambda(p,f(b)),f(x))
      case groupBy(x)
        => groupBy(f(x))
      case orderBy(x)
        => orderBy(f(x))
      case coGroup(x,y)
        => coGroup(f(x),f(y))
      case cross(x,y)
        => cross(f(x),f(y))
      case reduce(m,x)
        => reduce(m,f(x))
      case repeat(Lambda(p,b),x,Lambda(pp,w),n)
        => repeat(Lambda(p,f(b)),f(x),Lambda(pp,f(w)),f(n))
      case Lambda(p,b)
        => Lambda(p,f(b))
      case TypedLambda(args,b)
        => TypedLambda(args,f(b))
      case Call(n,es)
        => Call(n,es.map(f(_)))
      case Apply(h,a)
        => Apply(f(h),f(a))
      case Let(p,v,b)
        => Let(p,f(v),f(b))
      case IfE(p,x,y)
        => IfE(f(p),f(x),f(y))
      case Tuple(es)
        => Tuple(es.map(f(_)))
      case Record(es)
        => Record(es.map{ case (n,v) => (n,f(v)) })
      case Collection(k,es)
        => Collection(k,es.map(f(_)))
      case Comprehension(m,h,qs)
        => Comprehension(m,f(h),qs.map(apply(_,f)))
      case Elem(m,x)
        => Elem(m,f(x))
      case Merge(x,y)
        => Merge(f(x),f(y))
      case _ => e
    }

  /** apply f to every statement in s */
  def apply ( s: Stmt, f: Stmt => Stmt ): Stmt =
    s match {
      case Block(l)
        => Block(l.map(f(_)))
      case ForS(v,a,b,c,body)
        => ForS(v,a,b,c,f(body))
      case ForeachS(v,e,body)
        => ForeachS(v,e,f(body))
      case IfS(p,t,e)
        => IfS(p,f(t),f(e))
      case _ => s
    }

  /** fold over patterns */
  def accumulatePat[T] ( p: Pattern, f: Pattern => T, acc: (T,T) => T, zero: T ): T =
    p match {
      case TuplePat(ps)
        => ps.map(f(_)).fold(zero)(acc)
      case _ => zero
    }

  /** fold over expressions */
  def accumulate[T] ( e: Expr, f: Expr => T, acc: (T,T) => T, zero: T ): T =
    e match {
      case Nth(x,_)
        => f(x)
      case Project(x,_)
        => f(x)
      case VectorIndex(b,i)
        => acc(f(b),f(i))
      case MatrixIndex(b,i,j)
        => acc(f(b),acc(f(i),f(j)))
      case flatMap(b,x)
        => acc(f(b),f(x))
      case groupBy(x)
        => f(x)
      case orderBy(x)
        => f(x)
      case coGroup(x,y)
        => acc(f(x),f(y))
      case cross(x,y)
        => acc(f(x),f(y))
      case reduce(_,x)
        => f(x)
      case repeat(b,x,w,n)
        => acc(acc(f(b),acc(f(w),f(x))),f(n))
      case Lambda(_,b)
        => f(b)
      case TypedLambda(_,b)
        => f(b)
      case Call(_,es)
        => es.map(f(_)).fold(zero)(acc)
      case Apply(h,a)
        => acc(f(h),f(a))
      case Let(_,v,b)
        => acc(f(v),f(b))
      case IfE(p,x,y)
        => acc(f(p),acc(f(x),f(y)))
      case Tuple(es)
        => es.map(f(_)).fold(zero)(acc)
      case Record(es)
        => es.map{ case (_,v) => f(v) }.fold(zero)(acc)
      case Collection(_,es)
        => es.map(f(_)).fold(zero)(acc)
      case Comprehension(_,h,qs)
        => acc(f(h),qs.map{
              case Generator(_,u) => f(u)
              case LetBinding(_,u) => f(u)
              case Predicate(u) => f(u)
              case GroupByQual(_,k) => f(k)
              case OrderByQual(k) => f(k)
           }.reduce(acc))
      case Elem(_,x)
        => f(x)
      case Merge(x,y)
        => acc(f(x),f(y))
      case _ => zero
    }

  /** return the list of all variables in the pattern p */
  def patvars ( p: Pattern ): List[String] = 
    p match {
      case VarPat(s)
        => List(s)
      case _ => accumulatePat[List[String]](p,patvars,_++_,Nil)
    }

  /** true if the variable v is captured in the pattern p */
  def capture ( v: String, p: Pattern ): Boolean =
    p match {
      case VarPat(s)
        => v==s
      case _ => accumulatePat[Boolean](p,capture(v,_),_||_,false)
    }

  def subst ( v: String, te: Expr, qs: List[Qualifier] ): List[Qualifier] =
    qs match {
      case Nil => Nil
      case Generator(p,u)::r
        => Generator(p,subst(v,te,u))::(if (capture(v,p)) r else subst(v,te,r))
      case LetBinding(p,u)::r
        => LetBinding(p,subst(v,te,u))::(if (capture(v,p)) r else subst(v,te,r))
      case Predicate(u)::r
        => Predicate(subst(v,te,u))::subst(v,te,r)
      case GroupByQual(p,k)::r
        => GroupByQual(p,subst(v,te,k))::(if (capture(v,p)) r else subst(v,te,r))
      case OrderByQual(k)::r
        => OrderByQual(subst(v,te,k))::subst(v,te,r)
    }

  /** beta reduction: substitute every occurrence of variable v in e with te */
  def subst ( v: String, te: Expr, e: Expr ): Expr =
    e match {
      case Var(s)
        => if (s==v) te else e
      case flatMap(Lambda(p,b),x)
        if capture(v,p)
        => flatMap(Lambda(p,b),subst(v,te,x))
      case lp@Lambda(p,_)
        if capture(v,p)
        => lp
      case lp@TypedLambda(args,_)
        if args.map(x => capture(v,VarPat(x._1))).reduce(_||_)
        => lp
      case lp@Let(p,_,_)
        if capture(v,p)
        => lp
      case Comprehension(m,h,qs)
        => Comprehension(m,subst(v,te,h),subst(v,te,qs))
      case _ => apply(e,subst(v,te,_))
    }

  /** substitute every occurrence of term 'from' in pattern p with 'to' */
  def subst ( from: String, to: String, p: Pattern ): Pattern =
    p match {
      case VarPat(s)
        if s==from
        => VarPat(to)
      case _ => apply(p,subst(from,to,_))
  }

  /** substitute every occurrence of the term 'from' in e with 'to' */
  def subst ( from: Expr, to: Expr, e: Expr ): Expr =
    if (e == from) to else apply(e,subst(from,to,_))

  /** number of times the variable v is accessed in e */
  def occurrences ( v: String, e: Expr ): Int =
    e match {
      case Var(s)
        => if (s==v) 1 else 0
      case flatMap(Lambda(p,_),x)
        if capture(v,p)
        => occurrences(v,x)
      case repeat(f,init,p,n)   // assume loop is executed 10 times
        => occurrences(v,f)*10+occurrences(v,init)+occurrences(v,n)+occurrences(v,p)*10
      case Lambda(p,_)
        if capture(v,p)
        => 0
      case TypedLambda(args,_)
        if args.map(x => capture(v,VarPat(x._1))).reduce(_||_)
        => 0
      case Let(p,_,_)
        if capture(v,p)
        => 0
      case Comprehension(_,h,qs)
        => qs.foldLeft(occurrences(v,h)) {
              case (r,Generator(p,u))
                => occurrences(v,u) + (if (capture(v,p)) 0 else r)
              case (r,LetBinding(p,u))
                => occurrences(v,u) + (if (capture(v,p)) 0 else r)
              case (r,Predicate(u))
                => occurrences(v,u) + r
              case (r,GroupByQual(p,k))
                => occurrences(v,k) + (if (capture(v,p)) 0 else r)
              case (r,OrderByQual(k))
                => occurrences(v,k) + r
           }
      case _ => accumulate[Int](e,occurrences(v,_),_+_,0)
    }

  /** number of times the variables in vs are accessed in e */
  def occurrences ( vs: List[String], e: Expr ): Int
    = vs.map(occurrences(_,e)).sum

  /** return the list of free variables in e that do not appear in except */
  def freevars ( e: Expr, except: List[String] ): List[String] =
    e match {
      case Var(s)
        => if (except.contains(s)) Nil else List(s)
      case flatMap(Lambda(p,b),x)
        => freevars(b,except++patvars(p))++freevars(x,except)
      case Lambda(p,b)
        => freevars(b,except++patvars(p))
      case TypedLambda(args,b)
        => freevars(b,except++args.map(_._1))
      case Let(p,v,b)
        => freevars(b,except++patvars(p))++freevars(v,except)
      case Comprehension(_,h,qs)
        => val (fs,es) = qs.foldLeft[(List[String],List[String])]((Nil,except)) {
              case ((fl,el),Generator(p,u))
                => (fl++freevars(u,el),el++patvars(p))
              case ((fl,el),LetBinding(p,u))
                => (fl++freevars(u,el),el++patvars(p))
              case ((fl,el),Predicate(u))
                => (fl++freevars(u,el),el)
              case ((fl,el),GroupByQual(p,k))
                => (fl++freevars(k,el),el++patvars(p))
              case ((fl,el),OrderByQual(k))
                => (fl++freevars(k,el),el)
           }
           fs++freevars(h,es)
      case _ => accumulate[List[String]](e,freevars(_,except),_++_,Nil)
    }

  /** return the list of free variables in e */
  def freevars ( e: Expr ): List[String] = freevars(e,Nil)

  /** Convert a pattern to an expression */
  def toExpr ( p: Pattern ): Expr
      = p match {
        case TuplePat(ps)
          => Tuple(ps.map(toExpr))
        case VarPat(n)
          => Var(n)
        case _ => Tuple(Nil)
      }
}
