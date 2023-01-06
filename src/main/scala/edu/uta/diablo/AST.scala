/*
 * Copyright © 2020-2023 University of Texas at Arlington
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
package edu.uta.diablo

import scala.util.parsing.input.{Positional,Position,NoPosition}

sealed abstract class Type
    case class AnyType () extends Type
    case class TypeParameter ( name: String ) extends Type
    case class BasicType ( name: String ) extends Type
    case class TupleType ( components: List[Type] ) extends Type
    case class RecordType ( components: Map[String,Type] ) extends Type
    case class SeqType ( element: Type ) extends Type
    case class ArrayType ( dimension: Int, element: Type ) extends Type
    case class MapType ( key: Type, element: Type ) extends Type
    case class ParametricType ( name: String, components: List[Type] ) extends Type
    case class FunctionType ( domain: Type, target: Type ) extends Type
    // storage type based on a storage mapping with type params and args
    case class StorageType ( mapping: String, typeParams: List[Type], args: List[Expr] ) extends Type

sealed abstract class Pattern extends Positional
    case class TuplePat ( components: List[Pattern] ) extends Pattern
    case class VarPat ( name: String ) extends Pattern
    case class StarPat () extends Pattern

sealed abstract class Qualifier
    case class Generator ( pattern: Pattern, var domain: Expr ) extends Qualifier
    case class LetBinding ( pattern: Pattern, domain: Expr ) extends Qualifier
    case class Predicate ( predicate: Expr ) extends Qualifier
    case class GroupByQual ( pattern: Pattern, key: Expr ) extends Qualifier
    case class AssignQual ( dest: Expr, value: Expr ) extends Qualifier
    case class VarDef ( name: String, atype: Type, value: Expr ) extends Qualifier

case class Case ( pat: Pattern, condition: Expr, body: Expr )

sealed abstract class Expr ( var tpe: Type = null ) extends Positional
    case class Var ( name: String ) extends Expr
    case class Nth ( tuple: Expr, num: Int ) extends Expr
    case class Project ( record: Expr, attribute: String ) extends Expr
    case class Index ( vector: Expr, index: List[Expr] ) extends Expr
    case class MapAccess ( map: Expr, key: Expr ) extends Expr
    case class Lambda ( pattern: Pattern, body: Expr ) extends Expr
    case class flatMap ( function: Lambda, input: Expr ) extends Expr
    case class groupBy ( input: Expr ) extends Expr
    case class reduce ( op: String, input: Expr ) extends Expr
    case class Let ( pat: Pattern, value: Expr, body: Expr ) extends Expr
    case class Call ( var name: String, var args: List[Expr] ) extends Expr
    case class MethodCall ( obj: Expr, method: String, args: List[Expr] ) extends Expr
    case class Apply ( function: Expr, arg: Expr ) extends Expr
    case class Coerce ( arg: Expr, tp: Type ) extends Expr
    case class IfE ( predicate: Expr, thenp: Expr, elsep: Expr ) extends Expr
    case class Tuple ( args: List[Expr] ) extends Expr
    case class Record ( args: Map[String,Expr] ) extends Expr
    case class MatchE ( expr: Expr, cases: List[Case] ) extends Expr
    case class Seq ( args: List[Expr] ) extends Expr
    case class Range ( first: Expr, last: Expr, step: Expr ) extends Expr
    case class Comprehension ( head: Expr, qualifiers: List[Qualifier] ) extends Expr
    case class Merge ( left: Expr, right: Expr ) extends Expr
    case class Block ( args: List[Expr] ) extends Expr
    case class While ( predicate: Expr, body: Expr ) extends Expr
    case class Assign ( destination: Expr, value: Expr ) extends Expr
    case class VarDecl ( name: String, atype: Type, value: Expr ) extends Expr
    case class Def ( name: String, params: List[(String,Type)], rtype: Type, body: Expr ) extends Expr
    // store: storage of a value based on a storage mapping with type params and args
    case class Store ( var mapping: String, typeParams: List[Type], args: List[Expr], value: Expr ) extends Expr
    // view: implicit lifting of the domain of a generator in a comprehension
    case class Lift ( mapping: String, storage: Expr ) extends Expr
    case class StringConst ( value: String ) extends Expr {
         override def toString: String = "StringConst(\""+value+"\")"
    }
    case class CharConst ( value: Char ) extends Expr
    case class IntConst ( value: Int ) extends Expr
    case class LongConst ( value: Long ) extends Expr
    case class DoubleConst ( value: Double ) extends Expr
    case class BoolConst ( value: Boolean ) extends Expr

/* AST for imperative loop-based programs */
sealed abstract class Stmt extends Positional
    case class VarDeclS ( varname: String, vtype: Option[Type], value: Option[Expr] ) extends Stmt
    case class BlockS ( stmts: List[Stmt] ) extends Stmt
    case class AssignS ( destination: Expr, value: Expr ) extends Stmt
    case class ForS ( varname: String, from: Expr, to: Expr, step: Expr, body: Stmt ) extends Stmt
    case class ForeachS ( pat: Pattern, domain: Expr, body: Stmt ) extends Stmt
    case class WhileS ( predicate: Expr, body: Stmt ) extends Stmt
    case class IfS ( predicate: Expr, thenp: Stmt, elsep: Stmt ) extends Stmt
    case class DefS ( name: String, params: List[(String,Type)], rtype: Type, body: Stmt ) extends Stmt
    case class ReturnS ( value: Expr ) extends Stmt
    case class ExprS ( value: Expr ) extends Stmt
    // declare a new storage mapping as an isomorphism store <-> view
    case class TypeMapS ( typeName: String, typeParams: List[String], params: Map[String,Type],
                          abstractType: Type, storageType: Type, liftedType: Type,
                          store: Lambda, view: Lambda ) extends Stmt


object AST {

  private var count = 0

  /** return a fresh variable name */
  def newvar: String = { count = count+1; "_v"+count }

  /** apply f to every pattern in p */
  def apply ( p: Pattern, f: Pattern => Pattern ): Pattern =
    p match {
      case TuplePat(ps) => TuplePat(ps.map(f))
      case _ => p
    }

  def apply ( tp: Type, f: Type => Type ): Type =
    tp match {
      case TupleType(ts)
        => TupleType(ts.map(f))
      case RecordType(es)
        => RecordType(es.map{ case (n,v) => (n,f(v)) })
      case SeqType(t)
        => SeqType(f(t))
      case ArrayType(d,t)
        => ArrayType(d,f(t))
      case MapType(k,v)
        => MapType(f(k),f(v))
      case ParametricType(n,ts)
        => ParametricType(n,ts.map(f))
      case FunctionType(d,t)
        => FunctionType(f(d),f(t))
      case StorageType(m,ps,as)
        => StorageType(m,ps.map(f),as)
      case _ => tp
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
      case AssignQual(d,e)
        => AssignQual(f(d),f(e))
      case VarDef(n,t,e)
        => VarDef(n,t,f(e))
    }

  /** apply f to every expression in e */
  def apply ( e: Expr, f: Expr => Expr ): Expr =
    e match {
      case Nth(x,n)
        => Nth(f(x),n)
      case Project(x,n)
        => Project(f(x),n)
      case Index(b,s)
        => Index(f(b),s.map(f))
      case MapAccess(m,k)
        => MapAccess(f(m),f(k))
      case Lambda(p,b)
        => Lambda(p,f(b))
      case flatMap(Lambda(p,b),x)
        => flatMap(Lambda(p,f(b)),f(x))
      case groupBy(x)
        => groupBy(f(x))
      case reduce(op,x)
        => reduce(op,f(x))
      case Let(p,v,b)
        => Let(p,f(v),f(b))
      case Call(n,es)
        => Call(n,es.map(f))
      case MethodCall(o,m,null)
        => MethodCall(f(o),m,null)
      case MethodCall(o,m,es)
        => MethodCall(f(o),m,es.map(f))
      case Apply(h,a)
        => Apply(f(h),f(a))
      case Coerce(u,tp)
        => Coerce(f(u),tp)
      case IfE(p,x,y)
        => IfE(f(p),f(x),f(y))
      case MatchE(x,cs)
        => MatchE(f(x),cs.map{ case Case(p,c,b) => Case(p,f(c),f(b)) })
      case Tuple(es)
        => Tuple(es.map(f))
      case Record(es)
        => Record(es.map{ case (n,v) => (n,f(v)) })
      case Comprehension(h,qs)
        => Comprehension(f(h),qs.map(apply(_,f)))
      case Seq(es)
        => Seq(es.map(f))
      case Range(i,l,s)
        => Range(f(i),f(l),f(s))
      case Merge(x,y)
        => Merge(f(x),f(y))
      case Block(es)
        => Block(es.map(f))
      case VarDecl(v,at,u)
        => VarDecl(v,at,f(u))
      case Def(n,ps,tp,b)
        => Def(n,ps,tp,f(b))
      case Assign(d,u)
        => Assign(f(d),f(u))
      case While(p,u)
        => While(f(p),f(u))
      case Store(m,ts,as,o)
        => Store(m,ts,as.map(f),f(o))
      case Lift(m,v)
        => Lift(m,f(v))
      case _ => e
    }

  /** apply f to every statement in s */
  def apply ( s: Stmt, f: Stmt => Stmt ): Stmt =
    s match {
      case BlockS(l)
        => BlockS(l.map(f))
      case ForS(v,a,b,c,body)
        => ForS(v,a,b,c,f(body))
      case ForeachS(v,e,body)
        => ForeachS(v,e,f(body))
      case WhileS(c,body)
        => WhileS(c,f(body))
      case IfS(p,t,e)
        => IfS(p,f(t),f(e))
      case DefS(n,s,tp,b)
        => DefS(n,s,tp,f(b))
      case _ => s
    }

  /** fold over patterns */
  def accumulatePat[T] ( p: Pattern, f: Pattern => T, acc: (T,T) => T, zero: T ): T =
    p match {
      case TuplePat(ps)
        => ps.map(f).fold(zero)(acc)
      case _ => zero
    }

  /** fold over expressions */
  def accumulate[T] ( e: Expr, f: Expr => T, acc: (T,T) => T, zero: T ): T =
    e match {
      case Nth(x,_)
        => f(x)
      case Project(x,_)
        => f(x)
      case Index(b,s)
        => s.map(f).fold(f(b))(acc)
      case MapAccess(b,i)
        => acc(f(b),f(i))
      case Lambda(_,b)
        => f(b)
      case flatMap(g,x)
        => acc(f(g),f(x))
      case groupBy(x)
        => f(x)
      case reduce(_,x)
        => f(x)
      case Call(_,es)
        => es.map(f).fold(zero)(acc)
      case MethodCall(o,_,null)
        => f(o)
      case MethodCall(o,_,es)
        => es.map(f).fold(f(o))(acc)
      case Apply(h,a)
        => acc(f(h),f(a))
      case Coerce(u,tp)
        => f(u)
      case Let(_,v,b)
        => acc(f(v),f(b))
      case IfE(p,x,y)
        => acc(f(p),acc(f(x),f(y)))
      case MatchE(x,cs)
        => cs.map{ case Case(p,c,b) => acc(f(c),f(b)) }.fold(f(x))(acc)
      case Tuple(es)
        => es.map(f).fold(zero)(acc)
      case Record(es)
        => es.map{ case (_,v) => f(v) }.fold(zero)(acc)
      case Seq(es)
        => es.map(f).fold(zero)(acc)
      case Range(i,l,s)
        => acc(acc(f(i),f(l)),f(s))
      case Comprehension(h,qs)
        => qs.map{
              case Generator(_,u) => f(u)
              case LetBinding(_,u) => f(u)
              case Predicate(u) => f(u)
              case GroupByQual(_,k) => f(k)
              case AssignQual(d,u) => acc(f(d),f(u))
              case VarDef(_,_,u) => f(u)
           }.fold(f(h))(acc)
      case Merge(x,y)
        => acc(f(x),f(y))
      case Block(es)
        => es.map(f).fold(zero)(acc)
      case VarDecl(_,_,u)
        => f(u)
      case Def(n,ps,tp,b)
        => f(b)
      case Assign(d,u)
        => acc(f(d),f(u))
      case While(p,u)
        => acc(f(p),f(u))
      case Store(m,ts,as,o)
        => as.map(f).fold(f(o))(acc)
      case Lift(m,v)
        => f(v)
      case _ => zero
    }

  /** fold over statements */
  def accumulateStmt[T] ( s: Stmt, f: Expr => T, acc: (T,T) => T, zero: T ): T =
     s match {
      case BlockS(l)
        => l.map(accumulateStmt(_,f,acc,zero)).fold(zero)(acc)
      case ForS(v,a,b,c,body)
        => acc(f(a),acc(f(b),acc(f(c),
               accumulateStmt(body,f,acc,zero))))
      case ForeachS(v,e,body)
        => acc(f(e),accumulateStmt(body,f,acc,zero))
      case WhileS(c,body)
        => acc(f(c),accumulateStmt(body,f,acc,zero))
      case IfS(p,t,e)
        => acc(f(p),acc(accumulateStmt(t,f,acc,zero),
                        accumulateStmt(e,f,acc,zero)))
      case DefS(n,s,tp,b)
        => accumulateStmt(b,f,acc,zero)
      case AssignS(d,e)
        => acc(f(d),f(e))
      case ReturnS(e)
        => f(e)
      case ExprS(e)
        => f(e)
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
        => v == s
      case _ => accumulatePat[Boolean](p,capture(v,_),_||_,false)
    }

  def subst ( v: String, te: Expr, hd: Expr, qs: List[Qualifier] ): (Expr,List[Qualifier]) =
    qs match {
      case Nil
        => (subst(v,te,hd),Nil)
      case q::r
        => val (nhd,nqs) = subst(v,te,hd,r)
           q match {
              case Generator(p,u)
                => if (capture(v,p))
                      (hd,Generator(p,subst(v,te,u))::r)
                   else (nhd,Generator(p,subst(v,te,u))::nqs)
              case LetBinding(p,u)
                => if (capture(v,p))
                      (hd,LetBinding(p,subst(v,te,u))::r)
                   else (nhd,LetBinding(p,subst(v,te,u))::nqs)
              case GroupByQual(p,u)
                => if (capture(v,p))
                      (hd,GroupByQual(p,subst(v,te,u))::r)
                   else (nhd,GroupByQual(p,subst(v,te,u))::nqs)
              case Predicate(u)
                => (nhd,Predicate(subst(v,te,u))::nqs)
              case AssignQual(d,u)
                => (nhd,AssignQual(subst(v,te,d),subst(v,te,u))::nqs)
              case VarDef(w,t,u)
                => (nhd,VarDef(w,t,subst(v,te,u))::(if (v == w) r:+Predicate(hd) else nqs))
           }
    }

  /** beta reduction: substitute every occurrence of variable v in e with te */
  def subst ( v: String, te: Expr, e: Expr ): Expr =
    e match {
      case Var(s)
        => if (s == v) te else e
      case lp@Lambda(p,_)
        if capture(v,p)
        => lp
      case lp@Let(p,_,_)
        if capture(v,p)
        => lp
      case MatchE(expr,cs)
        => MatchE(subst(v,te,expr),
                  cs.map{ case cp@Case(p,c,b)
                            => if (capture(v,p)) cp
                               else Case(p,subst(v,te,c),subst(v,te,b)) })
      case Comprehension(h,qs)
        => val (nh,nqs) = subst(v,te,h,qs)
           Comprehension(nh,nqs)
      case _ => apply(e,subst(v,te,_))
    }

  /** substitute every occurrence of term 'from' in pattern p with 'to' */
  def subst ( from: String, to: String, p: Pattern ): Pattern =
    p match {
      case VarPat(s)
        if s == from
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
      case Lambda(p,_)
        if capture(v,p)
        => 0
      case Let(p,_,_)
        if capture(v,p)
        => 0
      case MatchE(expr,cs)
        => if (occurrences(v,expr) > 0)
              10  // if v gets pattern-matched, assume its components are used 10 times 
           else cs.map{ case Case(p,c,b)
                          => if (capture(v,p)) 0
                             else occurrences(v,c)+occurrences(v,b) }.sum
      case Comprehension(h,qs)
        => qs.foldLeft(occurrences(v,h)) {
              case (r,Generator(p,u))
                => occurrences(v,u) + (if (capture(v,p)) 0 else r)
              case (r,LetBinding(p,u))
                => occurrences(v,u) + (if (capture(v,p)) 0 else r)
              case (r,Predicate(u))
                => occurrences(v,u) + r
              case (r,GroupByQual(p,k))
                => occurrences(v,k) + (if (capture(v,p)) 0 else r)
              case (r,AssignQual(d,u))
                => occurrences(v,d) + occurrences(v,u) + r
              case (r,VarDef(w,t,u))
                => occurrences(v,u) + (if (v == w) 0 else r)
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
      case Lambda(p,b)
        => freevars(b,except++patvars(p))
      case flatMap(Lambda(p,b),x)
        => freevars(b,except++patvars(p))++freevars(x,except)
      case Let(p,v,b)
        => freevars(b,except++patvars(p))++freevars(v,except)
      case MatchE(expr,cs)
        => cs.map{ case Case(p,c,b)
                     => val pv = except++patvars(p)
                        freevars(b,pv)++freevars(c,pv)
                     }.fold(freevars(expr,except))(_++_)
      case Comprehension(h,qs)
        => val (fs,es) = qs.foldLeft[(List[String],List[String])]((Nil,except)) {
              case ((fl,el),Generator(p,u))
                => (fl++freevars(u,el),el++patvars(p))
              case ((fl,el),LetBinding(p,u))
                => (fl++freevars(u,el),el++patvars(p))
              case ((fl,el),Predicate(u))
                => (fl++freevars(u,el),el)
              case ((fl,el),GroupByQual(p,k))
                => (fl++freevars(k,el),el++patvars(p))
              case ((fl,el),AssignQual(d,u))
                => (fl++freevars(d,el)++freevars(u,el),el)
              case ((fl,el),VarDef(w,t,u))
                => (fl++freevars(u,el),el:+w)
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

  def getPos ( e: Expr ): Position = {
    val zero = NoPosition
    def max ( x: Position, y: Position ) = if (x<y) y else x
    accumulate[Position](e,getPos(_),max,zero)
  }

  def getPos ( e: Stmt ): Position = {
    val zero = NoPosition
    def max ( x: Position, y: Position ) = if (x<y) y else x
    accumulateStmt[Position](e,getPos(_),max,zero)
  }

  def setPositions ( e: Expr, pos: Position ): Unit = {
    val npos = if (e.pos == NoPosition) pos else e.pos
    e.pos = npos
    accumulate[Unit](e,setPositions(_,npos),(x:Unit,y:Unit)=>x,())
  }

  def setPositions ( e: Stmt, pos: Position ): Unit = {
    val npos = if (e.pos == NoPosition) pos else e.pos
    e.pos = npos
    accumulateStmt[Unit](e,setPositions(_,npos),(x:Unit,y:Unit)=>x,())
  }

  def setPos ( e: Expr, pos: Position ): Unit = {
    if (e.pos == NoPosition) {
      e.pos = pos
      accumulate[Unit](e,setPos(_,pos),(x:Unit,y:Unit)=>x,())
    }
  }

  def setPos ( e: Stmt, pos: Position ): Unit = {
    if (e.pos == NoPosition) {
      e.pos = pos
      accumulateStmt[Unit](e,setPos(_,pos),(x:Unit,y:Unit)=>x,())
    }
  }

  def setPos ( src: Expr, dst: Expr ): Expr = {
    if (src.pos != NoPosition)
      setPos(dst,src.pos)
    dst
  }

  def setPos ( src: Stmt, dst: Expr ): Expr = {
    if (src.pos != NoPosition)
      setPos(dst,src.pos)
    dst
  }

  def type2string ( tp: Type ): String
    = tp match {
      case StorageType(_,_,_)
        => type2string(Typechecker.unfold_storage_type(tp))
      case TupleType(List(t))
        => type2string(t)
      case TupleType(Nil)
        => "EmptyTuple"
      case TupleType(cs)
        => "("+cs.map(type2string).mkString(",")+")"
      case RecordType(cs) if cs.nonEmpty
        => "("+cs.values.map(type2string).toList.mkString(",")+")"
      case ParametricType(n,cs) if cs.nonEmpty
        => n+"["+cs.map(type2string).mkString(",")+"]"
      case ParametricType(n,Nil)
        => n
      case ArrayType(d,t)
        => (0 until d).foldLeft(type2string(t)) { case (r,_) => s"Array[$r]" }
      case MapType(k,v)
        => "Map["+type2string(k)+","+type2string(v)+"]"
      case SeqType(t)
        => "List["+type2string(t)+"]"
      case FunctionType(dt,rt)
        => type2string(dt)+"=>"+type2string(rt)
      case BasicType(n)
        => n
      case TypeParameter(v)
        => v
      case AnyType()
        => "Any"
      case _ => "Any"
    }

}
