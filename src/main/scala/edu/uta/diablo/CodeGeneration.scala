/*
 * Copyright © 2020 University of Texas at Arlington
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

import scala.reflect.macros.whitebox.Context
import scala.reflect.macros.TypecheckException
import scala.language.experimental.macros
import java.io._


abstract class CodeGeneration {
  val c: Context
  import c.universe.{Expr=>_,Block=>_,Apply=>_,Assign=>_,Return=>_,_}
  import AST._
  import edu.uta.diablo.{Type=>DType}

  var line: Int = 0

  /** contains bindings from patterns to Scala types */
  type Environment = List[(c.Tree,c.Tree)]

  /** add a new binding from a pattern to a Scala type in the Environment */
  def add ( p: Pattern, tp: c.Tree, env: Environment ): Environment
    = (code(p),tp)::env

  val char_maps = Map( '+' -> "plus", '-' -> "minus", '*' -> "times", '/' -> "div", '%' -> "percent",
                       '|' -> "bar", '&' -> "amp", '!' -> "bang", '^' -> "up", '~' -> "tilde",
                       '=' -> "eq", '<' -> "less", '>' -> "greater", ':' -> "colon", '?' -> "qmark",
                       '\\' -> "bslash" )

  /** Scala translates special chars in method names to $names */
  def method_name ( n: String ): String =
    n.foldLeft("") {
      case (r,d)
        => r+(char_maps.get(d) match {
                        case Some(s) => '$'+s
                        case _ => d
                      })
    }

  /** Return the range type of functionals */
  def returned_type ( tp: c.Tree ): c.Tree
    = tp match {
         case tq"$d => $r"
           => returned_type(r)
         case _ => tp
      }
  
  /** convert a Type to a Tree. There must be a better way to do this */
  def type2tree ( tp: c.Type ): c.Tree = {
    val ntp = if (tp <:< c.typeOf[AnyVal]) tp.toString.split('(')(0) else tp
    val Typed(_,etp) = c.parse("x:("+ntp+")")
    etp
  }

  def Tree2Type ( tp: c.Tree ): DType =
    tp match {
      case tq"(..$cs)" if cs.length > 1
        => TupleType(cs.map(Tree2Type))
      case tq"$n[..$cs]" if cs.nonEmpty
        => ParametricType(n.toString,cs.map(Tree2Type))
      case _
        => BasicType(tp.toString)
    }

  def get_type_name ( name: String ): c.Tree
    = name.split('.').toList match {
            case List(m)
              => tq"${TypeName(m)}"
            case (m::s):+n
              => Select(s.foldLeft[c.Tree](Ident(TermName(m))) {
                                case (r,m) => Select(r,TermName(m))
                              },
                        TypeName(n))
            case _ => tq""
           }

  def Type2Tree ( tp: DType ): c.Tree =
    tp match {
      case TupleType(cs) if cs.nonEmpty
        => val tcs = cs.map(Type2Tree)
           tq"(..$tcs)"
      case ParametricType(n,cs) if cs.nonEmpty
        => val tcs = cs.map(Type2Tree)
           val tn = get_type_name(n)
           tq"$tn[..$tcs]"
      case ParametricType(n,Nil)
        => val tn = get_type_name(n)
           tq"$tn"
      case ArrayType(d,t)
        => (0 to d).foldLeft(Type2Tree(t)) { case (r,_) => tq"Array[$r]" }
      case MapType(k,v)
        => val kc = Type2Tree(k)
           val vc = Type2Tree(v)
           tq"Map[$kc,$vc]"
      case SeqType(t)
        => val tc = Type2Tree(t)
           tq"List[$tc]"
      case BasicType(n)
        => get_type_name(n)
      case _ => tq""
    }

  /** Return the type of Scala code, if exists
   *  @param code Scala code
   *  @param env an environment that maps patterns to types
   *  @return the type of code, if the code is typechecked without errors
   */
  def getOptionalType ( code: c.Tree, env: Environment ): Either[c.Tree,TypecheckException] = {
    val cc = var_decls.foldLeft(code){ case (r,(v,vt))
                                         => val vc = TermName(v)
                                            q"($vc:$vt) => $r" }
    val fc = env.foldLeft(cc){ case (r,(p,tq"Any"))
                                 => q"{ case $p => $r }"
                               case (r,(p,tp))
                                 => val nv = TermName(c.freshName("x"))
                                    q"($nv:$tp) => $nv match { case $p => $r }" }
    val te = try c.Expr[Any](c.typecheck(q"{ import edu.uta.diablo._; $fc }")).actualType
             catch { case ex: TypecheckException
                       => //println("@@@ "+code+" "+env+" "+fc)
                          return Right(ex)
                   }
    Left(returned_type(type2tree(te)))
  }

  /** Return the type of Scala code
   *  @param code Scala code
   *  @param env an environment that maps patterns to types
   *  @return the type of code
   */
  def getType ( code: c.Tree, env: Environment ): c.Tree = {
    getOptionalType(code,env) match {
      case Left(tp) => tp
      case Right(ex)
        => println(s"Typechecking error at line $line: ${ex.msg}")
           println("Code: "+code)
           println("Var Decls: "+var_decls)
           println("Bindings: "+env)
           val sw = new StringWriter
           ex.printStackTrace(new PrintWriter(sw))
           println(sw.toString)
           c.abort(c.universe.NoPosition,s"Typechecking error at line $line: ${ex.msg}")
    }
  }

  /** Typecheck the query using the Scala's typechecker */
  def typecheck ( e: Expr, env: Environment = List() ): c.Tree
    = getType(codeGen(e,env),env)

  /** Typecheck the query using the Scala's typechecker */
  def typecheckOpt ( e: Expr, env: Environment = List() ): Option[c.Tree]
    = getOptionalType(codeGen(e,env),env) match {
        case Left(tp) => Some(tp)
        case _ => None
    }

  /** Return the result type of a function using the Scala's typechecker */
  def typecheck_call ( f: String, args: List[DType] ): Option[DType] = {
    val vs = args.zipWithIndex.map{ case (_,i) => "x"+i }
    val env: Environment
          = vs.zip(args).map{ case (v,t) => (code(VarPat(v)),Type2Tree(t)) }.toList
    typecheckOpt(Call(f,vs.map(Var(_))),env).map(Tree2Type(_))
  }

  /** Return the result type of a method using the Scala's typechecker */
  def typecheck_method ( o: DType, m: String, args: List[DType] ): Option[DType] = {
    if (args == null)
       typecheckOpt(MethodCall(Var("x"),m,null),
                    List((code(VarPat("x")),Type2Tree(o)))).map(Tree2Type(_))
    else {
      val vs = args.zipWithIndex.map{ case (_,i) => "x"+i }
      val vo = "x"
      val env: Environment
          = (code(VarPat("x")),Type2Tree(o))::
               vs.zip(args).map{ case (v,t) => (code(VarPat(v)),Type2Tree(t)) }.toList
      typecheckOpt(MethodCall(Var("x"),m,vs.map(Var(_))),env).map(Tree2Type(_))
    }
  }

  /** For a collection ec, return the element type */
  def typedCodeOpt ( ec: c.Tree, env: Environment ): Option[c.Tree]
    = getOptionalType(ec,env) match {
        case Left(atp)
          => try {
                val ctp = c.Expr[Any](c.typecheck(q"(x:$atp) => x.head")).actualType
                Some(returned_type(type2tree(ctp)))
             } catch { case ex: TypecheckException
                         => try {
                               val ctp = c.Expr[Any](c.typecheck(q"(x:$atp) => x.first()")).actualType
                               Some(returned_type(type2tree(ctp)))
                            } catch { case ex: TypecheckException
                                 => return None }
                     }
        case Right(ex) => None
      }

  /** For a collection e, return the element type and the code of e */
  def typedCode ( e: Expr, env: Environment ): (c.Tree,c.Tree) = {
    val ec = codeGen(e,env)
    typedCodeOpt(ec,env) match {
      case Some(v) => (v,ec)
      case _ => c.abort(c.universe.NoPosition,
                        s"Expression $ec is not a collection (line $line)")
    }
  }

  /** Translate a Pattern to a Scala pattern */
  def code ( p: Pattern ): c.Tree = {
    import c.universe._
    p match {
      case TuplePat(ps)
        => val psc = ps.map(code)
           pq"(..$psc)"
      case VarPat(v)
        => val tv = TermName(v)
           pq"$tv"
      case _ => pq"_"
    }
  }

  /** Is this pattern irrefutable (always matches)? */
  def irrefutable ( p: Pattern ): Boolean = true

  /** Eta expansion for method and constructor argument list to remove the placeholder syntax
   *  e.g., _+_ is expanded to (x,y) => x+y
   */
  def codeList ( es: List[Expr], f: List[c.Tree] => c.Tree, env: Environment ): c.Tree = {
    val n = es.map{ case Var("_") => 1; case _ => 0 }.sum
    if (n == 0)
       return f(es.map(codeGen(_,env)))
    val ns = es.map{ case Var("_") => val nv = TermName(c.freshName("x"))
                                      (nv,q"$nv":c.Tree)
                     case e => (null,codeGen(e,env)) }
    val tpt = tq""  // empty type
    val vs = ns.flatMap{ case (null,_) => Nil; case (v,_) => List(q"val $v: $tpt") }
    val ne = f(ns.map(_._2))
    q"(..$vs) => $ne"
  }

  var var_decls = collection.mutable.Map[String,c.Tree]()

  def element_type ( tp: c.Tree ): c.Tree
    = tp match {
        case tq"Array[$atp]"
          => element_type(atp)
        case _ => tp
      }

  def set_element_type ( tp: c.Tree, etp: c.Tree ): c.Tree
    = tp match {
        case tq"Array[$atp]"
          => val ntp = set_element_type(atp,etp)
             tq"Array[$ntp]"
        case _ => etp
      }

  def mapAccess ( x: Expr, i: Expr, env: Environment ): c.Tree = {
    val xc = codeGen(x,env)
    val ic = codeGen(i,env)
    (getOptionalType(xc,env),ic,getOptionalType(ic,env)) match {
      case (Left(tq"edu.uta.diablo.Matrix"),q"($i,$j)",_)
        => q"$xc($i,$j)"
      case (Left(tq"Array[$t]"),q"(..$is)",_)
        => is.foldLeft[c.Tree](xc) { case (r,n) => q"$r($n)" }
      case (Left(tq"Array[$t]"),_,Left(tq"(..$its)"))
        if its.length > 1
        => val as = (1 to its.length).foldLeft[c.Tree](xc) {
                          case (r,n) => val v = TermName("_"+n); q"$r(k.$v)"
                    }
           q"{ val k = $ic; $as }"
      case _ => q"$xc($ic)"
    }
  }

  /** Generate Scala code for expressions */
  def codeGen ( e: Expr, env: Environment ): c.Tree = {
    e match {
      case flatMap(Lambda(p,Seq(List(b))),x)
        if toExpr(p) == b
        => codeGen(x,env)
      case flatMap(Lambda(p,Seq(List(b))),x)
        if irrefutable(p)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.map(($nv:$tp) => $nv match { case $pc => $bc })"
      case flatMap(Lambda(p,b),x)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           if (irrefutable(p))
              q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc })"
           else q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc; case _ => Nil })"
      case MethodCall(x,"reduceByKey",List(Lambda(p,b)))
        => val (tp,xc) = typedCode(x,env)
           val pc = code(p)
           tp match {
             case tq"($kt,$et)"
               => val bc = codeGen(b,add(p,tq"($et,$et)",env))
                  q"$xc.reduceByKey{ case $pc => $bc }"
             case _ => throw new Exception("Wrong reduceByKey: "+e)
           }
      case groupBy(x)
        => val xc = codeGen(x,env)
           q"$xc.groupBy(_._1).mapValues( _.map(_._2))"
      case reduce(m,x)
        => val xc = codeGen(x,env)
           val fnc = TermName(method_name(m))
           q"$xc.reduce(_ $fnc _)"
      case Nth(x,n)
        => val xc = codeGen(x,env)
           val nc = TermName("_"+n)
           q"$xc.$nc"
      case Index(u,is)
        => val uc = codeGen(u,env)
           val isc = is.map(i => codeGen(i,env))
           isc.foldLeft(uc){ case (r,i) => q"$r($i)" }
      case Tuple(es)
        => codeList(es,cs => q"(..$cs)",env)
      case Call("map",Nil)
        => q"scala.collection.mutable.Map[Any,Any]()"
      case Call("array",d)
        => val dc = d.map(codeGen(_,env))
           q"Array.ofDim[Any](..$dc)"
      case Call("matrix",List(n,m))
        => val nc = codeGen(n,env)
           val mc = codeGen(m,env)
           q"Matrix($nc,$mc)"
      case Call("tile",Nil)
        => val ts = tileSize*tileSize
           q"Array.ofDim[Any]($ts)"
      case Call(n,es)
        => val fm = TermName(method_name(n))
           codeList(es,cs => q"$fm(..$cs)",env)
      case MethodCall(Var("_"),m,null)
        => val nv = TermName(c.freshName("x"))
           val fm = TermName(method_name(m))
           val tpt = tq""  // empty type
           val p = q"val $nv: $tpt"
           q"($p) => $nv.$fm"
      case MethodCall(x,m,null)
        if m.length == 1 && char_maps.contains(m(0))
        => val xc = codeGen(x,env)
           val fm = TermName("unary_"+method_name(m))
           q"$xc.$fm"
      case MethodCall(x,m,null)
        => val xc = codeGen(x,env)
           val fm = TermName(method_name(m))
           q"$xc.$fm"
      case MethodCall(x@MapAccess(Var(v),k),"=",List(y))
        => val yc = codeGen(y,env)
           val ty = getType(yc,env)
           getType(codeGen(Var(v),env),env) match {
             case tq"scala.collection.mutable.Map[Any,Any]"
               => val tk = typecheck(k,env)
                  var_decls += ((v,tq"Map[$tk,$ty]"))
             case tp
               => element_type(tp) match {
                     case tq"Any"
                       => var_decls += ((v,set_element_type(tp,ty)))
                     case _ => ;
                  }
           }
           val xc = codeGen(x,env)   // must be last
           q"$xc = $yc"
      case MethodCall(Tuple(xs),"=",List(y))
        => val yc = codeGen(y,env)  // y must be first to setup var_decls
           val v = TermName(c.freshName("x"))
           val xc = xs.zipWithIndex.map {
                      case (x,n)
                        => val xc = codeGen(x,env)
                           val nc = TermName("_"+(n+1))
                           q"$xc = $v.$nc"
                   }
           q"{ val $v = $yc; ..$xc }"
      case MethodCall(x,"=",List(y))
        => val yc = codeGen(y,env)  // y must be first to setup var_decls
           val xc = codeGen(x,env)
           q"$xc = $yc"
      case MethodCall(x@MapAccess(Var(v),k),m,List(y))
        => val z = if (m==":+") Seq(List(y)) else y
           val yc = codeGen(y,env)
           getType(codeGen(Var(v),env),env) match {
             case tq"scala.collection.mutable.Map[Any,Any]"
               => val tk = typecheck(k,env)
                  val tz = typecheck(z,env)
                  var_decls += ((v,tq"Map[$tk,$tz]"))
             case tp
               => element_type(tp) match {
                     case tq"Any"
                       => var_decls += ((v,set_element_type(tp,typecheck(z,env))))
                     case _ => ;
                  }
           }
           val xc = codeGen(x,env)   // must be last
           val fm = TermName(method_name(m))
           q"$xc.$fm($yc)"
      case Apply(f,x)
        => val fc = codeGen(f,env)
           val xc = codeGen(x,env)
           q"$fc($xc)"
      case MethodCall(x,m,es)
        => val fm = TermName(method_name(m))
           codeList(x+:es,{ case cx+:cs => q"$cx.$fm(..$cs)" },env)
      case MapAccess(v,k)
        => mapAccess(v,k,env)
      case Seq(Nil)
        => q"Nil"
      case Seq(s)
        => val sc = s.map(codeGen(_,env))
           q"List(..$sc)"
      case IfE(p,x,y)
        => val pc = codeGen(p,env)
           val xc = codeGen(x,env)
           val yc = codeGen(y,env)
           q"if ($pc) $xc else $yc"
      case MatchE(x,List(Case(VarPat(v),BoolConst(true),b)))
        if occurrences(v,b) == 1
        => codeGen(subst(v,x,b),env)
      case MatchE(x,List(Case(p@VarPat(v),BoolConst(true),b)))
        => val xc = codeGen(x,env)
           val pc = TermName(v)
           val tp = getType(xc,env)
           typedCodeOpt(xc,env) match {
                case Some(_)
                  => val nv = Var(v)
                     val bc = codeGen(subst(Var(v),nv,b),add(p,tp,env))
                     return q"{ val $pc:$tp = $xc; $bc }"
                case None =>
           } 
           val bc = codeGen(b,add(p,tp,env))
           q"{ val $pc:$tp = $xc; $bc }"
      case MatchE(x,List(Case(p,BoolConst(true),b)))
        if irrefutable(p)
        => val xc = codeGen(x,env)
           val tp = getType(xc,env)
           val pc = code(p)
           val bc = codeGen(b,add(p,tp,env))
           q"{ val $pc:$tp = $xc; $bc }"
      case MatchE(x,cs)
        => val xc = codeGen(x,env)
           val tp = getType(xc,env)
           val cases = cs.map{ case Case(p,BoolConst(true),b)
                                 => val pc = code(p)
                                    val bc = codeGen(b,add(p,tp,env))
                                    cq"$pc => $bc"
                               case Case(p,n,b)
                                 => val pc = code(p)
                                    val nc = codeGen(n,env)
                                    val bc = codeGen(b,add(p,tp,env))
                                    cq"$pc if $nc => $bc"
                             }
           q"($xc:$tp) match { case ..$cases }"
      case Lambda(p@VarPat(v),b)
        => val tpt = tq""  // empty type
           val vc = TermName(v)
           val bc = codeGen(b,add(p,tpt,env))
           val pp = q"val $vc: $tpt"
           q"($pp) => $bc"
      case Lambda(p,b)
        => val tpt = tq""  // empty type
           val pc = code(p)
           val bc = codeGen(b,add(p,tpt,env))
           q"{ case $pc => $bc }"
      case Block(s)
        => val sc = s.map{ case Seq(List(u)) => codeGen(u,env); case u => codeGen(u,env) }
           q"{ ..$sc }"
      case Assign(d,Seq(u::_))
        => val dc = codeGen(d,env)
           val uc = codeGen(u,env)
           q"$dc = $uc"
      case VarDecl(v,tp,Seq(Nil))
        => val vc = TermName(v)
           val tc = Type2Tree(tp)
           val init = tp match {
                         case BasicType("Int") => q"0"
                         case BasicType("Double") => q"0.0"
                         case _ => q"null"
                      }
           //q"var $vc:$tc = $init"
           q"var $vc:$tc = _"
      case VarDecl(v,tp,Seq(u::_))
        => val vc = TermName(v)
           val uc = codeGen(u,env)
           val tc = Type2Tree(tp)
           q"var $vc:$tc = $uc"
      case Def(f,ps,tp,b)
        => val fc = TermName(f)
           val bc = codeGen(b,ps.map {
                       case (v,t)
                         => val vc = TermName(v)
                            (q"$vc",Type2Tree(t)) 
                    }.toList++env)
           val tc = Type2Tree(tp)
           val psc = ps.map{ case (v,tp)
                               => val vc = TermName(v)
                                  val tc = Type2Tree(tp)
                                  q"val $vc: $tc" }
           q"def $fc (..$psc): $tc = $bc"
      case IntConst(n)
        => q"$n"
      case LongConst(n)
        => q"$n"
      case DoubleConst(n)
        => q"$n"
      case StringConst(s)
        => q"$s"
      case CharConst(s)
        => q"$s"
      case BoolConst(n)
        => q"$n"
      case Var(v)
        => Ident(TermName(v))
      case _ => throw new Exception("Unrecognized AST: "+e)
    }
  }

  /** Generate Scala code for statements */
  def codeGen ( e: Stmt, env: Environment ): c.Tree =
    e match {
      case BlockS(s)
        => val nenv = s.foldLeft(env){ case (r,VarDeclS(v,_,Some(u)))
                                         => val tv = TermName(v)
                                            (pq"$tv",typecheck(u,r))::r
                                       case (r,u) => r }
           val stmts = s.flatMap{ case VarDeclS(_,_,_) => Nil; case x => List(codeGen(x,nenv)) }
           val decls = s.flatMap{ case x@VarDeclS(_,_,_) => List(codeGen(x,nenv)); case x => Nil }
           q"{ ..$decls; ..$stmts }"
      case AssignS(d,u)
        => val dc = codeGen(d,env)
           val uc = codeGen(u,env)
           q"$dc = $uc"
      case ForS(v,n,m,k,b)
        => val nv = TermName(v)
           val bc = codeGen(b,add(VarPat(v),tq"Int",env))
           val nc = codeGen(n,env)
           val mc = codeGen(m,env)
           val kc = codeGen(m,env)
           q"{ var $nv = $nc; while($nv < $mc){ $bc; $nv += $kc } }"
      case ForeachS(p@VarPat(v),x,b)
        => val (tp,xc) = typedCode(x,env)
           val nv = TermName(v)
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.foreach(($nv:$tp) => $bc)"
      case ForeachS(p,x,b)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.foreach(($nv:$tp) => $nv match { case $pc => $bc })"
      case WhileS(p,b)
        => val pc = codeGen(p,env)
           val bc = codeGen(b,env)
           q"while($pc) $bc"
      case IfS(p,x,y)
        => val pc = codeGen(p,env)
           val xc = codeGen(x,env)
           val yc = codeGen(y,env)
           q"if($pc) $xc else $yc"
      case VarDeclS(v,_,Some(Call("map",Nil)))
        => val vc = TermName(v)
           if (var_decls.contains(v)) {
              val tq"Map[$kt,$vt]" = var_decls(v)
              q"val $vc = collection.mutable.Map[$kt,$vt]()"
           } else q"val $vc = collection.mutable.Map[Any,Any]()"
      case VarDeclS(v,_,Some(Call("array",d)))
        => val vc = TermName(v)
           val dc = d.map(codeGen(_,env))
           val etp = if (var_decls.contains(v)) element_type(var_decls(v)) else tq"Any"
           q"val $vc = Array.ofDim[$etp](..$dc)"
      case VarDeclS(v,_,Some(Call("tile",d)))
        => val ts = tileSize*tileSize
           val vc = TermName(v)
           val etp = if (var_decls.contains(v)) element_type(var_decls(v)) else tq"Any"
           q"val $vc = Array.ofDim[$etp]($ts)"
      case VarDeclS(v,None,Some(u))
        => val vc = TermName(v)
           val uc = codeGen(u,env)
           q"var $vc = $uc"
      case VarDeclS(v,Some(tp),Some(u))
        => val vc = TermName(v)
           val tc = Type2Tree(tp)
           val uc = codeGen(u,env)
           q"var $vc:$tc = $uc"
      case VarDeclS(v,Some(tp),None)
        => val vc = TermName(v)
           val tc = Type2Tree(tp)
           q"var $vc:$tc"
      case DefS(f,ps,tp,b)
        => val fc = TermName(f)
           val bc = codeGen(b,ps.map {
                       case (v,t)
                         => val vc = TermName(v)
                            (q"$vc",Type2Tree(t)) 
                    }.toList++env)
           val tc = Type2Tree(tp)
           val psc = ps.map{ case (v,tp)
                               => val vc = TermName(v)
                                  val tc = Type2Tree(tp)
                                  q"val $vc: $tc" }
           q"def $fc (..$psc): $tc = $bc"
      case ReturnS(u)
        => val uc = codeGen(u,env)
           q"return $uc"
      case ExprS(u)
        => codeGen(u,env)
    }
}
