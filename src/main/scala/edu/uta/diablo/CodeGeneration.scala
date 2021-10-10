/*
 * Copyright © 2020-2021 University of Texas at Arlington
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

import scala.reflect.macros.{TypecheckException, whitebox}
import scala.language.experimental.macros
import java.io._


abstract class CodeGeneration {
  val c: whitebox.Context
  import c.universe.{Expr=>_,Block=>_,Apply=>_,Assign=>_,Return=>_,_}
  import AST._
  import edu.uta.diablo.{Type=>DType}

  var line: Int = 0

  /** contains bindings from patterns to Scala types; may have duplicate bindings */
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

  def isUnitType ( tp: c.Tree ): Boolean
    = tp match {
         case tq"Unit" => true
         case _ => false
      }

  /** Convert a Type to a Tree. There must be a better way to do this */
  def type2tree ( tp: c.Type ): c.Tree = {
    val ntp = if (tp <:< c.typeOf[AnyVal]) tp.toString.split('(')(0) else tp
    val Typed(_,etp) = c.parse("x:("+ntp+")")
    etp
  }

  /* Convert a Scala type to a Diablo type */
  def Tree2Type ( tp: c.Tree ): DType =
    tp match {
      case tq"(..$cs)" if cs.length > 1
        => TupleType(cs.map(Tree2Type))
      case tq"Array[$t]"
        => Tree2Type(t) match {
              case ArrayType(d,tp)
                => ArrayType(d+1,tp)
              case tp => ArrayType(1,tp)
           }
      case tq"Map[$kt,$vt]"
        => MapType(Tree2Type(kt),Tree2Type(vt))
      case tq"List[$et]"
        => SeqType(Tree2Type(et))
      case tq"$n[..$cs]" if cs.nonEmpty
        => ParametricType(n.toString,cs.map(Tree2Type))
      case tq"Any"
        => AnyType()
      case tq"Nothing"
        => AnyType()
      case _
        => BasicType(tp.toString)
    }

  /* Convert a path x.y.z.. to a Scala type name */
  def get_type_name ( name: String ): c.Tree
    = name.split('.').toList match {
            case List(m)
              => tq"${TypeName(m)}"
            case List(n,"type")
              => SingletonTypeTree(Ident(TermName(n)))
            case (m::s):+n
              => Select(s.foldLeft[c.Tree](Ident(TermName(m))) {
                                    case (r,m) => Select(r,TermName(m))
                        },
                        TypeName(n))
            case _ => tq""
           }

  /* Convert a Diablo type to a Scala type */
  def Type2Tree ( tp: DType ): c.Tree
    = tp match {
      case StorageType(_,_,_)
        => Type2Tree(Typechecker.unfold_storage_type(tp))
      case TupleType(cs) if cs.nonEmpty
        => val tcs = cs.map(Type2Tree)
           tq"(..$tcs)"
      case RecordType(cs) if cs.nonEmpty
        => val tcs = cs.values.map(Type2Tree).toList
           tq"(..$tcs)"
      case ParametricType(n,cs) if cs.nonEmpty
        => val tcs = cs.map(Type2Tree)
           val tn = get_type_name(n)
           tq"$tn[..$tcs]"
      case ParametricType(n,Nil)
        => val tn = get_type_name(n)
           tq"$tn"
      case ArrayType(d,t)
        => (0 until d).foldLeft(Type2Tree(t)) { case (r,_) => tq"Array[$r]" }
      case MapType(k,v)
        => val kc = Type2Tree(k)
           val vc = Type2Tree(v)
           tq"Map[$kc,$vc]"
      case SeqType(t)
        => val tc = Type2Tree(t)
           tq"List[$tc]"
      case BasicType(n)
        => get_type_name(n)
      case TypeParameter(v)
        => tq"String"
      case _ => tq""
    }

  /** Return the type of Scala code, if exists
   *  @param code Scala code
   *  @param env an environment that maps patterns to types
   *  @return the type of code, if the code is typechecked without errors
   */
  def getOptionalType ( code: c.Tree, env: Environment ): Either[c.Tree,TypecheckException] = {
    val fc = env.foldLeft(code) {
                case (r,(Bind(v@TermName(_),_),tp))
                  => val nv = TermName(c.freshName("x"))
                     q"($nv:$tp) => { var $v = $nv; $r }"
                case (r,(p,tp))
                  => val nv = TermName(c.freshName("x"))
                     q"($nv:$tp) => $nv match { case $p => $r }"
             }
    val te = try c.Expr[Any](c.typecheck(q"{ import edu.uta.diablo._; $fc }")).actualType
             catch { case ex: TypecheckException
                       => //println("%%% "+code+"\n"+env)
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
    typecheckOpt(Call(f,vs.map(Var)),env).map(Tree2Type)
  }

  /** Return the result type of a method using the Scala's typechecker */
  def typecheck_method ( o: DType, m: String, args: List[DType] ): Option[DType] = {
    val vo = c.freshName("x")
    if (args == null) {
       typecheckOpt(MethodCall(Var(vo),m,null),
                    List((code(VarPat(vo)),Type2Tree(o)))).map(Tree2Type)
    } else {
      val vs = args.zipWithIndex.map{ case (_,i) => vo+i }
      val env: Environment
          = (code(VarPat(vo)),Type2Tree(o))::
               vs.zip(args).map{ case (v,t) => (code(VarPat(v)),Type2Tree(t)) }.toList
      typecheckOpt(MethodCall(Var(vo),m,vs.map(Var)),env).map(Tree2Type)
    }
  }

  /** For a collection ec, return the element type */
  def typedCodeOpt ( ec: c.Tree, env: Environment ): Option[c.Tree]
    = getOptionalType(ec,env) match {
        case Left(tq"$c[$etp]")   // assumes c is a collection type
          => Some(etp)
        case Left(atp)
          => try {     // for Range types that are not parametric
                val ctp = c.Expr[Any](c.typecheck(q"(x:$atp) => x.head")).actualType
                Some(returned_type(type2tree(ctp)))
             } catch { case ex: TypecheckException
                         => try {
                               val ctp = c.Expr[Any](c.typecheck(q"(x:$atp) => x.first()")).actualType
                               Some(returned_type(type2tree(ctp)))
                            } catch { case ex: TypecheckException => return None }
                     }
        case Right(ex) => None
      }

  /** For a collection e, return the element type and the code of e */
  def typedCode ( e: Expr, env: Environment ): (c.Tree,c.Tree) = {
    val ec = codeGen(e,env)
    typedCodeOpt(ec,env) match {
      case Some(v) => (v,ec)
      case _
        => getOptionalType(ec,env) match {
              case Right(ex)
                => throw ex
              case Left(tp)
                => throw new Error(s"Expression $ec is not a collection (found type $tp)\nBindings: "+env)
           }
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

  def element_type ( tp: c.Tree ): c.Tree
    = tp match {
        case tq"$c[$atp]"
          => atp
        case _ => tp
      }

  def set_element_type ( tp: c.Tree, etp: c.Tree ): c.Tree
    = tp match {
        case tq"Array[$atp]"
          => val ntp = set_element_type(atp,etp)
             tq"Array[$ntp]"
        case _ => etp
      }

  /** Generate Scala code for e as a statement */
  def codeStmt ( e: Expr, env: Environment ): c.Tree
    = e match {
        case Seq(List(u))
          => codeStmt(u,env)
        case IfE(p,x,Seq(Nil))
          => val pc = codeGen(p,env)
             val xc = codeStmt(x,env)
             q"if($pc) $xc"
        case IfE(p,x,y)
          => val pc = codeGen(p,env)
             val xc = codeStmt(x,env)
             val yc = codeStmt(y,env)
             q"if($pc) $xc else $yc"
        case flatMap(Lambda(p@VarPat(v),b),Range(n,m,k))
          // a while-loop is more efficient than a foreach
          => val nv = TermName(v)
             val bc = codeStmt(b,add(p,tq"Int",env))
             val nc = codeGen(n,env)
             val mc = codeGen(m,env)
             val kc = codeGen(k,env)
             q"{ var $nv = $nc; while($nv <= $mc){ $bc; $nv += $kc } }"
        case flatMap(Lambda(p@VarPat(v),b),x)
          => val (tp,xc) = typedCode(x,env)
             val nv = TermName(v)
             val bc = codeStmt(b,add(p,tp,env))
             q"$xc.foreach(($nv:$tp) => $bc)"
        case flatMap(Lambda(p,b),x)
          => val pc = code(p)
             val (tp,xc) = typedCode(x,env)
             val nv = TermName(c.freshName("x"))
             val bc = codeStmt(b,add(p,tp,env))
             q"$xc.foreach(($nv:$tp) => $nv match { case $pc => $bc })"
        case MethodCall(x@flatMap(Lambda(p,u),b),"toList",null)
          => codeStmt(x,env)
        case MethodCall(x@MethodCall(flatMap(Lambda(p,u),b),"toList",null),"toList",null)
          => codeStmt(x,env)
        case Let(p,u,b)
          => val pc = code(p)
             val uc = codeGen(u,env)
             val tc = getType(uc,env)
             val bc = codeStmt(b,add(p,tc,env))
             q"{ val $pc: $tc = $uc; $bc }"
        case Block(Nil)
          => q"()"
        case Block(es:+Seq(x::_))
          => codeStmt(Block(es:+x),env)
        case Block(s@(es:+x))
          => val (nes,nenv) = es.foldLeft[(List[c.Tree],Environment)]((Nil,env)) {
                               case ((s,el),u@VarDecl(v,TypeParameter(_),b))
                                 => val vc = TermName(v)
                                    val (tc,_) = typedCode(b,el)
                                    ( s:+codeGen(u,el), (pq"$vc",tc)::el )
                               case ((s,el),u@VarDecl(v,tp,_))
                                 => val vc = TermName(v)
                                    val tc = Type2Tree(tp)
                                    ( s:+codeGen(u,el), (pq"$vc",tc)::el )
                               case ((s,el),u@Def(f,ps,tp,b))
                                 => val fc = TermName(f)
                                    val pt = TupleType(ps.values.toList)
                                    val tc = Type2Tree(FunctionType(pt,tp))
                                    ( s:+codeGen(u,el), (pq"$fc",tc)::el )
                               case ((s,el),u)
                                 => (s:+codeStmt(u,el),el)
                                       
                            }
           val xc = codeStmt(x,nenv)
           q"{ ..$nes; $xc }"
        case u
          => codeGen(u,env)
    }

  def zero ( tp: DType ): c.Tree
    = tp match {
         case BasicType("Int") => q"0"
         case BasicType("Long") => q"0L"
         case BasicType("Double") => q"0.0"
         case BasicType("Boolean") => q"false"
         case SeqType(_) => q"Nil"
         case TupleType(ts)
           => val tts = ts.map(zero)
              q"(..$tts)"
         case ParametricType(ab,List(etp))
           if ab == TypeMappings.arrayBuffer
           => val tab = get_type_name(ab)
              val etc = Type2Tree(etp)
              q"new $tab[$etc]()"
         case _ => q"null"
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
           if (isUnitType(getType(bc,add(p,tp,env))))
             return codeStmt(e,env)
           q"$xc.map(($nv:$tp) => $nv match { case $pc => $bc })"
      case flatMap(Lambda(p,Let(q,y,Seq(List(b)))),x)
        if irrefutable(p)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val qc = code(q)
           val yc = codeGen(y,add(p,tp,env))
           val tc = getType(yc,add(p,tp,env))
           val bc = codeGen(b,add(q,tc,add(p,tp,env)))
           if (isUnitType(getType(bc,add(q,tc,add(p,tp,env)))))
             return codeStmt(e,env)
           q"$xc.map(($nv:$tp) => $nv match { case $pc => { val $qc: $tc = $yc; $bc } })"
      case flatMap(Lambda(p,b),x)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           if (isUnitType(element_type(getType(bc,add(p,tp,env)))))
             return codeStmt(e,env)
           if (irrefutable(p))
              q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc })"
           else q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc; case _ => Nil })"
      case MethodCall(x,"reduceByKey",List(Lambda(p,b)))
        => val (tp,xc) = typedCode(x,env)
           val pc = code(p)
           val nx = TermName(c.freshName("x"))
           val ny = TermName(c.freshName("y"))
           tp match {
             case tq"($kt,$et)"
               => val bc = codeGen(b,add(p,tq"($et,$et)",env))
                  q"$xc.reduceByKey(($nx:$et,$ny:$et) => ($nx,$ny) match { case $pc => $bc })"
             case _ => throw new Exception("Wrong reduceByKey: "+e)
           }
      case MethodCall(x,"reduceByKey",List(Lambda(p,b),n))
        => val (tp,xc) = typedCode(x,env)
           val pc = code(p)
           val nx = TermName(c.freshName("x"))
           val ny = TermName(c.freshName("y"))
           val nc = codeGen(n,env)
           tp match {
             case tq"($kt,$et)"
               => val bc = codeGen(b,add(p,tq"($et,$et)",env))
                  q"$xc.reduceByKey(($nx:$et,$ny:$et) => ($nx,$ny) match { case $pc => $bc },$nc)"
             case _ => throw new Exception("Wrong reduceByKey: "+e)
           }
      case Call("outerJoin",List(x,y,Lambda(p,b)))
        => val (tp,xc) = typedCode(x,env)
           val pc = code(p)
           val yc = codeGen(y,env)
           val nx = TermName(c.freshName("x"))
           val ny = TermName(c.freshName("y"))
           tp match {
             case tq"($kt,$et)"
               => val bc = codeGen(b,add(p,tq"($et,$et)",env))
                  q"outerJoin($xc,$yc,($nx:$et,$ny:$et) => ($nx,$ny) match { case $pc => $bc })"
             case _ => throw new Exception("Wrong outerJoin: "+e)
           }
      case groupBy(x)
        => val xc = codeGen(x,env)
           q"$xc.groupBy(_._1).mapValues( _.map(_._2)).toList"
      case reduce(m,x)
        if m.matches("^[a-zA-Z0-9_]*$")
        => val xc = codeGen(x,env)
           val fnc = TermName(method_name(m))
           q"$xc.reduce( (x,y) => $fnc(x,y) )"
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
      case Record(es)
        => codeList(es.values.toList, cs => q"(..$cs)",env)
      case Call("map",Nil)
        => q"scala.collection.mutable.Map[Any,Any]()"
      case Call("array",d)
        => val dc = d.map(codeGen(_,env))
           q"Array.ofDim[Any](..$dc)"
      case Call("inRange",List(i,n1,n2,IntConst(1)))
        => val ic = codeGen(i,env)
           val nc1 = codeGen(n1,env)
           val nc2 = codeGen(n2,env)
           q"$ic >= $nc1 && $ic <= $nc2"
      case Call("inRange",List(i,n1,n2,n3))
        => val ic = codeGen(i,env)
           val nc1 = codeGen(n1,env)
           val nc2 = codeGen(n2,env)
           val nc3 = codeGen(n3,env)
           q"$ic >= $nc1 && $ic <= $nc2 && ($ic-$nc1) % $nc3 == 0"
      case Call("zero",List(v))
        => val (tp,vc) = typedCode(v,env)
           tp match {
             case tq"Int" => q"0"
             case tq"Long" => q"0L"
             case tq"Double" => q"0.0"
             case _ => q"null"
           }
      case Call("binarySearch",s:+v)
        if s.length == 4
        => // add a zero to the arguments
           val sc = s.map(codeGen(_,env))
           val (tp,vc) = typedCode(v,env)
           val zero = tp match {
                         case tq"Int" => q"0"
                         case tq"Long" => q"0L"
                         case tq"Double" => q"0.0"
                         case _ => q"null"
                      }
           q"binarySearch(..$sc,$vc,$zero)"
      case Call(n,es)
        => val fm = TermName(method_name(n))
           codeList(es,cs => q"$fm(..$cs)",env)
      case Project(x,a)
        if x.tpe != null
        => x.tpe match {
              case RecordType(cs)
                if cs.contains(a)
                => codeGen(Nth(x,cs.keys.toList.indexOf(a)+1),env)
              case _ => codeGen(MethodCall(x,a,null),env)
           }
      case Project(x,a)
        => codeGen(MethodCall(x,a,null),env)
      case Assign(d,Seq(u::_))
        => val uc = codeGen(u,env)
           val dc = codeGen(d,env)
           q"$dc = $uc"
      case Assign(Tuple(xs),y)
        => val yc = codeGen(y,env)
           val v = TermName(c.freshName("x"))
           val xc = xs.zipWithIndex.map {
                      case (x,n)
                        => val xc = codeGen(x,env)
                           val nc = TermName("_"+(n+1))
                           q"$xc = $v.$nc"
                   }
           q"{ val $v = $yc; ..$xc }"
      case Assign(d,u)
        => val uc = codeGen(u,env)
           val dc = codeGen(d,env)
           q"$dc = $uc.head"
      case MethodCall(Var("_"),m,null)
        => val nv = TermName(c.freshName("x"))
           val fm = TermName(method_name(m))
           val tpt = tq""  // empty type
           val p = q"val $nv: $tpt"
           q"($p) => $nv.$fm"
      case MethodCall(x,m,null)
        if List("length","rows","cols","dims").contains(m)
        => val xc = codeGen(x,env)
           getOptionalType(xc,env) match {
             case Left(tq"(..$ts)") if ts.length>1
               => m match {
                    case "length" => q"$xc._1"
                    case "rows" => q"$xc._1"
                    case "cols" => q"$xc._2"
                    case _
                      => val es = (1 until ts.length).map(i => q"$xc.${TermName("_"+i)}")
                         q"(..$es)"
                  }
             case _
               => val fm = TermName(method_name(m))
                  q"$xc.$fm"
           }
      case MethodCall(x,m,null)
        if m.length == 1 && char_maps.contains(m(0))
        => val xc = codeGen(x,env)
           val fm = TermName("unary_"+method_name(m))
           q"$xc.$fm"
      case MethodCall(x,m,null)
        => val xc = codeGen(x,env)
           val fm = TermName(method_name(m))
           q"$xc.$fm"
      case Apply(f,x)
        => val fc = codeGen(f,env)
           val xc = codeGen(x,env)
           q"$fc($xc)"
      case MethodCall(x,m,es)
        => val fm = TermName(method_name(m))
           codeList(x+:es,{ case cx+:cs => q"$cx.$fm(..$cs)" },env)
      case MapAccess(x,i)
        => val xc = codeGen(x,env)
           val ic = codeGen(i,env)
           q"$xc($ic)"
      case Seq(Nil)
        => q"Nil"
      case Seq(s)
        => val sc = s.map(codeGen(_,env))
           q"List(..$sc)"
      case Range(i,MethodCall(l,"-",List(IntConst(1))),IntConst(1))
        => val ic = codeGen(i,env)
           val lc = codeGen(l,env)
           q"$ic.until($lc)"
      case Range(i,l,IntConst(1))
        => val ic = codeGen(i,env)
           val lc = codeGen(l,env)
           q"$ic.to($lc)"
      case Range(i,l,s)
        => val ic = codeGen(i,env)
           val lc = codeGen(l,env)
           val sc = codeGen(s,env)
           q"$ic.to($lc,$sc)"
      case IfE(p,x,y)
        => val pc = codeGen(p,env)
           val xc = codeGen(x,env)
           val yc = codeGen(y,env)
           q"if ($pc) $xc else $yc"
     case Let(p,u,b)
        => val pc = code(p)
           val uc = codeGen(u,env)
           val tc = getType(uc,env)
           val bc = codeGen(b,add(p,tc,env))
           q"{ val $pc: $tc = $uc; $bc }"
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
      case Lambda(TuplePat(ps),b)
        => val tpt = tq""  // empty type
           val pc = ps.map{ case VarPat(v) => val vc = TermName(v); q"val $vc: $tpt"
                            case p => code(p) }
           val bc = codeGen(b,ps.foldLeft[Environment](env){ (r,p) => add(p,tpt,r) })
           q"{ (..$pc) => $bc }"
      case Block(Nil)
        => q"()"
      case Block(es:+Seq(x::_))
        => codeGen(Block(es:+x),env)
      case Block(s@(es:+x))
        => val (nes,nenv) = es.foldLeft[(List[c.Tree],Environment)]((Nil,env)) {
                               case ((s,el),u@VarDecl(v,TypeParameter(_),b))
                                 => val vc = TermName(v)
                                    val (tc,_) = typedCode(b,el)
                                    ( s:+codeGen(u,el), (pq"$vc",tc)::el )
                               case ((s,el),u@VarDecl(v,tp,_))
                                 => val vc = TermName(v)
                                    val tc = Type2Tree(tp)
                                    ( s:+codeGen(u,el), (pq"$vc",tc)::el )
                               case ((s,el),u@Def(f,ps,tp,b))
                                 => val fc = TermName(f)
                                    val pt = TupleType(ps.values.toList)
                                    val tc = Type2Tree(FunctionType(pt,tp))
                                    ( s:+codeGen(u,el), (pq"$fc",tc)::el )
                               case ((s,el),u)
                                 => (s:+codeStmt(u,el),el)
                            }
           val xc = codeGen(x,nenv)
           q"{ ..$nes; $xc }"
       case VarDecl(v,tp,Seq(Nil))
        => val vc = TermName(v)
           val init = zero(tp)
           val tc = Type2Tree(tp)
           q"var $vc:$tc = $init"
      case VarDecl(v,_,Seq(List(Call("zero",List(u)))))
        => val (tp,_) = typedCode(u,env)
           val zero = tp match {
                        case tq"Int" => q"0"
                        case tq"Long" => q"0L"
                        case tq"Double" => q"0.0"
                        case _ => q"null"
                      }
           val vc = TermName(v)
           q"val $vc: $tp = $zero"
      case VarDecl(v,tp,Seq(List(Call("map",Nil))))
        => val vc = TermName(v)
           val tq"Map[$kt,$vt]" = Type2Tree(tp)
           q"var $vc = collection.mutable.Map[$kt,$vt]()"
      case VarDecl(v,tp@ArrayType(_,tt@TupleType(_)),Seq(List(Call("array",d))))
        => val vc = TermName(v)
           val tc = element_type(Type2Tree(tp))
           val dc = d.map(codeGen(_,env))
           val z = zero(tt)
           q"var $vc = Array.tabulate[$tc](..$dc)(i => $z)"
      case VarDecl(v,tp,Seq(List(Call("array",d))))
        => val vc = TermName(v)
           val tc = element_type(Type2Tree(tp))
           val dc = d.map(codeGen(_,env))
           q"var $vc = Array.ofDim[$tc](..$dc)"
      case VarDecl(v,tp,Seq(u::_))
        => val vc = TermName(v)
           val uc = codeGen(u,env)
           val tc = Type2Tree(tp)
           q"var $vc:$tc = $uc"
      case VarDecl(v,tp,u)
        => val vc = TermName(v)
           val uc = codeGen(u,env)
           val tc = Type2Tree(tp)
           q"var $vc:$tc = $uc.head"
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
      case While(Seq(List(p)),b)
        => val pc = codeGen(p,env)
           val bc = codeGen(b,env)
           q"while($pc) $bc"
      case While(p,b)
        => val pc = codeGen(p,env)
           val bc = codeGen(b,env)
           q"while($pc.head) $bc"
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
      case Var("null")
        => q"null"
      case Var(v)
        => Ident(TermName(v))
      case _ => throw new Exception("Unrecognized AST: "+e)
    }
  }

  /** Generate Scala code for statements */
  def codeGen ( e: Stmt, env: Environment ): c.Tree =
    e match {
      case BlockS(s)
        => val ns = s.foldLeft[(List[c.Tree],Environment)]((Nil,env)) {
                               case ((s,el),u@VarDeclS(v,_,Some(x)))
                                 => val vc = TermName(v)
                                    val tc = typecheck(x,el)
                                    ( s:+codeGen(u,el), (pq"$vc",tc)::el )
                               case ((s,el),u@DefS(f,ps,tp,b))
                                 => val fc = TermName(f)
                                    val pt = TupleType(ps.values.toList)
                                    val tc = Type2Tree(FunctionType(pt,tp))
                                    ( s:+codeGen(u,el), (pq"$fc",tc)::el )
                               case ((s,el),u)
                                 => (s:+codeGen(u,el),el)
                            }._1
           q"{ ..$ns }"
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
           q"{ var $nv = $nc; while($nv <= $mc){ $bc; $nv += $kc } }"
      case ForeachS(p@VarPat(v),Range(n,m,k),b)
        // a while-loop is more efficient than a foreach
        => val nv = TermName(v)
           val bc = codeGen(b,add(p,tq"Int",env))
           val nc = codeGen(n,env)
           val mc = codeGen(m,env)
           val kc = codeGen(k,env)
           q"{ var $nv = $nc; while($nv <= $mc){ $bc; $nv += $kc } }"
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
           q"val $vc = collection.mutable.Map[Any,Any]()"
      case VarDeclS(v,Some(tp),Some(Seq(List(Call("array",d)))))
        => val vc = TermName(v)
           val tc = element_type(Type2Tree(tp))
           val dc = d.map(codeGen(_,env))
           q"var $vc = Array.ofDim[$tc](..$dc)"
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
      case _ => q"()"
    }
}
