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

import Typechecker.tuple
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.token.StdTokens
import scala.util.parsing.input.{NoPosition,CharArrayReader}
import scala.util.matching.Regex

trait MyTokens extends StdTokens {
  case class LongLit ( chars: String ) extends Token
  case class DoubleLit ( chars: String ) extends Token
  case class CharLit ( chars: String ) extends Token
  case class InfixOpr ( chars: String ) extends Token
  case class IncrOpr ( chars: String ) extends Token
}

class MyLexical extends StdLexical with MyTokens {
  /* a parser for regular expressions */
  def regex ( r: Regex ): Parser[String]
      = new Parser[String] {
            def apply ( in: Input )
                = r.findPrefixMatchOf(in.source.subSequence(in.offset,in.source.length)) match {
                        case Some(matched)
                          => Success(in.source.subSequence(in.offset,in.offset+matched.end).toString,
                                     in.drop(matched.end))
                        case None => Failure("string matching regex `"+r+"' expected but "+in.first+" found",in)
                  }
      }

  override def token: Parser[Token] = incrOpr | infixOpr | longLit | doubleLit | charLit | super.token

  /* long integers */
  def longLit: Parser[Token]
      = regex("""[0-9]+[Ll]""".r) ^^ { LongLit }

  /* floating point numbers */
  def doubleLit: Parser[Token]
      = regex("""[0-9]*[.][0-9]+([eE][+-]?[0-9]+)?[FfDd]?""".r) ^^ { DoubleLit }

  /* character literal */
  def charLit: Parser[Token]
      = regex("""'[^']'""".r) ^^ { CharLit }

  /* an infix operator can be any sequence of special chars, except delimiters, etc */ 
  def infixOpr: Parser[Token]
      = regex("""[^\s\w$()\[\]{}'"`.;,\\/]+""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else InfixOpr(s) }

  def incrOpr: Parser[Token]
      = regex("""[^\s\w$()\[\]{}'"`.;,\\/\=]+\=""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else IncrOpr(s) }
}

object Parser extends StandardTokenParsers {
  import AST._
  var queryText: String = ""

  override val lexical = new MyLexical

  lexical.delimiters ++= List( "(" , ")" , "[", "]", "{", "}", "," , ":", ";", ".", "=>", "=", "->", "<-",
                               "||", "&&", "!", "==", "<=", ">=", "<", ">", "!=", "+", "-", "*", "/", "%",
                               ":=", "#", "^", "|", "&", "..", "::" )

  lexical.reserved ++= List( "var", "for", "in", "do", "while", "if", "else", "true", "false", "def", "let",
                             "return", "typemap", "group", "by", "tensor" )

  /* groups of infix operator precedence, from low to high */
  val operator_precedence: List[Parser[String]]
      = List( "..", "||", "^", "&&"|"&", "<="|">="|"<"|">", "=="|"!=", "+"|"-", "*"|"/"|"%", "=" )

  /* all infix operators not listed in operator_precedence have the same highest precedence */  
  val infixOpr: Parser[String]
      = accept("infix operator",{ case t: lexical.InfixOpr => t.chars })
  val incrOpr: Parser[String]
      = accept("increment operator",{ case t: lexical.IncrOpr => t.chars })
  val precedence: List[Parser[String]]
      = operator_precedence :+ infixOpr
  val allInfixOpr: Parser[String]
      = operator_precedence.fold(infixOpr)(_|_)

  /* group infix operations into terms based on the operator precedence, from low to high */
  def terms ( level: Int ): Parser[(Expr,Expr)=>Expr]
      = precedence(level) ^^
        { case ".." => (x:Expr,y:Expr) => Range(x,y,IntConst(1))
          case "=" => (x:Expr,y:Expr) => Assign(x,Seq(List(y)))
          case op => (x:Expr,y:Expr) => MethodCall(x,op,List(y)) }
  def infix ( level: Int ): Parser[Expr]
      = positioned(if (level >= precedence.length) conses
                   else infix(level+1) * terms(level))

  def fromRaw ( s: String ): String = s.replace("""\n""","\n")
        
  def expr: Parser[Expr]
      = infix(0) | factor

  def sem: Parser[Option[String]] = opt( ";" )

  def char: Parser[String]
      = accept("char literal",{ case t: lexical.CharLit => t.chars })

  def int: Parser[Int]
      = numericLit ^^ { _.toInt }

  def long: Parser[Long]
      = accept("long literal",{ case t: lexical.LongLit => t.chars.init.toLong })

  def double: Parser[Double]
      = accept("double literal",{ case t: lexical.DoubleLit => t.chars.toDouble })

  def conses: Parser[Expr]      /* :: is treated specially: right associative, flips operands */
      = positioned(
        rep1sep( matches, "::" ) ^^
        { es => es.init.foldRight(es.last)
                  { case (e,r) => MethodCall(r,"::",List(e)) } })

  def matches: Parser[Expr]
      = factor ~ rep( "match" ~ "{" ~ rep1sep( "case" ~ pat ~ opt( "if" ~> expr ) ~ "=>" ~ expr, sem ) ~ "}" ) ^^
        { case a~as
            => as.foldLeft(a){ case (r,_~_~cs~_)
                                 => MatchE(r,cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                                     case _~p~_~_~b => Case(p,BoolConst(true),b) }) } }

 def factorList ( e: Expr ): Parser[Expr]
     = positioned(
         "[" ~ rep1sep( expr, "," ) ~ "]" ^^
         { case _~s~_ => Index(e,s) }
       | "." ~ ident ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
         { case _~m~_~el~_ => MethodCall(e,m,el) }
       | "." ~ ident ^^
         { case _~a => MethodCall(e,a,null) }
       | "#" ~ ident ^^
         { case _~a => Project(e,a) }
       | "#" ~ int ^^
         { case _~n => Nth(e,n) }
       )

 def factor: Parser[Expr]
      = positioned(
        term ~ rep( factorList(IntConst(0)) ) ^^
        { case e~s => s.foldLeft(e){
                          case (r,Project(_,a)) => Project(r,a)
                          case (r,Nth(_,n)) => Nth(r,n)
                          case (r,Index(_,s)) => Index(r,s)
                          case (r,MethodCall(_,m,el)) => MethodCall(r,m,el)
                          case (r,_) => r } })

 def dest: Parser[Expr]
      = positioned(
        ident ~ rep( factorList(IntConst(0)) ) ^^
        { case nm~s
            => val e: Expr = Var(nm)
               s.foldLeft(e) {
                  case (r,Project(_,a)) => Project(r,a)
                  case (r,Nth(_,n)) => Nth(r,n)
                  case (r,Index(_,s)) => Index(r,s)
                  case (r,MethodCall(_,m,el)) => MethodCall(r,m,el)
                  case (r,_) => r }
        })

  def qual: Parser[Qualifier]
      = ( "group" ~ "by" ~ pat ~ opt( ":" ~ expr ) ^^
          { case _~_~p~Some(_~e) => GroupByQual(p,e)
            case _~_~p~None => val e = toExpr(p); e.pos = p.pos; GroupByQual(p,e) }
        | "let" ~ pat ~ "=" ~ expr ^^
          { case _~p~_~e => LetBinding(p,e) }
        | "var" ~ ident ~ ":" ~ stype ~ "=" ~ expr ^^
          { case _~v~_~t~_~e => VarDef(v,t,e) }
        | pat ~ "<-" ~ expr ^^
          { case p~_~e => Generator(p,e) }
        | "(" ~ rep1sep( pat, "," ) ~ ")" ~ "<=" ~ expr ^^    // full spatial tensor access
          { case _~ps~_~_~e => Generator(TuplePat(ps),Call("_full",List(e))) }
        | dest ~ "=" ~ expr ^^
          { case d~_~e => AssignQual(d,e) }
        | expr ^^ Predicate
        | failure("illegal start of qualifier")
        )

  def compr: Parser[Comprehension]
    = positioned(
      "[" ~ expr ~ "|" ~ repsep( qual, "," ) ~ "]" ^^
      { case _~e~_~qs~_ => Comprehension(e,qs) })

  def term: Parser[Expr]
      = positioned(
          compr
        | "tensor" ~ opt("*") ~ "(" ~ repsep( expr, "," ) ~ ")"
              ~ "(" ~ repsep( expr, "," ) ~ ")" ~ term ^^
          { case _~None~_~ds~_~_~ss~_~e
              => Call(s"tensor_${ds.length}_${ss.length}",
                      List(tuple(ds),tuple(ss),e))
            case _~_~_~ds~_~_~ss~_~e
              => val cm = if (data_frames) "dataset" else "rdd"
                 Call(s"${cm}_block_tensor_${ds.length}_${ss.length}",
                      List(tuple(ds),tuple(ss),e)) }
        | "tensor" ~ opt("*") ~ "(" ~ repsep( expr, "," ) ~ ")" ~ term ^^
          { case _~None~_~ds~_~e
              => Call(s"tensor_${ds.length}_0",
                      List(tuple(ds),Tuple(Nil),e))
            case _~_~_~ds~_~e
              => val cm = if (data_frames) "dataset" else "rdd"
                 Call(s"${cm}_block_tensor_${ds.length}_0",
                      List(tuple(ds),tuple(Nil),e)) }
        | ident ~ "*" ~ expr ^?
          { case "map"~_~e => Call("block_map",List(e)) }
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ~ opt( compr ) ^^
          { case "lift"~_~List(Var(n),e)~_~None => Lift(n,e)
            case n~_~el~_~Some(c) => Call(n,el:+c)
            case n~_~es~_~None => Call(n,es) }
        | ident ~ compr ^^
          { case n~c => Call(n,List(c)) }
        | ident ~ "{" ~ ident ~ "=>" ~ compr ~ "}" ~ expr ^^
          { case n~_~v~_~c~_~e => Call(n,List(Lambda(VarPat(v),c),e)) }
        | "var" ~ ident ~ ":" ~ stype ~ opt("=" ~ expr) ^^
          { case _~v~_~t~None => VarDecl(v,t,Seq(Nil))
            case _~v~_~t~Some(_~e) => VarDecl(v,t,Seq(List(e))) }
        | "var" ~ ident ~ "=" ~ expr ^^
          { case _~v~_~e => VarDecl(v,AnyType(),Seq(List(e))) }
        | dest ~ incrOpr ~ expr ^^
          { case d~op~e => Assign(d,Seq(List(MethodCall(d,op.init,List(e))))) }
        | "if" ~ "(" ~ expr ~ ")" ~ expr ~ opt("else" ~ expr) ^^
          { case _~_~p~_~t~Some(_~e) => IfE(p,t,e)
            case _~_~p~_~t~None => IfE(p,t,Block(Nil)) }
        | "while" ~ "(" ~ expr ~ ")" ~ expr ^^
          { case _~_~p~_~s => While(p,s) }
        | "(" ~ repsep( pat, "," ) ~ ")" ~ "=>" ~ expr ^^
          { case _~ps~_~_~b => Lambda(TuplePat(ps),b) }
        | "(" ~ expr ~ ")" ^^
          { case _~e~_ => e }
        | "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case _~es~_ => if (es.length==1) es.head else Tuple(es) }
        | "<" ~ rep1sep( ident ~ "=" ~ expr, "," ) ~ ">" ^^
          { case _~es~_ => Record(es.map{ case n~_~v => (n,v) }.toMap) }
        | "true" ^^^ { BoolConst(true) }
        | "false" ^^^ { BoolConst(false) }
        | "{" ~> rep1sep( "case" ~ pat ~ opt( "if" ~> expr ) ~ "=>" ~ expr, sem ) <~ "}" ^^
          { cs => { val nv = newvar
                    Lambda(VarPat(nv),
                           MatchE(Var(nv),
                                  cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                          case _~p~_~_~b => Case(p,BoolConst(true),b) })) } }
        | "{" ~ rep( expr ~ sem ) ~ "}" ^^
          { case _~ss~_ => if (ss.length==1) ss.head match { case s~_ => s }
                           else Block(ss.map{ case s~_ => s }) }
        | ident ~ "=>" ~ expr ^^
          { case v~_~b => Lambda(VarPat(v),b) }
        | ident ~ ":" ~ stype ^^
          { case v~_~t => Coerce(Var(v),t) }
        | "[" ~ repsep( expr, "," ) ~ "]" ^^
          { case _~es~_ => Seq(es) }
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case f ~_~ps~_ => Call(f,ps) }
        | ( "-" | "+" | "!" ) ~ expr ^^
          { case o~e => MethodCall(e,"unary_"+o,null) }
        | allInfixOpr ~ "/" ~ factor ^^
          { case op~_~e => reduce(op,e) }
        | ident ^^
          { s => Var(s) }
         | double ^^
          { s => DoubleConst(s) }
        | long ^^
          { s => LongConst(s) }
        | int ^^
          { s => IntConst(s) }
        | stringLit ^^
          { s => StringConst(fromRaw(s)) }
        | char ^^
          { s => CharConst(fromRaw(s).apply(1)) }
        | failure("illegal start of expression")
        )

  def lambda: Parser[Lambda]
      = positioned(
          "(" ~ repsep( pat, "," ) ~ ")" ~ "=>" ~ expr ^^
          { case _~ps~_~_~b => Lambda(TuplePat(ps),b) }
        | ident ~ "=>" ~ expr ^^
          { case v~_~b => Lambda(VarPat(v),b) }
        | failure("Expected a Lambda expression")
        )

  def pat: Parser[Pattern]
      = positioned(
        "(" ~ repsep( pat, "," ) ~ ")"
          ^^ { case _~ps~_ => if (ps.length==1) ps.head else TuplePat(ps) }
        | "_"
          ^^^ { StarPat() }
        | ident
          ^^ { s => if (s == "_") StarPat() else VarPat(s) }
        | failure("illegal start of pattern")
        )

  def subst ( tp: Type, s: List[String] ): Type
    = tp match {
        case BasicType(n) if s.contains(n) => TypeParameter(n)
        case _ => apply(tp,subst(_,s))
      }

  def subst ( e: Expr, s: List[String] ): Expr
    = e match {
        case VarDecl(v,at,b)
          => VarDecl(v,subst(at,s),subst(b,s))
        case _ => apply(e,subst(_,s))
      }

  def mapdef: Parser[(String,List[(String,Type)],Expr)]
    = "def" ~ ident ~ "(" ~ repsep( ident ~ ":" ~ stype, "," ) ~ ")" ~ "=" ~ expr ^^
      { case _~f~_~params~_~_~body
          => (f,params.map{ case v~_~t => (v,t) },body) }

  def stmt: Parser[Stmt]
      = positioned(
          "var" ~ ident ~ ":" ~ stype ~ opt( "=" ~ expr ) ^^
          { case _~v~_~t~None => VarDeclS(v,Some(t),None)
            case _~v~_~t~Some(_~e) => VarDeclS(v,Some(t),Some(e)) }
        | "var" ~ ident ~ "=" ~ expr ^^
          { case _~v~_~e => VarDeclS(v,None,Some(e)) }
        | "typemap" ~ ident ~ opt("[" ~ rep1sep(ident,",") ~ "]") ~
            "(" ~ repsep( ident ~ ":" ~ stype, "," ) ~ ")" ~ ":" ~ stype ~
            "{" ~ mapdef ~ mapdef ~ "}" ^?
          { case _~v~pts~_~args~_~_~at~_~Tuple3("view",vps,vb)~Tuple3("store",sps,sb)~_
              => val ts = pts match { case Some(_~s~_) => s; case _ => Nil }
                 val as = args.map{ case v~_~t => (v,subst(t,ts)) }
                 val st = tuple(vps.map(_._2))
                 val lt = tuple(sps.map(_._2))
                 TypeMapS(v,ts,as.toMap,subst(at,ts),subst(st,ts),subst(lt,ts),
                          Lambda(tuple(vps.map(x => VarPat(x._1))),subst(vb,ts)),
                          Lambda(tuple(sps.map(x => VarPat(x._1))),subst(sb,ts))) }
        | "{" ~ rep( stmt ~ sem ) ~ "}" ^^
          { case _~ss~_ => if (ss.length==1) ss.head match { case s~_ => s }
                           else BlockS(ss.map{ case s~_ => s }) }
        | dest ~ "=" ~ expr ^^
          { case d~_~e => AssignS(d,e) }
        | dest ~ incrOpr ~ expr ^^
          { case d~op~e => AssignS(d,MethodCall(d,op.init,List(e))) }
        | "for" ~ ident ~ "=" ~ expr ~ "," ~ expr ~ opt( "," ~ expr ) ~ "do" ~ stmt ^^
          { case _~v~_~a~_~b~None~_~s => ForS(v,a,b,IntConst(1),s)
            case _~v~_~a~_~b~Some(_~c)~_~s => ForS(v,a,b,c,s) }
        | "for" ~ pat ~ "in" ~ expr ~ "do" ~ stmt ^^
          { case _~p~_~e~_~s => ForeachS(p,e,s) }
        | "while" ~ "(" ~ expr ~ ")" ~ stmt ^^
          { case _~_~p~_~s => WhileS(p,s) }
        | "if" ~ "(" ~ expr ~ ")" ~ stmt ~ opt( ";" ~ "else" ~ stmt ) ^^
          { case _~_~p~_~st~None => IfS(p,st,BlockS(Nil))
            case _~_~p~_~st~Some(_~_~se) => IfS(p,st,se) }
        | "def" ~ ident ~ "(" ~ repsep( ident ~ ":" ~ stype, "," ) ~ ")" ~ ":" ~ stype ~ opt("=") ~ stmt ^^
          { case _~f~_~params~_~_~tp~_~body
              => DefS(f,params.map{ case v~_~t => (v,t) },tp,body) }
        | "return" ~ expr ^^
          { case _~e => ReturnS(e) }
        | expr ^^ ExprS
        | failure("illegal start of statement")
       )

  def stype: Parser[Type]
      = simpleType ~ rep( "->" ~ stype ) ^^
        { case d~ts => ts.foldRight(d){ case (_~t,r) => FunctionType(r,t) } }

  val array_pat = """array(\d+)""".r

  val tensor_pat = """tensor_(\d+)_(\d+)""".r
  val bool_tensor_pat = """bool_tensor_(\d+)_(\d+)""".r
  val block_tensor_pat = """(rdd_block_|dataset_block|)tensor_(\d+)_(\d+)""".r

  def simpleType: Parser[Type]
      = ( "(" ~ repsep( stype, "," ) ~ ")" ^^
          { case _~List(tp)~_ => tp
            case _~ts~_ => TupleType(ts) }
        | "<" ~ rep1sep( ident ~ ":" ~ stype, "," ) ~ ">" ^^
          { case _~cs~_ => RecordType(cs.map{ case n~_~t => (n,t)}.toMap) }
        | ident ~ "[" ~ stype ~ "]" ^^
          { case "list"~_~t~_ => SeqType(t)
            case "vector"~_~t~_ => ArrayType(1,t)
            case "matrix"~_~t~_ => ArrayType(2,t)
            case array_pat(n)~_~t~_ => ArrayType(n.toInt,t)
            case (n@block_tensor_pat(_,dn,sn))~_~t~_
              => StorageType(n,List(t),List(tuple(1.to(dn.toInt).map(i => IntConst(block_dim_size)).toList),
                                            tuple(1.to(dn.toInt).map(i => IntConst(block_dim_size)).toList)))
            case n~_~t~_ => ParametricType(n,List(t)) }
        | ident ~ "*" ~ "[" ~ stype ~ "]" ^^
          { case (n@tensor_pat(dn,sn))~_~_~t~_
              => StorageType("block_"+n,List(t),
                             List(tuple(1.to(dn.toInt).map(i => IntConst(block_dim_size)).toList),
                                  tuple(1.to(dn.toInt).map(i => IntConst(block_dim_size)).toList)))
            case n~_~_~t~_ => ParametricType(n+"*",List(t)) }
        | ident ~ "*" ~ "[" ~ stype ~ "," ~ stype ~ "]" ^?
          { case "map"~_~_~k~_~v~_ => StorageType("block_map",List(k,v),Nil) }
        | rep1sep( ident, "." ) ~ "[" ~ rep1sep( stype, "," ) ~ "]" ^^
          { case List("map")~_~List(kt,vt)~_ => MapType(kt,vt)
            case ns~_~ts~_ => ParametricType(ns.mkString("."),ts) }
        | rep1sep( ident, "." ) ^^
          { case List(n@bool_tensor_pat(dn,sn))
              => StorageType(n,Nil,1.to(dn.toInt+sn.toInt).map(i => IntConst(block_dim_size)).toList)
            case s => BasicType(s.mkString(".")) }
        )

  // if true, display query string at run-time
  val print_queries = false

  def program: Parser[Stmt]
      = rep( stmt ~ sem ) ^^
        { ss => BlockS(ss.flatMap {
                  case s~_ => if (print_queries)
                                List(ExprS(Call("println",List(StringConst(s.toString)))),s)
                              else List(s)
                }) }

  def line_reader ( line: String)
    = new lexical.Scanner(new CharArrayReader(line.toArray))

  /** Parse a statement */
  def parse ( line: String ): Stmt
      = phrase(positioned(program))(line_reader(line)) match {
          case Success(e,_)
            => setPositions(e:Stmt,NoPosition)
               e:Stmt
          case m => println(m); BlockS(Nil)
        }

  /** Parse an expression */
  def parse_expr ( line: String ): Expr
      = phrase(positioned(expr))(line_reader(line)) match {
          case Success(e,_)
            => setPositions(e:Expr,NoPosition)
               e:Expr
          case m => println(m); Block(Nil)
        }

  def main ( args: Array[String] ): Unit = {
    println(Pretty.print(parse(args(0))))
  }
}
