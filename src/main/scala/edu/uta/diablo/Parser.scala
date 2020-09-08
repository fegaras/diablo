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

import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.token.StdTokens
import scala.util.matching.Regex


trait MyTokens extends StdTokens {
  case class LongLit ( chars: String ) extends Token
  case class DoubleLit ( chars: String ) extends Token
  case class CharLit ( chars: String ) extends Token
  case class InfixOpr ( chars: String ) extends Token
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

  override def token: Parser[Token] = infixOpr | longLit | doubleLit | charLit | super.token

  /* long integers */
  def longLit: Parser[Token]
      = regex("""[0-9]+[Ll]""".r) ^^ { LongLit }

  /* floating point numbers */
  def doubleLit: Parser[Token]
      = regex("""[0-9]*[\.][0-9]+([eE][+-]?[0-9]+)?[FfDd]?""".r) ^^ { DoubleLit }

  /* character literal */
  def charLit: Parser[Token]
      = regex("""'[^']'""".r) ^^ { CharLit }

  /* an infix operator can be any sequence of special chars, except delimiters, etc */ 
  def infixOpr: Parser[Token]
      = regex("""[^\s\w\$\(\)\[\]\{\}\'\"\`\.\;\,\\/]+""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else InfixOpr(s) }
}

object Parser extends StandardTokenParsers {
  var queryText: String = ""

  override val lexical = new MyLexical

  lexical.delimiters += ( "(" , ")" , "[", "]", "{", "}", "," , ":", ";", ".", "=>", "=", "->", "<-",
                          "||", "&&", "!", "==", "<=", ">=", "<", ">", "!=", "+", "-", "*", "/", "%",
                          "#", "^", "|", "&", "+=", "*=", "&&=", "||=" )

  lexical.reserved += ( "var", "for", "in", "do", "while", "if", "else", "true", "false", "def", "let",
                        "return", "typemap", "to", "with", "array" )

  /* groups of infix operator precedence, from low to high */
  val operator_precedence: List[Parser[String]]
      = List( "||", "^", "&&"|"&", "<="|">="|"<"|">", "=="|"!=", "+"|"-", "*"|"/"|"%", ":" )

  /* all infix operators not listed in operator_precedence have the same highest precedence */  
  val infixOpr: Parser[String]
      = accept("infix operator",{ case t: lexical.InfixOpr => t.chars })
  val precedence: List[Parser[String]]
      = operator_precedence :+ infixOpr
  val allInfixOpr: Parser[String]
      = operator_precedence.fold(infixOpr)(_|_)

  /* group infix operations into terms based on the operator precedence, from low to high */
  def terms ( level: Int ): Parser[(Expr,Expr)=>Expr]
      = precedence(level) ^^
        { op => (x:Expr,y:Expr) => MethodCall(x,op,List(y)) }
  def infix ( level: Int ): Parser[Expr]
      = if (level >= precedence.length) conses
        else infix(level+1) * terms(level)

  def fromRaw ( s: String ): String = s.replaceAllLiterally("""\n""","\n")
        
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
      = rep1sep( matches, "::" ) ^^
        { es => es.init.foldRight(es.last)
                  { case (e,r) => MethodCall(r,"::",List(e)) } }

  def matches: Parser[Expr]
      = factor ~ rep( "match" ~ "{" ~ rep1sep( "case" ~ pat ~ opt( "if" ~> expr ) ~ "=>" ~ expr, sem ) ~ "}" ) ^^
        { case a~as
            => as.foldLeft(a){ case (r,_~_~cs~_)
                                 => MatchE(r,cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                                     case _~p~_~_~b => Case(p,BoolConst(true),b) }) } }

 def factorList ( e: Expr ): Parser[Expr]
     = ( "[" ~ rep1sep( expr, "," ) ~ "]" ^^
         { case _~s~_ => Index(e,s) }
       | "." ~ ident ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
         { case _~m~_~el~_ => MethodCall(e,m,el) }
       | "." ~ ident ^^
         { case _~a => Project(e,a) }
       | "#" ~ int ^^
         { case _~n => Nth(e,n) }
       )

 def factor: Parser[Expr]
      = term ~ rep( factorList(IntConst(0)) ) ^^
        { case e~s => s.foldLeft(e){
                          case (r,Project(_,a)) => Project(r,a)
                          case (r,Nth(_,n)) => Nth(r,n)
                          case (r,Index(_,s)) => Index(r,s)
                          case (r,_) => r } }

  def qual: Parser[Qualifier]
      = ( "group" ~ "by" ~ pat ~ opt( ":" ~ expr ) ^^
          { case _~_~p~Some(_~e) => GroupByQual(p,e)
            case _~_~p~None => GroupByQual(p,AST.toExpr(p)) }
        | "let" ~ pat ~ "=" ~ expr ^^
          { case _~p~_~e => LetBinding(p,e) }
        | pat ~ ("<-" | "=") ~ expr ^^
          { case p~_~e => Generator(p,e) }
        | expr ^^ Predicate
        | failure("illegal start of qualifier")
        )

  def compr: Parser[Comprehension]
    = "[" ~ expr ~ "|" ~ repsep( qual, "," ) ~ "]" ^^
      { case _~e~_~qs~_ => Comprehension(e,qs) }

  def term: Parser[Expr]
      = ( compr
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ~ opt( compr ) ^^
          { case n~_~el~_~Some(c) => Call(n,List(Tuple(el),c))
            case n~_~es~_~None => Call(n,es) }
        | ident ~ compr ^^
          { case n~c => Call(n,List(c)) }
        | ident ~ "{" ~ ident ~ "=>" ~ compr ~ "}" ~ expr ^^
          { case n~_~v~_~c~_~e => Call(n,List(Lambda(VarPat(v),c),e)) }
        | "if" ~ "(" ~ expr ~ ")" ~ expr ~ "else" ~ expr ^^
          { case _~_~p~_~t~_~e => IfE(p,t,e) }
        | "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case _~es~_ => if (es.length==1) es.head else Tuple(es) }
        | "<" ~ rep1sep( ident ~ "=" ~ expr, "," ) ~ ">" ^^
          { case _~es~_ => Record(es.map{ case n~_~v => (n,v) }.toMap) }
        | "true" ^^^ { BoolConst(true) }
        | "false" ^^^ { BoolConst(false) }
        | "{" ~> rep1sep( "case" ~ pat ~ opt( "if" ~> expr ) ~ "=>" ~ expr, sem ) <~ "}" ^^
          { cs => { val nv = AST.newvar
                    Lambda(VarPat(nv),
                           MatchE(Var(nv),
                                  cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                          case _~p~_~_~b => Case(p,BoolConst(true),b) })) } }
        | "(" ~ repsep( pat, "," ) ~ ")" ~ "=>" ~ expr ^^
          { case _~ps~_~_~b => Lambda(TuplePat(ps),b) }
        | ident ~ "=>" ~ expr ^^
          { case v~_~b => Lambda(VarPat(v),b) }
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

  def pat: Parser[Pattern]
      = ( "(" ~ repsep( pat, "," ) ~ ")"
          ^^ { case _~ps~_ => if (ps.length==1) ps.head else TuplePat(ps) }
        | "_"
          ^^^ { StarPat() }
        | ident
          ^^ { s => if (s == "_") StarPat() else VarPat(s) }
        | failure("illegal start of pattern")
        )

  def stmt: Parser[Stmt]
      = ( "var" ~ ident ~ ":" ~ stype ~ opt( "=" ~ expr ) ^^
          { case _~v~_~t~None => VarDeclS(v,Some(t),None)
            case _~v~_~t~Some(_~e) => VarDeclS(v,Some(t),Some(e)) }
        | "var" ~ ident ~ "=" ~ expr ^^
          { case _~v~_~e => VarDeclS(v,None,Some(e)) }
        | "typemap" ~ opt("[" ~ rep1sep(ident,",") ~ "]") ~ stype ~ "to" ~ stype ~ "with" ~ expr ~ "," ~ expr ^?
          { case _~Some(_~s~_)~ft~_~tt~_~(h1@Lambda(_,_))~_~(h2@Lambda(_,_))
              => TypeMapS(s,ft,tt,h1,h2)
            case _~None~ft~_~tt~_~(h1@Lambda(_,_))~_~(h2@Lambda(_,_))
              => TypeMapS(Nil,ft,tt,h1,h2) }
        | "{" ~ rep( stmt ~ ";" ) ~ "}" ^^
          { case _~ss~_ => if (ss.length==1) ss.head match { case s~_ => s }
                           else BlockS(ss.map{ case s~_ => s }) }
        | factor ~ "=" ~ expr ^?
          { case (d:Var)~_~e => AssignS(d,e)
            case (d:Nth)~_~e => AssignS(d,e)
            case (d:Project)~_~e => AssignS(d,e)
            case (d:Index)~_~e => AssignS(d,e) }
        | factor ~ ( "+=" | "*=" | "&&=" | "||=" ) ~ expr ^?
          { case (d:Var)~op~e => AssignS(d,MethodCall(d,op.init,List(e)))
            case (d:Nth)~op~e => AssignS(d,MethodCall(d,op.init,List(e)))
            case (d:Project)~op~e => AssignS(d,MethodCall(d,op.init,List(e)))
            case (d:Index)~op~e => AssignS(d,MethodCall(d,op.init,List(e))) }
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
        | "def" ~ ident ~ "(" ~ repsep( ident ~ ":" ~ stype, "," ) ~ ")" ~ ":" ~ stype ~ stmt ^^
          { case _~f~_~params~_~_~tp~body
              => DefS(f,params.map{ case v~_~t => (v,t) }.toMap,tp,body) }
        | "return" ~ expr ^^
          { case _~e => ReturnS(e) }
        | expr ^^ ExprS
        | failure("illegal start of statement")
       )

  def stype: Parser[Type]
      = simpleType ~ rep( "->" ~ stype ) ^^
        { case d~ts => ts.foldRight(d){ case (_~t,r) => FunctionType(r,t) } }

  def simpleType: Parser[Type]
      = ( "(" ~ rep1sep( stype, "," ) ~ ")" ^^
          { case _~ts~_ => if (ts.length==1) ts.head else TupleType(ts) }
        | "<" ~ rep1sep( ident ~ ":" ~ stype, "," ) ~ ">" ^^
          { case _~cs~_ => RecordType(cs.map{ case n~_~t => (n,t)}.toMap) }
        | "array" ~ "[" ~ int ~ "," ~ stype ~ "]" ^^
          { case _~_~d~_~t~_ => ArrayType(d,t) }
        | ident ~ "[" ~ rep1sep( stype, "," ) ~ "]" ^^
          { case "list"~_~List(t)~_ => SeqType(t)
            case "vector"~_~List(t)~_ => ArrayType(1,t)
            case "matrix"~_~List(t)~_ => ArrayType(2,t)
            case n~_~ts~_ => ParametricType(n,ts) }
        | ident ~ opt("*") ~ "[" ~ rep1sep( stype, "," ) ~ "]" ^^
          { case n~Some(_)~_~ts~_ => ParametricType(n+"*",ts)
            case n~None~_~ts~_ => ParametricType(n,ts) }
        | ident ^^ { s => BasicType(s) }
        )

  def program: Parser[Stmt]
      = rep( stmt ~ sem ) ^^
        { ss => BlockS(ss.map{ case s~_ => s }) }

  /** Parse a statement */
  def parse ( line: String ): Stmt
      = phrase(program)(new lexical.Scanner(line)) match {
          case Success(e,_) => e:Stmt
          case m => println(m); BlockS(Nil)
        }

  def main ( args: Array[String] ) {
    println(edu.uta.diablo.Pretty.print(parse(args(0)).toString))
  }
}
