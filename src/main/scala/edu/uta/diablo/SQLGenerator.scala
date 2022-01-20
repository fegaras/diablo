/*
 * Copyright © 2022 University of Texas at Arlington
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

object SQLGenerator {
  import AST._
  import ComprehensionTranslator._
  import Typechecker.{typecheck,bindPattern,unfold_storage_type,typecheck_var}

  type Env = Map[String,Expr]

  case class SQL ( select: List[Expr], from: Env, where: List[Expr],
                   groupBy: Option[Expr], having: List[Expr] )

  def bind ( p: Pattern, e: Expr, env: Env ): Env
    = p match {
        case VarPat(v)
          => env+(v->e)
        case TuplePat(ps)
          => e match {
               case Tuple(es)
                 => (ps zip es).foldLeft(env) { case (m,(q,u)) => bind(q,u,m) }
               case _ => ps.zipWithIndex.foldLeft(env) { case (m,(q,i)) => bind(q,Nth(e,i+1),m) }
             }
        case _ => env
      }

  def translate ( hs: Expr, qs: List[Qualifier] ): (SQL,List[Expr]) = {
    val (el,SQL(s,f,w,g,h),env)
        = qs.foldLeft[(List[Expr],SQL,Env)]((Nil,SQL(Nil,Map(),Nil,None,Nil),Map())) {
             case ((es,SQL(s,f,w,g,h),env),e)
               => e match {
                    case Generator(VarPat(v),Range(n1,n2,n3))
                      => val (nn1,el1) = translate(n1,env)
                         val (nn2,el2) = translate(MethodCall(n2,"-",List(IntConst(1))),env)
                         val (nn3,el3) = translate(n3,env)
                         val nu = Call("range",List(nn1,nn2,nn3))
                         (es++el1++el2++el3,SQL(s,f+(v->nu),w,g,h),env+(v->MethodCall(Var(v),"id",null)))
                    case Generator(p,Lift("dataset",u))
                      => val v = newvar
                         val nu = translate_domain(u)
                         val view = MethodCall(nu,"createOrReplaceTempView",List(StringConst(v)))
                         (es:+view,SQL(s,f+(v->Var(v)),w,g,h),bind(p,Var(v),env+(v->Var(v))))
                    case Generator(p,Lift("rdd",u))
                      => val v = newvar
                         val nu = translate_domain(u)
                         val view = MethodCall(MethodCall(nu,"toDF",null),
                                               "createOrReplaceTempView",List(StringConst(v)))
                         (es:+view,SQL(s,f+(v->Var(v)),w,g,h),bind(p,Var(v),env+(v->Var(v))))
                    case Generator(p,u)
                      => throw new Error("Cannot convert to SQL: "+Comprehension(hs,qs))
                    case Predicate(u)
                      if g.isEmpty
                      => val (nu,el) = translate(u,env)
                         (es++el,SQL(s,f,w:+nu,g,h),env)
                    case Predicate(u)
                      => val (nu,el) = translate(u,env)
                         (es++el,SQL(s,f,w,g,h:+nu),env)
                    case LetBinding(p,u)
                      => val (nu,el) = translate(u,env)
                         (es++el,SQL(s,f,w,g,h),bind(p,nu,env))
                    case GroupByQual(p,k)
                      => val (nk,el) = translate(k,env)
                         (es++el,SQL(s,f,w,Some(nk),h),bind(p,nk,env))
                  }
          }
    val (nh,nl) = translate(hs,env)
    ( nh match {
         case Tuple(ts)
           => SQL(ts,f,w,g,h)
         case _ => SQL(List(nh),f,w,g,h)
      }, el++nl )
  }

  def translate_domain ( e: Expr ): Expr
    = e match {
        case Nth(u,n)
          => Nth(translate_domain(u),n)
        case _ => e
      }

  val sql_oprs = Map( "+"->"+", "-"->"-", "*"->"*", "/"->"/", "%"->"%",
                      "&&" -> "and", "||" -> "or",
                      "=="->"=", "<"->"<", ">"->">", "<="->"<=", ">="->">=" )

  val sql_udafs = Map( "+"->"SUM", "*"->"PROD", "max"->"MAX", "min"->"MIN" )

  def typeof ( v: String, e: Expr ): Type
    = e match {
        case Var(w) if w==v => e.tpe
        case _ => accumulate[Type](e,typeof(v,_),(x:Type,y:Type)=>if (x==null) y else x,null)
      }

  def localvars ( vars: List[String], env: Env ): List[String]
    = vars.flatMap(v => if (env.contains(v))
                          if (Var(v) == env(v))
                            List(v)
                          else List(v)//v::localvars(freevars(env(v)),env)
                        else Nil)

  def translate ( e: Expr, env: Env ): (Expr,List[Expr])
    = e match {
        case Var(v)
          if env.contains(v)
          => if (env(v) == e) (e,Nil) else translate(env(v),env)
        case Var(v)
          => typecheck_var(v) match {
                case Some(tp)
                  => val fname = "f"+newvar
                     (Call(fname,Nil),
                      List(Block(List(Def(fname,Nil,tp,e),
                                      MethodCall(MethodCall(Var("spark"),"udf",null),
                                                 "register",
                                                 List(StringConst(fname),Call("udf",List(Var(fname)))))))))
                case _ => (e,Nil)
             }
        case IntConst(n) => (e,Nil)
        case LongConst(n) => (e,Nil)
        case BoolConst(n) => (e,Nil)
        case DoubleConst(n) => (e,Nil)
        case StringConst(n) => (e,Nil)
        case Nth(u,n)
          => val (cu,ds) = translate(u,env)
             (Nth(cu,n),ds)
        case Tuple(es)
          => val (ces,ds)
                = es.foldLeft[(List[Expr],List[Expr])]((Nil,Nil)) {
                     case ((cs,ds),u)
                       => val (cu,d) = translate(u,env)
                          (cs:+cu,ds++d)
                  }
             (Tuple(ces),ds)
        case Call(f,es) 
          if List("range").contains(f)
          => val (ces,ds)
                = es.foldLeft[(List[Expr],List[Expr])]((Nil,Nil)) {
                     case ((cs,ds),u)
                       => val (cu,d) = translate(u,env)
                          (cs:+cu,ds++d)
                  }
             (Call(f,ces),ds)
        case MethodCall(x,"id",null)
          => (e,Nil)
        case MethodCall(x,f,List(y))
          if List("contains").contains(f)
          => val (cx,nx) = translate(x,env)
             val (cy,ny) = translate(y,env)
             (MethodCall(cx,f,List(cy)),nx++ny)
        case MethodCall(x,op,List(y))
          if sql_oprs.contains(op)
          => val (cx,nx) = translate(x,env)
             val (cy,ny) = translate(y,env)
             (MethodCall(cx,sql_oprs(op),List(cy)),nx++ny)
        case reduce(op,u)
          if sql_udafs.contains(op)
          => val (cu,ds) = translate(u,env)
             (Call(sql_udafs(op),List(cu)),ds)
        case reduce(f,u)
          => val (cu,ds) = translate(u,env)
             (Call(f,List(cu)),ds)
        case _
          => val fs = localvars(freevars(e),env).distinct
             val fname = "f"+newvar
             val type_env = fs.map(v => (v,typeof(v,e)))
             val tenv = type_env.toMap
             val tp = typecheck(e,tenv)
             val args = fs.map(x => tenv(x) match {
                                         case SeqType(_)
                                           => Call("collect_list",List(env(x)))
                                         case _ => env(x)
                                    })
             // Spark UDFs can handle at most 10 arguments
             if (fs.length > 10) {
               val nv = newvar
               (Call(fname,List(Tuple(args))),   // put args in a tuple
                List(Block(List(Def(fname,List((nv,tuple(type_env.map(_._2)))),tp,
                                    MatchE(Var(nv),List(Case(tuple(fs.map(VarPat(_))),BoolConst(true),e)))),
                                MethodCall(MethodCall(Var("spark"),"udf",null),
                                           "register",
                                           List(StringConst(fname),Call("udf",List(Var(fname)))))))))
             } else (Call(fname,args),
                     List(Block(List(Def(fname,type_env,tp,e),
                                     MethodCall(MethodCall(Var("spark"),"udf",null),
                                                "register",
                                                List(StringConst(fname),Call("udf",List(Var(fname)))))))))
      }

  def toSQL ( e: Expr ): String
    = e match {
        case Var(v) => v
        case IntConst(n) => n.toString
        case LongConst(n) => n.toString
        case BoolConst(n) => n.toString
        case DoubleConst(n) => n.toString
        case StringConst(n)
          => "\'"+n+"\'"
        case Nth(x,n)
          => toSQL(x)+"._"+n
        case Tuple(es)
          => "("+es.map(toSQL).mkString(",")+")"
        case MethodCall(x,"id",null)
          => toSQL(x)+".id"
        case MethodCall(x,"contains",es)
          => "array_contains("+toSQL(x)+","+es.map(toSQL).mkString(",")+")"
        case MethodCall(x,op,List(y))
          => "("+toSQL(x)+" "+op+" "+toSQL(y)+")"
        case Call(f,es)
          => f+"("+es.map(toSQL).mkString(",")+")"
        case _ => e.toString
      }

  def toSQL ( sql: SQL ): String
    = sql match {
          case SQL(ts,f,w,g,h)
            => val tss = ts.zipWithIndex.map{ case (t,i) => toSQL(t)+" AS _"+(i+1) }.mkString(", ")
               val fs = f.map{ case (v,Var(w)) if v==w => v
                               case (v,u) => toSQL(u)+" AS "+v }.mkString(", ")
               val ws = if (w.isEmpty) "" else " WHERE "+w.map(toSQL).mkString(" and ")
               val gs = g match {
                          case Some(Tuple(es))
                            => " GROUP BY "+es.map(toSQL).mkString(", ")
                          case Some(e)
                            => " GROUP BY "+toSQL(e)
                          case _ => ""
                        }
               val hs = if (h.isEmpty) "" else " HAVING "+h.map(toSQL).mkString(" and ")
               "SELECT "+tss+" FROM "+fs+ws+gs+hs
      }

  def translate_sql ( h: Expr, qs: List[Qualifier] ): Expr = {
    val tp = typecheck(Comprehension(h,qs))
    val (se,el) = translate(h,qs)
    val sql = toSQL(se)
    Block( el:+MethodCall(Var("spark"),"sql",List(StringConst(sql))) )
  }

  def translate_sql ( h: Expr, qs: List[Qualifier], acc: Lambda, zero: Expr, map: Option[Lambda] ): Expr = {
    val tp = typecheck(Comprehension(h,qs))
    val ztp = typecheck(zero)
    val (se,el) = translate(h,qs)
    val SQL(List(index,value),f,w,None,Nil) = se
    val rname = newvar
    val update = Assign(Var("result"),Seq(List(Apply(acc,Tuple(List(Var("result"),Var("x")))))))
    val reducer = Def(rname,List(("s",SeqType(ztp))),ztp,
                      Block(List(VarDecl("result",ztp,Seq(List(zero))),
                                 flatMap(Lambda(VarPat("x"),Seq(List(update))),
                                         Var("s")),
                                 Var("result"))))
    val aggr = MethodCall(MethodCall(Var("spark"),"udf",null),
                          "register",
                          List(StringConst(rname),Call("udf",List(Var(rname)))))
    map match {
       case Some(Lambda(mp,mb))
         => val mname = newvar
            val mtp = typecheck(mb,bindPattern(mp,unfold_storage_type(ztp),Map()))
            val mapper = Def(mname,List(("_x",ztp)),mtp,MatchE(Var("_x"),List(Case(mp,BoolConst(true),mb))))
            val mapr = MethodCall(MethodCall(Var("spark"),"udf",null),
                                  "register",
                                  List(StringConst(mname),Call("udf",List(Var(mname)))))
            val sql = toSQL(SQL(List(index,Call(mname,List(Call(rname,List(Call("collect_list",
                                                                                List(value))))))),
                                f,w,Some(index),Nil))
            Block( el:+reducer:+aggr:+mapper:+mapr
                   :+MethodCall(Var("spark"),"sql",List(StringConst(sql))) )
       case _
         => val sql = toSQL(SQL(List(index,Call(rname,List(Call("collect_list",List(value))))),
                                f,w,Some(index),Nil))
            Block( el:+reducer:+aggr
                   :+MethodCall(Var("spark"),"sql",List(StringConst(sql))) )
    }
  }
}
