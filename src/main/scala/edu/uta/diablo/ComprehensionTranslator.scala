/*
 * Copyright © 2020-2022 University of Texas at Arlington
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

import scala.annotation.tailrec
import scala.util.matching.Regex


object ComprehensionTranslator {
  import AST._
  import Typechecker._
  import Lifting.{store,lift,getTypeMap}
  import TypeMappings.{block_tensor_tiles}
  import SQLGenerator.{translate_sql,outerJoinSQL}

  val ignore: Expr = Block(Nil)

  // Tensor used in the current assignment
  var array_assignment: Option[Expr] = None

  // Block tensor used in the current assignment
  var block_array_assignment: Option[Expr] = None

  @tailrec
  def zeroValue(tp: Type ): Expr
    = if (tp == intType) IntConst(0)
      else if (tp == longType) LongConst(0)
      else if (tp == doubleType) DoubleConst(0.0)
      else if (tp == boolType) BoolConst(false)
      else tp match {
          case SeqType(_) => Var("Nil")
          case TupleType(List(etp)) => zeroValue(etp)
          case _ => Var("null")
      }

  def zeroValue ( monoid: String, tp: Type ): Expr = {
    def error (): Expr = throw new Error("The monoid "+monoid+" for type "+tp+" does not have a zero value")
    if (tp == intType)
       monoid match { case "+" => IntConst(0); case "*" => IntConst(1)
                      case "min" => IntConst(Int.MinValue)
                      case "max" => IntConst(Int.MaxValue)
                      case _ => error() }
    else if (tp == longType)
       monoid match { case "+" => LongConst(0)
                      case "*" => LongConst(1)
                      case "min" => LongConst(Long.MinValue)
                      case "max" => LongConst(Long.MaxValue)
                      case _ => error() }
    else if (tp == doubleType)
       monoid match { case "+" => DoubleConst(0.0)
                      case "*" => DoubleConst(1.0)
                      case "min" => DoubleConst(Double.MinValue)
                      case "max" => DoubleConst(Double.MaxValue)
                      case _ => error() }
    else if (tp == boolType)
       monoid match { case "&&" => BoolConst(true)
                      case "||" => BoolConst(false)
                      case _ => error() }
    else error()
  }

  def optimize ( e: Expr ): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

  /* general span for comprehensions; if a qualifier matches, split there and continue with cont */
  @tailrec
  def matchQ ( qs: List[Qualifier], filter: Qualifier => Boolean,
               cont: List[Qualifier] => Option[List[Qualifier]] ): Option[List[Qualifier]]
    = qs match {
        case q::r
          if filter(q)
          => cont(qs) match {
               case r@Some(s) => r
               case _ => matchQ(r,filter,cont)
             }
        case _::r
          => matchQ(r,filter,cont)
        case _ => None
    }

  def tuple ( s: List[Expr] ): Expr
    = s match { case List(x) => x; case _ => Tuple(s) }

  def tuple ( s: List[Pattern] ): Pattern
    = s match { case List(x) => x; case _ => TuplePat(s) }

  def tuple ( s: List[Type] ): Type
    = s match { case List(x) => x; case _ => TupleType(s) }

  val tensor_pat: Regex = """(full_|)tensor_(\d+)_(\d+)""".r
  val bool_tensor_pat: Regex = """(full_|)bool_tensor_(\d+)_(\d+)""".r

  def isTensor ( name: String ): Boolean
    = name match { case tensor_pat(_,_,_) => true
                   case bool_tensor_pat(_,_,_) => true
                   case _ => false }

  def isTensor ( e: Expr ): Boolean
    = e match { case Lift(tensor,_) => isTensor(tensor); case _ => false }

  def isBoolTensor ( name: String ): Boolean
    = name match { case bool_tensor_pat(_,_,_) => true; case _ => false }

  def tensor_dims ( name: String ): (Int,Int)
    =  name match {
         case tensor_pat(_,dn,sn) => (dn.toInt,sn.toInt)
         case bool_tensor_pat(_,dn,sn) => (dn.toInt,sn.toInt)
         case _ => (0,0)
       }

  val block_tensor_pat: Regex = """(full_|)(rdd|dataset)_block_tensor_(\d+)_(\d+)""".r
  val block_bool_tensor_pat: Regex = """(full_|)(rdd|dataset)_block_bool_tensor_(\d+)_(\d+)""".r

  def isBlockTensor ( name: String ): Boolean
    = name match {
        case block_tensor_pat(_,_,_,_) => true
        case block_bool_tensor_pat(_,_,_,_) => true
        case _ => false
      }

  def isDatasetTensor ( name: String ): Boolean
    = name match {
        case block_tensor_pat(_,"dataset",_,_) => true
        case block_bool_tensor_pat(_,"dataset",_,_) => true
        case _ => false
      }

  def block_type ( name: String ): String
    = name match {
        case block_tensor_pat(_,tp,_,_) => tp
        case block_bool_tensor_pat(_,tp,_,_) => tp
        case _ => ""
      }

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
    }

  def isSparseTensor ( e: Expr ): Boolean
    = e match {
        case Lift(name,_)
          => name match {
                case tensor_pat(_,_,sn) => sn.toInt > 0
                case bool_tensor_pat(_,_,sn) => sn.toInt > 0
                case _ => false }
        case _ => false
      }

  def unlift_comprehensions ( e: Expr ): Expr
    = e match {
        case Lift(f,x)
          => lift(f,x)
        case Comprehension(h,qs)
          => optimize(Comprehension(h,qs.map(q => apply(q,(u:Expr) => unlift_comprehensions(u)))))
        case reduce(_,_)
          => e
        case _
          => apply(e,unlift_comprehensions)
      }

  /* default translator for list comprehensions with no group-by */
  def default_translator_nogb ( h: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.foldRight[(Expr,List[String])]((Seq(List(translate(h,vars))),vars)) {
         case (Generator(p,u),(r,s))
           => (flatMap(Lambda(p,r),translate(u,s)),
               patvars(p)++s)
         case (LetBinding(p,u),(r,s))
           => (Let(p,translate(u,s),r),
               patvars(p)++s)
         case (Predicate(p),(r,s))
           => (IfE(translate(p,s),r,Seq(Nil)),s)
         case (AssignQual(d,u),(r,s))
           => (Block(List(Assign(d,Seq(List(u))),r)),s)
         case (VarDef(v,t,u),(r,s))
           => (Block(List(VarDecl(v,t,Seq(List(u))),r)),s)
         case (_,(r,s)) => (r,s)
      }._1

  /* default translator for list comprehensions */
  def default_translator ( h: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
               case (r,GroupByQual(p,k)::s)
                 => val groupByVars = patvars(p)
                    val usedVars = freevars(Comprehension(h,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                    val sv = newvar
                    val nr = default_translator(Tuple(List(k,tuple(usedVars.map(Var)))),r,vars)
                    val unzips = usedVars.map(v => LetBinding(VarPat(v),
                                                              flatMap(Lambda(tuple(usedVars.map(VarPat)),
                                                                             Seq(List(Var(v)))),
                                                                      Var(sv))))
                    default_translator(h,Generator(TuplePat(List(p,VarPat(sv))),
                                                   groupBy(nr))::(unzips++s),vars)
               case _ 
                 => val Comprehension(nh,nqs) = unlift_comprehensions(Comprehension(h,qs))
                    default_translator_nogb(nh,nqs,vars)
             }

/*---------------------------- Generate tensor operations ------------------------------------------*/

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(u@Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("_x"),Seq(List(IntConst(1)))),u))
        case Project(u@Var(v),"length")
          if vars.contains(v)
          => reduce("+",flatMap(Lambda(VarPat("_x"),Seq(List(IntConst(1)))),u))
        case _ => apply(e,yieldReductions(_,vars))
    }

  def findReducedTerms ( e: Expr, vars: List[String] ): List[(String,Expr)]
    = e match {
        case reduce(_,Var(v))
          if vars.contains(v)
          => List((v,e))
        case reduce(_,flatMap(_,Var(v)))
          if vars.contains(v)
          => List((v,e))
        case Var(v)
          if vars.contains(v)
          => List((v,e))
        case _ => accumulate[List[(String,Expr)]](e,findReducedTerms(_,vars),_++_,Nil)
      }

  def mcall ( m: String, x: Expr, y: Expr ): Expr
    = if (m.matches("^[a-zA-Z0-9_]*$"))
        Call(m,List(x,y))
      else MethodCall(x,m,List(y))

  /* translate a tensor comprehension with a group-by when the group-by key is equal to the head key */
  def tensor_groupby_eqkey ( tensor: String, tp: Type, dims: List[Expr],
                             head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => assert(toExpr(p) == key,"The group-by key must be equal to the head key")
                   val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dims.length
                   val vars = dims.map(x => newvar)
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   // the map index in row-major format
                   val idx = dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    Index(Var(xv),List(idx)))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t,Index(Var(v),List(idx))) } ++ lvs
                   // replace the reduced terms in head and ts with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => subst(from,to,r)
                                               }
                   val size = dims.reduce[Expr]{ case (x,y) => MethodCall(x,"*",List(y)) }
                   val dsize = if (dn==0) IntConst(0)
                               else dims.take(dn).reduce[Expr]{ case (x,y) => MethodCall(x,"*",List(y)) }
                   val ssize = if (sn==0) IntConst(0)
                               else dims.drop(dn).reduce[Expr]{ case (x,y) => MethodCall(x,"*",List(y)) }
                   // all vectors used in aggregations are vectors of size d1*d2*...
                   def vector_decl ( v: String, tp: Type )
                     = VarDecl(v,ArrayType(1,tp),
                               Seq(List(Call("array_buffer_dense",List(size,zeroValue(tp))))))
                   // vector declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(vector_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => vector_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(Index(Var(xv),List(idx)),
                                                     MethodCall(Index(Var(xv),List(idx)),
                                                                ":+",
                                                                List(tuple(liftedVars.map(Var))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     mcall(m,Index(Var(v),List(idx)),Apply(Lambda(p,u),x))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(Index(Var(v),List(idx)),
                                                     mcall(m,Index(Var(v),List(idx)),x)))
                                case _ => Nil
                              }
                   // the traversal indices are i1, i2, ... with i1<d1, i2<d2, ...
                   val conds = dims.zipWithIndex.map {
                                  case (d,i) => Predicate(MethodCall(Var("i"+(i+1)),"<",List(d)))
                               }
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),k)::
                                  conds++xvincr++incr)
                   val buffer = "buffer"   // dense vector that holds the result values
                   val zero = zeroValue(tp)
                   def convert ( e: Expr ): Expr
                     = if (sn == 0)
                         e     // the result is a dense tensor
                       else if (dn == 0)
                              if (isBoolTensor(tensor))
                                Call("array2tensor_bool",List(ssize,e))
                              else Call("array2tensor",List(ssize,zero,e))
                              else if (isBoolTensor(tensor))
                                     Call("array2tensor_bool",List(dsize,ssize,e))
                              else Call("array2tensor",List(dsize,ssize,zero,e))
                   def build ( zero: Expr, array: Expr ): Expr
                     = if (sn == 0)
                         Call("array_buffer_dense",List(dsize,zero,array))
                       else if (dn == 0)
                              if (isBoolTensor(tensor))
                                Call("array_buffer_sparse_bool",List(ssize,array))
                              else Call("array_buffer_sparse",List(ssize,zero,array))
                              else if (isBoolTensor(tensor))
                                     Call("array_buffer_bool",List(dsize,ssize,array))
                              else Call("array_buffer",List(dsize,ssize,zero,array))
                   val b = ne match {
                             case Index(Var(v),_)
                               if reducedVars.contains(v) && ts.isEmpty
                               => val tp = reducedTermTypes(v)
                                  val dcl = array_assignment match {
                                                 case Some(a)   // buffer must be the assignment destination
                                                   => VarDecl(v,ArrayType(1,tp),
                                                              Seq(List(build(zeroValue(tp),a))))
                                                 case _ => vector_decl(v,tp)
                                            }
                                  Block(List(dcl,Comprehension(ignore,nqs++nts),convert(Var(v))))
                             case _
                               // when there are more qualifiers after group-by
                               // or the head value is not a simple aggregation
                               => val rs = dims.zipWithIndex.map {   // range over all indices
                                              case (d,i) => Generator(VarPat("i"+(i+1)),
                                                                 Range(IntConst(0),
                                                                       MethodCall(d,"-",List(IntConst(1))),
                                                                       IntConst(1)))
                                           }
                                  Block(vector_decl(buffer,tp)::init ++
                                        List(Comprehension(ignore,nqs),
                                             Comprehension(Assign(Index(Var(buffer),List(idx)),
                                                                  Seq(List(ne))),
                                                           rs++nts),
                                             convert(Var(buffer))))
                           }
                   val nb = unlift_comprehensions(b)
                   translate(tuple(dims:+nb),vars)
              case _ => default_translator(head,cqs,Nil)
            }
    }

  /* translate a tensor comprehension with a group-by when the group-by key is NOT equal to the head key */
  def tensor_groupby_neqkey ( tensor: String, tp: Type, dims: List[Expr],
                              head: Expr, cqs: List[Qualifier] ): Expr = {
    val Tuple(List(key,body)) = head
    val result_keys = key match { case Tuple(ks) => ks; case _ => List(key) }
    val (dn,sn) = tensor_dims(tensor)
    cqs.span{ case GroupByQual(p,k) => false; case _ => true } match {
              case (qs,GroupByQual(p,k)::ts)
                => val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(head,groupByVars).intersect(comprVars(qs)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(head,ts),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   // non-groupby variables that are used in a reduction in head
                   val reducedVars = reducedTerms.map(_._1)
                   // non-groupby variables used in head as is (not reduced)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   // the type of reduced terms
                   val reducedTermTypes = (reducedTerms.map{ case (v,u) => (v,typecheck(u)) }
                                           ++rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                               .map{ case (v,u) => (v,typecheck(u)) }).toMap
                   val ndims = dims.length
                   val vars = dims.map(x => newvar)
                   val xv = newvar    // the vector variable that contains the liftedVars values
                   // the map index in row-major format
                   val idx = dims.tail.zipWithIndex.foldLeft[Expr](Var("i1")) {
                                case (r,(e,i))
                                  => MethodCall(MethodCall(r,"*",List(e)),"+",List(Var("i"+(i+2))))
                             }
                   // the ith variable in liftedVars is computed from xv[idx].map(_.i)
                   val lvs = liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                     List(Generator(tuple(liftedVars.map(VarPat)),
                                                                    MapAccess(Var(xv),idx))))))
                   // vector values that compute all non-groupby variables in head
                   val env = reducedTerms.map{ case (v,t) => (t, MapAccess(Var(v),idx)) } ++ lvs
                   // replace the reduced terms in head with vector values using env
                   val Comprehension(ne,nts) = env.foldLeft(yieldReductions(Comprehension(body,ts),
                                                                            usedVars)) {
                                                   case (r,(from,to)) => subst(from,to,r)
                                               }
                   // all collections used in aggregations are Maps
                   def map_decl ( v: String, tp: Type )
                     = VarDecl(v,MapType(intType,tp),Seq(List(Call("map",Nil))))
                   // map declarations; xv vector is not needed if the head is a single aggregation
                   val init = (if (liftedVars.isEmpty) Nil
                               else List(map_decl(xv,TupleType(liftedVars.map(reducedTermTypes(_)))))) ++
                              reducedVars.map(v => map_decl(v,reducedTermTypes(v)))
                   // append the lifted variables not reduced to xv[idx]
                   val xvincr = if (liftedVars.isEmpty) Nil
                                else List(AssignQual(MapAccess(Var(xv),idx),
                                                     IfE(MethodCall(Var(xv),"contains",List(idx)),
                                                         MethodCall(MapAccess(Var(xv),idx),
                                                                    ":+",
                                                                    List(tuple(liftedVars.map(Var)))),
                                                         Seq(List(tuple(liftedVars.map(Var)))))))
                   // one vector update for each reduction
                   val incr = reducedTerms.flatMap {
                                case (v,reduce(m,flatMap(Lambda(p,Seq(List(u))),x)))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         mcall(m,MapAccess(Var(v),idx),Apply(Lambda(p,u),x)),
                                                         Apply(Lambda(p,u),x))))
                                case (v,reduce(m,x))
                                  => List(AssignQual(MapAccess(Var(v),idx),
                                                     IfE(MethodCall(Var(v),"contains",List(idx)),
                                                         mcall(m,MapAccess(Var(v),idx),x),
                                                         x)))
                                case _ => Nil
                              }
                   // the new comprehension qualifiers
                   val nqs = qs++(LetBinding(tuple(1.to(ndims).map(i => VarPat("i"+i)).toList),key)::
                                  xvincr++incr)
                   val rv = newvar
                   val rs = dims.zipWithIndex.map {   // range over all indices
                               case (d,i) => Generator(VarPat("i"+(i+1)),
                                                       Range(IntConst(0),
                                                             MethodCall(d,"-",List(IntConst(1))),
                                                             IntConst(1)))
                                             }
                   val conds = reducedTerms.map {
                                  case (v,t)
                                    => Predicate(MethodCall(Var(v),"contains",List(idx)))
                               }
                   val b = Block(VarDecl(rv,ArrayType(1,tp),
                                                Seq(List(Call("array",List(dims.reduce[Expr] {
                                                       case (x,y) => MethodCall(x,"*",List(y))
                                                     })))))::
                                        init ++ List(Comprehension(ignore,nqs),
                                                     Comprehension(Assign(Index(Var(rv),List(idx)),
                                                                          Seq(List(ne))),
                                                                   rs++conds++nts),
                                                     Var(rv)))
                   val res = if (sn == 0)
                               tuple(dims:+b)    // the result is already a dense tensor
                             else { val vv = newvar
                                    val iv = newvar
                                    val ivars = tuple(1.to(ndims).map(i => Var("i"+i)).toList)
                                    val pvars = tuple(1.to(ndims).map(i => VarPat("i"+i)).toList)
                                    // copy the dense result to a sparse tensor
                                    Block(List(VarDecl(vv,StorageType(s"tensor_${ndims}_0",List(tp),dims),
                                                       Seq(List(tuple(dims:+b)))),
                                               Store(tensor,List(tp),dims,
                                                     Comprehension(Tuple(List(ivars,Var(iv))),
                                                             List(Generator(TuplePat(List(pvars,
                                                                                     VarPat(iv))),
                                                                            Lift(s"tensor_${ndims}_0",
                                                                                 Var(vv))))))))
                                  }
                   translate(res,vars)
              case _ => default_translator(head,cqs,Nil)
            }
    }


/*---------------------------- Generate RDD operations ------------------------------------------*/

  /* Is this generator domain an RDD? Generator domains have been lifted by the Lifter */
  def isRDD ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case Lift("rdd",_) => true
        case Lift("dataset",_) => true
        case Lift("block_map",_) => true
        case _ => false
      }

  def is_rdd_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isRDD(u); case _ => false }

  def qual_vars ( qs: List[Qualifier] ): Set[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }.toSet

  def contains ( e: Expr, includes: Set[String], excludes: Set[String] ): Boolean = {
    val vars = freevars(e).toSet
    vars.intersect(includes).nonEmpty &&
      vars.intersect(excludes.diff(includes)).isEmpty
  }

  // for a lifted RDD storage, return the RDD collection
  def get_rdd ( e: Expr ): Expr
    = e match {
        case Lift(block_tensor_pat(_,_,dn,sn),x)
          => block_tensor_tiles(dn.toInt,sn.toInt,x)
        case Lift(block_bool_tensor_pat(_,_,dn,sn),x)
          => block_tensor_tiles(dn.toInt,sn.toInt,x)
        case Lift("rdd",x) => x
        case Lift("dataset",x) => x
        case _ => e
      }

  def block_arrays_to_rdds ( qs: List[Qualifier] ): List[Qualifier]
    = qs.flatMap {
               case Generator(p,Lift(f@block_tensor_pat(_,_,dn,sn),x))
                 => List(Generator(p,lift(f,x)))
               case Generator(p,Lift(f@block_bool_tensor_pat(_,_,dn,sn),x))
                 => List(Generator(p,lift(f,x)))
               case q => List(q)
             }

  /* finds a sequence of predicates in qs that refer to the pattern variables xs */
  def findFilterPred ( xs: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]] = {
    val qvars = qual_vars(qs)
    matchQ(qs,{ case Predicate(e)
                    => contains(e,xs,qvars)
                  case _ => false },
                { case (p::s)
                    => findFilterPred(xs,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })
  }

  def findFilter ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case (Generator(p,e))::r
                    => findFilterPred(patvars(p).toSet,r) match {
                         case Some(ps)
                           => Some(Generator(p,get_rdd(e))::ps)
                         case _ => None }
                  case _ => None })

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]] = {
    val qvars = qual_vars(qs)
    matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((contains(e1,xs,qvars) && contains(e2,ys,qvars))
                        || (contains(e2,xs,qvars) && contains(e1,ys,qvars)))
                  case _ => false },
                { case (p::s)
                    => findEqPred(xs,ys,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })
  }

  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,e1)::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,
                                                              patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case Generator(p1,Lift(_,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                                 { case Generator(p2,Lift(_,e2))::r2
                                     => Some(List(Generator(p1,e1),
                                                  Generator(p2,e2)))
                                  case _ => None })
                  case _ => None })

  /* matches an RDD traversal */
  def findTraversal ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isRDD(e) => true; case _ => false },
                { case q::_
                    => Some(q::qs.filter(_ != q))
                  case _ => None })

  def translate_rdd ( hs: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
               case (r,GroupByQual(p,k)::s)        // RDD group-by becomes reduceByKey
                => val groupByVars = patvars(p)
                   // non-groupby variables used in head
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Seq(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case e
                                      => Seq(List(e))
                                  }
                   // aggregation monoids
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   // the reduceByKey merge function
                   val m = if (ms.length == 1)
                              Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                     mcall(ms.head,Var("_x"),Var("_y")))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y))
                                                         => mcall(m,Var(x),Var(y)) }))
                                }
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => subst(from,Var(to),r) }
                   val Comprehension(nh,ns) = lift(yieldReductions(Comprehension(hs,s),usedVars))
                   val red = MethodCall(Store("rdd",Nil,Nil,       // type parameter?
                                              Comprehension(Tuple(List(k,tuple(gs))),r)),
                                        "reduceByKey",List(m))
                   translate_rdd(nh,Generator(TuplePat(List(p,tuple(env.map(x => VarPat(x._2))))),
                                              red)::ns,vars)
              case _
                => findJoin(qs) match {      // RDD join
                     case Some((Generator(p1,d1))::(Generator(p2,d2))::cs)
                       => val qvars = qual_vars(qs)
                          val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p1).toSet,qvars)) e1 else e2 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (contains(e1,patvars(p2).toSet,qvars)) e1 else e2 })
                          val left = flatMap(Lambda(p1,Seq(List(Tuple(List(jt1,toExpr(p1)))))),
                                             get_rdd(d1))
                          val right = flatMap(Lambda(p2,Seq(List(Tuple(List(jt2,toExpr(p2)))))),
                                              get_rdd(d2))
                          val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("_x"))),
                                                                Seq(List(Var("_x")))),
                                                         MethodCall(left,"join",List(right,IntConst(number_of_partitions))))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the join
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)                       // don't remove join conditions
                              },vars)
              case _
                => findCross(qs) match {     // RDD cross product
                     case Some(List(Generator(p1,d1),Generator(p2,d2)))
                       => val z = Generator(TuplePat(List(p1,p2)),
                                            Lift("rdd",
                                                 MethodCall(get_rdd(d1),
                                                            "cartesian",
                                                            List(get_rdd(d2)))))
                          translate_rdd(hs,qs.flatMap {
                               case Generator(p,_) if p==p1 => List(z) // replace 1st generator with the cross
                               case Generator(p,_) if p==p2 => Nil     // remove 2nd generator
                               case x => List(x)
                              },vars)
              case _
                => findTraversal(qs) match {    // an RDD traversal
                     case Some(Generator(p,e)::nqs)
                       => flatMap(Lambda(p,translate_rdd(hs,nqs,patvars(p)++vars)),
                                  get_rdd(e))
                     case _ 
                       => qs.foldRight[(Expr,List[String])]((Seq(List(translate(hs,vars))),vars)) {
                             case (Generator(p,u),(r,s))
                               => (flatMap(Lambda(p,r),get_rdd(u)),
                                   patvars(p)++s)
                             case (LetBinding(p,u),(r,s))
                               => (Let(p,translate(u,vars),r),
                                   patvars(p)++s)
                             case (Predicate(p),(r,s))
                               => (IfE(translate(p,s),r,Seq(Nil)),s)
                             case (_,(r,s)) => (r,s)
                          }._1
                   }
              }
          }
    }

  def translate_dataset ( hs: Expr, qs: List[Qualifier], vars: List[String] ): Expr
    = if (data_frames)
        translate_sql(hs,qs)
      else translate_rdd(hs,qs,vars)


/*---------------------------- Tiled Comprehensions ------------------------------------------*/

  /* Is this generator domain a Tiled RDD? Generator domains have been lifted by the Lifter */
  def isTiled ( e: Expr ): Boolean
    = e match {
        case Lift(name,_) if isBlockTensor(name) => true
        case _ => false
      }

  def is_tiled_comprehension ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case Generator(p,u) => isTiled(u); case _ => false }

  def hasGroupBy ( qs: List[Qualifier] ): Boolean
    = qs.exists{ case GroupByQual(_,_) => true; case _ => false }

  def hasGroupByKey ( qs: List[Qualifier], key: Expr ): Boolean
    = qs.exists{ case GroupByQual(p,_) => key == toExpr(p); case _ => false }

  // tiled values are normaly (indices,value), but can be ((indices,value),(indices,value)) etc
  // if they are the results of a join
  def tile_indices ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(i),VarPat(_)))
          => List(i)
        case TuplePat(List(TuplePat(ps),VarPat(_)))
          if ps.forall(_.isInstanceOf[VarPat])
          => ps.flatMap{ case VarPat(i) => List(i); case _ => Nil }
        case TuplePat(ps)
          => ps.flatMap(tile_indices)
        case _ => Nil
      }

  def tile_indices ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_indices(p); case _ => Nil }

  def tile_values ( p: Pattern ): List[String]
    = p match {
        case TuplePat(List(VarPat(_),VarPat(v)))
          => List(v)
        case TuplePat(List(TuplePat(ps),VarPat(v)))
          if ps.forall(_.isInstanceOf[VarPat])
          => List(v)
        case TuplePat(ps)
          => ps.flatMap(tile_values)
        case _ => Nil
      }

  def tile_values ( qs: List[Qualifier] ): List[String]
    = qs.flatMap{ case Generator(p,u) if isTiled(u) => tile_values(p); case _ => Nil }

  def tile_type ( block: String ): String
    = block match {
        case block_tensor_pat(full,_,dn,sn)
          => s"${full}tensor_${dn}_$sn"
        case block_bool_tensor_pat(full,_,dn,sn)
          => s"${full}bool_tensor_${dn}_$sn"
      }

  def tile_type ( block: String, tp: Type ): String = {
    val isBool = tp == boolType
    block match {
        case block_tensor_pat(full,_,dn,sn)
          => if (isBool && sn.toInt > 0)
               s"${full}bool_tensor_${dn}_$sn"
              else s"${full}tensor_${dn}_$sn"
        case block_bool_tensor_pat(full,_,dn,sn)
          => if (isBool && sn.toInt > 0)
               s"${full}bool_tensor_${dn}_$sn"
              else s"${full}tensor_${dn}_$sn"
      }
  }

  def tileType ( block: String, tp: Type ): Type = {
     val Some(TypeMapS(_,tvs,args,_,st,_,_,_)) = Lifting.getTypeMap(tile_type(block,tp))
     TupleType(List(TupleType(args.map(tp => intType).toList),
                    substType(st,Some(tvs.map(tv => tv -> tp).toMap))))
  }


/*----------------------- Tiled comprehension without groupBy that preserves tiling -------------------
 * tensor*(...)[ ((i,j,...),e) | ... ]
 * Requirements:
 * 1) no group-by
 * 2) comprehension indices (i,j,...) are vars
 * 3) i,j,... are unique (indices from tensor*, tensor, and range)
 * ----------------------------------------------------------------------------------------------------*/

  def correlated_indices ( qs: List[Qualifier], indices: Set[String] ): Set[String]
    = qs.foldLeft(indices) {
        case (ks,Predicate(MethodCall(Var(i),"==",List(Var(j)))))
          => if (ks.contains(i))
               ks+j
             else if (ks.contains(j))
                    ks+i
             else ks
        case (ks,_) => ks
      }

  def unique_indices ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,u)
          if isTiled(u)
          => tile_indices(p)
        case Generator(TuplePat(List(k,_)),u)
          if isTensor(u)
          => patvars(k)
        case Generator(VarPat(i),Range(_,_,_))
          => List(i)
        case _ => Nil
      }

  def constant_int ( e: Expr ): Boolean
    = e match {
        case IntConst(_) => true
        case LongConst(_) => true
        case MethodCall(x,op,List(y))
          => List("*","+","%","/").contains(op) &&
                constant_int(x) && constant_int(y)
        case _ => false
      }

  def constant_index ( e: Expr ): Boolean
    = e match {
        case Var(_) => true
        case Tuple(s) => s.forall(constant_index)
        case _ => constant_int(e)
      }

  def preserves_tiling ( key: Expr, qs: List[Qualifier] ): Boolean
    = !hasGroupBy(qs) && constant_index(key) && {
         var key_vars = freevars(key).toSet
         val indices = unique_indices(qs).toSet
         val cis = correlated_indices(qs,key_vars)
         key_vars.forall(indices.contains) && indices == cis
      }

  def local_expr ( e: Expr, vars: List[String] ): Boolean
    = !freevars(e, vars).exists(v => typecheck_var(v).isEmpty)

  def rdd_qualifier_vars ( qs: List[Qualifier], vars: List[String] ): List[String]
    = qs.foldLeft[List[String]] (vars) {
          case (s,Generator(TuplePat(List(p,VarPat(v))),Lift(m,_)))
            if isTensor(m) || isBlockTensor(m)
            => s++patvars(p):+v
          case (s,Generator(p,Lift("rdd",_)))
            => s++patvars(p)
          case (s,Generator(p,Lift("dataset",_)))
            => s++patvars(p)
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,LetBinding(p,e))
            if local_expr(e,s)
            => s++patvars(p)
          case (s,_) => s
      }

  def prefix ( prefix: String, v: String ): String = "_"+prefix+"_"+v

  val block_pat: Regex = """(full_|)(dataset|rdd)_block_(bool_|)tensor_(\d+)_(\d+)""".r

  // from the comprehension qualifiers qs, generate the RDD qualifiers
  def rdd_qualifiers ( qs: List[Qualifier], vars: List[String], shuffle: Boolean = false ): List[Qualifier] = {
    val local_vars = rdd_qualifier_vars(qs,vars)
    val unique_is = unique_indices(qs)
    qs.flatMap (
        q => q match {
          case Generator(TuplePat(List(p,VarPat(v))),
                         Lift(block_pat(full,cm,bool,dn,sn),e))
            => val is = patvars(p)
               Generator(tuple(List(tuple(is.map(i => VarPat(prefix("coord",i)))),
                                    VarPat(prefix("tile",v)))),
                         Lift(cm,block_tensor_tiles(dn.toInt,sn.toInt,e)))::
                  (if (shuffle)   // will contain all needed tiles after group-by
                     List(LetBinding(VarPat(prefix("tiles",v)),
                                     tuple(List(tuple(is.map(i => Var(prefix("coord",i)))),
                                                Var(prefix("tile",v))))))
                   else Nil)
          case Generator(_,Lift("rdd",_))
            => List(q)
          case Generator(_,Lift("dataset",_))
            => List(q)
          case Generator(VarPat(i),Range(n1,n2,n3))
            => List(Generator(VarPat(prefix("coord",i)),
                              Range(MethodCall(n1,"/",List(IntConst(block_dim_size))),
                                    MethodCall(n2,"/",List(IntConst(block_dim_size))),
                                    n3)))
          case Generator(TuplePat(List(p,VarPat(v))),
                         Lift(tensor,e))
            if isTensor(tensor)
            => patvars(p).zipWithIndex.
                  map{ case (i,k) => Generator(VarPat(prefix("coord",i)),
                                          Range(IntConst(0),
                                                MethodCall(MethodCall(Nth(e,k+1),
                                                                      "-",List(IntConst(1))),
                                                           "/",List(IntConst(block_dim_size))),

                                                IntConst(1))) }
          case LetBinding(p,e)
            if freevars(e).intersect(local_vars).isEmpty
            => List(q)
          case Predicate(MethodCall(Var(i),"==",List(Var(j))))
            if unique_is.contains(i) && unique_is.contains(j)
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                                         "==",List(Var(prefix("coord",j))))))
/*
          case Predicate(MethodCall(Var(i),"==",List(e)))
            if unique_is.contains(i) && freevars(e,Nil).intersect(unique_is).isEmpty
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                         "==",List(MethodCall(e,"/",List(IntConst(block_dim_size)))))))
          case Predicate(MethodCall(e,"==",List(Var(i))))
            if unique_is.contains(i) && freevars(e,Nil).intersect(unique_is).isEmpty
            => List(Predicate(MethodCall(Var(prefix("coord",i)),
                          "==",List(MethodCall(e,"/",List(IntConst(block_dim_size)))))))
*/
          case _ => Nil
      })
  }

  def tile_vars ( qs: List[Qualifier], vars: List[String] ): List[String]
    = qs.foldLeft[List[String]] (vars) {
          case (s,Generator(TuplePat(List(p,VarPat(v))),Lift(m,_)))
            if isTensor(m) || isBlockTensor(m)
            => s++patvars(p):+v
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,LetBinding(p,e))
            if local_expr(e,s)
            => s++patvars(p)
          case (s,_) => s
      }

  def block_tile_vars ( qs: List[Qualifier] ): List[String]
    = qs.foldLeft[List[String]] (Nil) {
          case (s,Generator(TuplePat(List(p,VarPat(v))),Lift(m,_)))
            if isBlockTensor(m)
            => s++patvars(p):+v
          case (s,Generator(VarPat(i),Range(_,_,_)))
            => s:+i
          case (s,_) => s
      }

  // from the comprehension qualifiers qs, generate the tile qualifiers
  def tile_qualifiers ( qs: List[Qualifier], vars: List[String], shuffle: Boolean = false ): List[Qualifier] = {
    val local_vars = tile_vars(qs,vars)
    val block_vars = block_tile_vars(qs)
    qs.flatMap (
        q => q match {
          case Generator(p,Lift("rdd",_))
            => Nil   // goes into the rdd_qualifiers
          case Generator(p,Lift("dataset",_))
            => Nil   // goes into the rdd_qualifiers
          case Generator(TuplePat(List(p,VarPat(v))),
                         Lift(block,_))
            if isBlockTensor(block)
            => val is = patvars(p)
               val lbinds = is.zipWithIndex.map {
                                 case (i,k)
                                   => LetBinding(VarPat(i),
                                                 MethodCall(MethodCall(Var(prefix("coord",i)),
                                                                       "*",List(IntConst(block_dim_size))),
                                                            "+",List(Var(prefix("tile",i)))))
                            }
               (if (shuffle)
                  List(Generator(tuple(List(tuple(is.map(i => VarPat(prefix("coord",i)))),
                                            VarPat(prefix("tile",v)))),
                                 Var(prefix("tiles",v))))
                else Nil)++
               (Generator(tuple(List(tuple(is.map(i => VarPat(prefix("tile",i)))),VarPat(v))),
                          Lift(tile_type(block),Var(prefix("tile",v))))::lbinds)
          case Generator(VarPat(i),Range(n1,n2,n3))
            => List(Generator(VarPat(prefix("tile",i)),
                              Range(IntConst(0),
                                    MethodCall(Var(prefix("size",i)),
                                               "-",List(IntConst(1))),
                                    IntConst(1))),
                    LetBinding(VarPat(i),
                               MethodCall(MethodCall(Var(prefix("coord",i)),
                                                     "*",List(IntConst(block_dim_size))),
                                          "+",List(Var(prefix("tile",i))))))
          case Generator(TuplePat(List(p,VarPat(v))),
                         Lift(tensor,e))
            if isTensor(tensor)
            => Generator(TuplePat(List(p,VarPat(v))),Lift(tensor,e))::
                    patvars(p).map( i => Predicate(MethodCall(Var(prefix("coord",i)),"==",
                                                List(MethodCall(Var(i),
                                                        "/",List(IntConst(block_dim_size)))))) )
          case Generator(_,u)
            if !isRDD(u)
            => List(q)
          case LetBinding(p,e)
            if local_expr(e,local_vars)
            => List(q)
/*
          case Predicate(p@MethodCall(x,"==",List(y)))
            if local_expr(x,block_vars) && local_expr(y,block_vars)
            // index equality on tiles become equality on tile indices since tile coordinates are equal
            => List(Predicate(block_vars.foldLeft[Expr](p) {
                                case (r,v) => subst(Var(v),Var(prefix("tile",v)),r)
                              }))
*/
          case Predicate(e)
            if local_expr(e,local_vars)
            => List(q)
          case _ => Nil
      })
  }

  // the last tile size is dim % block_dim_size
  def tile_dimensions ( vars: List[String], dims: List[Expr], shuffle: Boolean = false ): List[Qualifier]
    = (vars zip dims).map {
          case (i,d)
            => LetBinding(VarPat(prefix("size",i)),
                          IfE(MethodCall(MethodCall(MethodCall(Var(if (shuffle) i
                                                                   else prefix("coord",i)),
                                                               "+",List(IntConst(1))),
                                                    "*",List(IntConst(block_dim_size))),
                                         ">",List(d)),
                              MethodCall(d,"%",List(IntConst(block_dim_size))),
                              IntConst(block_dim_size)))
      }

  def preserve_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                       vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(k,e))
          => val is = freevars(k)
             val is_array_assign = block_array_assignment.nonEmpty
             val tensor = tile_type(block,tp)
             val (dn,sn) = tensor_dims(tensor)
             val tbinds = tile_dimensions(is,dims)
             val tile_dims = is.map( i => Var(prefix("size",i)) )
             val tile_coords = is.map( i => Var(prefix("coord",i)) )
             val tile_indices = tuple(is.map{ i => MethodCall(Var(i),"%",
                                                     List(IntConst(block_dim_size))) })
             val tc = Comprehension(Tuple(List(tile_indices,e)),
                                    tile_qualifiers(qs,vars))
             val tile = Store(tensor,List(tp),tile_dims,tc)
             if (isDatasetTensor(block)) {
               val Comprehension(nhs,nqs)
                     = optimize(Comprehension(Tuple(List(tuple(tile_coords),tile)),
                                              rdd_qualifiers(qs,vars)++tbinds))
               if (trace) println("Comprehension that preserves tilling:\n"
                                  +Pretty.print(Comprehension(nhs,nqs)))
               val sql = translate_sql(nhs,nqs)
               val Some(TypeMapS(_,tvs,_,_,st,_,_,_)) = getTypeMap(tile_type(block,tp))
               val stp = substType(st,Some(tvs.map(_->tp).toMap))
               val ds = block_array_assignment match {
                           case Some(array)
                             => val tensor = tile_type(block,tp)
                                val (dn,sn) = tensor_dims(tensor)
                                val dest = Nth(array,dn+sn+1)
                                val f = Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),Var("_y"))
                                outerJoinSQL(dest,sql,f,stp)
                           case _ => sql
                        }
               store("dataset",List(tileType(block,tp)),dims,ds)
             } else if (is_rdd_comprehension(qs) || is_array_assign) {
               val otile = translate(optimize(tile),vars)
               val mtile = if (is_array_assign)
                             add_initial_array(otile,Nth(Var("_array"),dn+sn+1))
                           else otile
               val assigns = block_array_assignment match {
                                case Some(array)
                                  => val array_coords = tuple(is.map( i => VarPat(prefix("array",i)) ))
                                     Generator(TuplePat(List(array_coords,VarPat("_array"))),
                                               Lift("rdd",Nth(array,dn+sn+1)))::
                                     is.map { i => Predicate(MethodCall(Var(prefix("array",i)),
                                                                  "==",List(Var(prefix("coord",i))))) }
                                case _ => Nil
                             }
               val Comprehension(nhs,nqs)
                       = optimize(Comprehension(Tuple(List(tuple(tile_coords),mtile)),
                                                rdd_qualifiers(qs,vars)++assigns++tbinds))
               if (trace) println("Comprehension that preserves tilling:\n"
                                  +Pretty.print(Comprehension(nhs,nqs)))
               tuple(dims:+translate_rdd(nhs,nqs,vars))
             } else {
               val p = tuple(is.map( i => VarPat(prefix("coord",i)) )
                             ++ is.map( i => VarPat(prefix("size",i)) ))
               val nc = Comprehension(toExpr(p),
                                      rdd_qualifiers(qs,vars)++tbinds)
               val rdd = flatMap(Lambda(p,Seq(List(tuple(List(tuple(tile_coords),tile))))),
                                 MethodCall(Var("spark_context"),
                                            "parallelize",
                                            List(translate(optimize(nc),vars),
                                                 IntConst(number_of_partitions))))
               tuple(dims:+rdd)
             }
      }


/*-------------- Tiled comprehension without groupBy that does not preserve tiling -------------------------*/

  def shuffles_tiles ( key: Expr, qs: List[Qualifier] ): Boolean
    = !hasGroupBy(qs) && {
         var key_vars = freevars(key).filter(v => typecheck_var(v).isEmpty).toSet
         val indices = unique_indices(qs).toSet
         val cis = correlated_indices(qs,key_vars)
         key_vars.forall(indices.contains) //&& indices == cis
      }

  /* shuffle the tiles of a tiled comprehension */
  def shuffle_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                      vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(p,h))
          => val ks = p match { case Tuple(ks) => ks; case _ => List(p) }
             val vs = ks.map{ _ => newvar }
             val fs = tile_indices(qs)
             val N = IntConst(block_dim_size)
             val tbinds = tile_dimensions(vs,dims,true)
             val tile_dims = vs.map( i => Var(prefix("size",i)) )
             def gkeys ( op: String ): List[Expr]
               = (ks zip vs).map {
                      case (k,vk)
                        => val is = freevars(k,Nil).intersect(fs)
                           val gk = is.map{ v => (v,MethodCall(MethodCall(Var(prefix("coord",v)),
                                                                          "*",List(N)),
                                                               "+",List(Var(prefix("tile",v))))) }
                           MethodCall(gk.foldLeft[Expr](k){ case (r,(v,e)) => subst(v,e,r) },
                                      op,List(N))
                      }
             // generate all the unique block coordinates from the current block coordinates
             //   used by the comprehension keys
             val unique_coords
                 = (ks zip vs zip dims zip gkeys("/")).flatMap {
                            case (((Var(v),vk),_),_)
                              => List(LetBinding(VarPat(vk),Var(prefix("coord",v))))
                            case (((k,vk),_),gkey)
                              => val is = freevars(k,Nil).intersect(fs)
                                 val ts = tuple(is.map{ v => VarPat(prefix("tile",v)) })
                                 List(Generator(VarPat(vk),
                                           Call("unique_values",
                                                List(Lambda(ts,gkey)))))
                         }
             val rqs = (rdd_qualifiers(qs,vars,true)++unique_coords:+
                               GroupByQual(tuple(vs.map(VarPat)),
                                           tuple(vs.map(Var))))++tbinds
             val tqs = (vs zip gkeys("/")).map {
                           case (vk,gkey)
                             => Predicate(MethodCall(Var(vk),"==",List(gkey)))
                       }
             val tile = Store(tile_type(block,tp),List(tp),tile_dims,
                              Comprehension(Tuple(List(Tuple(gkeys("%")),h)),
                                            tile_qualifiers(qs,vars,true)++tqs))
            if (trace) println("Comprehension that does not preserve tilling:\n"
                               +Pretty.print(Comprehension(Tuple(List(tuple(vs.map(Var)),tile)),rqs)))
             val Comprehension(nhs,nqs) = optimize(Comprehension(Tuple(List(tuple(vs.map(Var)),tile)),rqs))
             val rdd = if (is_rdd_comprehension(qs))
                         translate_dataset(nhs,nqs,vars)
                       else MethodCall(Var("spark_context"),
                                       "parallelize",
                                       List(translate_dataset(nhs,nqs,vars),
                                            IntConst(number_of_partitions)))
             if (isDatasetTensor(block))
               store("dataset",List(tileType(block,tp)),dims,rdd)
             else tuple(dims:+rdd)
    }


/* -------------------- a group-by on block tensors -----------------------------------------*/

  def hasGroupByTiling ( qs: List[Qualifier], key: Expr ): Boolean
    = qs.exists {
        case GroupByQual(kp,_)
          => key == toExpr(kp)
        case _ => false
      }

  def groupBy_tiles ( block: String, hs: Expr, qs: List[Qualifier],
                      vars: List[String], tp: Type, dims: List[Expr] ): Expr
    = hs match {
        case Tuple(List(kp,head))
          => qs.span{ case GroupByQual(gp,_) => toExpr(gp) != kp; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val ttp = tile_type(block,tp)
                   val ndims = dims.length
                   val groupByVars = p match {
                                       case VarPat(_) if ndims > 1
                                         => freevars(k)
                                       case _ => patvars(p) }
                   // non-groupby variables used in head
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val h = yieldReductions(head,usedVars)
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars).distinct
                   assert(rt.nonEmpty,"Expected aggregations in a group-by comprehension")
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Seq(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case e
                                      => Seq(List(e))
                                  }
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   val msTypes = rt.map{ case (v,u) => typecheck(u) }
                   def nvar ( s: String ) = tuple(1.to(ndims).map(i => Var(s+i)).toList)
                   def nvarp ( s: String ) = tuple(1.to(ndims).map(i => VarPat(s+i)).toList)
                   def combine ( x: String, y: String, m: String, tp: Type ): Expr = {
                     val zero = zeroValue(tp)
                     val mst = Call("merge_tensors",
                                    List(Nth(Var(x),ndims+1),Nth(Var(y),ndims+1),
                                         Lambda(TuplePat(List(VarPat("v"),VarPat("w"))),
                                                mcall(m,Var("v"),Var("w"))),
                                         zero))
                     Tuple(1.to(ndims).map(i => Nth(Var(x),i)).toList:+mst)
                   }
                   val md = h match {
                              case reduce(_,_)
                                => Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                          combine("_x","_y",ms.head,msTypes.head))
                              case _
                                => { val xs = rt.map(_ => newvar)
                                     val ys = rt.map(_ => newvar)
                                     Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                          TuplePat(ys.map(VarPat)))),
                                            Tuple((ms zip msTypes zip (xs zip ys))
                                                      .map{ case ((m,tp),(x,y))
                                                              => combine(x,y,m,tp) } ))
                                   }
                   }
                   val tbinds = tile_dimensions(groupByVars,dims)
                   val rqs = rdd_qualifiers(qs,vars)
                   val tile_dims = groupByVars.map( i => Var(prefix("size",i)) )
                   val tile_keys = tuple(groupByVars.map( v => VarPat(prefix("tile",v)) ))
                   val tindices = tile_indices(qs).map( i => (i,Var(prefix("tile",i))) )
                   val tgb_key = tindices.foldLeft(k) { case (r,(from,to)) => subst(from,to,r) }
                   val tiles = (rt zip msTypes).map {
                                 case ((_,u),tp)
                                   => (Store(tile_type(block,tp),List(tp),tile_dims,
                                             Comprehension(Tuple(List(toExpr(tile_keys),u)),
                                                   (tile_qualifiers(r,vars)
                                                    :+GroupByQual(tile_keys,tgb_key))++s)))
                               }
                   val tile_coords = tuple(groupByVars.map( v => VarPat(prefix("coord",v)) ))
                   val coord_indices = tile_indices(qs).map( i => (i,Var(prefix("coord",i))) )
                   val coord_gb_key = coord_indices.foldLeft(k) { case (r,(from,to)) => subst(from,to,r) }
                   val nc = Comprehension(Tuple(List(toExpr(tile_coords),tuple(tiles))),
                                          (rqs:+LetBinding(tile_coords,coord_gb_key))++tbinds)
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def liftExpr ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => subst(from,Var(to+"_"),r) }
                   val liftedTile
                     = liftExpr(h) match {
                         case Var(v)
                           => Var(v.dropRight(1))
                         case nh
                         => val first_aggr = Var(env.head._2)
                            val tile_dims = (1 to ndims).map( i => Nth(first_aggr,i)).toList
                            Store(ttp,List(tp),tile_dims,
                                  Comprehension(Tuple(List(nvar("i0_"),nh)),
                               env.map(_._2).zip(msTypes).zipWithIndex.flatMap {
                                  case ((v,tp),i)
                                    => val ttp =  tile_type(block,tp)
                                       Generator(TuplePat(List(nvarp("i"+i+"_"),
                                                               VarPat(v+"_"))),
                                                 Lift(ttp,Var(v)))::
                                       (if (i > 0)
                                          1.to(ndims).map(j => Predicate(MethodCall(Var("i"+i+"_"+j),
                                                                   "==",List(Var("i0_"+j))))).toList
                                        else Nil)
                               }))
                       }
                   if (isDatasetTensor(block)) {
                       val ndims = dims.map( i => IntConst(block_dim_size) )
                       // empty tile:
                       val zero = tuple(msTypes.map(tp => Store(tile_type(block,tp),
                                                                List(tp),ndims,Seq(Nil))))
                       val rval = tuple(env.map(x => VarPat(x._2)))
                       val mapper = if (liftedTile != toExpr(rval))
                                      Some(Lambda(rval,liftedTile))
                                    else None
                       // translate it to DataFrames SQL
                       val sql = translate_sql(Tuple(List(toExpr(tile_coords),tuple(tiles))),
                                               (rqs:+LetBinding(tile_coords,coord_gb_key))++tbinds,
                                               md,zero,mapper)
                       val Some(TypeMapS(_,tvs,_,_,st,_,_,_)) = getTypeMap(tile_type(block,tp))
                       val stp = substType(st,Some(tvs.map(_->tp).toMap))
                       val ds = block_array_assignment match {
                                   case Some(array)
                                     => val tensor = tile_type(block,tp)
                                        val (dn,sn) = tensor_dims(tensor)
                                        val dest = Nth(array,dn+sn+1)
                                        outerJoinSQL(dest,sql,md,stp)
                                   case _ => sql
                                 }
                       store("dataset",List(tileType(block,tp)),dims,ds)
                   } else {
                       val rdd = block_array_assignment match {
                                   case Some(array)
                                     => val tensor = tile_type(block,tp)
                                        val (dn,sn) = tensor_dims(tensor)
                                        val dest = Nth(array,dn+sn+1)
                                        Call("outerJoin",
                                             List(dest,
                                                  MethodCall(Store("rdd",Nil,Nil,nc),
                                                             "reduceByKey",
                                                             List(md,IntConst(number_of_partitions))),
                                                  md))
                                   case _ => MethodCall(Store("rdd",Nil,Nil,nc),
                                                        "reduceByKey",List(md,IntConst(number_of_partitions)))
                                 }
                       val rval = tuple(env.map(x => VarPat(x._2)))
                       if (trace) println("Comprehension without group-by:\n"
                                          +Pretty.print(Comprehension(Tuple(List(kp,liftedTile)),
                                                     List(Generator(TuplePat(List(p,rval)),rdd)))))
                       val res =  translate_rdd(Tuple(List(kp,liftedTile)),
                                                List(Generator(TuplePat(List(p,rval)),rdd)),vars)
                       translate(Tuple(dims:+res),vars)
                   }
            case _ => throw new Error("Expected a group-by comprehension: "
                                      +Comprehension(hs,qs))
          }
    }


/* -------------------- GroupBy Join using the SUMMA algorithm -----------------------------------------*/

  def findJoinGBKeys ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]] = {
    val qvars = qual_vars(qs)
    matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((contains(e1,xs,qvars) && contains(e2,ys,qvars))
                        || (contains(e2,xs,qvars) && contains(e1,ys,qvars)))
                  case GroupByQual(p,Tuple(List(gx,gy)))
                    if ((contains(gx,xs,qvars) && contains(gy,ys,qvars))
                        || (contains(gy,xs,qvars) && contains(gx,ys,qvars)))
                    => true
                  case _ => false },
                { case (p@Predicate(MethodCall(e1,"==",List(e2))))::s
                    => findJoinGBKeys(xs,ys,s) match {
                          case None => None
                          case Some(l) => Some(p::l)
                       }
                  case (g@GroupByQual(p,Tuple(List(gx,gy))))::_
                    => Some(List(g))
                  case _::_ => None
                })
  }

  def findGroupByJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = if (qs.map{ case Generator(_,u) if isTiled(u) => 1; case _ => 0 }.sum != 2) None
      else matchQ(qs,{ case Generator(_,e1) if isTiled(e1) => true; case _ => false },
                { case (g1@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e2) if isTiled(e2) => true; case _ => false },
                                 { case (g2@Generator(p2,e2))::r2
                                     => findJoinGBKeys(patvars(p1).toSet,patvars(p2).toSet,r2) match {
                                           case Some(l) => Some(g1::g2::l)
                                           case _ => None
                                        }
                                  case _ => None })
                  case _ => None })

  def translate_groupby_join ( block: String, hs: Expr, qs: List[Qualifier], vars: List[String],
                               tp: Type, dims: List[Expr] ): Option[Expr]
    = if (!groupByJoin) None
      else findGroupByJoin(qs) match {
         case Some((g1@Generator(p1,d1))::(g2@Generator(p2,d2))
                   ::(cs:+(g@GroupByQual(p,k@Tuple(List(gx,gy))))))
           => val N = IntConst(block_dim_size)
              val qvars = qual_vars(qs)
              val jt1 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                  => if (contains(e1,patvars(p1).toSet,qvars)) e1 else e2
                                case _ => d1 }
              val jt2 = cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                  => if (contains(e1,patvars(p2).toSet,qvars)) e1 else e2
                                case _ => d1 }
              val (ngx,ngy) = if (contains(gx,patvars(p1).toSet,qvars)) (gx,gy) else (gy,gx)
              val (r,_::s) = qs.span(_ != g)
              val groupByVars = patvars(p)
              val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                    .intersect(comprVars(r)).distinct
              val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                        usedVars)
              val c = Comprehension(Tuple(List(toExpr(p),tuple(rt.map(_._2)))),
                                    List(Generator(TuplePat(List(VarPat("k1"),
                                                        tuple(tile_values(p1)
                                                               .map(v => VarPat(prefix("tile",v)))))),
                                                   Var("__v1")),
                                         Generator(TuplePat(List(VarPat("k2"),
                                                        tuple(tile_values(p2)
                                                               .map(v => VarPat(prefix("tile",v)))))),
                                                   Var("__v2")),
                                         Predicate(MethodCall(Var("k1"),"==",List(Var("k2")))))++
                                    tile_qualifiers(r,vars):+g)
              val tile_dims = 1.to(dims.length).map(i => N).toList
              val tile = Store(tile_type(block,tp),List(tp),tile_dims,c)
              def num_of_tiles ( size: Expr )
                = MethodCall(MethodCall(MethodCall(size,"+",List(IntConst(block_dim_size-1))),
                             "/",List(N)),"-",List(IntConst(1)))
              val kv = newvar
              val left_size::right_size::_ = dims
              val left = translate_rdd(Tuple(List(Tuple(List(ngx,Var(kv))),
                                                  Tuple(List(tuple(jt1),
                                                             tuple(tile_values(p1).map(Var)))))),
                                       List(Generator(p1,d1),
                                            Generator(VarPat(kv),
                                                      Range(IntConst(0),
                                                            num_of_tiles(right_size),
                                                            IntConst(1)))),vars)
              val right = translate_rdd(Tuple(List(Tuple(List(Var(kv),ngy)),
                                                   Tuple(List(tuple(jt2),
                                                              tuple(tile_values(p2).map(Var)))))),
                                        List(Generator(p2,d2),
                                             Generator(VarPat(kv),
                                                       Range(IntConst(0),
                                                             num_of_tiles(left_size),
                                                             IntConst(1)))),vars)
              val nq = Generator(TuplePat(List(tuple(groupByVars.map{ v => VarPat(prefix("coord",v)) }),
                                               TuplePat(List(VarPat("__v1"),VarPat("__v2"))))),
                                 Lift("rdd",MethodCall(left,"cogroup",List(right))))
              val rdd = translate_rdd(Tuple(List(toExpr(p),tile)),
                                      rdd_qualifiers(qs.flatMap( q => if ((g::g2::cs).contains(q)) Nil
                                                                      else if (q==g1) List(nq) else List(q) ),
                                                     vars),vars)
              Some(tuple(dims:+rdd))
         case _ => None
    }


/* -------------------- translate block tensor comprehensions -----------------------------------------*/

  /* matches the equi-join ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findTileJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                { case (Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield Generator(p1,e1)::Generator(p2,e2)::c
                                  case _ => None })
                  case _ => None })

  /* matches the cross product ...,p1 <- e1,...,p2 <- e2,...   */
  def findTileCross ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                { case (Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e) if isTiled(e) => true; case _ => false },
                                 { case (Generator(p2,e2))::r2
                                     => Some(List(Generator(p1,e1),Generator(p2,e2)))
                                  case _ => None })
                  case _ => None })

  def filter_tile_predicates ( qs: List[Qualifier], indices: List[String] ): List[Qualifier]
    = qs.filter{ case Predicate(MethodCall(Var(i),"==",List(Var(j))))
                   => indices.contains(i) && indices.contains(j)
                 case Predicate(e) => false
                 case _ => true }

  var QLcache: Option[Expr] = None

  def div ( e: Expr, N: Expr ): Expr
    = e match {
        case Tuple(es)
          => Tuple(es.map(e => MethodCall(e,"/",List(N))))
        case _ => MethodCall(e,"/",List(N))
      }

  def mod ( e: Expr, N: Expr ): Expr
    = e match {
        case Tuple(es)
          => Tuple(es.map(e => MethodCall(e,"%",List(N))))
        case _ => MethodCall(e,"%",List(N))
      }

  def translate_tiled ( block: String, hs: Expr, qs: List[Qualifier], vars: List[String],
                        tp: Type, dims: List[Expr] ): Expr
    = hs match {
      case Tuple(List(p,h))   // a tiled comprehension that preserves tiling
        if preserves_tiling(p,qs)
        => preserve_tiles(block,hs,qs,vars,tp,dims)
      case Tuple(List(p,_))   // a tiled comprehension that doesn't preserve tiling
        if shuffles_tiles(p,qs)
        => shuffle_tiles(block,hs,qs,vars,tp,dims)
      case _    // groupBy join
        if { QLcache = translate_groupby_join(block,hs,qs,vars,tp,dims); QLcache.nonEmpty }
        => QLcache.get
      case Tuple(List(kp,_))   // group-by tiled comprehension with group-by-key == comprehension key
        if hasGroupByTiling(qs,kp) && is_tiled_comprehension(qs)
        => groupBy_tiles(block,hs,qs,vars,tp,dims)
      case Tuple(List(kp,u)) // group-by tiled comprehension with group-by-key != comprehension key
        if hasGroupBy(qs) && is_tiled_comprehension(qs)
        // should raise an error instead
        => qs.span{ case GroupByQual(p,_) => false; case _ => true } match {
                    case (r,gb@GroupByQual(p,k)::s)
                       => val nhs = Tuple(List(toExpr(p),u))
                          val sgb = Store("block_map",List(typecheck(kp),typecheck(u)),Nil,
                                          Comprehension(hs,qs))
                          val nv = newvar
                          val nk = newvar
                          val res = Store(block,List(tp),dims,
                                          Comprehension(Tuple(List(Var(nk),Var(nv))),
                                                        List(Generator(TuplePat(List(VarPat(nk),VarPat(nv))),
                                                                       sgb))))
                          translate(res,vars)
                     case _ => throw new Error("Unexpected error in tiled groupBy")
                   }
        case _
          if isDatasetTensor(block) && is_rdd_comprehension(qs)
          => val mp = qs.flatMap {
                         case q@Generator(p,Lift(b,x))
                           if isBlockTensor(b)
                           => List(q -> newvar)
                         case q => Nil
                      }.toMap
             val ns = qs.map {
                         case q@Generator(p,Lift(b,x))
                           if isBlockTensor(b)
                           => Generator(p,Lift(block_type(b),Var(mp(q))))
                         case q => q
                       }
             val Comprehension(nh,nqs) = optimize(Comprehension(hs,ns))
             // pull out block tensors from the comprehension as RDDs
             val rdd = translate_rdd(nh,nqs,vars)
             val cm = if (data_frames) "dataset" else "rdd"
             val rdd_block = block match {
                               case block_tensor_pat(full,_,dn,sn)
                                 => s"${full}rdd_block_tensor_${dn}_$sn"
                               case block_bool_tensor_pat(full,_,dn,sn)
                                 => s"${full}rdd_block_bool_tensor_${dn}_$sn"
                               case _ => block
                             }
             getTypeMap(rdd_block)
             val Some(TypeMapS(_,List(tv),_,_,st,_,_,_)) = getTypeMap(tile_type(block,tp))
             val stp = TupleType(List(tuple(dims.map(x => intType)),substType(st,Some(Map(tv->tp)))))
             val ds = mp.foldLeft[Expr](store(rdd_block,List(tp),dims,Lift("rdd",rdd))) {
                           case (r,((q@Generator(p,_),v)))
                             => Let(VarPat(v),
                                    Store(cm,List(tp),Nil,
                                          translate(optimize(Comprehension(toExpr(p),List(q))),vars)),r)
                      }
             store("dataset",List(stp),dims,Nth(ds,dims.length+1))
        case _
          if is_rdd_comprehension(qs)
          // A tiled comprehension that depends on RDDs
          => val mp = qs.flatMap {
                         case q@Generator(p,Lift(b,x))
                           if isBlockTensor(b)
                           => List(q -> newvar)
                         case q => Nil
                      }.toMap
             val ns = qs.map {
                         case q@Generator(p,Lift(b,x))
                           if isBlockTensor(b)
                           => Generator(p,Lift(block_type(b),Var(mp(q))))
                         case q => q
                       }
             val Comprehension(nh,nqs) = optimize(Comprehension(hs,ns))
             // pull out block tensors from the comprehension as RDDs
             val rdd = translate_dataset(nh,nqs,vars)
             val cm = if (data_frames) "dataset" else "rdd"
             mp.foldLeft[Expr](store(block,List(tp),dims,Lift("rdd",rdd))) {
                           case (r,((q@Generator(p,_),v)))
                             => Let(VarPat(v),
                                    Store(cm,List(tp),Nil,
                                          translate(optimize(Comprehension(toExpr(p),List(q))),vars)),r)
                      }
        case _
          => store(block,List(tp),dims,translate(Comprehension(hs,qs),vars))
    }


/* -------------------- handle array assignments in DIQL loops (updates and increments) ----------------------- */

  val array_assigns = true

  val array_buffer_pat: Regex = "array_buffer([_a-z]*)".r

  def add_initial_array ( e: Expr, a: Expr ): Expr
    = e match {
        case Call(f@array_buffer_pat(_),args)
          => Call(f,args:+a)
        case _ => apply(e,add_initial_array(_,a))
      }

  def translate_array_assign ( e: Expr, vars: List[String] ): Expr
    = e match {
      case Call("update_array",List(Var(a),u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isTensor(tensor)
        => val (dn,sn) = tensor_dims(tensor)
           val st = add_initial_array(store(tensor,List(tp),args,x),Nth(Var(a),dn+sn+1))
           Seq(List(translate(st,vars)))
      case Call("update_array",List(Var(a),u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isBlockTensor(tensor)
        => block_array_assignment = Some(Var(a))
           val res = translate(u,vars)
           block_array_assignment = None
           res
      case Call("increment_array",List(Var(a),op,u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isTensor(tensor)
        => val (dn,sn) = tensor_dims(tensor)
           array_assignment = Some(Nth(Var(a),dn+sn+1))
           val res = translate(u,vars)
           array_assignment = None
           res
      case Call("increment_array",List(dest@Var(a),op,u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isBlockTensor(tensor)
        => block_array_assignment = Some(dest)
           val res = translate(u,vars)
           block_array_assignment = None
           res
      case Call(_,_:+z)
        => apply(z,translate(_,vars))
  }


/*----------------------------------------------------------------------------------------------------*/

  // get all generator domains that are RDD
  def rdd_generators ( qs: List[Qualifier] ): Map[Expr,String]
    = qs.foldLeft[Map[Expr,String]] (Map()) {
         case (r,Generator(p,u))
           if isRDD(u)
           => r+(u -> newvar)
         case (r,_) => r
      }

  /** Translate comprehensions to optimized algebra */
  def translate ( e: Expr, vars: List[String] ): Expr = {
    e match {
      case Store("rdd",tps,args,Comprehension(hh,qqs))
        => val Comprehension(h,qs) = optimize(Comprehension(hh,block_arrays_to_rdds(qqs)))
           translate(if (is_rdd_comprehension(qs))
                       // special rules for RDD comprehensions
                       translate_rdd(h,qs,vars)
                     else optimize(store("rdd",tps,args,Comprehension(h,qs))),vars)
      case Store(block,tps,dims,c@Comprehension(_,_))
        // special rules for tiled comprehensions
        if isBlockTensor(block)
        => val Comprehension(h,qs) = optimize(c)
           val tp = tps match { case List(tp) => tp; case _ => boolType }
           translate(translate_tiled(block,h,qs,vars,tp,dims),vars)
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupByKey(qqs,key)
        => tensor_groupby_eqkey(array,boolType,dims,head,qqs)
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupBy(qqs)
        => tensor_groupby_neqkey(array,boolType,dims,head,qqs)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isTensor(array)
           && hasGroupByKey(qqs,key)
        => tensor_groupby_eqkey(array,tp,dims,head,qqs)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isTensor(array)
           && hasGroupBy(qqs)
        => tensor_groupby_neqkey(array,tp,dims,head,qqs)
      case reduce(op,x@Comprehension(h,qs))
        if is_tiled_comprehension(qs)
        // total aggregation on tiled comprehensions
        => val tile_value = translate(reduce(op,Comprehension(h,tile_qualifiers(qs,vars))),vars)
           val nq = rdd_qualifiers(qs,vars)
           val Comprehension(nhs,nqs) = optimize(Comprehension(tile_value,nq))
           if (data_frames)
             translate_sql(nhs,nqs,op)
           else MethodCall(translate_rdd(nhs,nqs,vars),
                           "reduce",
                           List(Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                       MethodCall(Var("_x"),op,List(Var("_y"))))))
      case reduce(op,Comprehension(h,qs))
        if is_rdd_comprehension(qs)
        // total RDD aggregation
        => MethodCall(translate_rdd(h,qs,vars),"reduce",
                      List(Lambda(TuplePat(List(VarPat("_x"),VarPat("_y"))),
                                  MethodCall(Var("_x"),op,List(Var("_y"))))))
      case reduce(op,x@Comprehension(h,qs))
        // total aggregation
        => val nv = newvar
           val nr = qs:+AssignQual(Var(nv),mcall(op,Var(nv),h))
           val etp = typecheck(h)
           val zero = zeroValue(op,etp)
           translate(Block(List(VarDecl(nv,etp,Seq(List(zero))),
                                Comprehension(ignore,nr),Var(nv))),vars)
      case Store(f,tps,args,u)
        // if no special rule applies, return storage of u: inv(u)
        => val su = optimize(store(f,tps,args,u))
           translate(su,vars)
      case Lift(f,x)
        // if no special rule applies, lift x: map(x)
        => translate(optimize(lift(f,x)),vars)
      case Comprehension(h,qs)
        => val Comprehension(nh,s) = optimize(Comprehension(h,qs))
           val rdds = rdd_generators(s)
           val nqs = s.map {
                        case Generator(p,u)
                          if rdds.contains(u)
                          => Generator(p,Var(rdds(u)))
                        case q => q
                     }
           val lqs = nqs.map {  // lift generator domains
                        case Generator(p,Lift(f,x))
                          => Generator(p,lift(f,x))
                        case q => q
                     }
           // all RDD generators must be puled out in let-bindings and 'collect'ed in memory
           rdds.foldLeft[Expr](translate(default_translator(nh,lqs,vars),vars)) {
                  case (r,((u,v))) => Let(VarPat(v),translate(u,vars),r)
           }
      case Block(es)
        => Block(es.foldLeft[(List[Expr],List[String])]((Nil,vars)) {
                     case ((r,s),e@VarDecl(v,u,x))
                       => (r:+translate(e,s),v::s)
                     case ((r,s),e)
                       => (r:+translate(e,s),s)
                 }._1)
      case Call(f,args)
        if List("update_array","increment_array").contains(f)
        => translate_array_assign(Call(f,args),vars)
      case _ => apply(e,x => translate(x,vars))
    }
  }

  def translate ( e: Expr ): Expr = translate(e,Nil)

  def has_side_effects ( e: Expr ): Boolean
    = e match {
        case MethodCall(_,op,_)
          if List("+=","append","update").contains(op)
          => true
        case Call(op,_)
          if List("arraySet").contains(op)
          => true
        case Assign(MapAccess(_,_),_)   // Map is not thread-safe
          => true
        case Assign(Var(_),_)
          => true
        case _ => accumulate[Boolean](e,has_side_effects,_||_,false)
      }

  /* parallelize first range flatMap */
  def parallelize ( e: Expr ): Expr
    = e match {
          case flatMap(f@Lambda(_,b),u@Range(n,m,s))
            if !has_side_effects(b)
            => MethodCall(flatMap(f,MethodCall(u,"par",null)),"toList",null)
          case _ => apply(e,parallelize)
      }
}
