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

import scala.annotation.tailrec
import scala.util.matching.Regex


object ComprehensionTranslator {
  import AST._
  import Typechecker._
  import TensorTranslator._
  import RDDTranslator._
  import TiledTranslator._
  import Lifting.{store,lift,getTypeMap}
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

  def qual_vars ( qs: List[Qualifier] ): Set[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }.toSet

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
        => val st = add_initial_array(store(tensor,List(tp),args,x),Nth(Var(a),3))
           Seq(List(translate(st,vars)))
      case Call("update_array",List(Var(a),u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isBlockTensor(tensor)
        => block_array_assignment = Some(Var(a))
           val res = translate(u,vars)
           block_array_assignment = None
           res
      case Call("increment_array",List(Var(a),op,u@Seq(List(Store(tensor,List(tp),args,x)))))
        if array_assigns && isTensor(tensor)
        => array_assignment = Some(Nth(Var(a),3))
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
        => apply(z,translate_array_assign(_,vars))
      case _ => e
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

  def block_arrays_to_rdds ( qs: List[Qualifier] ): List[Qualifier]
    = qs.flatMap {
        case Generator(p,Lift(f@block_tensor_pat(_,_,dn,sn),x))
          => List(Generator(p,lift(f,x)))
        case Generator(p,Lift(f@block_bool_tensor_pat(_,_,dn,sn),x))
          => List(Generator(p,lift(f,x)))
        case q => List(q)
      }

  /** Translate comprehensions to optimized algebra */
  def translate ( e: Expr, vars: List[String] ): Expr = {
    e match {
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupByKey(qqs,key)
        => translate(tensor_groupby_eqkey(array,boolType,dims,head,qqs),vars)
      case Store(array,Nil,dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // boolean array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isBoolTensor(array)
           && hasGroupBy(qqs)
        => translate(tensor_groupby_neqkey(array,boolType,dims,head,qqs),vars)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is equal to the comprehension key)
        if isTensor(array)
           && hasGroupByKey(qqs,key)
        => translate(tensor_groupby_eqkey(array,tp,dims,head,qqs),vars)
      case Store(array,List(tp),dims,Comprehension(head@Tuple(List(key,u)),qqs))
        // array comprehension with a group-by (when group-by key is NOT equal to the comprehension key)
        if isTensor(array)
           && hasGroupBy(qqs)
        => translate(tensor_groupby_neqkey(array,tp,dims,head,qqs),vars)
      case MethodCall(Store("rdd",tps,args,x),"reduce",f)
        => MethodCall(translate(x,vars),"reduce",f)
      case reduce(op,Comprehension(h,qs))
        // total aggregation for in-memory comprehension
        if !is_rdd_comprehension(qs)
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
        => Block(es.foldLeft[(List[Expr],List[String])] ((Nil,vars)) {
                     case ((r,s),e@VarDecl(v,u,x))
                       => (r:+translate(e,s),v::s)
                     case ((r,s),e)
                       => (r:+translate(e,s),s)
                 }._1)
      case Call(f,args)
        if List("update_array","increment_array").contains(f)
        => translate_array_assign(Call(f,args.map(translate(_,vars))),vars)
      case _ => apply(e,translate(_,vars))
    }
  }

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
            // parRange doesn't work
            // => MethodCall(flatMap(f,Call("parRange",List(n,m,s))),"toList",null)
            => MethodCall(flatMap(f,MethodCall(u,"par",null)),"toList",null)
          case _ => apply(e,parallelize)
      }
}
