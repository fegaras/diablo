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
package edu.uta

import scala.language.experimental.macros
import org.apache.spark.SparkContext
import diablo.Parser.parse
import scala.collection.mutable
import scala.reflect.macros.whitebox
import scala.reflect.macros.whitebox.Context

package object diablo {
  var trace = true
  var groupByJoin = false
  var parallel = true
  var blockSize = 100000000
  var block_dim_size = 1000

  var spark_context: SparkContext = _

  def range ( n1: Long, n2: Long, n3: Long ): List[Long]
    = n1.to(n2,n3).toList

  def inRange ( i: Long, n1: Long, n2: Long, n3: Long ): Boolean
    = i>=n1 && i<= n2 && (i-n1)%n3 == 0

  def binarySearch[@specialized T] ( key: Int, from: Int, to: Int,
                                     rows: Array[Int], values: Array[T], zero: T ): T = {
    var low = from
    var high = to-1
    while (low <= high) {
      val mid = (low + high) >>> 1
      val d = rows(mid)
      if (d == key)
        return values(mid)
      else if (d > key)
        high = mid - 1
      else if (d < key)
        low = mid + 1
    }
    zero
  }

  def binarySearch ( key: Int, from: Int, to: Int, rows: Array[Int] ): Boolean = {
    var low = from
    var high = to-1
    while (low <= high) {
      val mid = (low + high) >>> 1
      val d = rows(mid)
      if (d == key)
        return true
      else if (d > key)
        high = mid - 1
      else if (d < key)
        low = mid + 1
    }
    false
  }

  def sort[T] ( from: Int, rows: mutable.ArrayBuffer[Int], values: mutable.ArrayBuffer[T] ) {
    val len = values.length-from
    if (len <= 1)
      return
    var arr = new mutable.ArrayBuffer[(Int,T)](len)
    var i = 0
    while (i < len) {
      arr.append( (rows(from+i),values(from+i)) )
      i += 1
    }
    arr = arr.sortBy(_._1)
    i = 0
    while (i < len) {
      rows(from+i) = arr(i)._1
      values(from+i) = arr(i)._2
      i += 1
    }
  }

  def sort ( from: Int, rows: mutable.ArrayBuffer[Int] ) {
    val len = rows.length-from
    if (len <= 1)
      return
    var arr = Array.ofDim[Int](len)
    var i = 0
    while (i < len) {
      arr(i) = rows(from+i)
      i += 1
    }
    scala.util.Sorting.quickSort(arr)
    i = 0
    while (i < len) {
      rows(from+i) = arr(i)
      i += 1
    }
  }

  private var typeMapsLib = false

  def opt ( e: Expr): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

  def q_impl ( c: Context ) ( query: c.Expr[String] ): c.Expr[Any] = {
    import c.universe.{Expr=>_,Type=>_,_}
    val context: c.type = c
    val cg = new { val c: context.type = context } with CodeGeneration
    val Literal(Constant(s:String)) = query.tree
    // hooks to the Scala compiler
    Typechecker.typecheck_var
       = ( v: String ) => cg.typecheckOpt(Var(v)).map(cg.Tree2Type)
    Typechecker.typecheck_method
       = ( o: Type, m: String, args: List[Type] ) => cg.typecheck_method(o,m,args)
    Typechecker.typecheck_call
       = ( f: String, args: List[Type] ) => cg.typecheck_call(f,args)
    val env: cg.Environment = Nil
    if (!typeMapsLib) {
      TypeMappings.init()
      typeMapsLib = true
    }
    Typechecker.useStorageTypes = false
    val q = parse(s)
    if (trace) println("Imperative program:\n"+Pretty.print(q))
    Typechecker.typecheck(q)
    val sq = Translator.translate(q)
    //if (trace) println("Comprehension:\n"+Pretty.print(sq))
    val n = opt(sq)
    if (trace) println("Normalized comprehension:\n"+Pretty.print(n))
    val le = opt(Lifting.lift(n))
    if (trace) println("Lifted comprehension:\n"+Pretty.print(le))
    Typechecker.clean(le)
    Typechecker.typecheck(le)  // the ComprehensionTranslator needs type info
    //Typechecker.check(le)
    val to = opt(ComprehensionTranslator.translate(le))
    val pc = if (parallel) ComprehensionTranslator.parallelize(to) else to
    if (trace) println("Compiled comprehension:\n"+Pretty.print(pc))
    val ec = cg.codeGen(pc,env)
    if (trace) println("Scala code:\n"+showCode(ec))
    val tc = cg.getType(ec,env)
    if (trace) println("Scala type: "+tc)
    context.Expr[Any](ec)
  }

  /** translate an array comprehension to Scala code */
  def q ( query: String ): Any = macro q_impl

  def parami_impl( c: whitebox.Context )(x: c.Expr[Int], b: c.Expr[Int] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Int)) = b.tree
    x.tree.toString.split('.').last match {
       case "blockSize" => blockSize = bv
       case "block_dim_size" => block_dim_size = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def parami ( x:Int, b: Int ): Unit = macro parami_impl

  def param_impl( c: whitebox.Context )(x: c.Expr[Boolean], b: c.Expr[Boolean] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Boolean)) = b.tree
    x.tree.toString.split('.').last match {
       case "trace" => trace = bv
       case "groupByJoin" => groupByJoin = bv
       case "parallel" => parallel = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def param ( x:Boolean, b: Boolean ): Unit = macro param_impl
}
