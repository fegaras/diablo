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
package edu.uta

import scala.language.experimental.macros
import org.apache.spark.SparkContext
import diablo.Parser.parse
import scala.reflect.macros.whitebox
import scala.reflect.macros.whitebox.Context

package object diablo extends diablo.ArrayFunctions {
  var trace = true               // print trace info
  var groupByJoin = false        // experimental SUMMA groupby-join
  var parallel = true            // Yes for multicore parellism
  var block_dim_size = 1000      // size of each dimension of a block tensor
  var number_of_partitions = 10  // num of partitions in shuffling operations
  var data_frames = false        // false for RDD, true for DataFrame

  val rddClass = "org.apache.spark.rdd.RDD"
  val datasetClass = "edu.uta.diablo.DiabloDataFrame"

  // a Spark DataFrame with type information at compile-time
  type DiabloDataFrame[T] = org.apache.spark.sql.DataFrame

  var collectionClass = rddClass

  var spark_context: SparkContext = _

  private var typeMapsLib = false

  def opt ( e: Expr): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))

  def q_impl( c: Context )(query: c.Expr[String] ): c.Expr[Any] = {
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
       case "block_dim_size" => block_dim_size = bv
       case "number_of_partitions" => number_of_partitions = bv
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
       case "data_frames"
         => data_frames = bv
            collectionClass = if (data_frames) datasetClass else rddClass
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def param ( x:Boolean, b: Boolean ): Unit = macro param_impl
}
