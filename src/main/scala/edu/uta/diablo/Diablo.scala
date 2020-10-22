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
package edu.uta

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros
import scala.reflect.ClassTag
import diablo.Parser.parse
import diablo.Translator.translate

import scala.collection.mutable

package object diablo {

  var trace = true
  var groupByJoin = true
  var parallel = true
  var tileSize = 1000

  // Contains the natural transformations for type abstractions
  var typeMaps = mutable.Map[String,TypeMapS]()

  def range ( n1: Long, n2: Long, n3: Long ): List[Long]
    = n1.to(n2,n3).toList

  def inRange ( i: Long, n1: Long, n2: Long, n3: Long ): Boolean
    = i>=n1 && i<= n2 && (i-n1)%n3 == 0

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
    cg.var_decls = collection.mutable.Map[String,c.Tree]()
    Lifting.initialize()
    Typechecker.useStorageTypes = false
    val q = parse(s)
    def opt ( e: Expr): Expr = Optimizer.optimizeAll(Normalizer.normalizeAll(e))
    if (trace) println("Imperative program:\n"+Pretty.print(q.toString))
    Typechecker.typecheck(q)
    val sq = Translator.translate(q)
    if (trace) println("Comprehension:\n"+Pretty.print(sq.toString))
    val n = opt(sq)
    if (trace) println("Normalized comprehension:\n"+Pretty.print(n.toString))
    val le = opt(Lifting.lift(n))
    if (trace) println("Lifted comprehension:\n"+Pretty.print(le.toString))
    val to = opt(ComprehensionTranslator.translate(le))
    val pc = if (parallel) ComprehensionTranslator.parallelize(to) else to
    if (trace) println("Compiled comprehension:\n"+Pretty.print(pc.toString))
    val ec = q"${cg.codeGen(pc,env)}.head"
    if (trace) println("Scala code:\n"+ec)
    val tc = cg.getType(ec,env)
    if (trace) println("Scala type: "+tc)
    context.Expr[Any](ec)
  }

  /** translate an array comprehension to Scala code */
  def q ( query: String ): Any = macro q_impl

  def parami_impl ( c: Context ) ( x: c.Expr[Int], b: c.Expr[Int] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Int)) = b.tree
    x.tree.toString.split('.').last match {
       case "tileSize" => tileSize = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def parami ( x:Int, b: Int ): Unit = macro parami_impl

  def param_impl ( c: Context ) ( x: c.Expr[Boolean], b: c.Expr[Boolean] ): c.Expr[Unit] = {
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
