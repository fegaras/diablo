/*
 * Copyright © 2019 University of Texas at Arlington
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

import scala.util.parsing.combinator.RegexParsers
import scala.util.Try


sealed abstract class PPTree
    case class PPNode ( name: String, children: List[PPTree] ) extends PPTree
    case class TupleNode ( children: List[PPTree] ) extends PPTree
    case class MapNode ( binds: List[(PPTree,PPTree)] ) extends PPTree
    case class LeafS ( value: String ) extends PPTree
    case class LeafL ( value: Long ) extends PPTree
    case class LeafD ( value: Double ) extends PPTree


/** Pretty printer for case classes */
object Pretty extends RegexParsers {

  val screen_size = 80
  var prefix = ""

  val ident: Parser[String] = """[_a-zA-Z][_\$\w]*""".r
  val value: Parser[String] = """[^,\)]+""".r
  val string: Parser[String] = """"[^"]*"""".r

  def tree: Parser[PPTree]
      = ( "Map" ~ "(" ~ repsep( ident ~ "->" ~ tree, "," ) ~ ")"
            ^^ { case _~_~as~_ => MapNode(as.map{ case v~_~a => (LeafS(v),a) }) }
          | ident ~ "(" ~ repsep( tree, "," ) ~ ")" ^^ { case f~_~as~_ => PPNode(f,as) }
          | "(" ~ repsep( tree, "," ) ~ ")" ^^ { case _~as~_ => TupleNode(as) }
          | "None" ^^ { _ => PPNode("None",List()) }
          | string ^^ { LeafS(_) }
          | value ^^ { v => Try(v.toInt).toOption match {
                                            case Some(i) => LeafL(i)
                                            case _ => Try(v.toDouble).toOption match {
                                                        case Some(d) => LeafD(d)
                                                        case _ => LeafS(v)
                                                      }
                                }
                     }
        )

  def size ( e: PPTree ): Int = {
    e match {
      case PPNode(f,as)
        => as.map(size(_)+1).sum + f.length + 2
      case TupleNode(as)
        => as.map(size(_)+1).sum + 4
      case MapNode(as)
        => as.map{ case (v,a) => size(v)+size(a)+4 }.sum + 4
      case LeafS(v)
        => v.length+2
      case LeafD(d)
        => d.toString.length
      case LeafL(i)
        => i.toString.length
    }
  }

  /** pretty-print trees */
  def pretty ( e: PPTree, position: Int ): String = {
    e match {
      case PPNode(f,l) if position+size(e) <= screen_size
        => l.map(pretty(_,position)).mkString(f+"(", ", ", ")")
      case PPNode(f,l)
        => l.map(pretty(_,position+f.length+1))
            .mkString(f+"(", ",\n"+prefix+" "*(position+f.length+1), ")")
      case TupleNode(l)
        => l.map(pretty(_,position)).mkString("( ", ", ", " )")
      case MapNode(l) if position+size(e) <= screen_size
        => l.map{ case (v,a) => pretty(v,position)+" = "+pretty(a,position) }.mkString("< ", ", ", " >")
      case MapNode(l)
        => l.map{ case (v,a) => pretty(v,position+2)+" = "+pretty(a,position+size(v)+3) }
            .mkString("< ", ",\n"+prefix+" "*(position+2), " >")
      case LeafS(v)
        => v.toString
      case LeafD(d)
        => d.toString
      case LeafL(i)
        => i.toString
    }
  }

 /** pretty-print the printout of a case class object */
  def print ( x: Any ): String = {
    parseAll(tree,x.toString) match {
      case Success(t,_) => pretty(t,0)
      case e => throw new java.lang.Error("Pretty.print error: "+e)
    }
  }
}
