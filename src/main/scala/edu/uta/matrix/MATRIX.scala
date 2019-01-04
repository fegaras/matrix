/*
 * Copyright © 2017, 2018 University of Texas at Arlington
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
package edu.uta.matrix

object MATRIX {
  def main ( args: Array[String] ) {
    val line = scala.io.Source.fromFile(args(0)).mkString
    val e = Parser.parse(line)
    new Typechecker().typecheck(e)
    println(Pretty.print(e.toString))
    val e1 = Translator.translate(e)
    println(Pretty.print(e1.toString))
    val ne = Normalizer.normalizeAll(e1)
    println(Pretty.print(ne.toString))
    println(new Typechecker().typecheck(ne))
  }
}
