package sympany

import scala.util.chaining._

import org.scalajs.dom
import org.scalajs.dom.document
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math.Simplify.simplify

object Main {

  def main(args: Array[String]): Unit = {
    sympany.ui.Graph.setup

    ui.Calculators.setupCalculatorList()
    ui.Calculators.selectCalculator()

    doStuff
  }
  
  def jslog(arg: Any): Unit =
    scalajs.js.Dynamic.global.console.log(arg.asInstanceOf[scalajs.js.Any])
  
  def time[R](str: String)(block: => R): R = {
    val t0 = System.nanoTime()
    val result = block
    val t1 = System.nanoTime()
    println(str + " => " + (t1 - t0)/1000000L + "ms")
    result
  }

  /*
   def showEquation(e: Sym) {
   val div = sympany.ui.Equations.makeElement(
   "p", "class" -> "mq-static", "innerText" -> e.toLatex)
   document.getElementById("equations").appendChild(div)
   js.eval("formatStaticEquations()")
   }
   */


  def doStuff() {}

  @JSExportTopLevel("simplify")
  def mainSimple(str: String) {
    println(Parse.parseLatex(str).get.pipe(simplify))
  }
  
}
