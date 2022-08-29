package sympany

import scala.util.chaining._

import org.scalajs.dom.document
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math.Simplify.simplify

object Main {

  /* This is the docstring
   * Pretty interesting, right!
   */
  def myfunc(arg: String, num: Int): Int = {

    return arg.length
  }

  def main(args: Array[String]): Unit = {
    sympany.ui.Graph.setup

    ui.Calculators.setupCalculatorList()
    ui.Calculators.selectCalculator()

    val mylist = Seq(1, 2, 3)
    println(mylist.filter(a => a + 2 == 4))
    mylist.groupBy(a => a + 2)

    Main.jslog(10)

    val a = 4
    a.pipe[List[Int]](List(_))
    a.!=(4)

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
   }
   */


  def doStuff() {}

  @JSExportTopLevel("simplify")
  def mainSimple(str: String) {
    Parse.parseLatex(str) match {
      case Some(e) => println(simplify(e))
      case None => println("Invalid expression!")
    }
  }
  
}
