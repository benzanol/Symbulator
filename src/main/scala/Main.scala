package sympany

import org.scalajs.dom
import org.scalajs.dom.document
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._

object Main {
  def main(args: Array[String]): Unit = {
    sympany.ui.Graph.setup
    sympany.ui.Equations.addEquation()
  }
  
  def jslog(arg: Any): Unit =
    scalajs.js.Dynamic.global.console.log(arg.asInstanceOf[scalajs.js.Any])
  
  def time[R](str: String, block: => R): R = {
    val t0 = System.nanoTime()
    val result = block
    val t1 = System.nanoTime()
    println(str + " => " + (t1 - t0)/1000000L + "ms")
    result
  }
  
}
