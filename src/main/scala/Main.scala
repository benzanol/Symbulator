package sympany

import org.scalajs.dom
import org.scalajs.dom.document
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math.IntegralRules
import sympany.math.Simplify

object Main {

  def main(args: Array[String]): Unit = {
    sympany.ui.Graph.setup
    sympany.ui.Equations.addEquation()
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

  def showEquation(e: Sym) {
    val div = sympany.ui.Equations.makeElement(
      "p", "class" -> "mq-static", "innerText" -> e.toLatex)
    document.getElementById("equations").appendChild(div)
    js.eval("formatStaticEquations()")
  }


  def doStuff {
    import Sym._
    import math.Integral._
    import math.IntegralRules._
    import Pattern._
    import Sym._

    println(PowP(=#?(1), __).matches(^(1, 1~2)))
    println(Simplify.sRules.first(^(1, 1~2)))

    //println(1.simple)
    //println(**(1, ^(1, 1~2)).simple)
    //println(^(1, 1~2).simple)

    //val e = **( V('x), SymSin(V('x)) )
    //println(integrate(SymIntegral(e)))
    //println(SymIntegral(SymSin(V('x))).simple)
    //showEquation(SymIntegral(**(SymVar('y))))
    //showEquation( **(S(2), ^(V('x), S(2)), SymSin(V('x)) ).integral.get )

  }
  
}
