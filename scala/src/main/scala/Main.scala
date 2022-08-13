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

    ui.Calculators.selectCalculator()
    ui.Calculators.setupCalculatorList()

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


  def doStuff() {
    import Sym._
    import Pattern._

    val func = { (s: SymSum) =>
      // Figure out the smallest exponent of x, the power of x to divide by
      val minExpt: SymR = s.exprs.map{ e =>
        AsProdP( AsPowP(XP, 'p), __*).matches(e)
          .headOption.map(_.apply('p).asInstanceOf[SymR])
          .getOrElse(SymR(0))
      }.foldLeft(SymPositiveInfinity(): SymR)(_ min _)

      if (minExpt.n != 0 && minExpt.d != 0) {
        // Subtract the min exponent from each power of x
        val rule = new Rule("", AsProdP( AsPowP(XP, 'p @@ RatP()), 'r @@ __*), {
          case (p: Sym, r: Seq[Sym]) =>
            ***( ^(X, ++(p, minExpt.negative)) +: r ).pipe(simplify)
        })

        // Sum the newly divided powers and try to solve
        val divided = +++( s.exprs.map{ e => rule.first(e).getOrElse{ **(e, ^(X, minExpt.negative)) } } )

        if (minExpt < 0) Seq(divided)
        else Seq(X, divided)

        // Don't bother if the smallest power is already 0 or undefined
      } else Nil
    }

    // SumP(Repeat( AsProdP( AsPowP(XP, RatP()), __*), min=2 ), Repeat(noxP())).matches(
    //   ++(^(X, 3), **(-2, ^(X, 2)), X)
    // ).pipe(println)

    println(func(++(^(X, 3), **(-2, ^(X, 2)), X)))
  }

  @JSExportTopLevel("simplify")
  def mainSimple(str: String) {
    println(Parse.parseLatex(str).get.pipe(simplify))
  }
  
}
