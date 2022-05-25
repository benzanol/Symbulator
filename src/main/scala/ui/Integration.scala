package sympany.ui

// Unlike math.Integral, which solves integrals, this provides the user interface
// for selecting points and curves to calculate integrals with

import org.scalajs.dom
import org.scalajs.dom.document
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.ui.Graph.IntersectionPoint
import sympany._

object Integration {
  var p1: Option[IntersectionPoint] = None
  var p2: Option[IntersectionPoint] = None
  var function: Option[Sym] = None
  var integral: Option[Sym] = None
  var solution: Option[Sym] = None

  var integralMode = false

  def enterIntegralSidebar() {
    integralMode = true
    document.getElementById("equation-sidebar").setAttribute("style", "display:none")
    document.getElementById("integral-sidebar").setAttribute("style", "")
  }

  @JSExportTopLevel("exitIntegralSidebar")
  def exitIntegralSidebar() {
    integralMode = false
    document.getElementById("equation-sidebar").setAttribute("style", "")
    document.getElementById("integral-sidebar").setAttribute("style", "display:none")

    p1 = None
    p2 = None
    function = None
    integral = None
    solution = None
  }

  def clickPoint(p: IntersectionPoint) {
    if (!integralMode) enterIntegralSidebar()

    if (p1.isDefined && p1.get == p) p1 = None
    else if (p2.isDefined && p2.get == p) p2 = None
    else if (p1.isEmpty) p1 = Some(p)
    else p2 = Some(p)

    if (p1.isDefined && p2.isDefined) {
      import Sym._

      this.function = Some(++(p1.get.funcs(0), **(-1, p1.get.funcs(1))))
      this.integral = function.get.integral

      if (integral.isDefined)
        this.solution = Some(
          ++(integral.get.replaceExpr('x, p2.get.x),
            **(-1, integral.get.replaceExpr('x, p1.get.x)))
            .simple
        )
    }

    updateUi()
  }

  def updateUi() {
    def setText(id: String, str: String) {
      document.getElementById(s"integral-$id").innerText = str
    }
    
    // Display the points
    for ((p, i) <- Seq(p1 -> 1, p2 -> 2))
      if (p.isDefined) setText(s"p${i}",
        s"p_$i = \\quad (${p.get.x.toLatex}, ${p.get.y.toLatex})")
      else setText(s"p${i}" , s"p_$i =")

    // Display the equations
    if (p1.isDefined) {
      setText(s"e1", "y_1 = " + p1.get.funcs(0).toLatex)
      setText(s"e2", "y_2 = " + p1.get.funcs(1).toLatex)
    } else {
      setText(s"e1", "y_1 =")
      setText(s"e2", "y_2 =")
    }

    for (i <- integral ; s <- solution) {
      val suScripts = s"_{${p1.get.x.toLatex}}^{${p2.get.x.toLatex}}"
      setText("solution1", s"\\int$suScripts ${function.get.toLatex}")
      setText("solution2", s" = \\left[ ${integral.get.toLatex} \\right]$suScripts")
      setText("solution3", " = " + solution.get.toLatex)
    }

    js.eval("formatStaticEquations()")
  }
}
