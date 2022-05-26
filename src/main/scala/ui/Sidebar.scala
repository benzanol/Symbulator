package sympany.ui

import org.scalajs.dom.document
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.Sym._
import sympany.ui.Graph.IntersectionPoint
import sympany.ui.Graph.JsContext

object Sidebar {
  var current: String = "equation"
  var currentDraw: Option[JsContext => Unit] = None

  val color = "#880088"

  def currentEl = document.getElementById(current + "-sidebar")

  var p1: Option[IntersectionPoint] = None
  var p2: Option[IntersectionPoint] = None
  var y1: Option[Sym] = None
  var y2: Option[Sym] = None

  def display(bool: Boolean): String =
    if (bool) "display:block"
    else "display:none"

  @JSExportTopLevel("selectSidebar")
  def selectSidebar(bar: String) {
    currentEl.setAttribute("style", "display:none")
    this.current = bar
    currentEl.setAttribute("style", "display:block")

    document.getElementById("current-points").setAttribute("style", display(bar != "equation"))

    if (bar == "equation") {
      this.p1 = None
      this.p2 = None
      this.y1 = None
      this.y2 = None
    }

    this.currentDraw = bar match {
      case "integral" => Some(IntegralSidebar.select())
      case "tangent" => Some(TangentSidebar.select())
      case _ => None
    }

    js.eval("formatStaticEquations()")
    Graph.draw
  }

  def clickPoint(p: IntersectionPoint) {
    if (p1.isDefined && p1.get == p) p1 = None
    else if (p2.isDefined && p2.get == p) p2 = None
    else if (p1.isEmpty) p1 = Some(p)
    else p2 = Some(p)

    if (y1.isEmpty || y2.isEmpty) {
      y1 = Some(p.funcs(0))
      y2 = Some(p.funcs(1))
    }

    for ((n, p) <- List(1 -> p1, 2 -> p2))
      for (e <- document.getElementsByClassName(s"p$n"))
        e.innerText = p.map{p => s"p_$n = " + p.toLatex}.getOrElse("")

    for ((n, y) <- List(1 -> y1, 2 -> y2))
      for (e <- document.getElementsByClassName(s"y$n"))
        e.innerText = y.map{y => s"y_$n = " + y.toLatex}.getOrElse("")

    if (current == "equation") selectSidebar("points")
    js.eval("formatStaticEquations()")
  }
}

object IntegralSidebar {
  import Sidebar._

  def setText(id: String, str: String) {
    document.getElementById(s"integral-$id").innerText = str
  }

  var function: Option[Sym] = None
  var integral: Option[Sym] = None
  var solution: Option[Sym] = None

  def select(): JsContext => Unit = {
    if (p1.isEmpty || p2.isEmpty || y1.isEmpty || y2.isEmpty) return this.draw(_)

    this.function = Some(++(p1.get.funcs(0), **(-1, p1.get.funcs(1))))
    this.integral = function.get.integral

    if (integral.isDefined)
      this.solution = Some(
        ++(integral.get.replaceExpr('x, p2.get.x),
          **(-1, integral.get.replaceExpr('x, p1.get.x)))
          .simple
      )

    for (i <- integral ; s <- solution) {
      val suScripts = s"_{${p1.get.x.toLatex}}^{${p2.get.x.toLatex}}"
      setText("solution1", s"\\int$suScripts ${function.get.toLatex}")
      setText("solution2", s" = \\left[ ${integral.get.toLatex} \\right]$suScripts")
      setText("solution3", " = " + solution.get.toLatex)
      setText("solution4", " ≈ " + solution.get.approx.head)
    }
    return this.draw(_)
  }

  def draw(ctx: JsContext) {
    
  }
}


object TangentSidebar {
  import Sidebar._

  def setText(id: String, str: String) {
    document.getElementById(s"tangent-$id").innerText = str
  }

  var function: Option[Sym] = None

  def select(): JsContext => Unit = {
    if (p1.isEmpty || y1.isEmpty) return this.draw(_)

    val p = p1.get
    val y = y1.get

    val slope = y.derivative.simple.replaceExpr(SymVar('x), p.x).simple
    val yint = ++(p.y, **(-1, slope, p.x)).simple

    this.function = Some(++(**(slope, 'x), yint))

    setText("equation", s"y = ${function.get.toLatex}")

    js.eval("formatStaticEquations()")

    return this.draw(_)
  }

  def draw(ctx: JsContext) {
    import Graph._

    ctx.strokeStyle = Sidebar.color
    
    val maxX = pos.x + (ctx.canvas.width - marginX) * pos.xs
    drawLine(
      canvasX(pos.x),
      canvasY(this.function.get.approx('x -> pos.x).head),
      canvasX(maxX),
      canvasY(this.function.get.approx('x -> maxX).head),
    )(ctx)
  }
}
