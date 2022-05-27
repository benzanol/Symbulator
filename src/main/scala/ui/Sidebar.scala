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
      case "distance" => Some(DistanceSidebar.select())
      case "slope" => Some(SlopeSidebar.select())
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

    selectSidebar("points")

    js.Dynamic.global.formatStaticEquations()
    Graph.draw
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

  def select(): JsContext => Unit =
    if (p1.isEmpty || p2.isEmpty || y1.isEmpty || y2.isEmpty) {
      return this.draw(_)
    } else {

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
    // Make sure that both points and both functions are defined
    for (gp1 <- Sidebar.p1 ; gp2 <- Sidebar.p2 ; f1 <- Sidebar.y1 ; f2 <- Sidebar.y2) {
      // Make sure that both points have defined x values
      for (x1 <- gp1.x.approx.headOption ; x2 <- gp2.x.approx.headOption) {
        ctx.beginPath()

        ctx.fillStyle = Sidebar.color + "66"

        // Go to the starting position
        ctx.moveTo(x1, Graph.canvasY(f1.approx('x -> x1).head))

        // Trace 100 points both functions
        for (x <- BigDecimal(x1) to BigDecimal(x2) by BigDecimal((x2 - x1) / 100.0)) {
          ctx.lineTo(Graph.canvasX(x.toDouble), Graph.canvasY(f1.approx('x -> x.toDouble).head))
        }
        for (x <- BigDecimal(x2) to BigDecimal(x1) by BigDecimal((x1 - x2) / 100.0)) {
          ctx.lineTo(Graph.canvasX(x.toDouble), Graph.canvasY(f2.approx('x -> x.toDouble).head))
        }

        ctx.closePath()
        ctx.fill()
      }
    }
  }
}



object TangentSidebar {
  import Sidebar._

  def setText(id: String, str: String) {
    document.getElementById(s"tangent-$id").innerText = str
  }

  var function: Option[Sym] = None

  def select(): JsContext => Unit =
    if (p1.isEmpty || y1.isEmpty) return this.draw(_)
    else {

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

object DistanceSidebar {
  import Sidebar._

  def setText(id: String, str: String) {
    document.getElementById(s"distance-$id").innerText = str
  }

  var distance: Option[Sym] = None
  var deltaX: Option[Sym] = None
  var deltaY: Option[Sym] = None
  var pos = List[Double]()

  def select(): JsContext => Unit =
    if (p1.isEmpty || p2.isEmpty) {
      this.pos = Nil
      return this.draw(_)
    } else {
      val (xa, xb, ya, yb) = (p1.get.x, p2.get.x, p1.get.y, p2.get.y)

      this.pos = List(xa, xb, ya, yb).map(_.approx.head)

      this.deltaX = Some(++(xb, **(-1, xa)).simple)
      this.deltaY = Some(++(yb, **(-1, ya)).simple)
      this.distance = Some(^(++(^(deltaX.get, 2), ^(deltaY.get, 2)), 1~2).simple)

      setText("deltax", s"\\Delta x = ${deltaX.get.toLatex}")
      setText("deltay", s"\\Delta y = ${deltaY.get.toLatex}")
      setText("distance", s"\\text{Distance} = ${distance.get.toLatex}")

      js.eval("formatStaticEquations()")

      return this.draw(_)
    }

  def draw(ctx: JsContext) =
    if (this.pos.length == 4) {
      import Graph._

      val (cx1, cx2) = (canvasX(this.pos(0)), canvasX(this.pos(1)))
      val (cy1, cy2) = (canvasY(this.pos(2)), canvasY(this.pos(3)))

      ctx.strokeStyle = Sidebar.color

      Graph.drawLine(cx1, cy1, cx2, cy2)(ctx)
      Graph.drawLine(cx1, cy1, cx2, cy1)(ctx)
      Graph.drawLine(cx2, cy1, cx2, cy2)(ctx)
    }
}

object SlopeSidebar {
  import Sidebar._

  def setText(id: String, str: String) {
    document.getElementById(s"slope-$id").innerText = str
  }

  var function: Option[Sym] = None

  def select(): JsContext => Unit =
    if (p1.isEmpty || p2.isEmpty) return this.draw(_)
    else {

      val (xa, xb, ya, yb) = (p1.get.x, p2.get.x, p1.get.y, p2.get.y)

      val slope = **( ++(yb, **(-1, ya)), ^(++(xb, **(-1, xa)), -1)).simple
      val yint = ++(ya, **(-1, slope, xa)).simple

      this.function = Some(++(**(slope, 'x), yint).simple)

      setText("slope", s"\\frac{\\Delta y}{\\Delta x} = ${slope.toLatex}")
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
