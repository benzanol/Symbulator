package sympany.ui

import scala.util.chaining._

import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.window
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._

object Graph {
  // Set up the graph when it is loaded for the first time
  def setup {
    fc.addEventListener("mousemove", panGraph)
    fc.addEventListener("wheel", zoomGraph)
    fc.addEventListener("mousemove", detectMouseAxes)

    fc.addEventListener("mousedown", { (e: Any) => mouseDown = true  })
    fc.addEventListener("mouseup",   { (e: Any) => mouseDown = false })
    fc.addEventListener("mouseout",  { (e: Any) => mouseDown = false })

    fc.addEventListener("mousemove", highlightPoints)
    fc.addEventListener("mouseout",  { (e: Any) => hidePointBox() })
    fc.addEventListener("mousedown", maybeClickPoint)

    window.addEventListener("resize", { (e: Any) => draw })

    setGraphs()
  }


  // Useful utils
  type JsCanvas = dom.HTMLCanvasElement
  type JsContext = dom.CanvasRenderingContext2D

  def drawLine(x1: Int, y1: Int, x2: Int, y2: Int, w: Int = -1)
    (implicit ctx: JsContext): Unit = {

    ctx.beginPath()

    if (w != -1)
      ctx.lineWidth = w

    ctx.moveTo(x1, y1)
    ctx.lineTo(x2, y2)
    ctx.stroke()
  }

  def canvasX(x: Double): Int = (marginX + (x - pos.x) / pos.xs).toInt
  def canvasY(y: Double): Int = (fc.height - marginY - (y - pos.y) / pos.ys).toInt

  val fc: JsCanvas = document.getElementById("graph-functions").asInstanceOf[JsCanvas]
  val fctx: JsContext = fc.getContext("2d").asInstanceOf[JsContext]

  val gc: JsCanvas = document.getElementById("graph-grid").asInstanceOf[JsCanvas]
  val gctx: JsContext = gc.getContext("2d").asInstanceOf[JsContext]

  // Remember the position of the graph
  case class GraphPos(x: Double, y: Double, xs: Double, ys: Double)
  var pos: GraphPos = GraphPos(0, 0, 0.01, 0.01)
  var (onXAxis, onYAxis) = (false, false)

  // Margins as variables are necessary because they need to be adjusted
  def marginX = Math.log10(pos.x.abs max (fc.height * pos.ys)).abs.toInt * 11 + 35
  def marginY = 20

  val pointRadius = 5

  var mouseDown = false


  // Figure out how to move the graph
  def panGraph(event: dom.MouseEvent) {
    // Only pan the graph if the mouse is down
    if (!mouseDown) return

    val dx = event.movementX * pos.xs
    val dy = -event.movementY * pos.ys
    pos = GraphPos(pos.x - dx, pos.y - dy, pos.xs, pos.ys)
    draw

  }

  def zoomGraph(event: dom.WheelEvent) {
    val scale = Math.pow(1.0008, event.deltaY);

    val (w, h) = (fc.width * pos.xs, fc.height * pos.ys)

    // Don't do anything if the scale is already too small or too large
    if (scale > 1 && (w*10 > Double.MaxValue || h*10 > Double.MaxValue)) return
    if (scale < 1 && (w/10 < Double.MinValue || h/10 < Double.MinValue)) return

    // Calculate the x and y position of the mouse pointer on the canvas
    val rect = fc.getBoundingClientRect
    val (mouseX, mouseY) = (event.clientX - rect.left, event.clientY - rect.top)

    // Calculate the change in x and y
    val dx = pos.xs * (mouseX - marginX) * (1 - scale)
    val dy = pos.ys * (fc.clientHeight - mouseY - marginY) * (1 - scale)

    // Only change one scale if the cursor is on one of the axes
    this.pos =
      if (onXAxis && !onYAxis) GraphPos(pos.x + dx, pos.y, pos.xs * scale, pos.ys)
      else if (onYAxis && !onXAxis) GraphPos(pos.x, pos.y + dy, pos.xs, pos.ys * scale)
      else GraphPos(pos.x + dx, pos.y + dy, pos.xs * scale, pos.ys * scale)

    // Redraw the graph
    draw
  }

  def detectMouseAxes(event: dom.MouseEvent) {
    // zoomGraph needs to know if the cursor is on the x or y axis,
    // and this needs to be calculated when moving the mouse

    // Figure out the position of the mouse and canvas
    val rect = fc.getBoundingClientRect
    val (mouseX, mouseY) = (event.clientX - rect.left, event.clientY - rect.top)

    // Figure out the position of the axes on the canvas
    val xAxisY = rect.height - marginY + pos.y/pos.ys
    val yAxisX = marginX - pos.x/pos.xs

    this.onXAxis = (xAxisY - mouseY).abs < 5
    this.onYAxis = (yAxisX - mouseX).abs < 5
  }


  // Draw the graph

  var graphs = Seq[Sym]()
  var points = Seq[IntersectionPoint]()
  var drawings = Seq[JsContext => Unit]()
  val colors = Seq("#AA0000", "#0000AA", "#008800")
  val graphThickness = 5
  val gridColor = "#AAAAAA"

  var segments = Seq[Seq[Seq[(Double, Double)]]]()

  case class IntersectionPoint(funcs: Seq[Sym], x: Sym, y: Sym, color: String) {
    def toLatex: String = s"\\left( ${x.toLatex}, \\quad \\quad ${y.toLatex} \\right)"
  }

  def setGraphs(
    exprs: Seq[Sym] = Nil,
    ps: Seq[(Sym, Sym, Sym)] = Nil,
    drawings: Seq[JsContext => Unit] = Nil
  ) {
    this.graphs = exprs

    this.points = ps.groupBy{t => (t._2, t._3)}.toSeq.map{
      case ((x, y), seq) => {
        val idx = exprs.indexOf(seq.head._1)
        new IntersectionPoint(seq.map(_._1), x, y,
          colors({if (idx == -1) 0 else idx} % colors.length)
        )
      }
    }

    this.drawings = drawings

    this.draw()
  }

  def draw() {
    // Hide the point box so that a point from a past function doesn't remain
    hidePointBox()

    // Make the canvas dimensions match their pixel dimensions
    fc.width = fc.clientWidth
    fc.height = fc.clientHeight
    gc.width = gc.clientWidth
    gc.height = gc.clientHeight


    // Draw the functions on the main canvas
    this.segments = Nil
    for (i <- 0 until graphs.length) {
      fctx.strokeStyle = colors(i % colors.length)
      segments :+= calculateSegments(graphs(i))
    }
    drawSegments()

    if (this.rainbow && this.rainbowTimer.isEmpty) {
      this.rainbowTimer = Some(js.eval("setInterval(repeatDraw, 100)").toString)
    } else if (!this.rainbow && this.rainbowTimer.isDefined) {
      js.eval(s"clearInterval(${rainbowTimer.get})")
      this.rainbowTimer = None
    }

    // Draw the points on the main canvas
    points.foreach{ p => drawPoint(p.x, p.y, p.color, false)(fctx) }

    // Draw the extra drawings on the main canvas
    for (d <- drawings)
      try {
        d.apply(fctx)
      } catch {
        case e: Throwable => ()
      }


    // Remove any of the function lines that went into the margin
    fctx.clearRect(0, 0, marginX, fc.height)
    fctx.clearRect(0, fc.height - marginY, fc.width, fc.height)


    // Draw the grid on the background canvas
    gctx.font = "14px Serif"
    gctx.strokeStyle = gridColor
    drawGrid(gctx)
  }

  def drawGrid(implicit ctx: JsContext) {
    // Loop through the same code twice for the horizontal and vertical lines
    for (horizontal <- List(true, false)) {
      val (start, size) =
        if (horizontal) (pos.y, (ctx.canvas.height - marginY) * pos.ys)
        else (pos.x, (ctx.canvas.width - marginX) * pos.xs)

      // The minimum pixel distance for grid lines is constant,
      // so calculate the minimum unit distance based on it
      val pixMin = 15
      val min = pixMin * (if (horizontal) pos.ys else pos.xs)
      val textPixMin = 100

      // Calculate all distances to draw grid lines at,
      // with the larger distanced grid lines being thicker than the closer ones
      var dists = List[BigDecimal](BigDecimal(10).pow(Math.ceil(Math.log10(size)).toInt))
      while (dists.head > min)
        dists = (
          if (Math.log10(dists.head.toDouble) % 1 != 0) BigDecimal(0) :: dists
          else if (0.1*dists.head >= min) (dists.head * 0.1) :: dists
          else if (0.2*dists.head >= min) (dists.head * 0.2) :: dists
          else if (0.5*dists.head >= min) (dists.head * 0.5) :: dists
          else BigDecimal(0) :: dists
        )

      // Remove the first element, because it is too small,
      // and then put the list in descending order
      dists = dists.tail.reverse

      // Keep shortening the distance until it gets too low
      for (i <- 0 until dists.length) {
        val dist: BigDecimal = dists(i)
        val pixDist: Double = (dist / (if (horizontal) -pos.ys else pos.xs)).toDouble

        // The x or y position of the current line being drawn
        // The pixel width needs to be a double to prevent getting progressively more inaccurate
        var cur: BigDecimal = dist * Math.ceil(start / dist.toDouble).toInt
        var pix: Double = cur.toDouble.pipe(if (horizontal) canvasY else canvasX)

        val thickness = dists.length - i

        // Calculate when to display text
        val textAll = pixDist.abs > textPixMin
        val powOf10 = textAll || Math.log10(dist.toDouble) % 1 == 0
        val text2s = textAll || (powOf10 && (pixDist.abs * 2) > textPixMin)
        val text5s = textAll || (!text2s && powOf10 && (pixDist.abs * 5) > textPixMin)

        // Draw each line for the current distance
        while (cur < start + size) {
          val pixInt = pix.toInt
          if (horizontal) drawLine(marginX, pixInt, ctx.canvas.width, pixInt, thickness)
          else drawLine(pixInt, 0, pixInt, ctx.canvas.height - marginY, thickness)

          if (textAll || (text2s && cur % (dist*2) == 0) || (text5s && cur % (dist*5) == 0))
            if (horizontal) ctx.fillText(cur.toString, 5, pixInt + 5)
            else ctx.fillText(cur.toString, pixInt - 10, ctx.canvas.height - 5)

          cur += dist
          pix += pixDist
        }
      }
    }
  }

  @JSExportTopLevel("repeatDraw")
  def repeatDraw() {
    fctx.clearRect(0, 0, fc.width, fc.height)
    drawSegments()
  }

  def drawSegments() =
    for (i <- 0 until this.segments.length ; s <- this.segments(i)) {
      fctx.strokeStyle = colors(i % colors.length)
      connectWithCurves(s)(fctx)
    }

  // Drawing special points
  def drawPoint(xe: Sym, ye: Sym, color: String, selected: Boolean = false)(implicit ctx: JsContext) {
    val (x, y) = (xe.approx(), ye.approx())
    if (!x.isFinite || !y.isFinite) return

    val cx = marginX + ((x - pos.x) / pos.xs).toInt
    val cy = ctx.canvas.height - marginY - ((y - pos.y) / pos.ys).toInt

    ctx.beginPath()

    ctx.lineWidth = 4
    ctx.strokeStyle = if (selected) "black" else color
    ctx.fillStyle = if (selected) "black" else "white"
    ctx.arc(cx, cy, pointRadius, 0, 2 * Math.PI)

    ctx.fill()
    ctx.stroke()
  }

  def connectWithCurves(points: Seq[(Double, Double)])(implicit ctx: JsContext) {
    ctx.lineWidth = graphThickness

    if (points.length < 2) return

    val ps = points.map{ t => (canvasX(t._1), canvasY(t._2)) }

    val height = ctx.canvas.height - marginY
    def inRange(y: Double) = (y >= 0) && (y <= height)

    // Draw the points (algorithm from stack overflow)
    ctx.moveTo(ps(0)._1, ps(0)._2);

    val timeOffset = 8 * System.nanoTime() / Math.pow(10, 7)

    if (!this.rainbow) ctx.beginPath()

    for (i <- 1 to ps.length - 4) {
      if (this.rainbow) ctx.beginPath()

      if (this.rainbow)
        ctx.strokeStyle = s"hsla(${i + timeOffset}, 100%, 50%, 1.0)";

      //if (i > ps.length - 5 || inRange(ps(i)._2) || inRange(ps(i+1)._2)) {
      val xc = (ps(i)._1 + ps(i + 1)._1) / 2;
      val yc = (ps(i)._2 + ps(i + 1)._2) / 2;

      val xc2 = (ps(i+2)._1 + ps(i + 1)._1) / 2;
      val yc2 = (ps(i+2)._2 + ps(i + 1)._2) / 2;

      if (this.rainbow && (i + timeOffset.toInt/8) % 300 == 0 && false) {

        val img = js.eval("let i = new Image() ; i.src = './Cat.png' ; i").asInstanceOf[dom.HTMLElement]

        val angle = Math.atan((yc2 - yc).toDouble / (xc2 - xc).toDouble)

        ctx.translate(xc, yc)
        ctx.rotate(angle)
        ctx.drawImage(img, -100, -100, 200, 200)
        ctx.rotate(-angle)
        ctx.translate(-xc, -yc)

      }

      ctx.moveTo(ps(i-1)._1, ps(i-1)._2);

      ctx.quadraticCurveTo(ps(i)._1, ps(i)._2, xc, yc);

      if (this.rainbow) {
        ctx.moveTo(ps(i)._1, ps(i)._2);

        ctx.quadraticCurveTo(xc, yc, xc2, yc2);
      }

      if (this.rainbow) ctx.stroke()
    }

    if (this.rainbow) ctx.beginPath()


    // Curve through the last two ps
    ctx.quadraticCurveTo(
      ps(ps.length - 2)._1, ps(ps.length - 2)._2, ps.last._1, ps.last._2);

    ctx.stroke()
  }

  // Rainbow mode
  var rainbow: Boolean = false
  var rainbowTimer: Option[String] = None

  @JSExportTopLevel("toggleRainbow")
  def toggleRainbow() {
    this.rainbow = !this.rainbow
    this.draw
  }


  // Display important points when the mouse hovers over them
  var currentPoint: Option[IntersectionPoint] = None

  def setPointer(pointer: Boolean) =
    document.getElementById("graph-container").setAttribute("style",
      if (pointer) "cursor:pointer" else ""
    )

  def highlightPoints(event: dom.MouseEvent) {
    val rect = fc.getBoundingClientRect()

    val mx = event.clientX - rect.left
    val my = event.clientY - rect.top

    for (p <- points) {
      val (x, y) = (p.x.approx(), p.y.approx())

      // Find the first point that is less than the min distance from the cursor
      if (Math.sqrt( Math.pow(canvasX(x)-mx, 2) + Math.pow(canvasY(y)-my, 2) ) < pointRadius) {

        // Set the current point
        currentPoint = Some(p)

        // Make the cursor a pointer
        setPointer(true)

        // Set the text of the point box and move it to the cursor
        val box = document.getElementById("point-box")
        box.innerText = s"\\left( ${p.x.toLatex}, \\quad ${p.y.toLatex} \\right)"
        box.setAttribute("style", s"left:${event.clientX + 10}px; top:${event.clientY + 10}px; display:block;")

        // Format the point as a latex equation
        js.eval("MQ.StaticMath(document.getElementById('point-box'));")

        return
      }
    }

    // If no points were found, make sure the box is hidden
    hidePointBox()
    setPointer(false)
    currentPoint = None
  }

  def hidePointBox() {
    val box = document.getElementById("point-box")
    box.innerHTML = ""
    box.setAttribute("style", "display:none;" )
  }

  def maybeClickPoint(event: dom.MouseEvent) =
    this.currentPoint match {
      case Some(p) => ()
      case None => ()
    }


  // Calculating the curve values

  /* Given one of the graph expressions, create a list of segments, each
   * segment being a list of points
   */
  def calculateSegments(sym: Sym): Seq[Seq[(Double, Double)]] = sym match {
    case SymVertical(x) =>
      return Seq(Seq(
        x.approx() -> -fctx.canvas.height * pos.xs,
        x.approx() -> fctx.canvas.height * pos.xs
      ))
    case _ => {
      // Make sure to include important points on the curve (extremas, holes, etc)
      val tiny = (fctx.canvas.width * pos.xs) / 1000000.0

      // Calculate the function and derivative
      return sym.expanded.flatMap{e => calculateFunctionSegments(
        { d: Double =>
          try {
            Some(e.at(d))
          } catch {
            case e: Throwable => None
          }
        }
      )};
    }
  }

  // Get a distrobution of points with higher density of points where there is a steeper derivative
  def calculateFunctionSegments(f: Double => Option[Double], extras: Seq[Double] = Nil):
      Seq[Seq[(Double, Double)]] = {

    val minY = pos.y
    val maxY = pos.y + (fc.height - marginY) * pos.ys
    //def inRange(y: Double) = (y >= minY) && (y <= maxY)
    def inRange(y: Double) = true

    // The total width of the screen in units
    val width = (fc.width - marginX) * pos.xs

    // The distance between calculated points will be a power of 1.5
    val dist = Math.pow(1.1, Math.round(Math.log(width / 500.0) / Math.log(1.1)))

    // The x position of the current point (starts slightly to the left of the screen)
    var x = pos.x - dist - (pos.x % dist)

    // When using an extra point, remember, where we were before
    var lastMultiple = x

    // The largest x value on the screen
    val max = pos.x + width + dist;

    // The extras that haven't yet been used - remove any that are outside of the screen
    var extrasLeft = extras.sortWith(_ < _).filter(_ > x).distinct

    // The list of points being made
    var segments = List(List[(Double, Double)]())

    while (x < max) {
      try {
        val y: Double = f(x).getOrElse{throw new ArithmeticException ; 0}

        // If the current, last, and last last were out of range, remove the last one
        if (segments.head.length >= 2 && !inRange(y) &&
          !inRange(segments.head(0)._2) && !inRange(segments.head(1)._2))
          segments = segments.head.tail :: segments.tail

        if (y.isFinite) segments = ((x, y) :: segments.head) :: segments.tail
        else throw new Exception

      } catch {
        case _: Throwable =>
          if (segments.head.nonEmpty) segments = Nil :: segments
      }

      x = lastMultiple + dist

      if (extrasLeft.nonEmpty && extrasLeft.head <= x) {
        x = extrasLeft.head
        extrasLeft = extrasLeft.tail
      } else if (Math.floor(x) > Math.floor(lastMultiple) && dist < 1) {
        x = Math.floor(x)
        lastMultiple = x
      } else {
        lastMultiple = x
      }
    }

    return segments
  }
}
