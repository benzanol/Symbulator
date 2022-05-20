package sympany.ui

import scala.util.chaining._

import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.window
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.Main.jslog
import sympany.Parse.parseLatex
import sympany.Sym.replaceExpr
import sympany.ui.SuperSym
import sympany._
import sympany.math._

object Graph {
  // Set up the graph when it is loaded for the first time
  def setup: Unit = {
	fc.addEventListener("mousemove", panGraph)
	fc.addEventListener("wheel", zoomGraph)
	
	fc.addEventListener("mousedown", { (e: Any) => mouseDown = true  })
	fc.addEventListener("mouseup",   { (e: Any) => mouseDown = false })
	fc.addEventListener("mouseout",  { (e: Any) => mouseDown = false })
	
	window.addEventListener("resize", { (e: Any) => draw })
	
	draw
  }

  type JsCanvas = dom.HTMLCanvasElement
  type JsContext = dom.CanvasRenderingContext2D

  private def drawLine(x1: Double, y1: Double, x2: Double, y2: Double, w: Int = -1)
	(implicit ctx: JsContext): Unit = {
	
	ctx.beginPath()
	
	if (w != -1)
	  ctx.lineWidth = w
	
	ctx.moveTo(x1, y1)
	ctx.lineTo(x2, y2)
	ctx.stroke()
  }
  
  private def canvasX(x: Double): Int = (marginX + (x - pos.x) / pos.xs).toInt
  private def canvasY(y: Double): Int = (fc.height - marginY - (y - pos.y) / pos.ys).toInt


  // Variables
  private val fc: JsCanvas = document.getElementById("graph-functions").asInstanceOf[JsCanvas]
  private val fctx: JsContext = fc.getContext("2d").asInstanceOf[JsContext]
  
  private val gc: JsCanvas = document.getElementById("graph-grid").asInstanceOf[JsCanvas]
  private val gctx: JsContext = gc.getContext("2d").asInstanceOf[JsContext]

  // Remember the position of the graph
  private case class GraphPos(x: Double, y: Double, xs: Double, ys: Double)
  private var pos: GraphPos = GraphPos(0, 0, 0.01, 0.01)
  
  // Margins as variables are necessary because they need to be adjusted
  private def marginX = Math.log10(pos.x.abs max (fc.height * pos.ys)).abs.toInt * 11 + 35
  private def marginY = 20

  private var mouseDown = false
  

  // Figure out how to move the graph
  @JSExportTopLevel("panGraph")
  def panGraph(event: dom.MouseEvent) {
	if (!mouseDown) return
	  
	val (cxs, cys) = (fc.width.toDouble / fc.clientWidth, fc.height.toDouble / fc.clientHeight)
	val (dx, dy) = (event.movementX*cxs * pos.xs, -event.movementY*cys * pos.ys)
	pos = GraphPos(pos.x - dx, pos.y - dy, pos.xs, pos.ys)
	draw
  }
  
  @JSExportTopLevel("zoomGraph")
  def zoomGraph(event: dom.WheelEvent) {
	val scale = Math.pow(1.0008, event.deltaY);
	
    val (w, h) = (fc.width * pos.xs, fc.height * pos.ys)
    if (scale > 1 && (w*10 > Double.MaxValue || h*10 > Double.MaxValue)) return
    if (scale < 1 && (w/10 < Double.MinValue || h/10 < Double.MinValue)) return
	  
	// Calculate the x and y position of the mouse pointer on the canvas
	val rect = fc.getBoundingClientRect
	val (mouseX, mouseY) = (event.clientX - rect.left, event.clientY - rect.top)
	
	// Calculate the change in x and y
	val dx = pos.xs * (mouseX - marginX) * (1 - scale)
	val dy = pos.ys * (fc.clientHeight - mouseY - marginY) * (1 - scale)
	
	// Update the position value
	pos = GraphPos(pos.x + dx, pos.y + dy, pos.xs * scale, pos.ys * scale)
	
	// Redraw the graph
	draw
  }


  // Draw the graph

  private var graphs = Seq[SuperSym]()
  private val colors = Seq("#AA0000", "#0000AA", "#008800")
  private val gridColor = "#AAAAAA"
  
  def setGraphs(exprs: Seq[SuperSym]): Unit = {
	this.graphs = exprs
	draw
  }
  
  def draw: Unit = {
	// Make the canvas dimensions match their pixel dimensions
	fc.width = fc.clientWidth
	fc.height = fc.clientHeight
	gc.width = gc.clientWidth
	gc.height = gc.clientHeight
	
	
	// Draw the functions on the main canvas
	for (i <- 0 until graphs.length) {
	  fctx.strokeStyle = colors(i % colors.length)
      
      graphs(i).all.foreach(drawExpression(_)(fctx))
	}
	
	// Remove any of the function lines that went into the margin
	fctx.clearRect(0, 0, marginX, fc.height)
	fctx.clearRect(0, fc.height - marginY, fc.width, fc.height)
	
	
	// Draw the grid on the background canvas
	gctx.font = "14px Serif"
	gctx.strokeStyle = gridColor
	drawGrid(gctx)
  }
  
  private def drawGrid(implicit ctx: JsContext): Unit = {
	// Loop through the same code twice for the horizontal and vertical lines
	for (horizontal <- List(true, false)) {
	  val (start, size) =
		if (horizontal) (pos.y, (ctx.canvas.height - marginY) * pos.ys)
		else (pos.x, (ctx.canvas.width - marginX) * pos.xs)
	  
	  // The minimum pixel distance for grid lines is constant,
	  // so calculate the minimum unit distance based on it
	  val pixMin = 15
	  val min = pixMin * (if (horizontal) pos.xs else pos.ys)
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
  
  // Drawing the actual function
  private def drawExpression(expr: SuperSym)(implicit ctx: JsContext): Unit = {
	ctx.beginPath();
	ctx.lineWidth = 5
    
    // Make sure to include important points on the curve (extremas, holes, etc)
    val tiny = (ctx.canvas.width * pos.xs) / 1000000.0
    
    val important = expr.importantPoints
      .map(_.approx(Map())).flatMap{n => List(n - tiny, n, n + tiny)}
    
    val undefined = expr.undefinedPoints
      .map(_.approx(Map())).flatMap{n => List(n - tiny, n + tiny)}
    
    // Calculate the function and derivative
    val f: Double => Double = expr.function.get
    val dfdx: Double => Double = { x => expr.derivative.approx(Map('x -> x)) }
	
	val segments = functionSegments(f, dfdx, important ++ undefined)
	
    
    segments.foreach(connectWithCurves)
	//connectWithLines(canvasPoints)(ctx)
	
    ctx.stroke()
  }
  
  // Get a distrobution of points with higher density of points where there is a steeper derivative
  private def functionSegments(f: Double => Double, dfdx: Double => Double, extras: Seq[Double] = Nil):
      Seq[Seq[(Double, Double)]] = {
    
    // The x position of the current point (starts slightly to the left of the screen)
	var x = pos.x
    
    val minY = pos.y
    val maxY = pos.y + (fc.height - marginY) * pos.ys
    def inRange(y: Double) = (y >= minY) && (y <= maxY)
    
    val width = (fc.width - marginX) * pos.xs
    val max = x + width;
    val dist = width / 500.0;
    
    // The extras that haven't yet been used - remove any that are outside of the screen
    var extrasLeft = extras.sortWith(_ < _).filter(_ > x).distinct
    
    // The list of points being made
	var segments = List(List[(Double, Double)]())
    
    while (x < max) {
      try {
        val y = f(x)
        
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
      
      x += dist
      
      if (extrasLeft.nonEmpty && extrasLeft.head <= x) {
        x = extrasLeft.head
        extrasLeft = extrasLeft.tail
      }
    }
	
	return segments
  }
  
  private def connectWithCurves(points: Seq[(Double, Double)])
    (implicit ctx: JsContext): Unit = {
	if (points.length < 2) return
      
    val ps = points.map{ t => (canvasX(t._1), canvasY(t._2)) }
    
    val height = ctx.canvas.height - marginY
    def inRange(y: Double) = (y >= 0) && (y <= height)
	
    // Draw the points (algorithm from stack overflow)
	ctx.moveTo(ps(0)._1, ps(0)._2);
    for (i <- 1 to ps.length - 3) {
      //if (i > ps.length - 5 || inRange(ps(i)._2) || inRange(ps(i+1)._2)) {
      val xc = (ps(i)._1 + ps(i + 1)._1) / 2;
      val yc = (ps(i)._2 + ps(i + 1)._2) / 2;
      ctx.quadraticCurveTo(ps(i)._1, ps(i)._2, xc, yc);
    }
    
    
    // Curve through the last two ps
    ctx.quadraticCurveTo(
	  ps(ps.length - 2)._1, ps(ps.length - 2)._2, ps.last._1, ps.last._2);
  }
  
  private def connectWithLines(points: Seq[(Int, Int)])
    (implicit ctx: JsContext): Unit = {
    if (points.length < 2) return
	  
	ctx.moveTo(points.head._1, points.head._1)
	for (i <- 1 to points.length - 2) {
      val p = points(i)
	  ctx.lineTo(p._1, p._2)
	  ctx.moveTo(p._1, p._2)
	}
	ctx.lineTo(points.last._1, points.last._2)
  }
}
