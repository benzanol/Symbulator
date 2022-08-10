package sympany.ui

import sympany._
import sympany.math._
import sympany.Sym._

import scala.scalajs.js
import js.annotation.JSExportTopLevel

import org.scalajs.dom
import org.scalajs.dom.document

import JsUtils.makeElement

object CalcSolver {
  import CalcFields._

  trait CalcSolution {
    def beforeNode: dom.Node
    def insideNode: dom.Node
    def afterNode: dom.Node

    def stringToNode(str: String, cls: String = "") =
      makeElement("div",
        "class" -> cls,
        "innerHTML" ->
          (str.replace("\\(", "<p class=\"mq-static\">")
            .replace("\\)", "</p>"))
      )

    def node: dom.Node = {
      val showBtn = makeElement("button",
        "class" -> "show-steps-btn",
        "innerText" -> "▹ Show Steps"
      )
      val hideBtn = makeElement("button",
        "class" -> "show-steps-btn",
        "innerText" -> "▿ Hide Steps"
      )

      val details = makeElement("div",
        "class" -> "solution-step-indented",
        "children" -> Seq(insideNode)
      )

      def updateHidden(expanded: Boolean) {
        details.asInstanceOf[js.Dynamic].hidden = !expanded
        hideBtn.asInstanceOf[js.Dynamic].hidden = !expanded
        showBtn.asInstanceOf[js.Dynamic].hidden = expanded
      }

      // Hide and show the details and buttons on click
      hideBtn.addEventListener("click", (event: Any) => updateHidden(false))
      showBtn.addEventListener("click", (event: Any) => updateHidden(true ))

      updateHidden(false)

      makeElement("div",
        "class" -> "solution-step",
        "children" -> Seq(
          beforeNode,
          showBtn, hideBtn, details,
          makeElement("br"),
          afterNode
        )
      )
    }
  }

  trait AsyncSolver {
    def step(): Option[Seq[CalcSolution]]
  }


  def integralDrawing(e1: Sym, e2: Sym, ctx: Graph.JsContext) {
    import Graph._

    // Make sure that both points and both functions are defined
    val x1 = Graph.pos.x - (10 * Graph.pos.xs)
    val y1 = e1.approx('x -> Graph.pos.x)
    val x2 = Graph.pos.x + (ctx.canvas.width - Graph.marginX) * Graph.pos.xs + (10 * Graph.pos.xs)
    val y2 = e1.approx('x -> x2)

    ctx.beginPath()

    ctx.fillStyle = "#8800BB66"

    // Go to the starting position
    ctx.moveTo(canvasX(x1), canvasY(y1))

    // Trace 100 points both functions
    for (x <- BigDecimal(x1) to BigDecimal(x2) by BigDecimal((x2 - x1) / 100.0)) {
      val y = e1.approx('x -> x.toDouble)
      if (y.isFinite && x.toDouble.isFinite)
        ctx.lineTo(canvasX(x.toDouble), canvasY(y))
    }
    for (x <- BigDecimal(x2) to BigDecimal(x1) by BigDecimal((x1 - x2) / 100.0)) {
      val y = e2.approx('x -> x.toDouble)
      if (y.isFinite && x.toDouble.isFinite)
        ctx.lineTo(canvasX(x.toDouble), canvasY(y))
    }

    ctx.closePath()
    ctx.fill()
  }

  class IntegralSolver(expr: Sym) extends AsyncSolver {
    private val iSolver = new Integral.IntegralSolver(
      expr.replaceExpr(SymVar('x), Sym.X)
    )

    def step(): Option[Seq[CalcSolution]] =
      iSolver.step() match {
        case None => None
        case Some(None) => Some(Nil)
        case Some(Some(rule)) => Some(Seq(rule))
      }
  }

  class IntegralResult(field: String) extends ResultField(field) {
    def makeSolver(es: Seq[Sym]) = new IntegralSolver(es(0))

    override def drawings: Seq[Graph.JsContext => Unit] =
      this.exprs.map{es => integralDrawing(es(0), 0, _)}.toSeq
  }

  class DoubleIntegralResult(f1: String, f2: String) extends ResultField(f1, f2) {
    def makeSolver(es: Seq[Sym]) = new IntegralSolver(++(es(0), **(-1, es(1))))

    override def drawings: Seq[Graph.JsContext => Unit] =
      this.exprs.map{es => integralDrawing(es(0), es(1), _)}.toSeq
  }
}

object CalcFields {
  import CalcSolver._

  class Calculator(val name: String)(val fields: CalcField*) {
    // Run step function for all fields
    def step(): Boolean = fields.map(_.step()).contains(false)

    def update() {
      for (f <- fields) f.update(this)

      //println(fields(0).asInstanceOf[EquationField].expr)
      //println(fields(1).asInstanceOf[ResultField].exprs)

      Graph.setGraphs(
        fields.flatMap(_.graphs),
        Nil,
        fields.flatMap(_.drawings)
      )
    }

    // Get an equation by a certain name
    def getEquation(name: String): Option[Sym] =
      fields.collect{ case e: EquationField => e }
        .find(_.name == name)
        .flatMap(_.expr)

    // Generate the dom representation
    val element = makeElement("div", "class" -> "calculator")
    this.element.replaceChildren(
      this.fields.flatMap{f => Seq(f.node, makeElement("br"))}:_*
    )
  }


  trait CalcField {
    val node: dom.Node

    // Called whenever an equation field is updated
    def update(c: Calculator): Unit = {}

    // A function that can be overriden by an equation to run
    // arbitrary code (function will be called continuously)
    def step(): Boolean = true

    def graphs: Seq[Sym] = Nil

    def drawings: Seq[Graph.JsContext => Unit] = Nil
  }

  class EquationField(val name: String) extends CalcField {
    // Create a blank node, then transform it into a mathquill field
    val node = makeElement("p")
    js.Dynamic.global.makeMQField(node, this.setLatex(_))

    // Keep track of the current latex string and expression
    var latex: String = ""
    var expr: Option[Sym] = None
    override def graphs = expr.toSeq

    def setLatex(newLatex: String) {
      latex = newLatex
      expr = Parse.parseLatex(newLatex)

      Calculators.tickCalculator()
    }
  }

  abstract class ResultField(fields: String*) extends CalcField {
    // Keep track of the current equation and solver for that equation
    var exprs: Option[Seq[Sym]] = None

    var solver: Option[AsyncSolver] = None
    def makeSolver(es: Seq[Sym]): AsyncSolver

    // Called whenever any equation is updated
    override def update(c: Calculator) {
      val newExprs = fields.flatMap(c.getEquation)

      if (exprs != Some(newExprs)) {
        exprs = Option.when(newExprs.length == fields.length)(newExprs)

        solutions = None
        updateNode()

        solver = exprs.map(makeSolver)
      }
    }

    // Generate the solutions for the equation
    var solutions: Option[Seq[CalcSolution]] = None
    override def step(): Boolean = {
      if (solver.isEmpty || solutions.isDefined) return true

      solutions = solver.get.step()

      if (solutions.isEmpty) return false

      // If a solution was found, update the html view
      updateNode()
      return true
    }


    // Generate the dom representation
    val node: dom.Element = makeElement("div")
    updateNode()

    private def updateNode() {
      node.replaceChildren(
        if (exprs.isEmpty) makeElement("p", "innterText" -> "No Equation!")
        else solutions match {
          case None => makeElement("p", "innerText" -> "Solving...")
          case Some(Nil) => makeElement("p", "innerText" -> "No solution")
          case Some(sols) => makeElement("div",
            "id" -> "solutions",
            "children" -> sols.flatMap{sol => Seq(
              makeElement("p", "innerText" -> ","), makeElement("br"), sol.node
            )}.drop(2) // Remove the first comma and newline
          )
        }
      )

      if (solutions.isDefined)
        js.Dynamic.global.formatStaticEquations()
    }
  }

  class TextField(text: String) extends CalcField {
    val node = makeElement("p", "innerText" -> text)
  }
}

object Calculators {
  import CalcSolver._
  import CalcFields._

  val calculators: Seq[Calculator] = Seq(
    new Calculator("Integral")(
      new EquationField("e1"),
      new IntegralResult("e1"),
    ),
    new Calculator("Area between curves")(
      new EquationField("e1"),
      new EquationField("e2"),
      new DoubleIntegralResult("e1", "e2"),
      new TextField("Area between curves:"),
    )
  )

  var currentCalculator = calculators(0)


  // Make a certain calculator the current one
  def selectCalculator(calc: Calculator = currentCalculator) {
    currentCalculator = calc
    calc.update()
    document.getElementById("current-calculator").replaceChildren(calc.element)
  }

  // Call JS to start the timer to step the current calculator
  def tickCalculator() {
    currentCalculator.update()
    js.Dynamic.global.tickCalculator(() => currentCalculator.step())
  }

  // Generate the right sidebar for all the calculators
  def setupCalculatorList(calcs: Seq[Calculator] = calculators) {
    val calcsDiv = document.getElementById("calculators")
    for (calc <- calcs) {
      val btn = makeElement("button", "class" -> "calc-btn", "innerText" -> calc.name)
      btn.addEventListener("click", (e: Any) => selectCalculator(calc))
      calcsDiv.appendChild(btn)
      calcsDiv.appendChild(makeElement("br"))
    }
  }
}
