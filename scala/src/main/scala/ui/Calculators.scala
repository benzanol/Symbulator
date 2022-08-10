package sympany.ui

import sympany._
import sympany.math._

import scala.scalajs.js
import js.annotation.JSExportTopLevel

import org.scalajs.dom
import org.scalajs.dom.document

import JsUtils.makeElement

object CalcSolver {
  trait AsyncSolver {
    def step(): Option[Seq[CalcSolution]]
  }

  trait CalcSolution {
    def beforeNode: dom.Node
    def insideNode: dom.Node
    def afterNode: dom.Node

    def stringToNode(str: String) = makeElement("div",
      "class" -> "mixed-equation-string",
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
}

object CalcFields {
  import CalcSolver._

  class Calculator(val name: String)(val fields: CalcField*) {
    // Run step function for all fields
    def step(): Boolean = fields.map(_.step()).contains(false)

    def update() {
      for (f <- fields) f.update(this)

      Graph.setGraphs(fields.flatMap(_.graphs()), Nil)
    }

    // Get an equation by a certain name
    def getEquation(name: String): Option[Sym] =
      fields.collect{ case e: EquationField => e }
        .find(_.name == name)
        .flatMap(_.expr)

    // Generate the dom representation
    val element = makeElement("div", "class" -> "calculator")
    this.element.replaceChildren(
      this.fields.map{f => f.node}:_*
    )
  }


  trait CalcField {
    val node: dom.Node

    // Called whenever an equation field is updated
    def update(c: Calculator): Unit = {}

    // A function that can be overriden by an equation to run
    // arbitrary code (function will be called continuously)
    def step(): Boolean = true

    def graphs(): Seq[Sym] = Nil
  }

  class EquationField(val name: String) extends CalcField {
    // Create a blank node, then transform it into a mathquill field
    val node = makeElement("p")
    js.Dynamic.global.makeMQField(node, this.setLatex(_))

    // Keep track of the current latex string and expression
    var latex: String = ""
    var expr: Option[Sym] = None
    override def graphs() = expr.toSeq

    def setLatex(newLatex: String) {
      latex = newLatex
      expr = Parse.parseLatex(newLatex)

      Calculators.tickCalculator()
    }
  }

  class ResultField(field: String, makeSolver: Sym => AsyncSolver) extends CalcField {
    // Keep track of the current equation and solver for that equation
    var expr: Option[Sym] = None
    var solver: Option[AsyncSolver] = None

    // Called whenever any equation is updated
    override def update(c: Calculator) {
      val newExpr = c.getEquation(field)

      if (newExpr != expr) {
        expr = newExpr
        solutions = None
        updateNode()

        solver = expr.map(makeSolver)
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
        if (expr.isEmpty) makeElement("p", "innterText" -> "No Equation!")
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
      new ResultField("e1", (e1) => new IntegralSolver(e1)),
    ),
    new Calculator("Area between curves")(
      new EquationField("e1"),
      new ResultField("e1", e1 => new IntegralSolver(e1)),
      new EquationField("e2"),
      new ResultField("e2", e2 => new IntegralSolver(e2)),
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
