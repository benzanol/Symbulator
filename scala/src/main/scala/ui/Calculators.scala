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
    def step(): Option[Seq[Solution]]
  }

  sealed trait HtmlLine {
    def toHtml: dom.Element
  }
  case class HtmlText(text: String) extends HtmlLine {
    def toHtml = makeElement("p", "innerText" -> text)
  }
  case class HtmlEquation(eqn: String) extends HtmlLine {
    def toHtml = makeElement("p", "innerText" -> eqn, "class" -> "mq-static")
  }

  class Solution(before: Seq[HtmlLine], after: Seq[HtmlLine], sub: Seq[Solution]) {
    def toHtml: dom.Element = {
      val details = makeElement("div",
        "style" -> "display:none",
        "children" -> Seq(
          makeElement("div",
            "style" -> "padding-left: 40px",
            "children" -> (after.map(_.toHtml) ++ sub.map(_.toHtml))
          )
        )
      )
      val hideBtn = makeElement("button", "innerText" -> "Hide Steps", "style" -> "display:none")
      val showBtn = makeElement("button", "innerText" -> "Show Steps", "style" -> "display:block")

      // Hide and show the details and buttons on click
      hideBtn.addEventListener("click", (event: Any) => {
        details.setAttribute("style", "display:none")
        hideBtn.setAttribute("style", "display:none")
        showBtn.setAttribute("style", "display:block")
      })
      showBtn.addEventListener("click", (event: Any) => {
        details.setAttribute("style", "display:block")
        hideBtn.setAttribute("style", "display:block")
        showBtn.setAttribute("style", "display:none")
      })

      makeElement("div",
        "style" -> f"padding-left: 40px",
        "children" -> (before.map(_.toHtml) ++ Seq(showBtn, hideBtn, details))
      )
    }
  }


  def makeIntegralSolver(expr: Sym) = new IntegralSolver(expr)
  class IntegralSolver(expr: Sym) extends AsyncSolver {
    private val iSolver = new Integral.IntegralSolver(
      expr.replaceExpr(SymVar('x), Sym.X)
    )

    def ruleToSolutions(rule: Integral.IntegralRule): Seq[Solution] =
      new Solution(
        Seq(HtmlEquation(SymIntegral(rule.integral).toLatex + " = " + rule.solution.toLatex)),
        Seq(HtmlText(rule.toString),
          HtmlEquation(SymIntegral(rule.integral).toLatex + " = " + rule.forward.toLatex)),
        rule.subRules.flatMap(ruleToSolutions)
      ) +: rule.afterRules.flatMap(ruleToSolutions)


    def step(): Option[Seq[Solution]] =
      iSolver.step() match {
        case None => None
        case Some(None) => Some(Nil)
        case Some(Some(rule)) => Some(ruleToSolutions(rule))
      }
  }
}

object Calculators {
  class Calculator(val name: String)(val fields: CalcField*) {
    // Manage whether this calculator is currently selected
    var current = false
    def select() {
      this.current = true

    }
    def deselect() {
      this.current = false
    }


    // Run the step functions of all the fields
    def step(): Boolean = fields.map(_.step()).contains(false)


    // Generate the dom representation
    val element = makeElement("div", "class" -> "calculator")
    this.element.replaceChildren(
      this.fields.map{f => f.node}:_*
    )
  }


  sealed trait CalcField {
    val node: dom.Node

    // A function that can be overriden by an equation to run
    // arbitrary code (function will be called continuously)
    def step(): Boolean = true

    def graphs(): Seq[Sym] = Nil
  }

  class EquationField() extends CalcField {
    // Create a blank node, then transform it into a mathquill field
    val node = makeElement("p")
    js.Dynamic.global.makeMQField(this.node, this.update(_))

    // Keep track of the current latex string and expression
    var latex: String = ""
    var expr: Option[Sym] = None

    def update(newLatex: String) {
      this.latex = newLatex
      this.expr = Parse.parseLatex(newLatex)
      for (r <- this.results) r.updateExpr(this.expr)

      // Start the calculator ticking again
      if (this.expr.isDefined) tickCalculator()
    }


    // List of results which depend on this equation
    private var results = Seq[ResultField]()
    def addResult(r: ResultField) {
      results +:= r
    }
  }

  import CalcSolver._
  class ResultField(eqn: EquationField, newSolver: Sym => AsyncSolver) extends CalcField {
    eqn.addResult(this)

    // Keep track of the current equation and solver for that equation
    var expr: Option[Sym] = None
    var solver: Option[AsyncSolver] = None

    def updateExpr(newExpr: Option[Sym]) {
      this.expr = newExpr
      this.solutions = None
      this.solver = newExpr.map(newSolver)

      this.updateNode()
    }


    // Generate the solutions for the equation
    var solutions: Option[Seq[CalcSolver.Solution]] = None
    override def step() = {
      if (solutions.isDefined || this.solver.isEmpty) true
      else {
        this.solutions = this.solver.get.step()

        // If a solution was found, update the html view
        if (this.solutions.isEmpty) false
        else {
          this.updateNode()
          true
        }
      }
    }


    // Generate the dom representation
    val node: dom.Element = makeElement("div")

    private def updateNode() {
      this.node.replaceChildren(
        (this.expr, this.solutions) match {
          case (None, _) => makeElement("p", "innterText" -> "No Equation!")
          case (Some(_), None) => makeElement("p", "innerText" -> "Solving...")
          case (Some(_), Some(Nil)) => makeElement("p", "innerText" -> "No solution")
          case (Some(_), Some(sols)) => makeElement("div",
            "id" -> "solutions",
            "children" -> sols.flatMap{sol => Seq(
              makeElement("p", "innerText" -> ","), makeElement("br"), sol.toHtml
            )}.drop(2) // Remove the first comma and newline
          )
        }
      )

      if (this.solutions.isDefined)
        js.Dynamic.global.formatStaticEquations()
    }

    updateNode()
  }

  class TextField(text: String) extends CalcField {
    val node = makeElement("p", "innerText" -> text)
  }


  def tickCalculator() {
    js.Dynamic.global.tickCalculator(currentCalculator.name)
  }

  @JSExportTopLevel("selectCalculator")
  def selectCalculator(name: String) {
    calculators.find(_.name == name) match {
      case Some(c) => {
        this.currentCalculator = c
        document.getElementById("sidebar").replaceChildren(c.element)
        tickCalculator()
      }
      case None => throw new Error(f"Not a calculator: $name")
    }
  }

  @JSExportTopLevel("stepCurrentCalculator")
  def stepCurrentCalculator(): Boolean = currentCalculator.step()


  val calculators: Seq[Calculator] = Seq(
    {
      val e1 = new EquationField()
      new Calculator("Integral")(
        new TextField("Hello!"),
        e1,
        new ResultField(e1, CalcSolver.makeIntegralSolver),
      )
    }
  )

  var currentCalculator = calculators(0)
}

