package sympany.ui

import scala.util.chaining._

import sympany._
import sympany.math._
import sympany.Sym._
import sympany.math.Simplify.simplify

import scala.scalajs.js
import js.annotation.JSExportTopLevel

import org.scalajs.dom
import org.scalajs.dom.document

import JsUtils._

object CalcSolver {
  import CalcFields._

  trait CalcSolution {
    def solution: Sym
    // Only displayed for sub nodes, before the show button
    def beforeNode: dom.Node
    // Displayed for subsequent nodes, and folded for sub nodes
    def insideNode(num: Int)(wrap: Sym => Sym): dom.Node
    // List of rules to be displayed after the inside node
    def rules: Seq[CalcSolution]

    def wrapFunc(e: Sym): Sym = e
    def wrappedInsideNode(num: Int)(wrap: Sym => Sym): org.scalajs.dom.Node = {
      /* How the current rule is displayed is dependent on the previous
       * rules, so `wrap` provides a way to display the expressions in
       * the rule in terms of the previous rules For example, replacing
       * x with u if there was previously a U-Sub.
       * 
       * Num indicates the number of steps listed before this one at the
       * same level, which could be used to number the steps
       */

      // If this rule created several new integrals, list them as sub
      // rules, but if it only created one, list it after, but at the
      // same level as, this rule
      if (rules.length == 1)
        makeElement("div", "children" -> (
          makeElement("div",
            "class" -> "solution-step-details",
            "children" -> Seq(insideNode(num)(wrap))
          ) +: rules.map{r => r.wrappedInsideNode(num + 1){e => this.wrapFunc(wrap(e))}}
        ))
      else
        makeElement("div",
          "class" -> "solution-step-details",
          "children" -> (insideNode(num)(wrap) +: rules.map(_.node))
        )
    }

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
        "children" -> Seq(wrappedInsideNode(0)(identity))
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
        )
      )
    }
  }

  class CustomSolution(val solution: Sym, before: String, inside: String)
    (val rules: Seq[CalcSolution]) extends CalcSolution {
    def beforeNode = stringToNode(before)
    def insideNode(num: Int)(wrap: Sym => Sym) = stringToNode(inside)
  }

  class ErrorSolution(text: String) extends CalcSolution {
    val rules = Nil
    val solution = 0

    def beforeNode = stringToNode(text, cls="result-description")
    def insideNode(num: Int)(wrap: Sym => Sym) = makeElement("p")
    override def node: dom.Node = beforeNode
  }


  trait AsyncSolver {
    def step(): (Seq[CalcSolution], Boolean)
  }

  class CustomSolver(solution: CalcSolution) extends AsyncSolver {
    def step() = (Seq(solution), false)
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

  class AsyncIntegralSolver(expr: Sym) extends AsyncSolver {
    private val iSolver = new Integral.IntegralSolver(
      expr.replaceExpr(SymVar('x), Sym.X)
    )

    def step(): (Seq[CalcSolution], Boolean) =
      iSolver.step() match {
        case None => (Nil, true)
        case Some(None) => (Nil, false)
        case Some(Some(rule)) => (Seq(rule), false)
      }
  }

  class IntegralResult(n: String)(field: String)(draw: Boolean) extends ResultField(n)(field) {
    def makeSolver(es: Seq[Seq[Sym]]) = new AsyncIntegralSolver(es(0)(0))

    override def drawings: Seq[Graph.JsContext => Unit] =
      if (draw) this.expressions.map{es => integralDrawing(es(0)(0), 0, _)}.toSeq
      else Nil
  }

  class DoubleIntegralResult(n: String)(f0: String, f1: String) extends ResultField(n)(f0, f1) {
    def makeSolver(es: Seq[Seq[Sym]]) = new AsyncIntegralSolver(++(es(0)(0), **(-1, es(1)(0))))

    override def drawings: Seq[Graph.JsContext => Unit] =
      this.expressions.map{es => integralDrawing(es(0)(0), es(1)(0), _)}.toSeq
  }


  class AsyncZeroSolver(expr: Sym) extends AsyncSolver {
    private val solver = new Zero.ZeroSolver(
      SymEquation(expr.replaceExpr(SymVar('x), Sym.X), 0)
    )

    var allZeros = Seq[Zero.ZeroRule]()
    var approxes = Set[Double]()

    def step(): (Seq[Zero.ZeroRule], Boolean) = {
      val stepped = solver.step()

      // Only add zeros who's end results are not already in the list,
      // and who aren't approximately equal to any of the existing
      // approximations
      for (z <- stepped._1)
        if (allZeros.find(_.endResult.get == z.endResult.get).isEmpty) {
          val apps = z.endResult.get.expanded.map(_.approx())
          if (apps.find(!_.isFinite).isEmpty && apps.find(approxes.contains(_)).isEmpty) {
            allZeros :+= z
            approxes ++= z.endResult.get.expanded.map(_.approx())
          }
        }

      return (allZeros, stepped._2)
    }
  }

  class ZeroResult(n: String)(field: String) extends ResultField(n)(field) {
    def makeSolver(es: Seq[Seq[Sym]]) = new AsyncZeroSolver(es(0)(0))

    override def points: Seq[(Sym, Sym, Sym)] = {
      for (es <- expressions.toSeq ; e <- es ; s <- solutions ; s1 <- s.solution.expanded)
      yield (e.head, s1, e.head.replaceExpr(SymVar('x), s1))
    }.toSeq
  }

  class IntersectionResult(n: String)(f0: String, f1: String) extends ResultField(n)(f0, f1) {
    def makeSolver(es: Seq[Seq[Sym]]) = new AsyncZeroSolver(++(es(0)(0), **(-1, es(1)(0))))

    override val title: String = "Intersections:"

    override def points: Seq[(Sym, Sym, Sym)] = {
      for (es <- expressions.toSeq ; e <- es ; s <- solutions ; s1 <- s.solution.expanded)
      yield (e.head, s1, e.head.replaceExpr(SymVar('x), s1))
    }.toSeq
  }


  class AreaBetweenCurvesResult(n: String)(e1: String, e2: String, i1: String, i2: String, ps: String)
      extends ResultField(n)(e1, e2, i1, i2, ps) {

    override val title: String = "Area Between Functions:"

    def makeSolver(es: Seq[Seq[Sym]]) = {
      es match {
        case Seq(Seq(e1), Seq(e2), Seq(i1), Seq(i2), ps) if ps.flatMap(_.expanded).length >= 2 =>
          new AreaBetweenCurvesSolver(e1, e2, i1, i2,
            ps.flatMap(_.expanded).sortWith(_.approx() < _.approx())
          )
        case _ => new CustomSolver(new ErrorSolution(es match {
          case Seq(_, _, _, _, Nil)    => "No intersection points found"
          case Seq(_, _, _, _, Seq(_)) => "Only 1 intersection point found"
          case Seq(_, _, Nil, Nil, _)  => "Integrals of equations not found"
        }))
      }

    }
  }

  class AreaBetweenCurvesSolver(e1: Sym, e2: Sym, i1: Sym, i2: Sym, xs: Seq[Sym]) extends AsyncSolver {
    // If this solver is created, xs should have atleast 2 elements
    if (xs.length < 2) throw new Error("Cannot solve for area with less than 2 intersections.")

    val rule: CalcSolution = (xs.init zip xs.tail)
      .foldRight(None: Option[CalcSolution]){
        case ((x1: Sym, x2: Sym), sub: Option[CalcSolution]) =>
          // The values of the integral difference at the start and end points
          val in1 = ++(i1.replaceExpr(X, x1), **(-1, i2.replaceExpr(X, x1)))
          val in2 = ++(i1.replaceExpr(X, x2), **(-1, i2.replaceExpr(X, x2)))
          val inDifference = simplify(++(in2, **(-1, in1)))

          // X in the center
          val middleX = x1.approx() + (x2.approx() - x1.approx()) / 2.0
          val e1Greater = e1.approx('x -> middleX) > e2.approx('x -> middleX)

          // The solution for this range
          val thisSolution = if (e1Greater) inDifference else **(-1, inDifference)
          // The solution for all the nested (later) ranges
          val prevSolution = sub.map(_.solution).getOrElse(SymInt(0))
          // Total solution so far
          val solution = simplify(++(prevSolution, thisSolution))
          //println(f"-1: $x1 -2: $x2 1: $in1 2: $in2 3: $thisSolution")

          val rangeStr = f"\\((${x1.toLatex}, ${x2.toLatex})\\)"
          val inequalityStr = f"\\(${e1.toLatex} ${if (e1Greater) ">" else "<"} ${e2.toLatex}\\)"

          val integralStr =
            if (e1Greater) f"(${e1.toLatex}) - (${e2.toLatex})"
            else f"(${e2.toLatex}) - (${e1.toLatex})"
          val integrationStr = f"\\(\\int_{${x1.toLatex}}^{${x2.toLatex}}${integralStr} = ${thisSolution.toLatex}\\)"

          Some(
            new CustomSolution(solution,
              f"\\(\\int_{${x1.toLatex}}^{${xs.last.toLatex}}" +
              f"\\mid ${++(e1, **(-1, e2)).toLatex} \\mid = ${solution.toLatex}",
              "<p>" + inequalityStr + " on interval " + rangeStr + "</p><br/>" + integrationStr
            )(sub.toSeq)
          )

      }.get

    def step(): (Seq[CalcSolution], Boolean) = (Seq(rule), false)

  }
}

object CalcFields {
  import CalcSolver._

  class Calculator(val name: String)(val fields: CalcField*) {
    // Run step function for all fields
    def step(): Boolean = fields.map(_.step()).contains(true)

    def update() {
      for (f <- fields) f.update(this)

      Graph.setGraphs(
        fields.flatMap(_.graphs),
        fields.flatMap(_.points),
        fields.flatMap(_.drawings)
      )
    }

    // Get an equation by a certain name
    def getExpressions(name: String): Option[Seq[Sym]] =
      fields.find(_.name == name).flatMap(_.results)

    // Generate the dom representation
    val element = makeElement("div", "class" -> "calculator")
    this.element.replaceChildren(
      this.fields.map(_.node):_*
    )
  }


  trait CalcField {
    val node: dom.Node

    // Expression to be used by other nodes
    def results: Option[Seq[Sym]]

    // How other fields will access the result
    def name: String


    // Called whenever an equation field is updated
    def update(c: Calculator): Unit = {}

    // Called continuously, and returns false when finished
    def step(): Boolean = false

    // List of expressions to put on the graph
    def graphs: Seq[Sym] = Nil

    // List of points to put on the graph
    def points: Seq[(Sym, Sym, Sym)] = Nil

    // List of extra things to draw on the graph
    def drawings: Seq[Graph.JsContext => Unit] = Nil
  }

  class EquationField(val name: String) extends CalcField {
    // Create a blank node, then transform it into a mathquill field
    val mqNode = makeElement("p", "id" -> f"mq-eqn-$name")
    val node = makeElement("div", "children" -> Seq(makeElement("br"), mqNode))
    js.Dynamic.global.makeMQField(mqNode, this.setLatex(_))

    // Keep track of the current latex string and expression
    var latex: String = ""
    var expression: Option[Sym] = None

    def results = expression.map(Seq(_))
    override def graphs = expression.toSeq

    def setLatex(newLatex: String) {
      latex = newLatex
      expression = Parse.parseLatex(newLatex)

      // Do not allow the expression to contain variables other than x and y
      def containsOtherVars(e: Sym): Boolean = e match {
        case SymVar(a) if !Seq('x, 'y, X.symbol).contains(a) => true
        case other => other.exprs.find(containsOtherVars).isDefined
      }
      if (expression.isDefined && containsOtherVars(expression.get))
        expression = None

      // Start stepping in case any result field depends on this field
      Calculators.tickCalculator()
    }
  }

  abstract class ResultField(val name: String)(fields: String*) extends CalcField {
    // Keep track of the current equation and solver for that equation
    var expressions: Option[Seq[Seq[Sym]]] = None

    // List of currently found solutions to the problem
    var solutions: Seq[CalcSolution] = Nil
    def results = Option.when(solver.isDefined)(solutions.map(_.solution))

    // Whether the solver is actively trying to find solutions
    var solving: Boolean = false

    var solver: Option[AsyncSolver] = None
    def makeSolver(es: Seq[Seq[Sym]]): AsyncSolver

    // Called whenever any equation is updated
    override def update(c: Calculator) {
      val newExprs: Seq[Seq[Sym]] = fields.flatMap(c.getExpressions)

      if (expressions != Some(newExprs)) {
        expressions = None
        solutions = Nil
        solver = None
        solving = false

        if (newExprs.length == fields.length) {
          expressions = Some(newExprs)
          solver = Some(makeSolver(newExprs))
          solving = true
        }

        updateNode()

      }
    }

    // Generate the solutions for the equation
    override def step(): Boolean = {
      if (!solving) return false

      val stepped = solver.get.step()
      solving = stepped._2

      // Redraw the node after finished solving
      if (!solving) updateNode()

      // If a solution was found, update the html view
      if (stepped._1 != solutions) {
        solutions = stepped._1
        updateNode()

        // Update any points/drawings
        // Start stepping in case any result field depends on this field
        Calculators.tickCalculator()
      }

      return solving
    }


    // Generate the dom representation
    val node: dom.Element = makeElement("div")
    updateNode()

    val title: String = ""

    private def updateNode() {
      node.replaceChildren(
        makeElement("p", "innerHTML" -> title, "class" -> "result-title")
          ,
        if (expressions.isEmpty && title == "") makeElement("p")
        else makeElement("div", "class" -> "result-contents", "children" -> Seq(
          if (expressions.isEmpty)
            makeElement("p",
              "class" -> "result-description",
              "innerText" -> "Enter equations"
            )
          else if (!solving && solutions.isEmpty)
            makeElement("p",
              "class" -> "result-description",
              "innerText" -> "No solutions found ):"
            )
          else makeElement("div",
            "class" -> "result-solutions",
            "children" -> (
              solutions.map(_.node)
                ++ Option.when(solving)(makeElement("p",
                  "class" -> "result-description",
                  "innerText" -> "Solving..."
                )).toSeq
            )
          )
        ))
      )
      js.Dynamic.global.formatStaticEquations()
    }
  }

  class HtmlField(text: String) extends CalcField {
    val name = "Text"
    val results = Some(Nil)
    val node = makeElement("div",
      "class" -> "text-field",
      "children" -> Seq(stringToNode(text))
    )
  }

  class BrField() extends CalcField {
    val name = "Break"
    val results = Some(Nil)
    val node = makeElement("br")
  }
}

object Calculators {
  import CalcSolver._
  import CalcFields._

  val calculators: Seq[Calculator] = Seq(
    new Calculator("Zeros")(
      new EquationField("e1"),
      new ZeroResult("z")("e1"),
    ),
    new Calculator("Intersections")(
      new EquationField("e1"),
      new EquationField("e2"),
      new IntersectionResult("i")("e1", "e2")
    ),
    new Calculator("Integral")(
      new EquationField("e1"),
      new IntegralResult("i")("e1")(true),
    ),
    new Calculator("Area between curves")(
      new EquationField("e1"),
      new IntegralResult("i1")("e1")(false),
      new EquationField("e2"),
      new IntegralResult("i2")("e2")(false),
      new BrField(),
      new IntersectionResult("ps")("e1", "e2"),
      new BrField(),
      new AreaBetweenCurvesResult("area")("e1", "e2", "i1", "i2", "ps")
    ),
  )

  var currentCalculator = calculators(0)


  // Make a certain calculator the current one
  def selectCalculator(calc: Calculator = currentCalculator) {
    currentCalculator = calc
    calc.update()
    document.getElementById("current-calculator").replaceChildren(calc.element)

    // Highlight the button for the current calculator
    document.getElementsByClassName("current-calc-btn").foreach(_.setAttribute("class", "calc-btn"))
    document.getElementById(nameToId(calc.name)).setAttribute("class", "calc-btn current-calc-btn")

    // Select the first equation box (won't work)
    calc.fields.collectFirst{ case f: EquationField =>
      js.eval(s"MQ(document.getElementById('mq-eqn-${f.name}')).focus()")
    }
  }

  // Call JS to start the timer to step the current calculator
  def tickCalculator() {
    currentCalculator.update()
    js.Dynamic.global.tickCalculator(() => currentCalculator.step())
  }

  // Generate the right sidebar for all the calculators
  def nameToId(name: String) = name.toLowerCase().replace(' ', '-')
  def setupCalculatorList(calcs: Seq[Calculator] = calculators) {
    val calcsDiv = document.getElementById("calculators")

    for (calc <- calcs) {
      val btn = makeElement("button",
        "class" -> "calc-btn",
        "id" -> nameToId(calc.name),
        "innerText" -> calc.name
      )

      btn.addEventListener("click", (e: Any) => selectCalculator(calc))
      calcsDiv.appendChild(btn)
      calcsDiv.appendChild(makeElement("br"))
    }
  }
}
