package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import sympany._
import sympany.math.Simplify.simplify
import sympany.Sym._
import sympany.Pattern._
import org.scalajs.dom.Node
import org.scalajs.dom.Element


object Zero {
  import ui.CalcSolver.CalcSolution
  import JsUtils._

  // Maximum number of nested zero solvers
  val maxDepth = 15

  type Eqn = SymEquation

  trait ZeroRule extends CalcSolution {
    def beforeNode: Node = endResult match {
      case None => stringToNode("Unsolved root")
      case Some(z) => stringToNode(f"\\(x = ${z.toLatex}\\)<br/>")
    }

    def endResult: Option[Sym]
    def solution = endResult.get


    def ruleDescription: String
    def insideNode(num: Int)(wrap: Sym => Sym) = JsUtils.stringToNode(
      // Have a bullet before the rule
      //"①②③④⑤⑥⑦⑧⑨"(num) + " " +
      "➣ " +

      // Include a brief description of the rule
      this.ruleDescription + "<br/>"

      // Show the transformation the rule is making
      ,
      cls = "solution-step-title"
    )
  }

  class FinalZeroRule(val expr: Eqn, zero: Sym, description: String) extends ZeroRule {
    def ruleDescription = f"$description<br/>\\(x = ${zero.toLatex}\\)"
    def endResult = Some(zero)
    def rules = Nil

    // Don't display the identity step (it is redundant)
    override def insideNode(num: Int)(wrap: Sym => Sym): Element =
      if (description == "Identity") makeElement("p")
      else super.insideNode(num)(wrap)
  }

  class IntermediateZeroRule(val expr1: Eqn, val expr2: Eqn, val description: String) extends ZeroRule {
    def ruleDescription = f"$description:<br/>\\(${expr2.toLatex}\\)"
    def endResult = rules.headOption.flatMap(_.endResult)

    // Each intermediate zero rule in a solution will have exactly 1
    // sub rule, and multiple instances of a single rule with
    // different sub rules will sometimes be needed
    var rules = Seq[ZeroRule]()
    def withSubRule(r: ZeroRule): IntermediateZeroRule = {
      val newR = new IntermediateZeroRule(expr1, expr2, description)
      newR.rules = Seq(r)
      return newR
    }
  }


  def oppositeExpression(e: Eqn): Eqn = SymEquation(e.right, e.left)

  class ZeroSolver(val expr: Eqn,
    history: mutable.Set[Eqn] = mutable.Set[Eqn](),
    depth: Int = 1
  ) {
    // Just for testing purposes
    import scala.scalajs.js
    def jsobj: js.Dictionary[Any] =  js.Dictionary(
      "expr" -> expr.toString(),
      "children" -> js.Array(fullQueue.map(_._2.jsobj):_*)
    )

    // Add the expression and its opposite to the history so they are never referenced again
    history.addAll(Seq(expr, oppositeExpression(expr)))

    // List of child solvers and the rules they go with
    var fullQueue: Seq[(IntermediateZeroRule, ZeroSolver)] = Nil
    var queue: Seq[(IntermediateZeroRule, ZeroSolver)] = Nil

    // Index as -1 indicates that the queue has not yet been generated
    var index = -1

    def firstStep(): (Seq[ZeroRule], Boolean) =
      ZeroPatterns.basicZeros(expr) match {
        // If there are basic zeros, return that and be finished
        case zs @ Seq(_, _*) => return (zs, false)
        case Nil => {
          // Make the queue all possible rules that aren't already in
          // the history, pairing each with its own solver
          queue = ZeroRules.allRules(expr)
            .filter{ r => !history.contains(r.expr2) }
            .map{ r => (r, new ZeroSolver(r.expr2, history, depth + 1)) }

          fullQueue = queue

          // Indicate that the queue has now been created
          index = 0

          // Don't return anything of interest yet
          (Nil, true)
        }
      }

    def step(): (Seq[ZeroRule], Boolean) =
      if (depth == maxDepth) (Nil, false)
      else if (index == -1) firstStep()
      else if (queue.isEmpty) (Nil, false)
      else {
        val next = queue(index)
        val stepped = next._2.step()

        // If the solver is finished, remove it from the queue
        if (!stepped._2) {
          queue = queue.take(index) ++ queue.drop(index + 1)
          index = 0
        } else {
          index = (index + 1) % queue.length
        }

        //if (stepped._1 != Nil) println(stepped._1)

        return (stepped._1.map(next._1.withSubRule), !queue.isEmpty)
      }
  }
}

object ZeroPatterns {
  import Zero._

  def basicZeros(eqn: Eqn): Seq[FinalZeroRule] =
    for ((zs, r) <- rules.allWithLabels(simplify(eqn)) ; z <- zs
      if ++(eqn.left, **(-1, eqn.right)).approx(X.symbol -> z.approx()).abs < 0.00000001
    )
    yield new FinalZeroRule(eqn, simplify(z), r.name)


  // Rules that will always result in a solution
  private val rules = new Rules[Seq[Sym]]()

  rules.+("Identity"){ EquationP(XP, noxP('a)) }{ case (a: Sym) => Seq(a) }

  rules.+("Quadratic formula:<br/>\\(x=\\frac{-b \\pm \\sqrt{b^2-4ac}}{2a}\\)"){
    EquationP(SumP(
      @?('as) @@ Repeat(AsProdP(PowP(XP, =#?(2)), Repeat(noxP())), min=1), // Any number of a*x^2
      @?('bs) @@ Repeat(AsProdP(XP, Repeat(noxP()))), // Any number of b*x
      @?('cs) @@ Repeat(noxP(), min=1) // Any number of c
    ), =?(0))
  }{ case (aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]) =>
      Seq(quadraticFormula(aS, bS, cS))
  }
  def quadraticFormula(aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]): Sym = {
    val List(a, b, c) = List(aS, bS, cS).map{ es: Seq[Sym] =>
      val realEs = es.map(_ match {
        case p: SymProd => p.exprs.filter(noX).pipe(***)
        case f if hasX(f) => SymInt(1)
        case f => f
      })
      +++(realEs).pipe(simplify)
    }
    **( ++( **(-1, b), +-{ ^(++(^(b, 2), **(-4, a, c)), 1~2) }), ^(**(2, a), -1)).pipe(simplify)
  }

  /*
   rules.+("Cubic formula"){
   SumP(
   @?('as) @@ Repeat(AsProdP(PowP(XP, =#?(3)), Repeat(noxP())), min=1), // Any number of a*x^3
   @?('bs) @@ Repeat(AsProdP(PowP(XP, =#?(2)), Repeat(noxP()))), // Any number of a*x^2
   @?('cs) @@ Repeat(AsProdP(XP, Repeat(noxP()))), // Any number of b*x
   @?('ds) @@ Repeat(noxP(), min=1) // Any number of c
   )
   }{ case (aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym], dS: Seq[Sym]) =>
   Seq(cubicFormula(aS, bS, cS, dS))
   }
   def cubicFormula(aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym], dS: Seq[Sym]): Sym = {
   val List(a, b, c, d) = List(aS, bS, cS, dS).map{ es: Seq[Sym] =>
   val realEs = es.map(_ match {
   case p: SymProd => p.exprs.filter(noX).pipe(***)
   case f if hasX(f) => SymInt(1)
   case f => f
   })
   +++(realEs).pipe(simplify)
   }
   val p = **(-1~3, b, ^(a, -1))
   val q = ++(^(p, 3), **(1~6, ++(**(b, c), **(-3, a, d)), ^(a, -2)))
   val r = **(1~3, c, ^(a, -1))
   val s = ^(++(^(q, 2), ^(++(r, **(-1, ^(p, 2))), 3)), 1~2)
   val x = ++( ^(++(q, SymPM(s)), 1~3), ^(++(q, **(-1, s)), 1~3), p)
   x
   }
   */
}

object ZeroRules {
  import Zero._

  def allRules(orig: Eqn): Seq[IntermediateZeroRule] = {
    for ((es, r) <- rules.allWithLabels(orig) ; (s, str) <- es.map{t => simplify(t._1) -> t._2} if s.isFinite)
    yield {
      new IntermediateZeroRule(orig, s.asInstanceOf[Eqn], if (str == "") r.name else str)
    }
  }

  val rules = new Rules[Seq[(Eqn, String)]]()

  //// Identities
  rules.+("Fancy identity"){ EquationP('l, 'r) }{
    case (l: Sym, r: Sym) =>
      Identity.identities(l).map{ i => SymEquation(simplify(i.full), r) ->
        f"${i.description}:<br/>\\(${i.from.toLatex} \\quad \\rightarrow \\quad ${i.to.toLatex}\\)" } ++
      Identity.identities(r).map{ i => SymEquation(l, simplify(i.full)) ->
        f"${i.description}:<br/>\\(${i.from.toLatex} \\quad \\rightarrow \\quad ${i.to.toLatex}\\)" }
  }

  //// Equation -> Expression
  rules.+("The solution to an equation is the zero of one side minus the other."){
    EquationP('l, 'r |> {(_: Sym) != SymInt(0)})
  }{ case (l: Sym, r: Sym) =>
      Seq( SymEquation(simplify(++(l, **(r, -1))), 0)  -> "")
  }

  //// Expression -> Equation
  rules.+("Subtract from both sides of the equation"){
    EquationP(SumP('es @@ __*), =?(0))
  }{ case (es: Seq[Sym]) =>
      for (i <- 0 until es.length if hasX(es(i)))
      yield SymEquation(es(i), **(-1, +++(es.take(i) ++ es.drop(i + 1)))) -> ""
  }

  rules.+("Divide from both sides of the equation"){
    EquationP(ProdP('f, 'r @@ __*), 'a)
  }{ case (a: Sym, f: Sym, r: Seq[Sym]) =>
      Seq( SymEquation( simplify(***(r)), simplify(**(a, ^(f, -1))) ) ->
        f"Divide \\(${f.toLatex}\\) from both sides of the equation"
      )
  }


  //// Inverse expressions
  rules.+("Cancel out log by using it as an exponent."){
    EquationP(LogP(hasxP('a), 'b), 'c)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(a, ^(b, c)) -> "") }

  rules.+("Get the base of a log by using a root."){
    EquationP(LogP('a, hasxP('b)), 'c)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(b, ^(a, ^(c, -1))) -> "") }

  rules.+("Cancel out a power using a root."){
    EquationP(PowP(hasxP('b), 'c), 'a)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(b, ^(a, ^(c, -1))) -> "") }

  rules.+("Cancel out an exponential using a log."){
    EquationP(PowP('b, hasxP('c)), 'a)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation('c, SymLog('a, 'b)) -> "") }

  //// Trig integrals
  rules.+("Take the inverse sine of each side"){
    EquationP(SinP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymASin(r))) -> "") }
  rules.+("Take the inverse cosine of each side"){
    EquationP(CosP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymACos(r))) -> "") }

  rules.+("Take the inverse sine of each side"){
    EquationP(SinP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymASin2(r))) -> "") }
  rules.+("Take the inverse cosine of each side"){
    EquationP(CosP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymACos2(r))) -> "") }

  rules.+("Take the inverse tangent of each side"){
    EquationP(TanP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymATan(r))) -> "") }

  rules.+("Take the sine of each side"){
    EquationP(ASinP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymSin(r))) -> "") }
  rules.+("Take the cosine of each side"){
    EquationP(ACosP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymCos(r))) -> "") }
  rules.+("Take the tangent of each side"){
    EquationP(ATanP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymTan(r))) -> "") }


  ///////////// Deal with this later

  // Divide by x until the lowest power of x is a constant
  rules.+("Factor \\(x\\) out of the equation"){
    EquationP('s @@ SumP(Repeat( AsProdP( AsPowP(XP, RatP()), __*), min=2 )), =?(0))
  }{ case s: SymSum =>
      val rule = new Rule[(Sym, SymR)]("Coefficient and power",
        AsProdP( AsPowP(XP, RatP('p)), 'c @@ __*),
        { case (c: Seq[Sym], p: SymR) => (simplify(***(c)), p) }
      )

      // Tuples of coefficient and power
      val tuples: Seq[(Sym, SymR)] = s.exprs.map(rule.first(_).get)

      // Figure out the smallest exponent of x, the power of x to divide by
      val minExpt: SymR = tuples.map(_._2).minBy(_.constant)

      if (minExpt.n == 0 || minExpt.d == 0) Nil else {
        // Subtract the min exponent from each power of x

        // Sum the newly divided powers and try to solve
        val newExprs = tuples.map{ case (c: Sym, p: SymR) => simplify(**(c, ^(X, p - minExpt))) }
        val divided = +++( newExprs )

        Seq(SymEquation(**(^(X, minExpt), divided), 0) -> {
          if (minExpt == SymInt(1)) "Factor \\(x\\) out of the equation"
          else f"Factor \\(x^{${minExpt.toLatex}}\\) out of the equation"
        })
      }
  }
}
