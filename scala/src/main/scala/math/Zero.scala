package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import sympany._
import sympany.math.Simplify.simplify
import sympany.Sym._
import sympany.Pattern._
import org.scalajs.dom.Node


object Zero {
  import ui.CalcSolver.CalcSolution
  import JsUtils._

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

  class FinalZeroRule(expr: Eqn, zero: Sym, description: String) extends ZeroRule {
    def ruleDescription = f"$description<br/>\\(x = ${zero.toLatex}\\)"
    def endResult = Some(zero)
    def rules = Nil
  }

  class IntermediateZeroRule(val expr1: Eqn, val expr2: Eqn, val description: String) extends ZeroRule {
    def ruleDescription = f"$description<br/>\\(${expr1.toLatex} \\rightarrow ${expr2.toLatex}\\)"
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

  class ZeroSolver(val expr: Eqn, history: mutable.Set[Eqn] = mutable.Set[Eqn]()) {
    // Add the expression and its opposite to the history so they are never referenced again
    history.addAll(Seq(expr, oppositeExpression(expr)))

    // List of child solvers and the rules they go with
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
            .map{ r => (r, new ZeroSolver(r.expr2, history)) }

          // Indicate that the queue has now been created
          index = 0

          // Don't return anything of interest yet
          (Nil, true)
        }
      }

    def step(): (Seq[ZeroRule], Boolean) =
      if (index == -1) firstStep()
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

        return (stepped._1.map(next._1.withSubRule), !queue.isEmpty)
      }
  }
}

object ZeroPatterns {
  import Zero._

  def basicZeros(eqn: Eqn): Seq[FinalZeroRule] =
    for ((zs, r) <- rules.allWithLabels(simplify(eqn)) ; z <- zs)
    yield new FinalZeroRule(eqn, simplify(z), r.name)


  // Rules that will always result in a solution
  private val rules = new Rules[Seq[Sym]]()

  rules.+("Identity"){ EquationP(XP, noxP('a)) }{ case (a: Sym) => Seq(a) }

  rules.+("When \\(x^p = 0\\), \\(x = 0\\) unless \\(p = 0\\)"){
    EquationP(AsPowP(XP, noxP('p)), =?(0))
  }{ case (p: Sym) => if (p == SymInt(0)) Nil else Seq(0) }

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
    for ((es, r) <- rules.allWithLabels(orig) ; s <- es.map(simplify) if s.isFinite)
    yield {
      new IntermediateZeroRule(orig, s.asInstanceOf[Eqn], r.name)
    }
  }

  val rules = new Rules[Seq[Eqn]]()

  //// Equation -> Expression
  rules.+("The solution to an equation is the zero of one side minus the other."){
    EquationP('l, 'r |> {(_: Sym) != SymInt(0)})
  }{ case (l: Sym, r: Sym) =>
      Seq( SymEquation(simplify(++(l, **(r, -1))), 0) )
  }

  //// Expression -> Equation
  rules.+("Subtract from both sides of the equation"){
    EquationP(SumP('es @@ __*), =?(0))
  }{ case (es: Seq[Sym]) =>
      for (i <- 0 until es.length if hasX(es(i)))
      yield SymEquation(es(i), **(-1, +++(es.take(i) ++ es.drop(i + 1))))
  }

  rules.+("Divide from both sides of the equation."){
    EquationP('p @@ ProdP(__*), 'a)
  }{ case (a: Sym, p: SymProd) =>
      p.exprs.map{ f => SymEquation( simplify(**(p, ^(f, -1))), simplify(**(a, ^(f, -1))) ) }
  }


  //// Inverse expressions
  rules.+("Cancel out log by using it as an exponent."){
    EquationP(LogP(hasxP('a), 'b), 'c)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(a, ^(b, c))) }

  rules.+("Get the base of a log by using a root."){
    EquationP(LogP('a, hasxP('b)), 'c)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(b, ^(a, ^(c, -1)))) }

  rules.+("Cancel out a power using a root."){
    EquationP(PowP(hasxP('b), 'c), 'a)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation(b, ^(a, ^(c, -1)))) }

  rules.+("Cancel out an exponential using a log."){
    EquationP(PowP('b, hasxP('c)), 'a)
  }{ case (a: Sym, b: Sym, c: Sym) => Seq(SymEquation('c, SymLog('a, 'b))) }

  //// Trig integrals
  rules.+("Use ASin to cancel out of Sin"){
    EquationP(SinP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymASin(r)))) }
  rules.+("Use ACos to cancel out of Cos"){
    EquationP(CosP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymACos(r)))) }
  rules.+("Use ATan to cancel out of Tan"){
    EquationP(TanP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymATan(r)))) }
  rules.+("Use Sin to cancel out of ASin"){
    EquationP(ASinP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymSin (r)))) }
  rules.+("Use Cos to cancel out of ACos"){
    EquationP(ACosP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymCos (r)))) }
  rules.+("Use Tan to cancel out of ATan"){
    EquationP(ATanP('a), 'r)
  }{ case (a: Sym, r: Sym) => Seq(SymEquation(a, simplify(SymTan (r)))) }


  ///////////// Deal with this later

  // Divide by x until the lowest power of x is a constant
  rules.+("x^3 + x^2 = x^2(x + 1)"){
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

        if (minExpt < 0) Seq(SymEquation(divided, 0))
        else Seq(SymEquation(X, 0), SymEquation(divided, 0))
      }
  }
}
