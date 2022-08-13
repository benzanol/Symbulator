package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import scala.scalajs.js.annotation.JSExportTopLevel
import scala.scalajs.js

import sympany._
import sympany.math.Simplify.simplify
import sympany.math.Derivative.derive
import sympany.Sym._
import sympany.Pattern._
import org.scalajs.dom.Node



object Zero {
  import ui.CalcSolver.CalcSolution
  import JsUtils._

  trait ZeroRule extends CalcSolution {
    def beforeNode: Node = endResult match {
      case None => stringToNode("Unsolved root")
      case Some(z) => stringToNode(f"\\(x = ${z.toLatex}\\)<br/>")
    }

    def endResult: Option[Sym]


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

  class FinalZeroRule(expr: Sym, zero: Sym, description: String) extends ZeroRule {
    def ruleDescription = f"$description<br/>\\(x = ${zero.toLatex}\\)"
    def endResult = Some(zero)
    def rules = Nil
  }

  class IntermediateZeroRule(val expr1: Sym, val expr2: Sym, val description: String) extends ZeroRule {
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

  def oppositeExpression(e: Sym): Sym = e match {
    case SymEquation(l, r) => SymEquation(r, l)
    case e => simplify(**(-1, e))
  }

  class ZeroSolver(val expr: Sym, history: mutable.Set[Sym] = mutable.Set[Sym]()) {
    history.addAll(Seq(expr, oppositeExpression(expr)))

    var zeros: Seq[ZeroRule] =
      ZeroPatterns.basicZeros(expr)
        .map{ case (z: Sym, d: String) => new FinalZeroRule(expr, z, d) }

    var queue: Seq[(IntermediateZeroRule, ZeroSolver)] = Nil

    // Index as -1 indicates that the queue has not yet been generated
    var index = -1

    def step(): (Seq[ZeroRule], Boolean) =
      if (queue.isEmpty && (index != -1 || !zeros.isEmpty)) (zeros, false)
      else if (index == -1) {
        // Make the queue all possible rules that aren't already in
        // the history, pairing each with its own solver

        queue = ZeroRules.allRules(expr)
          .filter{ r => !history.contains(r.expr2) }
          .map{ r => (r, new ZeroSolver(r.expr2, history)) }

        // Add the new rules to the history
        history.addAll(queue.map(_._1.expr2))

        // Add negatives/reverses to prevent duplicate rules
        history.addAll(queue.map(_._1.expr2).map(oppositeExpression))

        // Indicate that the queue has now been created
        index = 0

        // Don't return anything of interest yet
        (Nil, true)

      } else {
        val next = queue(index)
        val stepped = next._2.step()

        // Add the zeros from the nested function to my zeros
        zeros ++= stepped._1

        // If the solver is finished, remove it from the queue
        if (!stepped._2) {
          queue = queue.take(index) ++ queue.drop(index + 1)
          index = 0
        }

        return (stepped._1.map(next._1.withSubRule), !queue.isEmpty)
      }
  }
}

object ZeroPatterns {
  def basicZeros(e: Sym): Seq[(Sym, String)] = (e match {
    case SymEquation(l, r) if l == X && noX(r) => Seq(r -> "Identity")
    case SymEquation(l, r) => zRules.allWithLabels(simplify(++(l, **(-1, r))))
    case e => zRules.allWithLabels(simplify(e))
  }).filter(_._1.isFinite)

  // Rules that will always result in a solution
  val zRules = new SeqRules()

  zRules.+("When \\(x^p = 0\\), \\(x = 0\\) unless \\(p = 0\\)"){
    AsPowP(XP, noxP('p))
  }{ case (p: Sym) => if (p == SymInt(0)) Nil else Seq(0) }

  zRules.+("Quadratic formula:<br/>\\(x=\\frac{-b \\pm \\sqrt{b^2-4ac}}{2a}\\)"){
    SumP(
      @?('as) @@ Repeat(AsProdP(PowP(XP, =#?(2)), Repeat(noxP())), min=1), // Any number of a*x^2
      @?('bs) @@ Repeat(AsProdP(XP, Repeat(noxP()))), // Any number of b*x
      @?('cs) @@ Repeat(noxP(), min=1) // Any number of c
    )
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
   zRules.+("Cubic formula"){
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

  def allRules(e: Sym): Seq[IntermediateZeroRule] = {
    val out = rules.allWithLabels(e)
    //println(f"IN = $e \nOUT=$out")
    return out.map{ case (z, str) =>
      new IntermediateZeroRule(e, simplify(z), str)
    }
  }

  val rules = new SeqRules()

  //// Equation -> Expression
  rules.+("The solution to an equation is the zero of one side minus the other."){
    EquationP(@?('l), @?('r))
  }{ case (l: Sym, r: Sym) =>
      Seq( simplify(++(l, **(r, -1))) )
  }

  //// Expression -> Equation
  rules.+("Subtract addends from both sides of an equation"){
    SumP('es @@ __*)
  }{ case (es: Seq[Sym]) =>
      for (i <- 0 until es.length if hasX(es(i)))
      yield SymEquation(es(i), **(-1, +++(es.take(i) ++ es.drop(i + 1))))
  }


  //// Control rules
  rules.+("Zero of a product is the zeros of the factors."){
    ProdP('es @@ __*) }{ case es: Seq[Sym] => es }

  rules.+("Plus Minus"){ PMP(@?('e)) }{ case e: Sym => Seq(e, **(-1, e)) }


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



  ///////////// Deal with this later
  rules.+("If log x = 0, x = 1"){
    LogP(@?('a) @@ hasxP(), __)
  }{ case a: Sym => Seq( ++(a, S(-1)) ) }

  // Good luck trying to understand this mess lol
  rules.+("ax^p + b => x +- (-b/a)^(1/p)"){
    AsSumP(AsProdP(AsPowP(XP, @?('p) @@ noxP()), @?('a) @@ Repeat(noxP())), @?('rest) @@ Repeat(noxP()))
  }{ case (a: Seq[Sym], SymInt(n), r: Seq[Sym]) if (n % 2 == 0) =>
      Seq(+-(^(**(S(-1), +++(r), if (a.isEmpty) S(1) else ^(+++(a), S(-1))), S(1, n))))
    case (a: Seq[Sym], p: Sym, r: Seq[Sym]) =>
      Seq(^(**(S(-1), +++(r), if (a.isEmpty) S(1) else ^(+++(a), S(-1))), ^(p, S(-1))))
  }

  // Divide by x until the lowest power of x is a constant
  rules.+("x^3 + x^2 = x^2(x + 1)"){
    's @@ SumP(Repeat( AsProdP( AsPowP(XP, RatP()), __*), min=2 ), Repeat(noxP()))
  }{ case s: SymSum =>
      // Figure out the smallest exponent of x, the power of x to divide by
      val minExpt: SymR = s.exprs.map{ e =>
        AsProdP( AsPowP(XP, 'p), __*).matches(e)
          .headOption.map(_.apply('p).asInstanceOf[SymR])
          .getOrElse(SymR(0))
      }.foldLeft(SymPositiveInfinity(): SymR)(_ min _)

      if (minExpt.n != 0 && minExpt.d != 0) {
        // Subtract the min exponent from each power of x
        val rule = new Rule("", AsProdP( AsPowP(XP, 'p @@ RatP()), 'r @@ __*), {
          case (p: Sym, r: Seq[Sym]) =>
            ***( ^(X, ++(p, minExpt.negative)) +: r ).pipe(simplify)
        })

        // Sum the newly divided powers and try to solve
        val divided = +++( s.exprs.map{ e => rule.first(e).getOrElse{ **(e, ^(X, minExpt.negative)) } } )

        if (minExpt < 0) Seq(divided)
        else Seq(X, divided)

        // Don't bother if the smallest power is already 0 or undefined
      } else Nil
  }
}


