package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import sympany._
import sympany.Sym._
import sympany.math.Derivative.derive
import sympany.math.Simplify.simplify

import scala.scalajs.js.annotation.JSExportTopLevel

object Integral {

  class IntegralSolver(val expr: Sym) {
    private var index = 0
    private var (
      solution: Option[Option[IntegralRule]],
      rules: Seq[(IntegralRule, Option[IntegralSolver])]
    ) = IntegralPatterns.basicSolve(expr) match {
      case Some(sol) => (Some(Some(sol)), Nil)
      case None => (None, IntegralRules.allRules(expr).map(_ -> None))
    }

    //println("Integral: " + expr.toString)
    //if (solution.isDefined) println("  Solution: " + solution.get.get.toString)
    //else for (r <- rules) println("  Rule: " + r._1.toString + "\n  Now: " + r._1.forward.toString)

    def step(): Option[Option[IntegralRule]] = {
      if (solution.isDefined) {}
      else if (rules.isEmpty) solution = Some(None)
      // Progress the current rule as determined by `index`
      else rules(index) match {

        // If there is an active solver for the current rule, step it
        case (r, Some(solver)) => solver.step() match {
          case None => index = (index + 1) % rules.length
          // If the current integral for that rule is unsolvable, // eliminate the rule
          case Some(None) => {
            rules = rules.take(index) ++ rules.drop(index + 1)
            index = 0
          }
          case Some(Some(sol)) => {
            r.solveNext(sol)
            rules = rules.updated(index, r -> None)
          }
        }

        // If there is no active solver, figure out if there are remaining integrals
        case (r, None) => r.nextIntegral(r.expression) match {
          // If there is another integral, create a new solver for it
          case Some(next) => rules = rules.updated(index, r -> Some(new IntegralSolver(next)))
          // If there are no new integrals, the expression is solved
          case None => solution = Some(Some(r))
        }
      }
      solution
    }
  }

  abstract class IntegralRule(val integral: Sym) {
    // Return an expression containing integrals, which when solved,
    // can be sent to `backward` to get the integral of `in`
    def forward: Sym
    var expression: Sym = forward

    // Turn the solved expression into the solution to `integral`
    def backward(sol: Sym): Sym
    def solution = backward(expression)

    // List of rules for solving the sub integrals of this expression
    protected var rules = Seq[IntegralRule]()
    //def subRules: Seq[IntegralRule] = if (rules.isEmpty) Nil else rules.init
    //def afterRules: Seq[IntegralRule] = if (rules.isEmpty) Nil else Seq(rules.last)
    def subRules: Seq[IntegralRule] = rules
    def afterRules: Seq[IntegralRule] = Nil

    // Functions to gradually turn `expression` into a solution
    def nextIntegral(e: Sym): Option[Sym] = {
      def containsIntegral(e: Sym): Boolean = e match {
        case SymIntegral(_) => true
        case _ => e.exprs.find(containsIntegral).isDefined
      }

      e match {
        case SymIntegral(in) if !containsIntegral(in) => Some(in)
        case a => a.exprs.flatMap(nextIntegral).headOption
      }
    }

    def solveNext(r: IntegralRule) {
      expression = expression.replaceExpr(
        SymIntegral(nextIntegral(expression).get),
        r.solution
      )
      rules :+= r
    }
  }

}

object IntegralPatterns {
  class BasicIRule(integral: Sym, known: Sym) extends Integral.IntegralRule(integral) {
    override def toString = f"Known integral"
    def forward = known
    def backward(sol: Sym) = sol
  }

  def basicSolve(expr: Sym): Option[BasicIRule] =
    iRules.first(expr).map{sol => new BasicIRule(expr, simplify(sol)) }
  
  import Pattern._

  val iRules = new Rules()

  iRules.+("Constant"){ noxP('c) }{ case (c: Sym) => **(c, X) }

  iRules.+("a * x^p"){
    AsPowP(XP, noxP('p))
  }{ case (p: Sym) => **(^(++(p, 1), -1), ^(X, ++(p, 1))) }

  iRules.+("a * sin x"){
    =?(SymSin(X))
  }{ case () => **(-1.s, SymCos(X)) }

  iRules.+("a * cos x"){
    =?(SymCos(X))
  }{ case () => SymSin(X) }

}

object IntegralRules {
  import Integral.IntegralRule

  def allRules(expr: Sym): Seq[IntegralRule] = expr match {
    case sum: SymSum => Seq(new SumRule(expr))
    case prod: SymProd if prod.exprs.find(Pattern.noX).isDefined =>
      Seq(new ProductRule(expr))
    case _ => {
      val usubs = allUsubs(expr)
      if (usubs.isEmpty) allParts(expr)
      else usubs
    }
  }

  // This does NOT include the strategy of making x appear out of
  // nowhere, as that adds a lot of unnecessary computation
  def allParts(expr: Sym): Seq[IntegralRule] = {
    val exprSet = simplify(expr) match {
      case prod: SymProd => prod.exprs.toSet
      case other => Set(other)
    }

    exprSet.subsets
      .filter(_.nonEmpty)
      .filter(_.size < exprSet.size)
      .map{us =>
        val u = simplify(***(us.toList))
        val dv = simplify(***((exprSet diff us).toList))
        new Parts(expr, u, dv)
      }.toSeq
  }

  def allUsubs(expr: Sym): Seq[USub] =
    expr.exprs.flatMap(getUsubs(expr, _))

  def getUsubs(expr: Sym, sub: Sym): Seq[USub] =
    sub.exprs.flatMap(getUsubs(expr, _)) .++(
      tryUsub(expr, sub).map(new USub(expr, sub, _)).toSeq
    )


  class ProductRule(integral: Sym) extends IntegralRule(integral) {
    override def toString = f"Separate Constant Factors"

    def forward: Sym = simplify(integral) match {
      case prod: SymProd => {
        val consts = prod.exprs.filter(Pattern.noX)
        val exprs = prod.exprs.filter(Pattern.hasX)
        simplify(***(consts :+ SymIntegral(***(exprs))))
      }
      case _ => SymIntegral(integral)
    }
    def backward(sol: Sym): Sym = sol

    override def subRules = rules
    override def afterRules = Nil
  }

  class SumRule(integral: Sym) extends IntegralRule(integral) {
    override def toString = f"Integral of a sum is a sum of integrals"

    def forward: Sym = integral match {
      case sum: SymSum => simplify(+++(sum.exprs.map(SymIntegral(_))))
      case _ => SymIntegral(integral)
    }
    def backward(sol: Sym): Sym = sol

    override def subRules = rules
    override def afterRules = Nil
  }

  class Parts(integral: Sym, val u: Sym, val dv: Sym) extends IntegralRule(integral) {
    override def toString = f"Integration by Parts u=$u dv=$dv"
    def v = SymIntegral(dv)
    def du = derive(u, X.symbol)

    def forward: Sym = simplify(++( **(u, v), **(-1, SymIntegral(**(du, v)))))
    def backward(sol: Sym): Sym = sol
  }

  class USub(integral: Sym, val u: Sym, val replaced: Sym) extends IntegralRule(integral) {
    override def toString = f"USub: u=$u"

    def forward = SymIntegral(replaced)
    def backward(sol: Sym): Sym = sol.replaceExpr(X, u)
  }

  // Return Some(replaced) if the usub succeeds, otherwise None
  def tryUsub(expr: Sym, u: Sym): Option[Sym] = {
    if (u.size == 1) return None

    val du = math.Derivative.derive(u, X.symbol)
    val divideDu = simplify(**(expr, ^(du, -1)))
    val replaced = divideDu.replaceExpr(u, SymVar('U))

    Option.unless(containsExpr(replaced, X)) {
      replaced.replaceExpr(SymVar('U), X)
    }
  }

}
