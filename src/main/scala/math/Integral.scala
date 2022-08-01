package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import sympany._
import sympany.Sym._
import sympany.math.Derivative.derive
import sympany.math.Simplify.simplify

import scala.scalajs.js.annotation.JSExportTopLevel

object IntegralSolver {
  type IRule = IntegralRules.Rule
  type ISol = IntegralSolution
  case class IntegralSolution(expr: Sym, history: Seq[IRule])

  class IntegralActor(val expr: Sym) {
    private var solution: Option[ISol] =
      IntegralPatterns.basicSolve(expr).map{sol =>
        IntegralSolution(sol, Seq(new IntegralRules.Known(expr, sol)))
      }

    private var index = 0
    private val exprActors: Seq[ExprActor] =
      if (solution.isDefined) Nil
      else IntegralRules.allRules(expr).map(new ExprActor(_))

    def step(): Option[ISol] = {
      if (solution.isEmpty) {
        val next = exprActors(index)
        index = (index + 1) % exprActors.length
        solution = next.step()
      }
      solution
    }
  }

  class ExprActor(rule: IRule) {
    private var expr = rule.forward
    private var history = Seq(rule)

    private var current: Option[IntegralActor] = None

    def step(): Option[ISol] = current match {
      case None => nextIntegral(expr) match {
        case None => Some(IntegralSolution(rule.backward(expr), history))
        case Some(next) => current = Some(new IntegralActor(next)) ; None
      }
      case Some(cur) => cur.step() match {
        case None => None
        case Some(IntegralSolution(sol, hist)) => {
          expr = simplify(expr.replaceExpr(SymIntegral(cur.expr), sol))
          history ++= hist
          current = None
          None
        }
      }
    }

    private def nextIntegral(e: Sym): Option[Sym] = {
      def containsIntegral(e: Sym): Boolean = e match {
        case SymIntegral(_) => true
        case _ => e.exprs.find(containsIntegral).isDefined
      }

      e match {
        case SymIntegral(in) if !containsIntegral(in) => Some(in)
        case a => a.exprs.flatMap(nextIntegral).headOption
      }
    }
  }

}

object IntegralHelpers {
  import IntegralSolver._

  @JSExportTopLevel("startIntegral")
  def startIntegral(str: String): IntegralActor = {
    return new IntegralActor(Parse.parseLatex(str).get.replaceExpr(SymVar('x), X))
  }

  @JSExportTopLevel("stepIntegral")
  def stepIntegral(process: IntegralActor): String = {
    try {
      process.step().toString()
    } catch {
      case e: Error => e.toString()
    }
  }

  @JSExportTopLevel("solveIntegral")
  def solveIntegral(str: String): Option[IntegralSolution] = {

    val integral = Parse.parseLatex(str).get.replaceExpr(SymVar('x), X)
    val proc = new IntegralActor(integral)

    while (proc.step().isEmpty) {}
    return proc.step()
  }

  @JSExportTopLevel("printIntegral")
  def printIntegral(str: String): Unit = solveIntegral(str) match {
    case None => Main.jslog("No solution!")
    case Some(IntegralSolution(sol, rules)) =>
      Main.jslog(f"${sol} \n Deriv=${simplify(derive(sol, X.symbol))}")
      for (r <- rules) Main.jslog(r.toString())
  }

  @JSExportTopLevel("testSub")
  def testSub(str: String) {
    val integral = Parse.parseLatex(str).get.replaceExpr(SymVar('x), X)
    for (rule <- IntegralRules.allUsubs(integral))
      Main.jslog(f"${rule.u} : => ${rule.replaced}")

  }
}

object IntegralPatterns {
  import Pattern._

  def basicSolve(expr: Sym): Option[Sym] =
    iRules.first(expr).map(simplify)

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
  def allRules(expr: Sym): Seq[Rule] = expr match {
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
  def allParts(expr: Sym): Seq[Rule] = {
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


  abstract class Rule(val orig: Sym) {
    def forward: Sym
    def backward(sol: Sym): Sym
  }

  class Known(orig: Sym, val known: Sym) extends Rule(orig) {
    override def toString = f"Known: Integral($orig) = $known"
    def forward = known
    def backward(sol: Sym) = sol
  }

  class ProductRule(orig: Sym) extends Rule(orig) {
    override def toString = f"Separate Constant Factors: $orig"
    def forward: Sym = orig match {
      case prod: SymProd => {
        val consts = orig.exprs.filter(Pattern.noX)
        val exprs = orig.exprs.filter(Pattern.hasX)
        simplify(***(consts :+ SymIntegral(***(exprs))))
      }
      case _ => SymIntegral(orig)
    }

    def backward(sol: Sym): Sym = sol
  }

  class SumRule(orig: Sym) extends Rule(orig) {
    override def toString = f"Split up Sum: $orig"
    def forward: Sym = orig match {
      case sum: SymSum => simplify(+++(sum.exprs.map(SymIntegral(_))))
      case _ => SymIntegral(orig)
    }

    def backward(sol: Sym): Sym = sol
  }

  class Parts(orig: Sym, val u: Sym, val dv: Sym) extends Rule(orig) {
    override def toString = f"Parts u=$u dv=$dv  =>  $orig -> ${this.forward}"
    val v = SymIntegral(dv)
    val du = derive(u, X.symbol)

    lazy val forward: Sym = simplify(++( **(u, v), **(-1, SymIntegral(**(du, v)))))
    def backward(sol: Sym): Sym = sol
  }

  class USub(orig: Sym, val u: Sym, val replaced: Sym) extends Rule(orig) {
    override def toString = f"USub: u=$u  =>  $orig -> ${replaced}"
    lazy val forward = SymIntegral(replaced)
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
