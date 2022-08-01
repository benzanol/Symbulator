package sympany.math

import scala.util.chaining._
import scala.collection.mutable

import sympany._
import sympany.Sym._
import sympany.math.Derivative.derive
import sympany.math.Simplify.simplify

import scala.scalajs.js.annotation.JSExportTopLevel

object IntegralHelpers {

  @JSExportTopLevel("startIntegral")
  def startIntegral(str: String): IntegralProcess = {
    return new IntegralProcess(Parse.parseLatex(str).get.replaceExpr(SymVar('x), X))
  }

  @JSExportTopLevel("stepIntegral")
  def stepIntegral(process: IntegralProcess): String = {
    try {
      process.step().toString()
    } catch {
      case e: Error => e.toString()
    }
  }

  @JSExportTopLevel("solveIntegral")
  def solveIntegral(str: String): Option[(Sym, Seq[IntegralRule.Rule])] = {

    val integral = Parse.parseLatex(str).get.replaceExpr(SymVar('x), X)
    val proc = new IntegralProcess(integral)

    while (proc.step() == Left(false)) {}
    return proc.step().toOption
  }

  @JSExportTopLevel("printIntegral")
  def printIntegral(str: String):Unit = solveIntegral(str) match {
    case None => Main.jslog("No solution!")
    case Some((sol, rules)) => Main.jslog(f"${sol} \n Deriv=${simplify(derive(sol, X.symbol))}")
  }

  @JSExportTopLevel("testSub")
  def testSub(str: String) {
    val integral = Parse.parseLatex(str).get.replaceExpr(SymVar('x), X)
    for (rule <- IntegralRule.allUsubs(integral))
      Main.jslog(f"${rule.u} : => ${rule.replaced}")

  }
}

class IntegralProcess(integral: Sym) {
  type IRule = IntegralRule.Rule

  val queue = mutable.ListBuffer[IntegralActor]()
  val integralActors = mutable.Map[Sym, IntegralActor]()
  val actor: IntegralActor = new IntegralActor(integral, Set())

  def step(): Either[Boolean, (Sym, Seq[IRule])] = {
    if (queue.isEmpty) actor.solution match {
      case Some(sol) => Right(sol, actor.history)
      case None => Left(true)

    } else {
      val next = queue.minBy(_.expr.size)
      queue -= next
      Main.jslog("Stepping: " + next.expr.toString())
      next.start()

      //for (e <- queue) Main.jslog(e.expr.toString)

      actor.solution match {
        case None => Left(queue.isEmpty)
        case Some(sol) => { queue.clear() ; Right(sol, actor.history) }
      }
    }
  }

  class IntegralActor(val expr: Sym, prevIns: Set[Sym]) {
    var solution: Option[Sym] = None
    var history: Seq[IRule] = Nil

    private var exprActors = Seq[ExprActor]()
    def start() {
      for (rule <- IntegralRule.allRules(expr)) {
        Main.jslog("new expr: " + expr.toString + " : " + rule.toString())
        exprActors +:= new ExprActor(rule.forward, this, rule, prevIns + expr)

        // If the previous ExprActor provided a solution to the
        // integral, no need to go on creating new ones
        if (this.solution.isDefined) {
          //Main.jslog("No new exprs needed!")
          return
        }
      }
    }

    def solve(sol: Sym, hist: Seq[IRule]) {
      //Main.jslog(f"Solved integral $expr as $sol")

      this.history = hist
      this.solution = Some(sol)

      for (exprActor <- references)
        exprActor.solveIntegral(expr, sol, hist)

      this.cancel()
    }

    private var references: Seq[ExprActor] = Nil
    def addReference(ea: ExprActor) {
      references +:= ea

      // If the solution was already found, relay this to the expression
      for (sol <- solution)
        ea.solveIntegral(expr, sol, history)
    }
    def removeReference(ea: ExprActor) {
      references = references.filter(_ != ea)

      // If this integral is no longer required by any expressions
      if (references.isEmpty && this.solution.isEmpty)
        this.cancel()
    }

    private def cancel() {
      queue -= this
      integralActors.remove(expr)
      exprActors.foreach(_.cancel)
    }


    // Check if the integral is easy to solve
    IntegralPatterns.basicSolve(expr) match {
      case Some(sol) => this.solve(sol, Nil)

      // If it isn't easy to solve, add it to the queue and map
      case None => {
        queue += this
        integralActors(expr) = this
      }
    }
  }

  class ExprActor(orig: Sym, parent: IntegralActor, rule: IRule, prevIns: Set[Sym]) {
    private var current = orig
    private var history = Seq(rule)

    private def replace(in: Sym, sol: Sym) {
      //Main.jslog("Replace: " + in.toString() + " --> " + sol.toString())
      //Main.jslog("Before: " + this.current.toString())
      this.current = simplify(this.current.replaceExpr(SymIntegral(in), sol))
      //Main.jslog("After: " + this.current.toString())
    }
    def solveIntegral(in: Sym, sol: Sym, hist: Seq[IRule]) {
      this.replace(in, sol)
      this.history ++= hist
      this.queueNext()
    }

    // Find the first non-nested integral in an expression, and return
    // the integral's sub expression
    private var workingIntegral: Option[IntegralActor] = None

    private def nextIntegral(expr: Sym): Option[Sym] = {
      def containsIntegral(e: Sym): Boolean = e match {
        case SymIntegral(_) => true
        case _ => e.exprs.find(containsIntegral).isDefined
      }

      expr match {
        case SymIntegral(in) if !containsIntegral(in) => Some(in)
        case a => a.exprs.flatMap(nextIntegral).headOption
      }
    }
    def queueNext(): Unit = nextIntegral(current) match {
      // If there are no new integrals, the expression is solved
      case None => this.parent.solve(
        simplify(this.rule.backward(this.current)),
        this.history
      )

      // If the next integral was a previous integral, this
      // ExprActor needs to be cancelled to avoid an infinite loop
      case Some(in) if prevIns.contains(in) => this.cancel()

      // Get the existing IntegralActor, or create a new one, and
      // set this ExprActor as a reference
      case Some(in) => {
        val actor = integralActors.get(in) match {
          case Some(existing) => existing
          case None => new IntegralActor(in, prevIns)
        }

        actor.addReference(this)
        this.workingIntegral = Some(actor)
      }
    }

    def cancel() {
      for (actor <- this.workingIntegral)
        actor.removeReference(this)
    }

    queueNext()
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

object IntegralRule {
  def allRules(expr: Sym): Seq[Rule] = expr match {
    case sum: SymSum => Seq(new SumRule(expr))
    case prod: SymProd if prod.exprs.find(Pattern.noX).isDefined =>
      Seq(new ProductRule(expr))
    case _ => allParts(expr) ++ allUsubs(expr)
  }

  def allParts(expr: Sym): Seq[Rule] = {
    val exprSet = simplify(expr) match {
      case prod: SymProd => prod.exprs.toSet
      case other => Set(other)
    }

    exprSet
      .subsets
      .filter(_.nonEmpty)
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

  class ProductRule(orig: Sym) extends Rule(orig) {
    override def toString = f"ProductRule"
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
    override def toString = f"SumRule"
    def forward: Sym = orig match {
      case sum: SymSum => simplify(+++(sum.exprs.map(SymIntegral(_))))
      case _ => SymIntegral(orig)
    }

    def backward(sol: Sym): Sym = sol
  }

  class Parts(orig: Sym, val u: Sym, val dv: Sym) extends Rule(orig) {
    override def toString = f"Parts u=$u  dv=$dv  =>  ${this.forward}"
    val v = SymIntegral(dv)
    val du = derive(u, X.symbol)

    lazy val forward: Sym = simplify(++( **(u, v), **(-1, SymIntegral(**(du, v)))))
    def backward(sol: Sym): Sym = sol
  }

  class USub(orig: Sym, val u: Sym, val replaced: Sym) extends Rule(orig) {
    override def toString = f"USub x -> $u  =>  ${replaced}"
    lazy val forward = SymIntegral(replaced)
    def backward(sol: Sym): Sym = sol.replaceExpr(X, u)
  }

  // Return Some(replaced) if the usub succeeds, otherwise None
  def tryUsub(expr: Sym, u: Sym): Option[Sym] = {
    if (u.size == 1) return None

    val du = math.Derivative.derive(u, X.symbol)
    val replaced = **(expr.replaceExpr(u, SymVar('U)), ^(du, -1)).pipe(simplify)

    def containsOtherVars(e: Sym): Boolean = e match {
      case SymVar('U) => false
      case SymVar(_) => true
      case _ => e.exprs.find(containsOtherVars).isDefined
    }

    Option.unless(containsOtherVars(replaced)) {
      replaced.replaceExpr(SymVar('U), X)
    }
  }

}
