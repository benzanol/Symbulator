package sympany.math

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import Sym._
import math.Simplify.simplify
import JsUtils._

object Derivative {

  import ui.CalcSolver._
  def getDerivatives(expr: Sym): Seq[Sym] = expr match {
    case SymDerivative(sub) => sub +: getDerivatives(sub)
    case e => e.exprs.flatMap(getDerivatives)

  }

  class DerivativeRule(expr: Sym, forward: Sym, description: String) extends CalcSolution {
    private val ddx = "\\frac{d}{dx}"

    val solution = derive(expr, X.symbol)

    val rules = getDerivatives(forward).filter(_ != X).map(derivativeRule)

    def beforeNode = stringToNode(f"\\($ddx ${expr.toLatex} = ${solution.toLatex}")
    def insideNode(num: Int)(wrap: Sym => Sym) =
      stringToNode(f"${description}<br/>\\($ddx ${expr.toLatex} = ${forward.toLatex}")
  }

  def derivativeRule(expr: Sym): CalcSolution = derivativeArgs(expr) match {
    case (desc, forward) => new DerivativeRule(expr, forward, "➣ " + desc)
  }
  def derivativeArgs(expr: Sym): (String, Sym) = expr match {
		case v: SymVar if v == X => ("\\(\\frac{d}{dx} (x) = 1\\)" -> 1)
		case SymVar(a) =>
      ("Substitute the derivative of an unknown variable with respect to x" ->
        SymVar(Symbol(s"d${a.name}/dx")))
		case _: SymConstant => ("The derivative of a constant is 0" -> 0)
    case SymEquation(l, r) =>
      ("Take the derivative of both sides of the equation" ->
        SymEquation(SymDerivative(l), SymDerivative(r)))
		case e: SymSum =>
      ("The derivative of a sum is the sum of the derivatives of its addends" ->
        +++(e.exprs.map(SymDerivative(_))))
		case e: SymProd if e.exprs.length == 0 => ("The derivative of a constant is 0" -> 0)
		case e: SymProd if e.exprs.length == 1 => derivativeArgs(e.exprs.head)
		case e: SymProd =>
      ("Product rule: \\(\\frac{d}{dx} a \\cdot b = \\frac{da}{dx} b + a \\frac{db}{dx}\\)" ->
        ++( **(SymDerivative(e.exprs.head), ***(e.exprs.tail)),
          **(e.exprs.head, SymDerivative(***(e.exprs.tail))) )
      )
    case SymPow(base, expt: SymR) if base == X =>
      ("Power rule: \\(\\frac{d}{dx} x^p = p x^{p-1})" ->
        **(expt, SymDerivative(base), ^(base, expt - S(1))))
    case SymPow(base, expt: SymR) =>
      ("Power rule: \\(\\frac{d}{dx} a^p = \\frac{da}{dp} p a^{p-1})" ->
        **(expt, SymDerivative(base), ^(base, expt - S(1))))
		case SymPow(base, expt) =>
      ("Exponent rule: \\(\\frac{d}{dx} a^p = a^p \\frac{d}{dx} (p \\cdot \\ln(a))\\)" ->
        **(^(base, expt), SymDerivative(**(expt, log(base)))))
		case SymLog(u, SymE()) =>
      ("The derivative of \\(\\ln x\\) is \\(\\frac{1}{x}\\)" ->
        **(SymDerivative(u), ^(u, S(-1))))
		case SymLog(pow, base) =>
      ("Division log rule: \\(\\log_b a = \\frac{\\ln a}{\\ln b}\\)" ->
        SymDerivative(**(log(pow), ^(log(base), S(-1)))))
    case SymPM(e) =>
      ("The derivative of a plus/minus expression is plus/minus the derivative of the expression" ->
        SymPM(SymDerivative(e)))
    case SymSin(e) =>
      ("The derivative of sine is cosine" ->
        **(SymDerivative(e), SymCos(e)))
    case SymCos(e) =>
      ("The derivative of cosine is negative sine" ->
        **(SymDerivative(e), S(-1), SymSin(e)))
    case SymTan(e) =>
      ("The derivative of tangent is secant squared" ->
        **(SymDerivative(e), ^(SymCos(e), -2)))
    case SymASin(e) =>
      ("The derivative of inverse sine is \\(\\frac{1}{\\sqrt(1 - x^2)}" ->
        **(SymDerivative(e), ^(++(1, **(-1, ^(e, 2))), -1~2)))
    case SymACos(e) =>
      ("The derivative of inverse cosine is \\(-\\frac{1}{\\sqrt(1 - x^2)}" ->
        **(-1, SymDerivative(e), ^(++(1, **(-1, ^(e, 2))), -1~2)))
    case SymATan(e) =>
      ("The derivative of inverse tangent is \\(\\frac{1}{1 + x^2}" ->
        **(SymDerivative(e), ++(1, ^(e, 2))))
      //case Integral.SymIntegral(sub) =>
    case SymVertical(_) =>
      ("The derivative of a vertical line is infinite" -> SymPositiveInfinity())
	}

  @JSExportTopLevel("derive")
  def derive(expr: Sym, v: Symbol): Sym =
    simplify(
	    expr match {
		    case SymVar(a) if a == v => SymInt(1)
		    case SymVar(a) => SymVar(Symbol(s"d${a.name}/d${v.name}"))
		    case _: SymConstant => S(0)
        case SymEquation(l, r) => SymEquation(derive(l, v), derive(r, v))
		    case e: SymSum => +++(e.exprs.map(derive(_, v)))
		    case e: SymProd if e.exprs.length == 0 => S(0)
		    case e: SymProd if e.exprs.length == 1 => derive(e.exprs.head, v)
		    case e: SymProd =>
          ++( **(derive(e.exprs.head, v), ***(e.exprs.tail)),
            **(e.exprs.head, derive(***(e.exprs.tail), v)) )
        case SymPow(base, expt: SymR) =>
          **(expt, derive(base, v), ^(base, expt - S(1)))
		    case SymPow(base, expt) => **(^(base, expt), derive(**(expt, log(base)), v))
		    case SymLog(u, SymE()) => **(derive(u, v), ^(u, S(-1)))
		    case SymLog(pow, base) => derive(**(log(pow), ^(log(base), S(-1))), v)
        case SymPM(e) => SymPM(derive(e, v))
        case SymSin(e) => **(derive(e, v), SymCos(e))
        case SymCos(e) => **(derive(e, v), S(-1), SymSin(e))
        case SymTan(e) => **(derive(e, v), ^(SymCos(e), -2))
        case SymASin(e) => **(derive(e, v), ^(++(1, **(-1, ^(e, 2))), -1~2))
        case SymACos(e) => **(-1, derive(e, v), ^(++(1, **(-1, ^(e, 2))), -1~2))
        case SymATan(e) => **(derive(e, v), ++(1, ^(e, 2)))
        //case Integral.SymIntegral(sub) => sub
        case SymVertical(_) => SymPositiveInfinity()
	    }
	  )
  
}
