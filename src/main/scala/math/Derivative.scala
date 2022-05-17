package sympany.math

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.symbolics._
import sympany.math.Simplify.simplify

object Derivative {

	@JSExportTopLevel("derivative")
	def derivative(expr: Sym, v: Symbol): Sym = simplify(
		expr match {
      case SymEquation(l, r) => SymEquation(derivative(l, v), derivative(r, v))
			case SymVar(a) if a == v => SymInt(1)
			case SymVar(a) => SymVar(Symbol(s"d${a.name}/d${v.name}"))
			case _: SymConstant => SymInt(0)
			case SymSum(exprs @ _*) => SymSum({ exprs.map(derivative(_, v)) }:_*)
			case SymProd(f) => derivative(f, v)
			case SymProd(e, rest @ _*) => SymSum(
				SymProd(derivative(e, v), SymProd(rest:_*)),
				SymProd(e, derivative(SymProd(rest:_*), v))
			)
			case SymPow(base, expt) => SymProd(SymPow(base, expt), derivative(SymProd(expt, SymLog(base)), v))
			case SymLog(u, SymE()) => SymProd(derivative(u, v), SymPow(u, SymInt(-1)))
			case SymLog(pow, base) => derivative(SymProd(SymLog(pow), SymPow(SymLog(base), SymInt(-1))), v)
      case SymPM(e) => SymPM(derivative(e, v))
		}
	)
}
