package sympany.math

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math.Simplify.simplify

object Derivative {
  
  @JSExportTopLevel("derive")
  def derive(expr: Sym, v: Symbol): Sym =
    simplify(
	  expr match {
		case SymVar(a) if a == v => SymInt(1)
		case SymVar(a) => SymVar(Symbol(s"d${a.name}/d${v.name}"))
		case _: SymConstant => SymInt(0)
        case SymEquation(l, r) => SymEquation(derive(l, v), derive(r, v))
		case SymSum(exprs @ _*) => SymSum({ exprs.map(derive(_, v)) }:_*)
		case SymProd(f) => derive(f, v)
		case SymProd(e, rest @ _*) => SymSum(
		  SymProd(derive(e, v), SymProd(rest:_*)),
		  SymProd(e, derive(SymProd(rest:_*), v))
		)
        case SymPow(base, expt: SymR) =>
          SymProd(expt, derive(base, v), SymPow(base, expt - SymInt(1)))
        case SymPow(base, expt) if sympany.Pattern.noX(expt) =>
          SymProd(derive(base, v), SymPow(base, SymSum(expt, SymInt(-1))))
		case SymPow(base, expt) => SymProd(SymPow(base, expt), derive(SymProd(expt, SymLog(base)), v))
		case SymLog(u, SymE()) => SymProd(derive(u, v), SymPow(u, SymInt(-1)))
		case SymLog(pow, base) => derive(SymProd(SymLog(pow), SymPow(SymLog(base), SymInt(-1))), v)
        case SymPM(e) => SymPM(derive(e, v))
        case SymSin(e) => SymProd(derive(e, v), SymCos(e))
        case SymCos(e) => SymProd(derive(e, v), SymInt(-1), SymSin(e))
	  }
	)
  
}
