package sympany.math

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.Sym._
import sympany.math.Simplify.simplify

object Derivative {
  
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
        //case Integral.SymIntegral(sub) => sub
        case SymVertical(_) => SymPositiveInfinity()
	  }
	)
  
}
