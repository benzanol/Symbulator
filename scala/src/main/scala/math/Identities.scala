package sympany.math

import sympany._
import sympany.math.Simplify.simplify
import sympany.Sym._
import sympany.Pattern._
import org.scalajs.dom.Node

object Identity {
  def identities(expr: Sym): Seq[(Sym, String)] = {
    val es = expr.exprs

    rules.allWithLabels(expr).map{ case (e, r) => (simplify(e), r.name) } ++ {
      for (i <- 0 until es.length ; (id, str) <- identities(es(i)))
      yield (expr.instance(es.updated(i, id):_*), str)
    }
  }

  val rules = new Rules[Sym]()

  rules.+("Double angle: \\( \\sin^2 x = \\frac{1 - \\cos(2x)}{2} \\)"){
    PowP(SinP('a), IntP('p) |> { (_:SymInt).n % 2 == 0 })
  }{ case (a: Sym, p: SymInt) => ^(**(1~2, ++(1, **(-1, SymCos(**(2, a))))), p / 2) }

  rules.+("Double angle: \\( \\cos^2 x = \\frac{1 + \\cos(2x)}{2} \\)"){
    PowP(SinP('a), IntP('p) |> { (_:SymInt).n % 2 == 0 })
  }{ case (a: Sym, p: SymInt) => ^(**(1~2, ++(1, SymCos(**(2, a)))), p / 2) }

  // Too powerful
  // rules.+("Double angle: \\( \\cos(2x) = 1 - 2 \\sin^2 x \\)"){
  //   CosP('a)
  // }{ case (a: Sym) => ++(1, **(-2, ^(SymSin(**(a, 1~2)), 2))) }

  // rules.+("Double angle: \\( \\cos(2x) = 2 \\cos^2 x - 1 \\)"){
  //   CosP('a)
  // }{ case (a: Sym) => ++(-1, **(2, ^(SymCos(**(a, 1~2)), 2))) }

  rules.+("Double angle: \\( \\cos(2x) = 1 - 2 \\sin^2 x \\)"){
    CosP(ProdP(=?(2), 'a))
  }{ case (a: Sym) => ++(1, **(-2, ^(SymSin(a), 2))) }

  rules.+("Double angle: \\( \\cos(2x) = 2 \\cos^2 x - 1 \\)"){
    CosP(ProdP(=?(2), 'a))
  }{ case (a: Sym) => ++(-1, **(2, ^(SymCos(a), 2))) }
}
