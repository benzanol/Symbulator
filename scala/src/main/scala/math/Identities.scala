package sympany.math

import scala.util.chaining._

import org.scalajs.dom.Node

import sympany._
import sympany.math.Simplify.simplify
import sympany.Sym._
import sympany.Pattern._

object Identity {
  case class AlgebraIdentity(full: Sym, from: Sym, to: Sym, description: String) {
    def withFull(e: Sym) = AlgebraIdentity(e, from, to, description)
  }

  def identities(expr: Sym): Seq[AlgebraIdentity] = {
    val es = expr.exprs

    rules.allWithLabels(expr).map{ case (e, r) =>
      AlgebraIdentity(simplify(e), expr, simplify(e), r.name) } ++ {
      for (i <- 0 until es.length ; id <- identities(es(i)))
      yield id.withFull(expr.instance(es.updated(i, id.full):_*))
    }
  }

  val rules = new Rules[Sym]()

  //// Mechanics
  rules.+("Expand integer power of sum"){
    PowP(SumP('s @@ __*), IntP('p) |> {(_: SymInt).toInt > 1})
  }{ case (p: SymInt, s: Seq[Sym]) =>
      (1 to p.toInt).foldLeft(Seq[Seq[Sym]](Nil)){ (acc: Seq[Seq[Sym]], _) =>
        for (es1 <- acc ; e2 <- s) yield e2 +: es1
      }.pipe{ seq: Seq[Seq[Sym]] => simplify(+++(seq.map(***))) }
  }

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
