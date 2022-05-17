package sympany.math

import scala.util.chaining._

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.symbolics._
import sympany.symbolics.Sym._
import sympany.patterns._
import sympany.patterns.Pattern._

object Simplify {
  val sRules = new Rules()
  
  @JSExportTopLevel("simplify")
  def simplify(expr: Sym): Sym =
    expr.mapExprs(simplify).pipe{e =>
      LazyList(sRules(e):_*)
        .flatMap(_.first(e))
        .headOption match {
          case Some(simpler) => simplify(simpler)
          case None => e
        }
    }
  
  def separateRoot(base: SymInt, root: SymInt): (SymInt, SymInt) =
    ( base.primeFactors.toList.foldLeft(#=(1)){ (a, t) => a * (t._1 ^ SymInt(t._2.n / root.n)) },
      base.primeFactors.toList.foldLeft(#=(1)){ (a, t) => a * (t._1 ^ SymInt(t._2.n % root.n)) }
    )
  
  sRules.+(SymPow())("x^0 = 1"){
    PowP(__, =#?(0))
  }{ case () => #=(1) }
  
  sRules.+(SymPow())("x^1 = x"){
    PowP(@?('b), =#?(1))
  }{ case b: Sym => b }
  
  sRules.+(SymPow())("0^x = 0"){
    PowP(=#?(0), __)
  }{ case () => #=(0) }
  
  sRules.+(SymPow())("1^x = 1"){
    PowP(=#?(1), __)
  }{ case () => #=(1) }
  
  // Roots - simplifies if greatest power of a prime factor is >= the root
  sRules.+(SymPow())("Factor powers out of roots"){
    @?('whole) @@ PowP(RatP(@?('n), @?('d)), FracP(=#?(1), @?('root)))
  }{ case (d: SymInt, n: SymInt, root: SymInt, whole: Sym) =>
      List(n, d).map(separateRoot(_, root)) match {
        case List((on, in), (od, id)) =>
          if (on == #=(1) && od == #=(1)) whole
          else **(on~od, ^((SymR(n.n.abs, d.n.abs) / (n~d)) * in~id, #=(1)~root))
      }
  }
  
  // (n/d) ^ (p/root) = (n^p)/(d^p) ^ (1/root)
  sRules.+(SymPow())("Simplify rational powers of rational bases"){
    PowP(RatP(@?('n), @?('d)), RatP(@?('p) |> { (_:SymInt) != #=(1) }, @?('root)))
  }{ case (d: SymInt, n: SymInt, p: SymInt, root: SymInt) =>
      if (p.n > 0) ^((n ^ p) / (d ^ p), #=(1)~root)
      else ^((d ^ (#=(0) - p)) / (n ^ (#=(0) - p)), #=(1)~root)
  }
  
  // (a^p1)^p2 = a^(p1*p2)
  sRules.+(SymPow())("Nested powers multiply"){
    PowP(PowP(@?('base), @?('p1)), @?('p2))
  }{ case (b: Sym, p1: Sym, p2: Sym) =>
      ^(b, **(p1, p2))
  }
  
  sRules.+(SymPow())("Power with a log as the exponent"){
    PowP(@?('b), LogP(@?('p), @?('b)))
  }{ case (b: Sym, p: Sym) => p }
  
  sRules.+(SymPow())("Power to a product with a log"){
    PowP(@?('b), ProdP(LogP(@?('p), @?('b)), @?('rest) @@ __*))
  }{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
      SymPow(p, SymProd(rest:_*))
  }
  
  sRules.+(SymPow())("Power to a sum with a log"){
    PowP(@?('b), SumP(LogP(@?('p), @?('b)), @?('rest) @@ __*))
  }{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
      SymProd(p, SymPow(b, SymProd(rest:_*)))
  }
  
  sRules.+(SymLog())("Log base a of a is 1"){
    LogP(@?('a), @?('a))
  }{ case (a: Sym) => #=(1) }
  
  sRules.+(SymProd())("Multiplicative identity is 1"){
    ProdP()
  }{ case () => #=(1) }
  
  sRules.+(SymProd())("Simplify product of a single number"){
    ProdP(@?('a))
  }{ case a: Sym => a }
  
  sRules.+(SymProd())("Product containing 0 is 0"){
    ProdP(=#?(0), __*)
  }{ case () => #=(0) }
  
  sRules.+(SymProd())("x*1 = x"){
    ProdP(=#?(1), @?('rest) @@ __*)
  }{ case rest: Seq[Sym] => **(rest:_*) }
  
  sRules.+(SymProd())("Merge nested products"){
    ProdP(@?('prod) @@ ProdP(__*), @?('rest) @@ __*)
  }{ case (prod: SymProd, rest: Seq[Sym]) =>
      SymProd({ prod.exprs ++ rest }:_*)
  }
  
  // Don't do this for rational bases, otherwise an infinite loop will be created
  sRules.+(SymProd())("Combine rational powers of similar bases being multiplied"){
    @?('whole) @@ ProdP(
      AsPowP(@?('base), @?('p1) @@ %?()),
      AsPowP(@?('base), @?('p2) @@ %?()),
      @?('rest) @@ __*
    )
  }{ case (base: Sym, p1: SymR, p2: SymR, rest: Seq[Sym], whole: Sym) =>
      if (base.isInstanceOf[SymR]) whole
      else SymProd({ ^(base, (p1 + p2)) +: rest }:_*)
  }
  
  sRules.+(SymProd())("Multiply rational factors"){
    ProdP(@?('a) @@ %?(), @?('b) @@ %?(), @?('rest) @@ __*)
  }{ case (a: SymR, b: SymR, rest: Seq[Sym]) =>
      SymProd({ (a * b) +: rest }:_*)
  }
  
  sRules.+(SymProd())("Multiply rational roots"){
    ProdP(
      PowP(@?('b1) @@ %?(), /?(=#?(1), @?('r1))),
      PowP(@?('b2) @@ %?(), /?(=#?(1), @?('r2))),
      @?('rest) @@ __*)
  }{ case (b1: SymR, b2: SymR, r1: SymInt, r2: SymInt, rest: Seq[Sym]) =>
      val lcm = SymInt((r1.n * r2.n) / (r1.n gcd r2.n))
      val newBase = (b1 ^ SymInt(lcm.n / r1.n)) * (b2 ^ SymInt(lcm.n / r2.n))
      SymProd({ ^(newBase, #=(1)~lcm) +: rest }:_*)
  }
  
  sRules.+(SymSum())("Additive identity is 0"){
    SumP()
  }{ case () => #=(0) }
  
  sRules.+(SymSum())("Simplify sum of a single number"){
    SumP(@?('a))
  }{ case (a: Sym) => a }
  
  sRules.+(SymSum())("0 in a sum goes away"){
    SumP(=#?(0), @?('rest) @@ __*)
  }{ case rest: Seq[Sym] => SymSum(rest:_*) }
  
  sRules.+(SymSum())("Merge nested sums"){
    SumP(@?('sum) @@ SumP(__*), @?('rest) @@ __*)
  }{ case (rest: Seq[Sym], sum: SymSum) =>
      SymSum({ sum.exprs ++ rest }:_*)
  }
  
  sRules.+(SymSum())("x*a? + x*b? = (a+b)*x"){
    SumP(
      First(ProdP(@?('f1) @@ RatP(), @?('u)), @?('u) &@ 'f1 -> #=(1)),
      First(ProdP(@?('f2) @@ RatP(), @?('u)), @?('u) &@ 'f2 -> #=(1)),
      @?('rest) @@ __*)
  }{ case (f1: SymR, f2: SymR, rest: Seq[SymR], u: Sym) =>
      SymSum({ **(f1 + f2, u) +: rest }:_*)
  }
  
  sRules.+(SymSum())("x*y*a? + x*y*b? = (a+b)*x*y"){
    SumP(
      ProdP(First(@?('f1) @@ RatP(), ~~ &@ 'f1 -> #=(1)), @?('us) @@ __*),
      ProdP(First(@?('f2) @@ RatP(), ~~ &@ 'f2 -> #=(1)), @?('us) @@ __*),
      @?('rest) @@ __*)
  }{ case (f1: SymR, f2: SymR, rest: Seq[SymR], us: Seq[Sym]) =>
      SymSum({ **({ (f1 + f2) +: us }:_*) +: rest }:_*)
  }
  
  sRules.+(SymSum())("Add rationals or similar products of rationals"){
    SumP(AsProdP(@?('a) @@ %?(), @?('r) @@ __*), AsProdP(@?('b) @@ %?(), @?('r) @@ __*), @?('rest) @@ __*)
  }{ case (a: SymR, b: SymR, r: Seq[Sym], rest: Seq[Sym]) =>
      SymSum({ SymProd({ (a + b) +: r }:_*) +: rest }:_*)
  }
  
  sRules.+(SymProd())("Distributive property"){
    ProdP(SumP(@?('terms) @@ __*), @?('n) @@ %?(), @?('rest) @@ __*)
  }{ case (n: Sym, rest: Seq[Sym], terms: Seq[Sym]) =>
      SymProd({ SymSum({ terms.map{ e => SymProd(e, n) } }:_*) +: rest }:_*)
  }
  
  sRules.+(SymPM())("Plus/minus 0 is 0"){ SymP(SymPM(#=(0))) }{ case () => #=(0) }

  sRules.+(SymPM())("Plus/minus -x is +-x"){
    PMP(@?('a) @@ RatP() |>[SymR] {a: SymR => (a.n*a.d) < 0})
  }{ case a: SymR => a.negative }

  sRules.+(SymProd())("Product moves inside plus-minus"){
    ProdP(PMP(@?('e)), @?('rest) @@ __*)
  }{ case (e: Sym, rest: Seq[Sym]) =>
      SymPM( SymProd({ e +: rest }:_*) )
  }
}
