package sympany.math

import scala.util.chaining._

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.Sym._
import sympany.Pattern._

object Simplify {
  val sRules = new Rules[Sym]()
  
  def simplify(expr: Sym): Sym = {
    //println("Simplify", expr)
    expr.mapExprs(simplify).pipe{e =>
      sRules.first(e) match {
        case Some(simpler) => simplify(simpler)
        case None => e
      }
    }
  }
  
  def separateRoot(base: SymInt, root: SymInt): (SymInt, SymInt) =
    ( base.primeFactors.toList.foldLeft(1.s){ (a, t) => a * (t._1 ^ SymInt(t._2.n / root.n)) },
      base.primeFactors.toList.foldLeft(1.s){ (a, t) => a * (t._1 ^ SymInt(t._2.n % root.n)) }
    )

  sRules.+("x^0 = 1"){
    PowP(__, =#?(0))
  }{ case () => 1.s }
  
  sRules.+("x^1 = x"){
    PowP('b, =#?(1))
  }{ case b: Sym => b }
  
  sRules.+("0^x = 0"){
    PowP(=#?(0), __)
  }{ case () => 0 }
  
  sRules.+("1^x = 1"){
    PowP(=#?(1), __)
  }{ case () => 1 }

  sRules.+("(-x)^2 = x^2"){
    PowP(ProdP(=#?(-1), 'bs @@ __*), IntP('p))
  }{ case (bs: Seq[Sym], p: SymInt) =>
      if (p.toInt % 2 == 0) ^( ***(bs), p )
      else **(-1, ^( ***(bs), p ))
  }
  
  // Roots - simplifies if greatest power of a prime factor is >= the root
  sRules.+("Factor powers out of roots"){
    'whole @@ PowP(RatP('n, 'd), FracP(=#?(1), 'root))
  }{ case (d: SymInt, n: SymInt, root: SymInt, whole: Sym) =>
      List(n, d).map(separateRoot(_, root)) match {
        case List((on, in), (od, id)) =>
          if (on == 1.s && od == 1.s) whole
          else **(on~od, ^((SymR(n.n.abs, d.n.abs) / (n~d)) * in~id, 1~root))
      }
  }
  
  // (n/d) ^ (p/root) = (n^p)/(d^p) ^ (1/root)
  sRules.+("Simplify rational powers of rational bases"){
    PowP(AsProdP(RatP('n, 'd), 'r @@ __*), 'pow @@ RatP('p |> { (_:SymInt) != 1.s }, 'root))
  }{ case (d: SymInt, n: SymInt, p: SymInt, pow: SymR, r: Seq[Sym], root: SymInt) =>
      val rat = {
        if (p.n > 0) ^((n ^ p) / (d ^ p), 1~root)
        else ^((d ^ (0.s - p)) / (n ^ (0.s - p)), 1~root)
      }
      if (r.isEmpty) rat
      else if (r.length == 1) **(^(r(0), pow), rat)
      else **(^(***(r), pow), rat)
  }
  
  // (a^p1)^p2 = a^(p1*p2)
  sRules.+("Nested powers multiply"){
    PowP(PowP('base, 'p1), 'p2)
  }{ case (b: Sym, p1: Sym, p2: Sym) =>
      ^(b, **(p1, p2))
  }
  
  sRules.+("Power with a log as the exponent"){
    PowP('b, LogP('p, 'b))
  }{ case (b: Sym, p: Sym) => p }
  
  sRules.+("Power to a product with a log"){
    PowP('b, ProdP(LogP('p, 'b), 'rest @@ __*))
  }{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
      SymPow(p, ***(rest))
  }
  
  sRules.+("Power to a sum with a log"){
    PowP('b, SumP(LogP('p, 'b), 'rest @@ __*))
  }{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
      **(p, SymPow(b, ***(rest)))
  }
  
  sRules.+("Log base a of a is 1"){
    LogP('a, 'a)
  }{ case (a: Sym) => 1 }
  
  sRules.+("Multiplicative identity is 1"){
    ProdP()
  }{ case () => 1 }
  
  sRules.+("Simplify product of a single number"){
    ProdP('a)
  }{ case a: Sym => a }
  
  sRules.+("Product containing 0 is 0"){
    ProdP(=#?(0), __*)
  }{ case () => 0 }
  
  sRules.+("x*1 = x"){
    ProdP(=#?(1), 'rest @@ __*)
  }{ case rest: Seq[Sym] => **(rest:_*) }
  
  sRules.+("Merge nested products"){
    ProdP('prod @@ ProdP(__*), 'rest @@ __*)
  }{ case (prod: SymProd, rest: Seq[Sym]) =>
      ***(prod.exprs ++ rest)
  }
  
  // The inner AsProdPs allow (x * (x * y)^-1) to become y^-1
  // This may be controversial, but it is necessary for usub to work
  sRules.+("Combine rational powers of similar bases being multiplied"){
    'whole @@ ProdP(
      AsPowP(AsProdP('base, 'r1 @@ __*), 'p1 @@ %?()),
      AsPowP(AsProdP('base, 'r2 @@ __*), 'p2 @@ %?()),
      'rest @@ __*
    )
  }{ case (base: Sym, p1: SymR, p2: SymR, r1: Seq[Sym], r2: Seq[Sym], rest: Seq[Sym], whole: Sym) =>
      // Don't do this for rational bases, otherwise an infinite loop will be created
      val rp1 = if (r1.isEmpty) Nil else Seq(^(***(r1), p1))
      val rp2 = if (r2.isEmpty) Nil else Seq(^(***(r2), p2))

      if (base.isInstanceOf[SymR]) whole
      else ***(^(base, (p1 + p2)) +: (rest ++ rp1 ++ rp2))
  }

  // This rule is controversial
  /*
   sRules.+("Power of product is a product of powers"){
   ProdP(PowP(ProdP('fs @@ __*), 'pow), 'rest @@ __*)
   }{ case (fs: Seq[Sym], pow: Sym, rest: Seq[Sym]) =>
   ***(fs.map(SymPow(_, pow)) ++ rest)
   }
   */

  sRules.+("Multiply rational factors"){
    ProdP('a @@ %?(), 'b @@ %?(), 'rest @@ __*)
  }{ case (a: SymR, b: SymR, rest: Seq[Sym]) =>
      ***((a * b) +: rest)
  }
  
  sRules.+("Multiply rational roots"){
    ProdP(
      PowP('b1 @@ %?(), /?(=#?(1), 'r1)),
      PowP('b2 @@ %?(), /?(=#?(1), 'r2)),
      'rest @@ __*)
  }{ case (b1: SymR, b2: SymR, r1: SymInt, r2: SymInt, rest: Seq[Sym]) =>
      val lcm = SymInt((r1.n * r2.n) / (r1.n gcd r2.n))
      val newBase = (b1 ^ SymInt(lcm.n / r1.n)) * (b2 ^ SymInt(lcm.n / r2.n))
      ***(^(newBase, 1~lcm) +: rest)
  }
  
  sRules.+("Additive identity is 0"){
    SumP()
  }{ case () => 0 }
  
  sRules.+("Simplify sum of a single number"){
    SumP('a)
  }{ case (a: Sym) => a }
  
  sRules.+("0 in a sum goes away"){
    SumP(=#?(0), 'rest @@ __*)
  }{ case rest: Seq[Sym] => +++(rest) }
  
  sRules.+("Merge nested sums"){
    SumP('sum @@ SumP(__*), 'rest @@ __*)
  }{ case (rest: Seq[Sym], sum: SymSum) =>
      +++(sum.exprs ++ rest)
  }
  
  sRules.+("3xy + 2xy = 5xy"){
    SumP(
      AsProdP(First('f1 @@ RatP(), ~~ &@ 'f1 -> 1.s), 'us @@ __*),
      AsProdP(First('f2 @@ RatP(), ~~ &@ 'f2 -> 1.s), 'us @@ __*),
      'rest @@ __*)
  }{ case (f1: SymR, f2: SymR, rest: Seq[SymR], us: Seq[Sym]) =>
      +++( **({ (f1 + f2) +: us }:_*) +: rest )
  }
  
  sRules.+("Add rationals or similar products of rationals"){
    SumP(AsProdP('a @@ %?(), 'r @@ __*), AsProdP('b @@ %?(), 'r @@ __*), 'rest @@ __*)
  }{ case (a: SymR, b: SymR, r: Seq[Sym], rest: Seq[Sym]) =>
      +++( ***((a + b) +: r) +: rest )
  }
  
  sRules.+("Distributive property"){
    ProdP(SumP('terms @@ __*), 'n @@ %?(), 'rest @@ __*)
  }{ case (n: Sym, rest: Seq[Sym], terms: Seq[Sym]) =>
      ***( +++( terms.map{ e => **(e, n) } ) +: rest )
  }
  
  sRules.+("Plus/minus 0 is 0"){ SymP(SymPM(0)) }{ case () => 0 }

  sRules.+("Plus/minus -1 is PM1"){
    PMP(AsProdP('n @@ %?() |> { (_: SymR) < 0 }, 'r @@ __*))
  }{ case (n: SymR, r: Seq[Sym]) => SymPM(***( n.negative +: r ))
  }

  sRules.+("Remove nested plus/minus"){ PMP(PMP('e)) }{ case e: Sym => SymPM(e) }
  
  sRules.+("Plus/minus -x is +-x"){
    PMP('a @@ RatP() |> {a: SymR => (a.n*a.d) < 0})
  }{ case a: SymR => a.negative }
  
  sRules.+("Product moves inside plus-minus"){
    ProdP(PMP('e), 'rest @@ __*)
  }{ case (e: Sym, rest: Seq[Sym]) =>
      SymPM( ***(e +: rest) )
  }

  /// Simplifying infinities

  sRules.+("Even root of negative number is undefined"){
    PowP( RatP() |> { (_: SymR) < 0 },
      RatP(SymP(1), IntP() |> { (_: SymInt).toInt % 2 == 0 }))
  }{ case () => SymUndefined() }

  sRules.+("Even root of negative number is undefined"){
    PowP( 'b @@ RatP() |> { (_: SymR) < 0 },
      'p @@ RatP(SymP(1), IntP() |> { (_: SymInt).toInt % 2 == 1 }))
  }{ case (b: SymR, p: SymR) => SymPow(b.negative, p) }

  sRules.+("Anything with an undefined is undefined"){
    AnyP() |> {e: Sym => Sym.containsExpr(e, SymUndefined())}
  }{ case () => SymUndefined() }

  sRules.+("Infinity minus infinity is undefined"){
    SumP( SymP(SymPositiveInfinity()), SymP(SymNegativeInfinity()), __* )
  }{ case () => SymUndefined() }

  sRules.+("Infinity times a number"){
    ProdP( SymP(SymPositiveInfinity()), 'a @@ RatP(), 'r @@ __* )
  }{ case (a: SymR, r: Seq[SymR]) =>
      if (a.n > 0) +++( SymPositiveInfinity() +: r )
      else if (a.n < 0) +++( SymNegativeInfinity() +: r )
      else SymUndefined()
  }

  sRules.+("Negative infinity times a number"){
    ProdP( SymP(SymNegativeInfinity()), 'a @@ RatP(), 'r @@ __* )
  }{ case (a: SymR, r: Seq[SymR]) =>
      if (a.constant > 0) +++( SymNegativeInfinity() +: r )
      else if (a.constant < 0) +++( SymPositiveInfinity() +: r )
      else SymUndefined()
  }

  sRules.+("Infinity to a power"){
    PowP( SymP(SymPositiveInfinity()), 'e @@ RatP() )
  }{ case (e: SymR) =>
      if (e.constant > 0) SymPositiveInfinity()
      else if (e.constant < 0) 0
      else SymUndefined()
  }

  sRules.+("Negative infinity to a power"){
    PowP( SymP(SymNegativeInfinity()), 'e @@ RatP() )
  }{ case (e: SymR) =>
      if (e.constant > 0) SymNegativeInfinity()
      else if (e.constant < 0) 0
      else SymUndefined()
  }

  /// Integral rules

  /*
   sRules.+("Basic Integrals"){
   'i @@ IntegralP()
   }{ case i: Integral.SymIntegral =>
   IntegralRules.basicIntegration(i).getOrElse(i)
   }

   sRules.+("Integral of a product is a product with an integral"){
   IntegralP( ProdP( ConstP('c), 'rest @@ __* ) )
   }{ case (c: SymConstant, rest: Seq[Sym]) =>
   **(c, math.Integral.SymIntegral(***(rest)))
   }

   sRules.+("Integral of a sum is a sum of integrals"){
   IntegralP( 's @@ SumP(__*) )
   }{ case s: SymSum =>
   +++( s.exprs.map(Integral.SymIntegral(_)) )
   }
   */

  /// Controversial

  sRules.+("Expand binomials"){
    PowP( 's @@ SumP( RatP(), ProdP(PowP(RatP(), RatP()), RatP()) ), IntP('p) )
  }{ case (p: SymInt, s: SymSum) =>
      (2 to p.n.toInt).foldLeft(s.exprs){ (acc, n) => distribute(acc, s.exprs) }.pipe(+++)
  }

  sRules.+("Expand simpler binomials"){
    PowP( 's @@ SumP( RatP(), PowP(RatP(), RatP()) ), IntP('p) )
  }{ case (p: SymInt, s: SymSum) =>
      (2 to p.n.toInt).foldLeft(s.exprs){ (acc, n) => distribute(acc, s.exprs) }.pipe(+++)
  }

  sRules.+("Expand power of root times fraction"){
    PowP( ProdP('n @@ RatP(), PowP('b, 'p @@ RatP()) ), IntP('i) |> { (_:SymInt) >= 0 } )
  }{ case (b: Sym, i: SymInt, n: SymR, p: SymR) => **(n^i, ^(b, p*i)) }

  def distribute(l1: Seq[Sym], l2: Seq[Sym]): Seq[Sym] =
    l1.flatMap{ a => l2.map{ b => **(a, b).pipe(simplify) } }

  //sRules.+("Expand out powers of polynomials"){
  //  PowP('s @@ SumP(Repeat(Or( AsPowP(VarP(), RatP()), RatP() ))), 'p @@ IntP())
  //}{ case (p: SymInt, s: SymSum) =>
  //    (2 to p.n.toInt).foldLeft(s.exprs){ (acc, n) => distribute(acc, s.exprs) }.pipe(+++)
  //}
}
