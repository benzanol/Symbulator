import scala.util.chaining._

// base^(1/root) = t._1 * t._2^(1/root)
def separateRoot(base: SymInt, root: SymInt): (SymInt, SymInt) =
  (base.primeFactors.toList.foldLeft(1:SymInt){ (a, t) => a * (t._1 ^ (t._2 / root)) },
    base.primeFactors.toList.foldLeft(1:SymInt){ (a, t) => a * (t._1 ^ (t._2 % root)) })

def simplify(e: Sym): Sym = matchFirst(e)(simplificationRules: _*)
  .pipe{n => if (n == e) e else simplify(n)}

val simplificationRules = Vector[(Pattern, Bindings => Sym)](
  // na/nb =>> a/b
  (Guard(Bind('f, FracP('n, 'd)), implicit env => ('f[SymFrac]).ratioGcd > 1),
    implicit env => SymFrac(
      'n[SymInt] / 'f[SymFrac].ratioGcd,
      'd[SymInt] / 'f[SymFrac].ratioGcd
    )),
  
  // 0/0 =>> undefined
  (FracP(ConstP(0), ConstP(0)),
    implicit env => SymUndefined()),
  
  // n/0 =>> infinity
  (FracP('n, ConstP(0)),
    implicit env => SymInfinity('n[SymInt] < 0)),
  
  // n/1 =>> n
  (FracP('n, ConstP(1)),
    implicit env => 'n[SymInt]),
  
  // n / -d =>> -n / d
  (Guard(FracP('n, 'd), implicit env => 'd[SymInt] < 0),
    implicit env => SymFrac(0 - 'n[SymInt], 0 - 'd[SymInt])),

  // u^0 =>> 1
  (PowP('_, ConstP(0)),
    implicit env => SymInt(1)),

  // u^1 =>> u
  (PowP('b, ConstP(1)),
    implicit env => 'b[Sym]),

  // Integer powers
  (PowP(IntP('b), IntP('p)),
    implicit env => 'b[SymInt] ^ 'p[SymInt]),
  
  // Roots - simplifies if greatest power of a prime factor is >= the root
  (Guard(PowP(RationalP('n, 'd), FracP(ConstP(1), 'root)),
    implicit env => ('n[SymInt].primeFactors.counts ++ 'd[SymInt].primeFactors.counts)
      .fold(0:SymInt)(_ max _)
      >= 'root[SymInt]),
    implicit env => List('n[SymInt], 'd[SymInt])
      .map(separateRoot(_, 'root[SymInt]))
      .pipe{ case List((on, in), (od, id)) =>
        SymProd(SymFrac(on, od), SymPow(SymFrac(in, id), 'root[SymInt].inverse)) }),

  // (n/d) ^ (p/root) = (n^p)/(d^p) ^ (1/root)
  (PowP(RationalP('n, 'd), FracP('p, 'root)),
    implicit env => SymPow(SymFrac('n[SymInt] ^ 'p[SymInt], 'd[SymInt] ^ 'p[SymInt]),
      'root[SymInt].inverse))
)
