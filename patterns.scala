import scala.util.chaining._
import scala.reflect.ClassTag

implicit class ImplicitMatchable(either: Either[Sym, Seq[Sym]]) {
  def expr  = either match { case Left(e)  => e }
  def exprs = either match { case Right(e) => e }
}

type Matchable = Either[Sym, Seq[Sym]]
type Bindings = Map[Symbol, Matchable]

trait Pattern {
  // The symbols that should get bound to the match of an expression
  def pattern: Pattern = this
  def matches(e: Sym): Seq[Bindings]

  // Seq( {Matched object/s} {Not included} {Possible bindings} )
  def matchesSeq(syms: Seq[Sym]): Seq[(Matchable, Seq[Sym], Seq[Bindings])] =
    (0 until syms.length).map{i =>
      (Left(syms(i)), syms.patch(i, Nil, 1), this.matches(syms(i)))
    }.filter(_._3 != Nil)
}

implicit class SymSymbol(s: Symbol) extends Pattern with Sym {
  def matches(e: Sym): Seq[Bindings] = Seq(Map(s -> Left(e)))
  def asSymbol: Symbol = this.s
  def apply[T](implicit env: Bindings): T =
    env(s).merge.asInstanceOf[T]
}

case class P[T]()(implicit tag: ClassTag[T]) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case e: T => Seq(Map())
    case _ => Seq()
  }
}
case class ConstP(c: Sym) extends Pattern {
  def matches(e: Sym) = if (e == c) Seq(Map()) else Seq()
}
case class AnyP() extends Pattern {
  def matches(e: Sym) = Seq(Map())
}
case class IntP(n: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case a: SymInt => matchSeveral((a -> n))
    case _ => Seq[Bindings]()
  }
}
case class FracP(n: Pattern = AnyP(), d: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case SymFrac(a, b) => matchSeveral((a -> n), (b -> d))
    case _ => Seq[Bindings]()
  }
}
case class PowP(base: Pattern = AnyP(), pow: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case SymPow(a, b) => matchSeveral((a -> base), (b -> pow))
    case _ => Seq[Bindings]()
  }
}
case class SumP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case SymSum(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Seq[Bindings]()
  }
}
case class ProdP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case SymProd(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Seq[Bindings]()
  }
}

case class Repeat(p: Pattern = AnyP(), min: Int = 0, max: Int = 0) extends Pattern {
  def matches(e: Sym) = Seq()
  override def matchesSeq(seq: Seq[Sym]): Seq[(Matchable, Seq[Sym], Seq[Bindings])] =
    // Creates a tuple of the form ( {match}, {rest} )
    seq.partition(p.matches(_) != Nil) match {
      case (matched, rest) if (matched.length < min) => Seq()
      case (matched, rest) if (max > 0 && matched.length > max) =>
        (0 until matched.length).combinations(max).map{idxs =>
          (Right[Sym, Seq[Sym]](idxs.map(matched(_))),
            rest ++ idxs.foldLeft(matched){(acc, i) => acc.patch(i, Nil, 1)},
            Seq[Bindings](Map()))
        }.toSeq
      case (matched, rest) => Seq( (Right(matched), rest, Seq(Map())) )
    }
}

case class Bind(s: Symbol, p: Pattern) extends Pattern {
  def matches(e: Sym): Seq[Bindings] =
    tryCombinations(p.matches(e), Seq[Bindings](Map(s -> Left(e))))
  override def matchesSeq(syms: Seq[Sym]) =
    p.matchesSeq(syms).map{ case (matched, rest, bindings) =>
      (matched, rest, tryCombinations(bindings, Seq[Bindings](Map(s -> matched))))
    }
  override def pattern = p.pattern
}

case class Guard(p: Pattern, guards: (Bindings => Boolean)*) extends Pattern {
  def matches(e: Sym): Seq[Bindings] =
    p.matches(e).filter{b => LazyList(guards:_*).map{f => f(b)}.indexOf(false) == -1}
}

def tryMerge(a: Bindings, b: Bindings): Option[Bindings] =
  Option.when((a.keySet & b.keySet).filter{k => a(k) != b(k)}.isEmpty)(a ++ b)

def tryCombinations(a: Seq[Bindings], b: Seq[Bindings]): Seq[Bindings] =
  a.flatMap{m1 => b.flatMap(tryMerge(m1, _))}

def matchSeveral(ts: (Sym, Pattern)*): Seq[Bindings] =
  ts.map{t => t._2.matches(t._1)}.foldLeft(Seq[Bindings](Map()))(tryCombinations)

def matchSeq(syms: Seq[Sym], ps: Seq[Pattern]): Seq[Bindings] = ps match {
  case Nil => if (syms.isEmpty) Seq(Map()) else Seq()
  case Seq(head, tail @ _*) => head.matchesSeq(syms)
      .flatMap{ case (_, rest, binds) =>
        tryCombinations(binds, matchSeq(rest, tail))
      }.distinct
}

// Using the matching to actually do things
def matchFirst(expr: Sym)(ps: (Pattern, Bindings => Sym)*): Sym =
  LazyList(ps:_*).map{t => (t._1.matches(expr), t._2)}.find(!_._1.isEmpty) match {
    case Some((Seq(bind, _*), func)) => func(bind)
    case None => expr
  }

