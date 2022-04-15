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
  override def toString = "'" + s.name
  def matches(e: Sym): Seq[Bindings] = {
    println(f"Testing ${s.name} with $e")
    s.name match {
      case "_" | "*" => Seq(Map())
      case _ => Seq(Map(s -> Left(e)))
    }
  }

  override def matchesSeq(syms: Seq[Sym]) = s.name match {
    case "*" => Seq((Right(syms), Nil, Seq(Map())))
    // Because matches('_) is already empty, we don't need to add an extra case for it here
    case _ => (0 until syms.length).map{i =>
      (Left(syms(i)), syms.patch(i, Nil, 1), this.matches(syms(i)))
    }.filter(_._3 != Nil)
  }
  

  def asSymbol: Symbol = this.s

  def bound(implicit env: Bindings): Boolean = env.contains(s)
  def apply[T](implicit env: Bindings): T = env(s).merge.asInstanceOf[T]
  def maybe[T](implicit env: Bindings): Option[T] =
    if (this.bound) Some(this.apply) else None
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
case class RationalP(n: Pattern = AnyP(), d: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Bindings] = e match {
    case SymFrac(a, b) => matchSeveral((a -> n), (b -> d))
    case a: SymInt => matchSeveral((a -> n), (SymInt(1) -> d))
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
    case SymSum(exprs @ _*) =>
      if (ps.nonEmpty && (ps.head == '*)) Seq(Map())
      else matchSeq(exprs, ps)
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

  override def pattern = p.pattern
}

case class Or(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Bindings] =
    ps.map(_.matches(e)).reduceLeft(_ ++ _).distinct

  override def matchesSeq(syms: Seq[Sym]): Seq[(Matchable, Seq[Sym], Seq[Bindings])] =
    // Get a sequence of all match groups from all patterns
    ps.flatMap(_.matchesSeq(syms))
  // Map(what was matched -> List(match groups))
      .groupBy(_._1)
  // List(sequence of match groups with the same match)
      .values
  // For each sequence of match groups, concatenate their binding lists
      .map(_.reduceLeft{ (a, b) => ( a._1, a._2, (a._3 ++ b._3).distinct ) })
      .toSeq // Shut the compiler up
}
case class And(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Bindings] =
    ps.map(_.matches(e)).reduceLeft(tryCombinations)

  override def matchesSeq(syms: Seq[Sym]): Seq[(Matchable, Seq[Sym], Seq[Bindings])] = {
    val matchGroupLists = ps.map(_.matchesSeq(syms))
    // Cycle through the match groups in the first pattern
    matchGroupLists.head.flatMap{ case (m, rest, binds) =>
      // Instances of the particular match for each pattern
      val instances = matchGroupLists.tail.map(_.find(_._1 == m))
      // The match is only valid if it matches every pattern
      if (instances.contains(None)) None
      else Some((m, rest, instances.map(_.get._3).foldLeft(binds)(tryCombinations)))
    }
  }
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
def matchWith(expr: Sym)(pattern: Pattern)(func: Bindings => Sym): Seq[Sym] =
  pattern.matches(expr).map(func).filter{ e => !(e == expr) }

def matchFirst(expr: Sym)(cases: (Pattern, Bindings => Sym)*): Option[Sym] =
  LazyList(cases:_*).map{ case (pat, func) => matchWith(expr)(pat)(func) }
    .find(_.nonEmpty) match {
      case Some(Seq(a, _*)) => Some(a)
      case _ => None
    }

def matchAll(expr: Sym)(cases: (Pattern, Bindings => Sym)*): Seq[Sym] = {
  cases.flatMap{ case (pattern, func) =>
    pattern.matches(expr).map(func)
  }
}
