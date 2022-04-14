import scala.util.chaining._
import scala.reflect.ClassTag

type Matchable = Either[Sym, Seq[Sym]]
type Bindings = Map[Symbol, Matchable]

trait Pattern {
  // The symbols that should get bound to the match of an expression
  def pattern: Pattern = this
  def matches(e: Sym): Seq[Bindings] = Seq()

  // Seq( {Matched object/s} {Not included} {Possible bindings} )
  def matchesSeq(syms: Seq[Sym]): Seq[(Matchable, Seq[Sym], Seq[Bindings])] =
    (0 until syms.length).map{i =>
      (Left(syms(i)), syms.patch(i, Nil, 1), this.matches(syms(i)))
    }.filter(_._3 != Nil)
}

implicit class PatternSymbol(s: Symbol) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = Seq(Map(s -> Left(e)))
}

case class P[T]()(implicit tag: ClassTag[T]) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case e: T => Seq(Map())
    case _ => Seq()
  }
}
case class AnyP() extends Pattern {
  override def matches(e: Sym) = Seq(Map())
}
case class IntP(n: Pattern = AnyP()) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case a: SymInt => matchSeveral((a -> n))
    case _ => Seq[Bindings]()
  }
}
case class FracP(n: Pattern = AnyP(), d: Pattern = AnyP()) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case SymFrac(a, b) => matchSeveral((SymInt(a) -> n), (SymInt(b) -> d))
    case _ => Seq[Bindings]()
  }
}
case class PowP(base: Pattern = AnyP(), pow: Pattern = AnyP()) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case SymPow(a, b) => matchSeveral((a -> base), (b -> pow))
    case _ => Seq[Bindings]()
  }
}
case class SumP(ps: Pattern*) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case SymSum(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Seq[Bindings]()
  }
}
case class ProdP(ps: Pattern*) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = e match {
    case SymProd(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Seq[Bindings]()
  }
}

case class Repeat(p: Pattern, min: Int = 0, max: Int = 0) extends Pattern {
  override def matches(e: Sym) = Nil
  override def matchesSeq(seq: Seq[Sym]) =
    // Creates a tuple of the form ( {match}, {rest} )
    seq.partition(p.matches(_) != Nil)
      .pipe{t => Seq( (Right(t._1), t._2, Seq(Map())) )}
}

case class Bind(s: Symbol, p: Pattern) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] =
    tryCombinations(p.matches(e), Seq[Bindings](Map(s -> Left(e))))
  override def matchesSeq(syms: Seq[Sym]) =
    p.matchesSeq(syms).map{ case (matched, rest, bindings) =>
      (matched, rest, tryCombinations(bindings, Seq[Bindings](Map(s -> matched))))
    }
  override def pattern = p.pattern
}

def tryMerge(a: Bindings, b: Bindings): Option[Bindings] =
  Option.when((a.keys.toSet & b.keys.toSet).filter{k => a(k) != b(k)}.isEmpty)(a ++ b)

def tryCombinations(a: Seq[Bindings], b: Seq[Bindings]): Seq[Bindings] =
  a.map{m1 => b.map(tryMerge(m1, _)).collect{ case Some(m) => m }}.flatten

def matchSeveral(ts: (Sym, Pattern)*): Seq[Bindings] =
  ts.map{t => t._2.matches(t._1)}.foldLeft(Seq[Bindings](Map()))(tryCombinations)

def matchSeq(syms: Seq[Sym], ps: Seq[Pattern]): Seq[Bindings] = ps match {
  case Nil => if (syms.isEmpty) Seq(Map()) else Seq()
  case Seq(head, tail @ _*) => head.matchesSeq(syms)
      .map{ case (_, rest, binds) => tryCombinations(binds, matchSeq(rest, tail)) }
      .flatten.distinct
}

