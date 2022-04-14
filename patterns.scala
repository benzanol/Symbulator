import scala.util.chaining._
import scala.reflect.runtime.universe.TypeTag

type Bindings = Map[Symbol, Any]

trait Pattern {
  // The symbols that should get bound to the match of an expression
  def pattern: Pattern = this
  def matches(e: Sym): Seq[Bindings] = Seq()

  // Seq( {Included} {Not included} {Possible bindings} )
  def matchesIn(syms: Seq[Sym]): Seq[(Any, Seq[Sym], Seq[Bindings])] =
    (0 until syms.length).map{i =>
      (syms(i), syms.patch(i, Nil, 1), this.matches(syms(i)))
    }.filter(_._3 != Nil)
}

implicit class PatternSymbol(s: Symbol) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] = Seq(Map(s -> e))
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
  override def matchesIn(seq: Seq[Sym]) =
    // Creates a tuple of the form ( {match}, {rest} )
    seq.partition(p.matches(_) != Nil)
      .pipe{t => Seq( (t._1, t._2, Seq(Map())) )}
}

case class Bind(s: Symbol, p: Pattern) extends Pattern {
  override def matches(e: Sym): Seq[Bindings] =
    tryCombinations(p.matches(e), Seq[Bindings](Map(s -> e)))
  override def matchesIn(syms: Seq[Sym]): Seq[(Any, Seq[Sym], Seq[Bindings])] =
    p.matchesIn(syms).map{ case (matched, rest, bindings) =>
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
  case Seq(head, tail @ _*) => head.matchesIn(syms)
      .map{ case (_, rest, binds) => tryCombinations(binds, matchSeq(rest, tail)) }
      .flatten.distinct
}

