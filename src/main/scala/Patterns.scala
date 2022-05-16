package sympany.patterns

import scala.util.chaining._

import sympany.symbolics._
import sympany.symbolics.Sym._

// Define functions used by the pattern matching system
object Pattern {
  type Binding = Map[Symbol, Any]

  case class SeqMatch(m: Any, rest: Seq[Sym], binds: Seq[Binding])

  def tryMerge(a: Binding, b: Binding): Option[Binding] =
    Option.when((a.keySet & b.keySet).filter{k => a(k) != b(k)}.isEmpty)(a ++ b)

  def tryCombinations(a: Seq[Binding], b: Seq[Binding]): Seq[Binding] =
    a.flatMap{m1 => b.flatMap(tryMerge(m1, _))}

  def matchSeveral(ts: (Sym, Pattern)*): Seq[Binding] =
    ts.map{t => t._2.matches(t._1)}.foldLeft(Seq[Binding](Map()))(tryCombinations)

  def matchSeq(syms: Seq[Sym], ps: Seq[Pattern]): Seq[Binding] =
    if (ps.isEmpty) {
      if (syms.isEmpty) Seq(Map()) else Seq()
    } else {
      ps.head.matchesSeq(syms)
        .flatMap{ case SeqMatch(_, rest, binds) =>
          tryCombinations(binds, matchSeq(rest, ps.tail))
        }.distinct
    }

  def callWithBind[T](b: Binding)(f: Any => T): T =
    b.toList
      .sortWith(_._1.name < _._1.name)
      .map(_._2)
      .pipe(listToTuple)
      .pipe(f)

  assert(callWithBind(Map()){ case () => 3 + 4 } == 7)
  assert(callWithBind(Map(('a, SymInt(3)))){ case a: SymInt => a.n < 4 } == true)
  assert(callWithBind(Map(('a, 1), ('b, 2), ('c, 3))){
    case (a: Int, b: Int, c: Int) => a + b + c
  } == 6)

  def listToTuple(list: List[Any]): Any = list match {
    case Nil                                => ()
    case List(a)                            => a
    case List(a, b)                         => (a, b)
    case List(a, b, c)                      => (a, b, c)
    case List(a, b, c, d)                   => (a, b, c, d)
    case List(a, b, c, d, e)                => (a, b, c, d, e)
    case List(a, b, c, d, e, f)             => (a, b, c, d, e, f)
    case List(a, b, c, d, e, f, g)          => (a, b, c, d, e, f, g)
    case List(a, b, c, d, e, f, g, h)       => (a, b, c, d, e, f, g, h)
    case List(a, b, c, d, e, f, g, h, i)    => (a, b, c, d, e, f, g, h, i)
    case List(a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, h, i, j)
  }

  def #?(p: Pattern = AnyP()) = IntP(p)
  def %?(n: Pattern = AnyP(), d: Pattern = AnyP()) = RatP(n, d)
  def /?(n: Pattern = AnyP(), d: Pattern = AnyP()) = FracP(n, d)
  def *?(ps: Pattern*) = ProdP(ps:_*)
  def +?(ps: Pattern*) = SumP(ps:_*)
  def ^?(base: Pattern = AnyP(), exp: Pattern = AnyP()) = PowP(base, exp)
  def logP(pow: Pattern = AnyP(), base: Pattern = AnyP()) = LogP(pow, base)
  def =?(sym: Sym) = SymP(sym)
  def =#?(int: Int) = SymP(SymInt(int))
  def @?(symbol: Symbol) = PatternVar(symbol)

  def __ = AnyP()
  def __* = Repeat()
  def ~~ = Repeat(max = 0)
  def *(p: Pattern = AnyP(), min: Int = 0, max: Int = 0) = Repeat(p, min, max)
  def XP = SymP(X)
}

import Pattern._

trait Pattern {
  /* The list of possible ways to bind the variables contained in a pattern to
   * match the given expression
   * If it returns an empty list, the pattern does not match the expression
   * If it returns a list with an empty map, the pattern matches the expression,
   * but without any variables being bound
   */
  def matches(e: Sym): Seq[Binding]

  /* For each possible match for specified expression, pass the match variables
   * to the function, and return the list of new expressions returned.
   * Don't include instances where the function returns the original expression.
   */
  def matchesApply(expr: Sym)(func: Any => Sym): Seq[Sym] =
    this.matches(expr)
      .map(callWithBind(_)(func))
      .filter{ e => !(e == expr) }

  /* Given a sequence of expressions, return a list of ways to match it.
   * The elements of the list contain what was matched, what wasn't matched, and
   * for that specific match, the list of possible ways to bind the variables.
   */
  def matchesSeq(syms: Seq[Sym]): Seq[SeqMatch] =
    (0 until syms.length).map{i =>
      SeqMatch(m = syms(i),
        rest = syms.patch(i, Nil, 1),
        binds = this.matches(syms(i)))
    }.filter(_.binds.nonEmpty)

  def &(o: Pattern) = And(this, o)
  def |(o: Pattern) = Or(this, o)
  def >(o: Pattern) = First(this, o)
  def &@(bind: (Symbol, Any)) = With(this, bind._1, bind._2)

  // `satisfies` always has a single argument, the entire expression, while `guards`
  // take the arguments from the current binding generated by `callWithBind`
  def |>[T <: Sym](satisfies: (T => Boolean)) = Satisfies(this, satisfies)
  def |>>(guard: Any => Boolean) = Guard(this, guard)
}

case class PatternVar(symbol: Symbol) extends Pattern {
  def matches(e: Sym) = Seq(Map(this.symbol -> e))
  def @@(p: Pattern) = Bind(this.symbol, p)
}
//implicit class ImplicitPatternVar(_s: Symbol) extends PatternVar(_s)

case class AnyP() extends Pattern {
  def matches(e: Sym) = Seq(Map())
}

case class ConstP() extends Pattern {
  def matches(e: Sym) = e match {
    case c: SymConstant => Seq(Map())
    case _ => Seq()
  }
}

case class SymP(c: Sym) extends Pattern {
  def matches(e: Sym) = if (e == c) Seq(Map()) else Seq()
}

case class Bind(v: Symbol, p: Pattern) extends Pattern {
  // tryCombinations will add the variable to the already existing binding,
  // while also making sure that there are no conflicts
  def matches(e: Sym): Seq[Binding] =
    tryCombinations(p.matches(e), Seq(Map(v -> e)))

  override def matchesSeq(syms: Seq[Sym]) =
    p.matchesSeq(syms).map{
      case SeqMatch(m, rest, bindings) =>
        SeqMatch(m = m, rest = rest,
          binds = tryCombinations(bindings, Seq(Map(v -> m))))
    }
}

case class With(p: Pattern, v: Symbol, bind: Any) extends Pattern {
  def matches(e: Sym): Seq[Binding] =
    tryCombinations(p.matches(e), Seq(Map(v -> bind)))

  override def matchesSeq(syms: Seq[Sym]) =
    p.matchesSeq(syms).map{ case SeqMatch(m, rest, binds) =>
      SeqMatch(m = m, rest = rest,
        binds = tryCombinations(binds, Seq(Map(v -> bind))))
    }
}

case class RatP(n: Pattern = AnyP(), d: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymFrac(a, b) => matchSeveral((SymInt(a) -> n), (SymInt(b) -> d))
    case a: SymInt => matchSeveral((a -> n), (SymInt(1) -> d))
    case _ => Seq()
  }
}

case class IntP(n: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case a: SymInt => matchSeveral((a -> n))
    case _ => Seq[Binding]()
  }
}

case class FracP(n: Pattern = AnyP(), d: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymFrac(a, b) => matchSeveral((SymInt(a) -> n), (SymInt(b) -> d))
    case _ => Seq[Binding]()
  }
}

case class SumP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymSum(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Nil
  }
}

case class ProdP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymProd(exprs @ _*) => matchSeq(exprs, ps)
    case _ => Nil
  }
}

case class PowP(base: Pattern = AnyP(), exp: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymPow(a, b) => matchSeveral((a -> base), (b -> exp))
    case _ => Seq[Binding]()
  }
}

case class LogP(pow: Pattern = AnyP(), base: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymLog(a, b) => matchSeveral((a -> pow), (b -> base))
    case _ => Seq[Binding]()
  }
}

case class Repeat(p: Pattern = AnyP(), min: Int = 0, max: Int = -1) extends Pattern {
  // If matched against a single object, return nothing
  def matches(e: Sym) = Seq()

  override def matchesSeq(seq: Seq[Sym]): Seq[SeqMatch] =
    // Separate expressions that match from those that dont
    seq.partition(p.matches(_).nonEmpty) match {

      // If there are fewer matches than the min, there are no possible ways to match
      case (matches, dontMatch) if (matches.length < min) => Seq()

      // If there is a specified maximum, get all possible combinations of said maximum
      case (matches, dontMatch) if (max >= 0 && matches.length > max) =>
        (0 until matches.length).combinations(max).map{idxs =>
          SeqMatch(m = idxs.map(matches(_)),
            // Remove the current matches from the match list, then add that to the non matches
            rest = dontMatch ++ idxs.foldLeft(matches)
              { (acc, i) => acc.patch(i, Nil, 1) },
            binds = Seq[Binding](Map()))
        }.toSeq

      // If no maximum is specified, only return one possibility, where all matches are present
      case (matches, dontMatch) =>
        Seq(SeqMatch(m = matches, rest = dontMatch, binds = Seq(Map())) )
    }
}

case class Guard(p: Pattern, guard: Any => Boolean) extends Pattern {
  // Run through each guard, and stop after one of them returns false
  def matches(e: Sym): Seq[Binding] =
    p.matches(e).filter{ b => callWithBind(b)(guard) }
}

case class Satisfies[T <: Sym](p: Pattern, f: T => Boolean) extends Pattern {
  def matches(e: Sym): Seq[Binding] =
    if (f(e.asInstanceOf[T])) p.matches(e)
    else Seq()
}

case class Or(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] =
    ps.map(_.matches(e)).reduceLeft(_ ++ _).distinct

  override def matchesSeq(syms: Seq[Sym]): Seq[SeqMatch] =
    // Get a sequence of all match groups from all patterns
    ps.flatMap(_.matchesSeq(syms))
  // Map(what was matched -> List(match groups))
      .groupBy(_.m)
  // List(sequence of match groups with the same match)
      .values
  // For each sequence of match groups, concatenate their binding lists
      .map(_.reduceLeft{ (a, b) =>
        SeqMatch(m = a.m,
          rest = a.rest,
          binds = (a.binds ++ b.binds).distinct ) })
      .toSeq // Shut the compiler up
}

case class First(ps: Pattern*) extends Pattern {
  // Return either the first nonempty binding list of ps, or Nil
  def matches(e: Sym): Seq[Binding] =
    LazyList(ps:_*).map(_.matches(e)).find(_.nonEmpty).getOrElse(Nil)

  // Return either the first nonempty SeqMatch list of ps, or Nil
  override def matchesSeq(syms: Seq[Sym]): Seq[SeqMatch] =
    LazyList(ps:_*).map(_.matchesSeq(syms)).find(_.nonEmpty).getOrElse(Nil)
}

case class And(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] =
    ps.map(_.matches(e)).reduceLeft(tryCombinations)

  override def matchesSeq(syms: Seq[Sym]): Seq[SeqMatch] =
    ps.flatMap(_.matchesSeq(syms))
      .groupBy(_.m)
      .values
      .filter(_.length == ps.length)
      .map{ seqMatches => SeqMatch(
        m = seqMatches.head.m,
        rest = seqMatches.head.rest,
        binds = seqMatches.map(_.binds).reduceLeft(tryCombinations))
      }.toSeq
}

case class AsSumP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymSum(exprs @ _*) => matchSeq(exprs, ps)
    case expr => matchSeq(Seq(expr), ps)
  }
}

case class AsProdP(ps: Pattern*) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymProd(exprs @ _*) => matchSeq(exprs, ps)
    case expr => matchSeq(Seq(expr), ps)
  }
}

case class AsPowP(base: Pattern = AnyP(), exp: Pattern = AnyP()) extends Pattern {
  def matches(e: Sym): Seq[Binding] = e match {
    case SymPow(a, b) => matchSeveral((a -> base), (b -> exp))
    case a => matchSeveral((a -> base), (SymInt(1) -> exp))
  }
}

class Rule(name: String, p: Pattern, f: Any => Sym) {
  def first(e: Sym): Option[Sym] =
    try {
      LazyList(p.matches(e):_*)
        .map(callWithBind[Sym](_)(f))
        .find(_.id != e.id)
    } catch {
      case err: Throwable =>
        println(f"Rule `$name` threw error `$err`") ; None
    }

  def all(e: Sym): Seq[Sym] =
    p.matches(e)
      .map(callWithBind[Sym](_)(f))
      .filter(_.id != e.id)
}

class Rules() {
  val rules = scala.collection.mutable.Map[Sym, Seq[Rule]]()
  def +(t: Sym)(n: String)(p: Pattern)(f: Any => Sym) =
    rules(t) = rules.getOrElse(t, Nil) :+ new Rule(n, p, f)

  def apply(sym: Sym): Seq[Rule] = {
    rules.toList
      .filter{ r => (r._1 == SymInt(0)) || (r._1.getClass.isInstance(sym)) }
      .flatMap(_._2)
  }

  def first(e: Sym): Option[Sym] =
    LazyList(apply(e):_*).flatMap(_.first(e)).headOption

  def all(e: Sym): Seq[Sym] =
    apply(e).foldLeft(Seq[Sym]()){ (acc, r) => acc ++ r.all(e) }
}
