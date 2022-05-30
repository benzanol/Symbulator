import scala.util.chaining._

def toMultiset[T](seq: Seq[T]): Map[T, Int] =
  seq.groupBy(identity).toList
    .map{ case (identity, list) => (identity, list.length) }
    .toMap

trait Sym {
  def exprs: Seq[Sym]
  def mapExprs(f: Sym => Sym): Sym

  def id: Any = this
  def ==(o: Sym) = this.id == o.id

  //def allHoles: Set[Sym] = exprHoles ++ extraHoles
  //def exprHoles: Set[Sym] = Set()
  //var extraHoles = Set[Sym] = Set()
  //def addHoles(newHoles: Set[Sym]): Unit =
  //  this.extraHoles = extraHoles ++ newHoles
  //def zeros: Set[Sym] = Set()
}

trait SymConstant extends Sym {
  def exprs = Seq(this)
  def mapExprs(f: Sym => Sym) = this
}

trait SymUnordered extends Sym

implicit class ImplicitSymVar(orig: Symbol) extends SymVar(orig)

case class SymVar(symbol: Symbol = 'x) extends SymConstant {
  override def toString = symbol.name
  def s = this
}

object SymR {
  def apply(n: BigInt = 1, d: BigInt = 1): SymR = {
    if (d == 0 && n == 0) return SymUndefined()
    else if (d == 0 && n > 0) return SymPositiveInfinity()
    else if (d == 0 && n < 0) return SymNegativeInfinity()

    val gcd: BigInt = n.abs gcd d.abs
    // 1 if d is positive, -1 if d is negative
    val one = d / d.abs

    if (d.abs / gcd == BigInt(1)) SymInt(one * n / gcd)
    else SymFrac(one * n / gcd, d.abs / gcd)
  }
}

trait SymR extends SymConstant {
  override def toString = f"$n/$d"
  def n: BigInt
  def d: BigInt

  def inverse: SymR = SymR(d, n)
  def negative: SymR = SymR(-n, d)
  def +(o: SymR): SymR = SymR((n * o.d) + (o.n * d), d * o.d)
  def -(o: SymR): SymR = this + o.negative
  def *(o: SymR): SymR = SymR(n * o.n, d * o.d)
  def /(o: SymR): SymR = this * o.inverse
  def ^(o: SymInt): SymR = SymR(n.pow(o.n.toInt))
}

case class SymFrac(n: BigInt = 1, d: BigInt = 1) extends SymR

implicit class ImplicitSymBigInt(original: BigInt) extends SymInt(original)
implicit class ImplicitSymInt(original: Int) extends SymInt(BigInt(original))

case class SymInt(n: BigInt = 1) extends SymR {
  override def toString = n.toString
  def d = BigInt(1)
  def s = this
  def ~(o: SymInt) = SymR(n, o.n)

  lazy val primeFactors: Map[SymInt, SymInt] = {
    var num = n.abs
    var f = 2
    var map = scala.collection.mutable.Map[SymInt, SymInt]()
    while (num > 1) {
      var count = 0
      while (num % f == 0) {count += 1 ; num /= f}
      if (count > 0) map += (SymInt(f) -> SymInt(count))
      f += 1
    }
    map.toMap
  }

  override def negative: SymInt = SymInt(-n)
  def +(o: SymInt): SymInt = SymInt(n + o.n)
  def -(o: SymInt): SymInt = this + o.negative
  def *(o: SymInt): SymInt = SymInt(n * o.n)
  override def ^(o: SymInt): SymInt = SymInt(n.pow(o.n.toInt))
}

case class SymUndefined() extends SymR {
  override def toString = "NaN"
  def n = 0
  def d = 0
}
case class SymPositiveInfinity() extends SymR {
  override def toString = "Inf"
  def n = 1
  def d = 0
}
case class SymNegativeInfinity() extends SymR {
  override def toString = "-Inf"
  def n = -1
  def d = 0
}

case class SymSum(exprs: Sym*) extends SymUnordered {
  override def toString = f"(+ " + exprs.mkString(" ") + ")"
  override def id = (SymSum, toMultiset(exprs.map(_.id)))
  def mapExprs(f: Sym => Sym) = SymSum(exprs.map(f):_*)
}

case class SymProd(exprs: Sym*) extends SymUnordered {
  override def toString = f"(* " + exprs.mkString(" ") + ")"
  override def id = (SymProd, toMultiset(exprs.map(_.id)))
  def mapExprs(f: Sym => Sym) = SymProd(exprs.map(f):_*)
}

case class SymPow(base: Sym = 1, expt: Sym = 1) extends Sym {
  override def toString = f"(^ $base $expt)"
  def exprs = Seq(base, expt)
  def mapExprs(f: Sym => Sym) = SymPow(f(base), f(expt))
}

case class SymLog(pow: Sym = 1, base: Sym = SymE()) extends Sym {
  override def toString = if (base == SymE()) f"(ln $pow)" else f"(log $pow $base)"
  def exprs = Seq(pow, base)
  def mapExprs(f: Sym => Sym) = SymLog(f(pow), f(base))
}

case class SymPM(expr: Sym = 1) extends Sym {
  override def toString = f"(+- $expr)"
  def exprs = Seq(expr)
  def mapExprs(f: Sym => Sym) = SymPM(f(expr))
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"
}
case class SymE() extends SymConstant {
  override def toString = "E"
}

def ++(es: Sym*) = SymSum(es:_*)
def **(es: Sym*) = SymProd(es:_*)
def ^(base: Sym, expt: Sym) = SymPow(base, expt)
def log(pow: Sym, base: Sym = SymE()) = SymLog(pow, base)
def +-(e: Sym) = SymPM(e)
def Pi = SymPi()
def E = SymE()
def X = SymVar('x)

def rev[T](l: List[T]): List[T] = l match {
  case Nil => Nil
  case h :: t => rev(t) :+ h
}

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

def callWithBind[T](b: Binding)(f: Any => T) =
  b.toList
    .sortWith(_._1.name < _._1.name)
    .map(_._2)
    .pipe(listToTuple)
    .pipe(f)

assert(callWithBind(Map()){ case () => 3 + 4 } == 7)
assert(callWithBind(Map(('a, 3.s))){ case a: SymInt => a.n < 4 } == true)
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
implicit class ImplicitPatternVar(_s: Symbol) extends PatternVar(_s)

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
    case SymFrac(a, b) => matchSeveral((a.s -> n), (b.s -> d))
    case a: SymInt => matchSeveral((a.s -> n), (1.s -> d))
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
    case SymFrac(a, b) => matchSeveral((a.s -> n), (b.s -> d))
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
    case a => matchSeveral((a -> base), (1.s -> exp))
  }
}

def #?(p: Pattern = AnyP()) = IntP(p)
def %?(n: Pattern = AnyP(), d: Pattern = AnyP()) = RatP(n, d)
def /?(n: Pattern = AnyP(), d: Pattern = AnyP()) = FracP(n, d)
def *?(ps: Pattern*) = ProdP(ps:_*)
def +?(ps: Pattern*) = SumP(ps:_*)
def ^?(base: Pattern = AnyP(), exp: Pattern = AnyP()) = PowP(base, exp)
def logP(pow: Pattern = AnyP(), base: Pattern = AnyP()) = LogP(pow, base)
def =?(sym: Sym) = SymP(sym)

def __ = AnyP()
def __* = Repeat()
def ~~ = Repeat(max = 0)
def *(p: Pattern = AnyP(), min: Int = 0, max: Int = 0) = Repeat(p, min, max)
def XP = SymP('x)

class Rule(name: String, p: Pattern, f: Any => Sym) {
  def first(e: Sym): Option[Sym] =
    try {
      LazyList(p.matches(e):_*)
        .map(callWithBind[Sym](_)(f))
        .find(_.id != e.id)
    } catch {
      case err => println(f"Rule `$name` threw error `$err`") ; None
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
      .filter{ r => (r._1 == 0.s) || (r._1.getClass.isInstance(sym)) }
      .flatMap(_._2)
  }

  def first(e: Sym): Option[Sym] =
    LazyList(apply(e):_*).flatMap(_.first(e)).headOption

  def all(e: Sym): Seq[Sym] =
    apply(e).foldLeft(Seq[Sym]()){ (acc, r) => acc ++ r.all(e) }
}

val sRules = new Rules()

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
  ( base.primeFactors.toList.foldLeft(1.s){ (a, t) => a * (t._1 ^ (t._2.n / root.n).s) },
    base.primeFactors.toList.foldLeft(1.s){ (a, t) => a * (t._1 ^ (t._2.n % root.n).s) }
  )

sRules.+(SymPow())("x^0 = 1"){
  PowP(__, =?(0))
}{ case () => 1 }

sRules.+(SymPow())("x^1 = x"){
  PowP('b, =?(1))
}{ case b: Sym => b }

sRules.+(SymPow())("0^x = 0"){
  PowP(=?(0), __)
}{ case () => 0.s }

sRules.+(SymPow())("1^x = 1"){
  PowP(=?(1), __)
}{ case () => 1.s }

// Roots - simplifies if greatest power of a prime factor is >= the root
sRules.+(SymPow())("Factor powers out of roots"){
  'whole @@ PowP(RatP('n, 'd), FracP(=?(1), 'root))
}{ case (d: SymInt, n: SymInt, root: SymInt, whole: Sym) =>
    List(n, d).map(separateRoot(_, root)) match {
      case List((on, in), (od, id)) =>
        if (on == 1.s && od == 1.s) whole
        else **(on~od, ^(((n.n.abs ~ d.n.abs) / (n~d)) * in~id, 1~root))
    }
}

// (n/d) ^ (p/root) = (n^p)/(d^p) ^ (1/root)
sRules.+(SymPow())("Simplify rational powers of rational bases"){
  PowP(RatP('n, 'd), RatP('p |> { (_:SymInt) != 1.s }, 'root))
}{ case (d: SymInt, n: SymInt, p: SymInt, root: SymInt) =>
    if (p.n > 0) ^((n ^ p) / (d ^ p), 1~root)
    else ^((d ^ (0.s - p)) / (n ^ (0.s - p)), 1~root)
}

// (a*b*c)^p =>> a^p * b^p * c^p
sRules.+(SymPow())("Power of product to product of powers"){
  PowP(ProdP('es @@ __*), 'expt)
}{ case (es: Seq[Sym], expt: Sym) =>
    **( { es.map(^(_, expt)) }:_* ) }

// (a^p1)^p2 = a^(p1*p2)
sRules.+(SymPow())("Nested powers multiply"){
  PowP(PowP('base, 'p1), 'p2)
}{ case (b: Sym, p1: Sym, p2: Sym) =>
    ^(b, **(p1, p2))
}

sRules.+(SymPow())("Power with a log as the exponent"){
  PowP('b, LogP('p, 'b))
}{ case (b: Sym, p: Sym) => p }

sRules.+(SymPow())("Power to a product with a log"){
  PowP('b, ProdP(LogP('p, 'b), 'rest @@ __*))
}{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
  SymPow(p, SymProd(rest:_*))
}

sRules.+(SymPow())("Power to a sum with a log"){
  PowP('b, SumP(LogP('p, 'b), 'rest @@ __*))
}{ case (b: Sym, p: Sym, rest: Seq[Sym]) =>
  SymProd(p, SymPow(b, SymProd(rest:_*)))
}

sRules.+(SymLog())("log(a^p) = p * log(a)"){
  LogP(PowP('powBase, 'expt), 'logBase)
}{ case (expt: Sym, logBase: Sym, powBase: Sym) =>
    **(expt, log(powBase, logBase))
}

sRules.+(SymLog())("log(a * b) =>> log(a) * log(b)"){
  LogP('prod @@ ProdP(__*), 'base)
}{ case (base: Sym, prod: SymProd) =>
    ++({ prod.exprs.map(log(_, base)) }:_*)
}

sRules.+(SymProd())("Multiplicative identity is 1"){
  ProdP()
}{ case () => 1.s }

sRules.+(SymProd())("Simplify product of a single number"){
  ProdP('a)
}{ case a: Sym => a }

sRules.+(SymProd())("Product containing 0 is 0"){
  ProdP(=?(0), __*)
}{ case () => 0 }

sRules.+(SymProd())("x*1 = x"){
  ProdP(=?(1), 'rest @@ __*)
}{ case rest: Seq[Sym] => **(rest:_*) }

sRules.+(SymProd())("Merge nested products"){
  ProdP('prod @@ ProdP(__*), 'rest @@ __*)
}{ case (prod: SymProd, rest: Seq[Sym]) =>
    SymProd({ prod.exprs ++ rest }:_*)
}

sRules.+(SymProd())("Distributive property"){
  ProdP(SumP('terms @@ __*), 'prod @@ __*)
}{ case (prod: Seq[Sym], terms: Seq[Sym]) =>
    SymSum({ terms.map{ e => SymProd({ e +: prod }:_*) } }:_*)
}

sRules.+(SymProd())("x^a * x^b = x^(a+b)"){
  ProdP(AsPowP('base, 'p1 @@ %?()), AsPowP('base, 'p2 @@ %?()), 'rest @@ __*)
}{ case (base: Sym, p1: SymR, p2: SymR, rest: Seq[Sym]) =>
    SymProd({ ^(base, (p1 + p2)) +: rest }:_*)
}

sRules.+(SymProd())("Multiply rational factors"){
  ProdP('a @@ %?(), 'b @@ %?(), 'rest @@ __*)
}{ case (a: SymR, b: SymR, rest: Seq[Sym]) =>
    SymProd({ (a * b) +: rest }:_*)
}

sRules.+(SymProd())("Multiply rational roots"){
  ProdP(PowP('b1 @@ %?(), /?(=?(1), 'r1)), PowP('b2 @@ %?(), /?(=?(1), 'r2)), 'rest @@ __*)
}{ case (b1: SymR, b2: SymR, r1: SymInt, r2: SymInt, rest: Seq[Sym]) =>
    val lcm = SymInt((r1.n * r2.n) / (r1.n gcd r2.n))
    val newBase = (b1 ^ SymInt(lcm.n / r1.n)) * (b2 ^ SymInt(lcm.n / r2.n))
    SymProd({ ^(newBase, 1~lcm) +: rest }:_*)
}

sRules.+(SymSum())("Additive identity is 0"){
  SumP()
}{ case () => 0.s }

sRules.+(SymSum())("Simplify sum of a single number"){
  SumP('a)
}{ case (a: Sym) => a }

sRules.+(SymSum())("Merge nested sums"){
  SumP('sum @@ SumP(__*), 'rest @@ __*)
}{ case (rest: Seq[Sym], sum: SymSum) =>
    SymSum({ sum.exprs ++ rest }:_*)
}

sRules.+(SymSum())("x*a? + x*b? = (a+b)*x"){
  SumP(
    First(ProdP('f1 @@ RatP(), 'u), 'u &@ 'f1 -> 1.s),
    First(ProdP('f2 @@ RatP(), 'u), 'u &@ 'f2 -> 1.s),
    'rest @@ __*)
}{ case (f1: SymR, f2: SymR, rest: Seq[SymR], u: Sym) =>
    SymSum({ **(f1 + f2, u) +: rest }:_*)
}

sRules.+(SymSum())("x*y*a? + x*y*b? = (a+b)*x*y"){
  SumP(
    ProdP(First('f1 @@ RatP(), ~~ &@ 'f1 -> 1.s), 'us @@ __*),
    ProdP(First('f2 @@ RatP(), ~~ &@ 'f2 -> 1.s), 'us @@ __*),
    'rest @@ __*)
}{ case (f1: SymR, f2: SymR, rest: Seq[SymR], us: Seq[Sym]) =>
    SymSum({ **({ (f1 + f2) +: us }:_*) +: rest }:_*)
}

sRules.+(SymSum())("Add rationals or similar products of rationals"){
  SumP(AsProdP('a @@ %?(), 'r @@ __*), AsProdP('b @@ %?(), 'r @@ __*), 'rest @@ __*)
}{ case (a: SymR, b: SymR, r: Seq[Sym], rest: Seq[Sym]) =>
    SymSum({ SymProd({ (a + b) +: r }:_*) +: rest }:_*)
}

sRules.+(SymPM())("Plus/minus 0 is 0"){ SymP(SymPM(0)) }{ case () => 0 }

def hasX(e: Sym): Boolean = e match {
  case SymVar('x) => true
  case e: SymConstant => false
  case e => LazyList(e.exprs:_*).map(hasX).find(_ == true).isDefined
}
def noX(e: Sym): Boolean = !hasX(e)

def hasxP(p: Pattern = __) = Satisfies(p, hasX)
def noxP(p: Pattern = __) = Satisfies(p, noX)

val aRules = new Rules()

aRules.+(SymSum())("Divide by common factor"){
  SumP(ProdP('h @@ Repeat(hasxP(), min=1), 'n @@ Repeat(noxP(), min=1)), 'rest @@ Repeat(noxP()))
}{ case (h: Seq[Sym], n: Seq[Sym], rest: Seq[Sym]) =>
  SymSum(SymProd(h:_*), SymProd(^(**(n:_*), -1), ++(rest:_*))).pipe(simplify)
}

def zero(e: Sym): Option[Sym] = zero(Seq(e), Nil)
def zero(es: Seq[Sym], old: Seq[Sym]): Option[Sym] = {
  println(f"Called with $es")
  LazyList(es:_*)
    // List of direct solutions
    .flatMap(zRules.first)
    // Option of the first valid solution in the list
    .headOption
    .map(simplify)
    // If there is a solution, turn it into a Some
    .map(Some(_))
    // If there is a Some(solution) return it, otherwise recurse
    .getOrElse{
      es.flatMap{ e => aRules.all(e)
        .filter(!old.contains(_))
        .filter(!es.contains(_))
      }.pipe{ newEs => if (newEs.isEmpty) None else zero(newEs, old ++ es) }
    }
}

val zRules = new Rules()

zRules.+(SymVar())("x = 0"){ =?('x) }{ case () => 0 }

zRules.+(SymSum())("x + a = 0"){
  SumP(XP, 'rest @@ __*)
}{ case rest: Seq[Sym] => SymProd(-1.s, SymSum(rest:_*)) }

zRules.+(SymProd())("x * a = 0"){
  ProdP(XP, __*)
}{ case () => 0 }

zRules.+(SymSum())("x^p + a => x +- (-a)^(1/p)"){
  AsSumP(PowP(XP, 'p @@ noxP()), 'rest @@ Repeat(noxP()))
}{ case (SymInt(n), r: Seq[Sym]) if (n % 2 == 0) => SymPM(SymPow(SymSum(r:_*), 1 ~ n))
  case (p: Sym, r: Seq[Sym]) => SymPow(SymProd(-1, SymSum(r:_*)), SymPow(p, -1))
}

val dRules = new Rules()

def derivative(e: Sym): Sym =
  dRules.first(e).map(simplify)
  .orElse{ dRules.first(simplify(e)).map(simplify) }
  .get

dRules.+(SymVar())("Derivative of x is 1"){ XP }{ case () => 1 }
dRules.+(0)("Derivative of a constant is 0"){ noxP() }{ case () => 0 }

dRules.+(SymSum())("d/dx u + v = du/dx + dv/dx"){
  SumP('es @@ __*)
}{ case es: Seq[Sym] => SymSum({ es.map(derivative) }:_*) }

dRules.+(SymProd())("d/dx c u = c u'"){
  ProdP('cs @@ Repeat(noxP(), min=1), 'us @@ Repeat(hasxP(), min=1))
}{ case (cs: Seq[Sym], us: Seq[Sym]) =>
  SymProd({ cs :+ derivative(simplify(SymProd(us:_*))) }:_*)
}

dRules.+(SymProd())("Product rule"){
  ProdP('a @@ hasxP(), 'bs @@ Repeat(hasxP(), min=1))
}{ case (a: Sym, bs: Seq[Sym]) =>
  SymSum(
    SymProd(a, derivative(simplify(SymProd(bs:_*)))),
    SymProd({ derivative(simplify(a)) +: bs }:_*)
  )
}

dRules.+(SymPow())("Power rule"){
  PowP(XP, 'p @@ noxP())
}{ case (p: Sym) => SymProd(p, SymPow('x, ++(p, -1))) }

dRules.+(SymPow())("d/dx e^u = u' e^u"){
  PowP(=?(E), 'p @@ hasxP())
}{ case p: Sym =>
  SymProd(derivative(p), SymPow(E, p))
}

dRules.+(SymPow())("n^u = e^(u ln(n))"){
  PowP('b, 'p @@ hasxP())
}{ case (b: Sym, p: Sym) =>
  derivative{ SymPow(E, simplify{ **(p, log(b)) }) }
}

dRules.+(SymLog())("d/dx ln(u) = u' / u"){
  LogP('u, =?(E))
}{ case u: Sym => SymProd(derivative(u), SymPow(u, -1)) }
