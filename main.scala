import scala.util.chaining._

trait Sym {
  def approx: Double
  lazy val s: Sym = this
}

implicit class SymMultiset[T](val m: Map[T, Int]) {
  override def toString = m.toList.sortWith(_._2 < _._2)
    .map{t => f"${t._2}(${t._1})"}.mkString(", ")

  def ==(o: SymMultiset[T]): Boolean = m == o.m

  def zipNums(o: SymMultiset[T], f: (Int, Int) => Int): SymMultiset[T] =
    SymMultiset((this.m.keys ++ o.m.keys).toList
      .map{k => (k, f(this.m.getOrElse(k, 0), o.m.getOrElse(k, 0)))}
      .filter(_._2 != 0)
      .toMap)

  def ++(o: SymMultiset[T]) = this.zipNums(o, _ + _)
  def --(o: SymMultiset[T]) = this.zipNums(o, _ - _)
  def &&(o: SymMultiset[T]) = this.zipNums(o, _ min _)
  def ||(o: SymMultiset[T]) = this.zipNums(o, _ max _)

  def keys = m.keys
  def counts = m.toList.map(_._2)
  def toList = m.toList
}

// Rationals

trait SymR extends Sym {
  override lazy val approx = n.toDouble / d.toDouble
  def n: Int
  def d: Int
  def sign: Int = if ((n < 0) == (d < 0)) 1 else -1

  lazy val myGcd = n gcd d
  override lazy val s: SymR =
    if (d == 0 && n == 0) SymUndefined()
    else if (d == 0) SymInfinity(n < 0)
    else if (d.abs/myGcd == 1) SymInt(this.sign * n.abs/myGcd)
    else SymFrac(this.sign * n.abs/myGcd, d.abs/myGcd)

  def inverse = SymFrac(d, n).s
  def ==(o: SymR) = (s.n == o.s.n) && (s.d == o.s.d)
  def +(o: SymR) = SymFrac(s.n*o.s.d + o.s.n*s.d, s.d * o.s.d).s
  def -(o: SymR) = SymFrac(s.n*o.s.d - o.s.n*s.d, s.d * o.s.d).s
  def *(o: SymR) = SymFrac(n*o.n, d*o.d).s
  def /(o: SymR) = (this * o.inverse).s
  def **(p: Int) = SymFrac(math.pow(n, p).toInt, math.pow(d, p).toInt).s

  def <(o: SymR): Boolean = (s.n * o.d) < (o.s.n * d)
  def >(o: SymR): Boolean = (s.n * o.d) > (o.s.n * d)
  def <=(o: SymR): Boolean = (s.n * o.d) <= (o.s.n * d)
  def >=(o: SymR): Boolean = (s.n * o.d) >= (o.s.n * d)

  def min(o: SymR): SymR = if (this <= o) this else o
  def max(o: SymR): SymR = if (this >= o) this else o
}

case class SymUndefined() extends SymR {
  def n = 0
  def d = 0
}

case class SymInfinity(negative: Boolean = false) extends SymR {
  def n = 1
  def d = 0
}

case class SymFrac(n: Int, d: Int = 1) extends SymR {
  override def toString = f"($n/$d)"

  def gcd(o: SymR): SymR = SymFrac(n gcd o.n, d lcm o.d)
  def lcm(o: SymR): SymR = SymFrac((n * o.d) lcm (o.n * d), d * o.d)
}

case class SymInt(n: Int) extends SymR {
  override def toString = n.toString
  def d = 1

  lazy val primeFactors: SymMultiset[Int] = {
    var num = n.abs
    var f = 2
    var map = scala.collection.mutable.Map[Int, Int]()
    while (num > 1) {
      var count = 0
      while (num % f == 0) {count += 1 ; num /= f}
      if (count > 0) map += (f -> count)
      f += 1
    }
    SymMultiset[Int](map.toMap)
  }

  def gcd(o: Int): Int = (this.primeFactors && o.primeFactors).toList
    .foldLeft(1){(acc, f) => acc * math.pow(f._1, f._2).toInt}
  def lcm(o: Int): Int = (n * o) / (n gcd o)
}

implicit class ImplicitSymInt(val num: Int) extends SymInt(num)

// Composed Expressions

object SymProd {
  // Separate for the purpose of adding
  def asProduct(o: Sym): (SymR, Set[Sym]) = o match {
    case SymProd(es) => es.partition(_.isInstanceOf[SymR])
        .pipe{t => (t._1.asInstanceOf[List[SymR]].foldLeft(1: SymR)(_ * _), t._2.toSet)}
    case e: SymR => (e, Set[Sym]())
    case e: Sym => (SymInt(1), Set(e))
  }
}

object SymPow {
  // Separate for the purpose of multiplying
  def asPower(o: Sym): SymPow = o match {
    case SymPow(base, power: SymR) => SymPow(base, power)
    case _ => SymPow(o, 1)
  }

  // (Outside, inside)
  // num^(1/root) = ._1 * ._2^(1/root)
  def separateRoot(num: Int, root: Int): (Int, Int) =
    num.primeFactors.toList.foldLeft((1, 1)){(acc, t) =>
      (acc._1 * math.pow(t._1, t._2 / root).toInt, acc._2 * math.pow(t._1, t._2 % root).toInt)}
}

case class SymProd(exprs: Seq[Sym]) extends Sym {
  lazy val approx = exprs.map(_.approx).product

  override lazy val s = {
    // (Rational, (Base, Root), Map(Expression -> Power))
    val tuple = exprs.map(_.s)
    // Merge any nested products
      .foldLeft(List[Sym]()){(acc, e) => e match {
        case SymProd(es) => acc ++ es
        case _ => acc :+ e
      }}.map(SymPow.asPower(_))
      .foldLeft((1: SymR, (1: SymR, 1: Int), Map[Sym, SymR]())){(a, e) => e match {
        case SymPow(b: SymR, SymInt(1)) => (a._1 * b, a._2, a._3)
        case SymPow(b: SymR, SymFrac(1, root: Int)) => (root lcm a._2._2).pipe{lcm =>
          (a._1, ((a._2._1 ** (lcm/a._2._2)) * (b ** (lcm/root)), lcm), a._3)
        }
        case SymPow(b, p: SymR) => (a._1, a._2, a._3.updated(b, a._3.getOrElse(b, SymInt(0)) + p))
        case _ => {println(f"ERROR: $e") ; a}
      }}

    val coRoot: (SymR, SymPow) = SymPow(tuple._2._1, tuple._2._2.inverse).s match {
      case SymProd(List(n: SymR, p: SymPow)) => (n, p)
      case p: SymPow => (SymInt(1), p)
    }

    var newExprs: List[Sym] = tuple._3.toList.map{t => t._2 match {
      case SymInt(0) => SymInt(1)
      case SymInt(1) => t._1
      case p: SymR => SymPow(t._1, p)
    }}.filter(_ != SymInt(1))

    if (coRoot._2.base != SymInt(1)) newExprs +:= coRoot._2
    if (tuple._1 * coRoot._1 != (1: SymR)) newExprs +:= tuple._1 * coRoot._1

    newExprs match {
      case Nil => SymInt(1)
      case List(e) => e
      case _ => SymProd(newExprs)
    }
  }
}

case class SymPow(base: Sym, pow: Sym) extends Sym {
  lazy val approx = math.pow(base.approx, pow.approx)

  override lazy val s = (base.s, pow.s) match {
    case (b: SymR, SymInt(p)) => SymFrac(math.pow(b.n, p).toInt, math.pow(b.d, p).toInt).s
    case (b: SymFrac, SymFrac(1, root)) => {
      val tN = SymPow.separateRoot(b.n, root)
      val tD = SymPow.separateRoot(b.d, root)
      SymFrac(tN._1, tD._1).s match {
        case SymInt(1) => SymPow(SymFrac(tN._2, tD._2).s, SymFrac(1, root))
        case o: SymR => SymProd(List(o, SymPow(SymFrac(tN._2, tD._2).s, SymFrac(1, root))))
      }
    }
    case (b: SymR, SymFrac(p, root)) => SymPow(SymPow(b, p), SymFrac(1, root)).s
    case _ => this
  }
}

case class SymSum(exprs: Seq[Sym]) extends Sym {
  lazy val approx = exprs.map(_.approx).sum
}

// Constance
case class SymPi() extends Sym {
  def approx = math.Pi
}
