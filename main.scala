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
  override lazy val approx = sign.toDouble * n.toDouble / d.toDouble
  def n: Int
  def d: Int
  def negative: Boolean = (n < 0) != (d < 0)
  def sign: Int = if (negative) -1 else 1

  def add(o: Sym) = o match {
    case o: SymR => Some(this + o)
    case _ => None
  }
  def mult(o: Sym) = o match {
    case o: SymR => Some(this * o)
    case _ => None
  }

  lazy val myGcd = n gcd d
  override lazy val s: SymR =
    if (d == 0 && n == 0) SymUndefined()
    else if (d == 0) SymInfinity(n < 0)
    else if (d.abs/myGcd == 1) SymInt(n.abs/myGcd, (sign*n < 0 != d < 0))
    else SymFrac(n.abs/myGcd, d.abs/myGcd, (sign*n < 0 != d < 0))

  def inverse = SymFrac(d, n, negative).s
  def ==(o: SymR) = (s.n == o.s.n) && (s.d == o.s.d)
  def +(o: SymR) = SymFrac(s.n*s.sign*o.s.d + o.s.n*o.s.sign*s.d, s.d * o.s.d).s
  def -(o: SymR) = SymFrac(s.n*s.sign*o.s.d - o.s.n*o.s.sign*s.d, s.d * o.s.d).s
  def *(o: SymR) = SymFrac(sign*o.sign*n*o.n, d*o.d).s
  def /(o: SymR) = (this * o.inverse).s
  def **(p: Int) = SymFrac(math.pow(n, p).toInt, math.pow(d, p).toInt).s

  def <(o: SymR): Boolean = (s.n*s.sign * o.d) < (o.s.n*o.s.sign * d)
  def >(o: SymR): Boolean = (s.n*s.sign * o.d) > (o.s.n*o.s.sign * d)
  def <=(o: SymR): Boolean = (s.n*s.sign * o.d) <= (o.s.n*o.s.sign * d)
  def >=(o: SymR): Boolean = (s.n*s.sign * o.d) >= (o.s.n*o.s.sign * d)

  def min(o: SymR): SymR = if (this <= o) this else o
  def max(o: SymR): SymR = if (this >= o) this else o
}

case class SymUndefined() extends SymR {
  def n = 0
  def d = 0
}

case class SymInfinity(override val negative: Boolean = false) extends SymR {
  def n = 1
  def d = 0
}

case class SymFrac(n: Int, d: Int = 1, override val negative: Boolean = false) extends SymR {
  override def toString = f"($n/$d)"

  def gcd(o: SymR): SymR = SymFrac(n gcd o.n, d lcm o.d)
  def lcm(o: SymR): SymR = SymFrac((n * o.d) lcm (o.n * d), d * o.d)
}

case class SymInt(n: Int, override val negative: Boolean = false) extends SymR {
  override def toString = n.toString
  def d = 1

  override lazy val s =
    if (n < 0) SymInt(n.abs, negative = true)
    else this

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

// Composed expressions

case class SymProd(exprs: Seq[Sym]) extends Sym {
  lazy val approx = exprs.map(_.approx).product

  def add(o: Sym) = None
  def mult(o: Sym) = o.s match {
    case SymProd(es) => Some(SymProd(exprs ++ es).s)
    case e => Some(SymProd(exprs :+ e).s)
  }

  lazy val coefficient = separate._1
  lazy val identity = separate._2
  lazy val separate = s match {
    case SymProd(es) => es.partition(_ match { case e: SymR => true case _ => false })
        .pipe{t => (t._1.asInstanceOf[List[SymR]].foldLeft(1: SymR)(_ * _), t._2.toSet)}
    case e: SymR => (e, Set[Sym]())
    case e: Sym => (SymInt(1), Set(e))
  }

  override lazy val s = {
    var newExprs = List[Sym]()
    var queue = exprs
    while (!queue.isEmpty) {
      // i should go from 1-queue.length to -1, which negated are the indices of the queue (skipping 0),
      // and then from 0 to newExprs.length-1, which are all of the indices of newExprs
      var i = 1 - queue.length
      while (i < newExprs.length)
        queue.head mult {if (i < 0) queue(-i) else newExprs(i)} match {
          case Some(prod) => {
            if (i < 0) queue = queue.take(-i) ++ queue.drop(-i + 1)
            else newExprs = newExprs.take(i) ++ newExprs.drop(i + 1)
            queue :+= prod
            i = newExprs.length + 1
          }
          case None => i += 1
        }
      if (i == newExprs.length) newExprs :+= queue.head
      queue = queue.tail
    }
    newExprs match {
      case Nil => SymInt(1)
      case List(e) => e
      case _ => SymProd(newExprs)
    }
  }
}

case class SymSum(exprs: Seq[Sym]) extends Sym {
  def approx = exprs.map(_.approx).sum
  def simplify =
    }

// Constance
case class SymPi() extends Sym {
  def approx = math.Pi
  def add(o: Sym) = o match {
    case p: SymPi => Some(SymProd(List(2, SymPi())))
    case p: SymProd if (p.identity == Set(SymPi())) =>
      Some(SymProd(List(p.coefficient + 1, SymPi())))
    case _ => None
  }

  def mult(o: Sym) = None
}
