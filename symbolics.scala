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

trait Sym {
  def approx: Double
}

trait SymR extends Sym {
  override lazy val approx = n.toDouble / d.toDouble
  def n: Int
  def d: Int

  lazy val ratioGcd: Int = n gcd d
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

case class SymFrac(n: Int, d: Int = 1) extends SymR {
  def gcd(o: SymR): SymR = SymFrac(n gcd o.n, d lcm o.d)
  def lcm(o: SymR): SymR = SymFrac((n * o.d) lcm (o.n * d), d * o.d)
}

case class SymInfinity(negative: Boolean = false) extends SymR {
  def n = 1
  def d = 0

  def gcd(o: SymR) = o
  def lcm(o: SymR) = this
}

case class SymUndefined() extends SymR {
  def n = 0
  def d = 0

  def gcd(o: SymR) = this
  def lcm(o: SymR) = this
}

case class SymSum(exprs: Sym*) extends Sym {
  lazy val approx = exprs.map(_.approx).sum
}

case class SymProd(exprs: Sym*) extends Sym {
  lazy val approx = exprs.map(_.approx).product
}

case class SymPow(base: Sym, pow: Sym) extends Sym {
  lazy val approx = math.pow(base.approx, pow.approx)
}
