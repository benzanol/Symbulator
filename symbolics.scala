import scala.util.chaining._

implicit class SymMultiset[T](val m: Map[T, SymInt]) {
  override def toString = m.toList.sortWith(_._2 < _._2)
    .map{t => f"${t._2}(${t._1})"}.mkString(", ")

  def ==(o: SymMultiset[T]): Boolean = m == o.m

  def zipNums(o: SymMultiset[T], f: (SymInt, SymInt) => SymInt): SymMultiset[T] =
    SymMultiset((this.m.keys ++ o.m.keys).toList
      .map{k => (k, f(this.m.getOrElse(k, SymInt(0)), o.m.getOrElse(k, SymInt(0))))}
      .filter(_._2 != SymInt(0))
      .toMap)

  def ++(o: SymMultiset[T]) = this.zipNums(o, _ + _)
  def --(o: SymMultiset[T]) = this.zipNums(o, _ - _)
  def &&(o: SymMultiset[T]) = this.zipNums(o, _ min _)
  def ||(o: SymMultiset[T]) = this.zipNums(o, _ max _)

  def keys = m.keys
  def counts = m.toList.map(_._2)
  def toList = m.toList
}

trait Sym

trait SymR extends Sym {
  def n: SymInt
  def d: SymInt

  lazy val ratioGcd: SymInt = n gcd d
  lazy val inverse = SymFrac(d, n)
}

case class SymInt(int: Int) extends SymR {
  def n = this
  def d = 1
  def toInt = int

  def +(o: SymInt) = SymInt((int: Int) + (o.int: Int))
  def -(o: SymInt) = SymInt((int: Int) - (o.int: Int))
  def *(o: SymInt) = SymInt((int: Int) * (o.int: Int))
  def /(o: SymInt) = SymInt((int: Int) / (o.int: Int))
  def %(o: SymInt) = SymInt((int: Int) % (o.int: Int))
  def ^(o: SymInt) = SymInt(math.pow(int, o.int).toInt)
  def min(o: SymInt) = SymInt(math.min(int, o.int))
  def max(o: SymInt) = SymInt(math.max(int, o.int))
  def abs = if (this >= 0) this else SymInt(math.abs(4))

  def ==(i: Int) = (int == i)
  def ==(o: SymInt) = (int == o.int)
  def <(o: SymInt) = (int: Int) < (o.int: Int)
  def >(o: SymInt) = (int: Int) > (o.int: Int)
  def <=(o: SymInt) = (int: Int) <= (o.int: Int)
  def >=(o: SymInt) = (int: Int) >= (o.int: Int)

  def gcd(o: SymInt): SymInt = (this.primeFactors && o.primeFactors).toList
    .foldLeft(SymInt(1)){(acc, f) => acc * (f._1 ^ f._2)}
  def lcm(o: SymInt): SymInt = (this * o) / (this gcd o)

  lazy val primeFactors: SymMultiset[SymInt] = {
    var num = math.abs(int)
    var f = 2
    var map = scala.collection.mutable.Map[SymInt, SymInt]()
    while (num > 1) {
      var count = 0
      while (num % f == 0) {count += 1 ; num /= f}
      if (count > 0) map += (SymInt(f) -> SymInt(count))
      f += 1
    }
    SymMultiset[SymInt](map.toMap)
  }
}

implicit class ImplicitSymInt(val original: Int) extends SymInt(original)

case class SymFrac(n: SymInt, d: SymInt = 1) extends SymR {
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

case class SymSum(exprs: Sym*) extends Sym

case class SymProd(exprs: Sym*) extends Sym

case class SymPow(base: Sym, pow: Sym) extends Sym
