object SymUtils {
  def primeFactors(num: Int): Map[Int, Int] = {
    val m = scala.collection.mutable.Map[Int, Int]()
    var n = num
    for (f <- 2 to n) {
      var ct = 0
      while (n % f == 0) { n /= f ; ct += 1 }
      if (ct > 0) m += (f -> ct)
    }
    return m.toMap
  }
}


/* short for Symbolic Coefficient (a scalar)
 - Each Symbolic Expression should have a corresponding coefficient,
 - by default 1.
 - What makes Symbolic Coefficients special is that they should always
 - be added together if given the opportunity. For example,
 - 3 root 2 + 1/3 root 2 always should become 10/3 root 2, while
 - pi root 2 + e root 2 shouldn't necessarily become (pi+e) root 2,
 - which is why pi and e are not considered coefficients.
 - n and d are the numerator and denominator
 */

trait SymC {
  def approx: Double
  def n: Int
  def d: Int
  def simplify: SymC = this
  
  def ==(o: SymC): Boolean =
    o.simplify.n == simplify.n && o.simplify.d == simplify.d
  def ==(o: Int): Boolean =
    simplify.d == 1 && simplify.n == o
  
  def +(b: SymC): SymC =
    SymCFrac(this.n*b.d + b.n*this.d, this.d * b.d)
  def *(b: SymC): SymC =
    SymCFrac(this.n * b.n, this.d*b.d)
}

case class SymCFrac(n: Int = 1, d: Int = 1) extends SymC {
  lazy val approx = n.toDouble / d.toDouble
  lazy val gcd = BigInt(n).gcd(d).toInt
  override lazy val simplify: SymC = SymCFrac(n / gcd, d / gcd)
  
  override lazy val toString =
    if (d == 1) n.toString
    else f"${n.toString} / ${d.toString}"
}

// Make integers automatically become Symbolic Coefficients
implicit class SymCInt(num: Int) extends SymC {
  lazy val n = num
  lazy val d = 1
  lazy val approx = num.toDouble
  override lazy val toString = num.toString
}



// Short for Symbolic
trait Sym {
  def approx: Double
  def simplify: Sym = this
  def ==(expr: Sym): Boolean = false
  def c: SymC
  def withC(c: SymC): Sym
}

case class SymUnit(c: SymC = 1) extends Sym {
  def withC(newC: SymC) = SymUnit(newC)
  lazy val approx = c.approx
  override lazy val toString = c.toString
  
  override def ==(expr: Sym) = expr match {
    case SymUnit(c1) => c == c1
    case _ => false
  }
}

case class SymRoot(num: Sym, root: Sym = SymUnit(2), c: SymC = 1) extends Sym {
  def withC(newC: SymC) = SymRoot(num, root, newC)
  lazy val approx = c.approx * math.pow(num.approx, 1.0 / root.approx)
  override lazy val toString = {if (c == 1) "" else c.toString + " "}
    .+(if (root == SymUnit(2)) "" else root.toString)
    .+("√" + num.toString)
  
  override def ==(expr: Sym) = expr match {
    case SymRoot(n2, r2, c2) => (num==n2) && (root==r2) && (c==c2)
    case _ => false
  }
}

case class SymProduct(exprs: Seq[Sym], c: SymC = 1) extends Sym {
  def withC(newC: SymC) = SymProduct(exprs, newC)
  lazy val approx = exprs.foldLeft(c.approx)(_ * _.approx)
  override lazy val simplify =
    SymProduct(exprs.filter{_ match { case u: SymUnit => false case _ => true }}
      .map(_.withC(1)),
      exprs.foldLeft(c)(_ * _.c).simplify)
}

case class SymSum(exprs: Seq[Sym], c: SymC = 1) extends Sym {
  def withC(newC: SymC) = SymSum(exprs, newC)
  lazy val approx = exprs.foldLeft(c.approx)(_ + _.approx)

}

SymProduct(List(
  SymUnit(SymCFrac(1, 2)),
  SymRoot(SymUnit(2), SymUnit(3), 2),
  SymUnit(5),
  SymRoot(SymUnit(2), SymUnit(3), 3)
)).simplify


List(
  SymUnit(SymCFrac(1, 2)),
  SymRoot(SymUnit(2), SymUnit(3), 2),
  SymUnit(5),
  SymRoot(SymUnit(2), SymUnit(3), 3)
