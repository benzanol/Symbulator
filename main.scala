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
 - It is a trait and not a class so that regular integers can be
 - implicitly made to become (partially atleast) a SymC
 - The limitation is that 1 == SymCInt(1) doesn't work, even though
 - SymCInt(1) == 1 works just fine
 - (can't figure out how to override the int's == operator)
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



case class Sym(e: SymE = SymUnit(), c: SymC = SymCInt(1)) {
  lazy val approx: Double = e.approx * c.approx
  def ==(s: Sym): Boolean = (e == s.e) && (c == s.c)
  override lazy val toString = e match {
    case SymUnit() => c.toString
    case _ => (if (c == SymCInt(1)) "" else c.toString + " ") + e.toString
  }
  def symplify = Sym(e.simplify.e, c * e.simplify.c)
}

// Short for Symbolic
trait SymE {
  def approx: Double
  lazy val simplify: Sym = Sym(this)
  def ==(expr: Sym): Boolean = false
}

case class SymUnit() extends SymE {
  lazy val approx = 1
  override lazy val toString = "U"
  
  def ==(expr: SymE) = expr match {
    case SymUnit() => true
    case _ => false
  }
}

case class SymRoot(num: Sym, root: Sym = Sym(c=2)) extends SymE {
  lazy val approx = math.pow(num.approx, 1.0 / root.approx)
  override lazy val toString =
    (if (root == Sym(c=2)) "" else root.toString) + "√" + num.toString
}

case class SymProduct(exprs: Seq[Sym]) extends SymE {
  lazy val approx = exprs.foldLeft(1.0)(_ * _.approx)
  override lazy val simplify =
    Sym(SymProduct(exprs.map(_.e)
      .filter{_ match { case SymUnit() => false case _ => true }}
      .map{exp => Sym(exp)}),
      exprs.foldLeft(1: SymC)(_ * _.c).simplify)
}

