import scala.util.chaining._

trait Sym {
  def exprs: Seq[Sym]
  def mapExprs(f: Sym => Sym): Sym
  def sym = this
}

/// Special Symbolic Traits
trait SymConstant extends Sym {
  def exprs = Seq(this)
  def mapExprs(f: Sym => Sym) = this
}

trait SymUnordered extends Sym

/// Rationals
object SymR {
  def apply(n: BigInt, d: BigInt = 1): SymR = {
    val gcd: BigInt = n.abs gcd d.abs
    // 1 if d is positive, -1 if d is negative
    val one = d / d.abs

    if (d.abs / gcd == BigInt(1)) SymInt(one * n / gcd)
    else SymFrac(one * n / gcd, d.abs / gcd)
  }
}

trait SymR extends SymConstant {
  def d: BigInt
  def n: BigInt

  def inverse: SymR = SymR(d, n)
  def negative: SymR = SymR(-n, d)
  def +(o: SymR): SymR = SymR((n * o.d) + (o.n * d), d * o.d)
  def -(o: SymR): SymR = this + o.negative
  def *(o: SymR): SymR = SymR(n * o.n, d * o.d)
  def /(o: SymR): SymR = this * o.inverse
}

case class SymFrac(n: BigInt, d: BigInt) extends SymR

case class SymInt(n: BigInt) extends SymR {
  def d = BigInt(1)
  def s = this
  def ~(o: SymInt) = SymR(n, o.n)
}

implicit class ImplicitSymBigInt(val original: BigInt) extends SymInt(original)
implicit class ImplicitSymInt(val original: Int) extends SymInt(BigInt(original))

/// Composed Expressions
case class SymSum(exprs: Sym*) extends SymUnordered {
  def mapExprs(f: Sym => Sym) = SymSum(exprs.map(f):_*)
}

case class SymProd(exprs: Sym*) extends SymUnordered {
  def mapExprs(f: Sym => Sym) = SymProd(exprs.map(f):_*)
}

case class SymPow(base: Sym, expt: Sym) extends Sym {
  def exprs = Seq(base, expt)
  def mapExprs(f: Sym => Sym) = SymPow(f(base), f(expt))
}

/// Constants
case class SymPi() extends SymConstant
case class SymE() extends SymConstant
