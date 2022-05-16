package sympany.symbolics

import scala.util.chaining._

object Sym {
  def toMultiset[T](seq: Seq[T]): Map[T, Int] =
    seq.groupBy(identity).toList
      .map{ case (identity, list) => (identity, list.length) }
      .toMap

  def replaceExpr(expr: Sym, target: Sym, replacement: Sym): Sym =
    if (expr == target) replacement
    else expr.mapExprs(replaceExpr(_, target, replacement))

  def ++(es: Sym*) = SymSum(es:_*)
  def **(es: Sym*) = SymProd(es:_*)
  def #=(i: BigInt) = SymInt(i)
  def ^(base: Sym, expt: Sym) = SymPow(base, expt)
  def log(pow: Sym, base: Sym = SymE()) = SymLog(pow, base)
  def +-(e: Sym) = SymPM(e)
  def Pi = SymPi()
  def E = SymE()
  def X = SymVar('x)
  def V(s: Symbol) = SymVar(s)
}

import Sym._

trait Sym {
	type Env = Map[Symbol, Double]
  def approx(implicit env: Env): Double

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

//implicit class ImplicitSymVar(orig: Symbol) extends SymVar(orig)

case class SymDecimal(decimal: BigDecimal) extends SymConstant {
  override def toString = decimal.toString
  def approx(implicit env: Env) = decimal.toDouble
}

case class SymVar(symbol: Symbol = 'x) extends SymConstant {
  override def toString = symbol.name
  def s = this

  def approx(implicit env: Env) = env.applyOrElse(symbol,
		{ s: Symbol => throw new Exception(s"Variable $symbol not defined") ; 0 }
	)
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
  def approx(implicit env: Env) = n.toDouble / d.toDouble
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

//implicit class ImplicitSymBigInt(original: BigInt) extends SymInt(original)
//implicit class ImplicitSymInt(original: Int) extends SymInt(BigInt(original))

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
  override def approx(implicit env: Env) = Double.NaN
  def n = 0
  def d = 0
}
case class SymPositiveInfinity() extends SymR {
  override def toString = "Inf"
  override def approx(implicit env: Env) = Double.PositiveInfinity
  def n = 1
  def d = 0
}
case class SymNegativeInfinity() extends SymR {
  override def toString = "-Inf"
  override def approx(implicit env: Env) = Double.NegativeInfinity
  def n = -1
  def d = 0
}

case class SymSum(exprs: Sym*) extends SymUnordered {
  override def toString = f"(+ " + exprs.mkString(" ") + ")"
  override def id = (SymSum, toMultiset(exprs.map(_.id)))
  def approx(implicit env: Env) = exprs.map(_.approx).sum
  def mapExprs(f: Sym => Sym) = SymSum(exprs.map(f):_*)
}

case class SymProd(exprs: Sym*) extends SymUnordered {
  override def toString = f"(* " + exprs.mkString(" ") + ")"
  override def id = (SymProd, toMultiset(exprs.map(_.id)))
  def approx(implicit env: Env) = exprs.map(_.approx).product
  def mapExprs(f: Sym => Sym) = SymProd(exprs.map(f):_*)
}

case class SymPow(base: Sym = SymInt(1), expt: Sym = SymInt(1)) extends Sym {
  override def toString = f"(^ $base $expt)"
  def approx(implicit env: Env) = Math.pow(base.approx, expt.approx)
  def exprs = Seq(base, expt)
  def mapExprs(f: Sym => Sym) = SymPow(f(base), f(expt))
}

case class SymLog(pow: Sym = SymInt(1), base: Sym = SymE()) extends Sym {
  override def toString = if (base == SymE()) f"(ln $pow)" else f"(log $pow $base)"
  def approx(implicit env: Env) = Math.log(pow.approx) / Math.log(base.approx)
  def exprs = Seq(pow, base)
  def mapExprs(f: Sym => Sym) = SymLog(f(pow), f(base))
}

case class SymPM(expr: Sym = SymInt(1)) extends Sym {
  override def toString = f"(+- $expr)"
  def approx(implicit env: Env) = expr.approx
  def exprs = Seq(expr)
  def mapExprs(f: Sym => Sym) = SymPM(f(expr))
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"
  def approx(implicit env: Env) = Math.PI
}
case class SymE() extends SymConstant {
  override def toString = "E"
  def approx(implicit env: Env) = Math.E
}
