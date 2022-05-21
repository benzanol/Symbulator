package sympany

import scala.util.chaining._

/// Helpful functions
object Sym {
  def replaceExpr(expr: Sym, target: Sym, replacement: Sym): Sym =
    if (expr == target) replacement
    else expr.mapExprs(replaceExpr(_, target, replacement))
  
  def containsExpr(expr: Sym, target: Sym): Boolean =
    if (expr == target) true
    else expr.exprs.map(containsExpr(_, target)).contains(true)
  
  def noParens(str: String): String =
    if (str.startsWith("\\left(")) str.substring(6, str.length - 7)
    else if (str.head == '(') str.substring(1, str.length - 1)
    else str
  
  def combos[T](l1: Seq[Seq[T]], l2: Seq[T]): Seq[Seq[T]] =
    l1.flatMap{a => l2.map{b => a :+ b}}
  
  def allCombos[T](ls: Seq[T]*): Seq[Seq[T]] =
    ls.foldLeft(Seq(Seq[T]()))(combos[T])
  
  def ++(es: Sym*) = SymSum(Multiset.fromSeq(es))
  def +++(es: Seq[Sym]) = SymSum(Multiset.fromSeq(es))
  def **(es: Sym*) = SymProd(Multiset.fromSeq(es))
  def ***(es: Seq[Sym]) = SymProd(Multiset.fromSeq(es))
  def ^(base: Sym, expt: Sym) = SymPow(base, expt)
  def log(pow: Sym, base: Sym = SymE()) = SymLog(pow, base)
  def +-(e: Sym) = SymPM(e)
  def S(i: BigInt) = SymInt(i)
  def S(n: BigInt, d: BigInt) = SymR(n, d)
  def Pi = SymPi()
  def E = SymE()
  def X = SymVar('X)
  def V(s: Symbol) = SymVar(s)
}

object Multiset {
  def toSeq[T](map: Map[T, Int]): Seq[T] =
    map.flatMap{ case (a, n) => Seq.fill(n)(a) }.toSeq

  def fromSeq[T](seq: Seq[T]): Map[T, Int] =
    seq.groupBy(identity).map{ case (k, vs) => (k, vs.length) }.toMap
}

import Sym._


/// To Latex
object Latex {
  def isNegative(e: Sym): Option[Sym] = e match {
    case r: SymR if r.n < 0 => Some(SymR(-r.n, r.d))
    case p: SymProd => {
      val op = p.exprs.collect{ case r: SymR => r }.find(_.n < 0)
      if (op.isEmpty) None
      else Some( p.exprs.updated(p.exprs.indexOf(op.get), op.get.negative).pipe(Sym.***) )
    }
    case _ => None
  }

  def wrappedLatex(e: Sym, pow: Boolean = false): String = e match {
    case SymSum(_) | SymProd(_) => "\\left(" + toLatex(e) + "\\right)"
    case _: SymLog | _: SymPM if pow => "\\left(" + toLatex(e) + "\\right)"
    case _ => toLatex(e)
  }

  def toLatex(e: Sym): String = e.simple match {
    case SymFrac(n, d) if n < 0 => s"- \\frac{${-n}}{$d}"
    case SymFrac(n, d) => s"\\frac{$n}{$d}"
    case SymInt(n) => n.toString
    case SymPositiveInfinity() => "\\infty"
    case SymNegativeInfinity() => "-\\infty"
    case SymUndefined() => "\\NaN"
    case SymE() => "e"
    case SymPi() => "\\pi"
    case SymEquation(l, r) => s"${toLatex(l)} = ${toLatex(r)}"
    case SymVar(s) if s.name contains '/' =>
      s.name.split("/").pipe{ case Array(dy, dx) => s"\\frac{$dy}{$dx}" }
    case SymVar(s) => s.name

    case s: SymSum if isNegative(s.exprs(1)).isDefined =>
      s"${toLatex(s.exprs.head)} ${toLatex(Sym.+++(s.exprs.tail))}"
    case s: SymSum if s.exprs(1).isInstanceOf[SymPM] =>
      s"${toLatex(s.exprs.head)} ${toLatex(Sym.+++(s.exprs.tail))}"
    case s: SymSum => s"${toLatex(s.exprs.head)} + ${toLatex(Sym.+++(s.exprs.tail))}"

    case p: SymProd =>
      p.exprs.flatMap{
        case SymFrac(n, d) if n == 1 => Seq( ^(S(d), S(-1)) )
        case SymFrac(n, d) if d == 1 => Seq( S(n) )
        case SymFrac(n, d) => Seq( ^(S(d), S(-1)), S(n) )
        case other => Seq(other)
      }.partitionMap{
        case SymPow(b, p) if isNegative(p).isDefined =>
          Right(SymPow(b, isNegative(p).get))
        case other => Left(other)
      }.pipe{ case (ns: List[Sym], ds: List[Sym]) => List[List[Sym]](ns, ds) }
        .map{ es => if (es contains SymInt(-1)) ("- ", es.filter(_ != SymInt(-1))) else ("", es) }
        .map{ case (str, es) => es match {
          case List() => str + "1"
          case _ => str + ***(es).exprs.map{
            case e: SymSum => s"\\left( ${toLatex(e)} \\right)"
            case e => toLatex(e)
          }.mkString(" ")
        }}.pipe{
          case List(n: String, "1") => n
          case List(n: String, "- 1") => "- " + n
          case List(n: String, d: String) => s"\\frac{$n}{$d}"
        }

    case SymPow(SymSin(expr), expt) => s"\\sin^{$expt} ${wrappedLatex(expr)}"
    case SymPow(SymCos(expr), expt) => s"\\cos^{$expt} ${wrappedLatex(expr)}"

    case SymPow(base, expt) if isNegative(expt).isDefined =>
      s"\\frac{1}{${toLatex(SymPow(base, isNegative(expt).get))}}"
    case SymPow(base, SymFrac(p, r)) =>
      if (r == 2) s"\\sqrt{${toLatex(SymPow(base, S(p)))}}"
      else s"\\sqrt[$r]{${toLatex(SymPow(base, S(p)))}}"
    case SymPow(base, expt) => s"${wrappedLatex(base, true)}^{${toLatex(expt)}}"

    case SymLog(pow, base) => base match {
      case _: SymE => s"\\ln ${wrappedLatex(pow)}"
      case _ => s"\\log_{${toLatex(base)}} ${wrappedLatex(pow)}"
    }
    case SymSin(expr) => s"\\sin ${wrappedLatex(expr)}"
    case SymCos(expr) => s"\\cos ${wrappedLatex(expr)}"
    case SymPM(expr) => s"\\pm ${wrappedLatex(expr)}"
  }
}

/// Symbolic trait
trait Sym {
  def toLatex: String = Latex.toLatex(this)

  def exprs: Seq[Sym]
  def instance(args: Sym*): Sym

  def mapExprs(f: Sym => Sym): Sym =
    instance(exprs.map(f):_*)

  lazy val expand: Seq[Sym] =
    exprs.map(_.expand)
      .foldLeft(Seq(Seq[Sym]())){ (acc, seq: Seq[Sym]) =>
        acc.flatMap{a => seq.map{b => a :+ b}}
      }.map{es => this.instance(es:_*)}


  type Bind = (Symbol, Double)
  def approx(env: Bind*): Seq[Double] = Nil


  lazy val simple: Sym = math.Simplify.simplify(this)
  lazy val derive: Sym = math.Derivative.derive(this, 'x)
  lazy val solve: Seq[Sym] = math.Solve.solve(this, 'x)


  //def allHoles: Set[Sym] = exprHoles ++ extraHoles
  //def exprHoles: Set[Sym] = Set()
  //var extraHoles = Set[Sym] = Set()
  //def addHoles(newHoles: Set[Sym]): Unit =
  //  this.extraHoles = extraHoles ++ newHoles
  //def zeros: Set[Sym] = Set()
}

/// Special traits
trait SymConstant extends Sym {
  lazy val exprs = Nil
  def instance(args: Sym*) = this

  override def approx(env: Bind*) = Seq(value)
  def value: Double
}


trait SymOp extends Sym {
  def operation(vs: Double*): Double

  override def approx(env: Bind*): Seq[Double] =
    exprs.map(_.approx(env:_*))
      .foldLeft(Seq(Seq[Double]())){ (acc, seq: Seq[Double]) =>
        acc.flatMap{a => seq.map{b => a :+ b}}
      }.map{ds => this.operation(ds:_*)}
}

/// Equation
case class SymEquation(left: Sym = SymInt(0), right: Sym = SymInt(0)) extends Sym {
  lazy val exprs = Seq(left, right)
  def instance(args: Sym*) = SymEquation(args(0), args(1))

  override def toString = left.toString + " = " + right.toString
}

/// Variables
//implicit class ImplicitSymVar(orig: Symbol) extends SymVar(orig)

case class SymVar(symbol: Symbol = 'x) extends Sym {
  lazy val exprs = Nil
  def instance(args: Sym*) = this
  override lazy val expand = Seq(this)
  override def approx(env: Bind*) = env.find(_._1 == symbol).map(_._2).toSeq

  override def toString = symbol.name
}

/// Constants
case class SymDecimal(decimal: BigDecimal) extends SymConstant {
  override def toString = decimal.toString

  lazy val value = decimal.toDouble
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"

  lazy val value = Math.PI
}

case class SymE() extends SymConstant {
  override def toString = "E"

  lazy val value = Math.E
}

/// Rational Constants
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
  def n: BigInt
  def d: BigInt

  override def toString = f"$n/$d"

  lazy val value = n.toDouble / d.toDouble
  
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

/// Operations
case class SymSum(mset: Map[Sym, Int]) extends SymOp {
  lazy val exprs = Multiset.toSeq(mset)
  def instance(args: Sym*) = SymSum(Multiset.fromSeq(args))

  def operation(vs: Double*) = vs.sum

  override def toString = f"(+ " + exprs.mkString(" ") + ")"
}

case class SymProd(mset: Map[Sym, Int]) extends SymOp {
  lazy val exprs = Multiset.toSeq(mset)
    .groupBy{ _ match {
      case _: SymR => 1
      case _: SymConstant => 2
      case _: SymVar => 3
      case _ => 4
    }}.toList.sortWith{ (a, b) => a._1 < b._1 }
    .map(_._2).flatten.toSeq

  def instance(args: Sym*) = SymProd(Multiset.fromSeq(args))

  def operation(vs: Double*) = vs.product

  override def toString = f"(* " + exprs.mkString(" ") + ")"
}

case class SymPow(base: Sym = SymInt(1), expt: Sym = SymInt(1)) extends SymOp {
  lazy val exprs = Seq(base, expt)
  def instance(args: Sym*) = SymPow(args(0), args(1))

  def operation(vs: Double*) = Math.pow(vs(0), vs(1))

  override def toString = f"(^ $base $expt)"
}

case class SymLog(pow: Sym = SymInt(1), base: Sym = SymE()) extends SymOp {
  lazy val exprs = Seq(pow, base)
  def instance(args: Sym*) = SymLog(args(0), args(1))

  def operation(vs: Double*) = Math.log(vs(0)) / Math.log(vs(1))

  override def toString = if (base == SymE()) f"(ln $pow)" else f"(log $pow $base)"
}

case class SymPM(expr: Sym = SymInt(1)) extends Sym {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymPM(args.head)
  override lazy val expand = Seq( SymInt(1), SymInt(-1) ).flatMap{ n =>
    expr.expand.map{ e: Sym => **(n, e) }
  }

  override def approx(env: Bind*) =
    List(1, -1).flatMap{ n => expr.approx(env:_*).map(_ * n) }

  override def toString = f"(+- $expr)"
}

case class SymSin(expr: Sym) extends SymOp {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymSin(args.head)

  def operation(vs: Double*) = Math.sin(vs.head)
}

case class SymCos(expr: Sym) extends Sym {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymCos(args.head)

  def operation(vs: Double*) = Math.cos(vs.head)
}

