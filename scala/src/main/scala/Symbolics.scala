package sympany

import scala.util.chaining._
import scala.collection.mutable

import sympany.math._

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

  // List(x, pi, x, x, 7), ** --> Set(**(x, 3), pi, 7)
  def exprSet(es: Seq[Sym], f: (Sym, Int) => Sym): Set[Sym] =
    es.groupBy(identity).map{
      case (e, Seq(_)) => e
      case (e, seq) => f(e, seq.length)
    }.toSet

  def ++(es: Sym*) = +++(es)
  def +++(es: Seq[Sym]) =
    es.groupBy(identity).map{
      case (e, Seq(_)) => e
      case (e, seq) => **(e, seq.length)
    }.toSet.pipe(SymSum)

  def **(es: Sym*) = ***(es)
  def ***(es: Seq[Sym]) =
    es.groupBy(identity).map{
      case (e, Seq(_)) => e
      case (e, seq) => ^(e, seq.length)
    }.toSet.pipe(SymProd)

  def ^(base: Sym, expt: Sym) = SymPow(base, expt)
  def log(pow: Sym, base: Sym = SymE()) = SymLog(pow, base)
  def +-(e: Sym) = SymPM(e)
  def S(i: BigInt) = SymInt(i)
  def S(n: BigInt, d: BigInt) = SymR(n, d)
  def Pi = SymPi()
  def E = SymE()
  def X = SymVar('*)
  def V(s: Symbol) = SymVar(s)

  implicit class ImplicitSymBigInt(_b: BigInt) extends SymInt(_b)
  implicit class ImplicitSymInt(_i: Int) extends SymInt(BigInt(_i))

  implicit class ImplicitSymVar(_s: Symbol) extends SymVar(_s)
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
    case SymSum(_) => "\\left(" + toLatex(e) + "\\right)"
    case SymProd(_) => toLatex(e).pipe{ l =>
      if (l.startsWith("\\frac") && !pow) l
      else ("\\left(" + toLatex(e) + "\\right)")
    }
    case _: SymLog | _: SymPM if pow => "\\left(" + toLatex(e) + "\\right)"
    case _ => toLatex(e)
  }

  def toLatex(e: Sym): String = math.Simplify.simplify(e) match {
    case SymFrac(n, d) if n < 0 => s"- \\frac{${-n}}{$d}"
    case SymFrac(n, d) => s"\\frac{$n}{$d}"
    case SymInt(n) => n.toString
    case SymPositiveInfinity() => "\\infty"
    case SymNegativeInfinity() => "-\\infty"
    case SymUndefined() => "\\NaN"
    case SymE() => "e"
    case SymPi() => "\\pi"
    case SymVar('*) => "x"
    case SymVar(s) if s.name contains '/' =>
      s.name.split("/").pipe{ case Array(dy, dx) => s"\\frac{$dy}{$dx}" }
    case SymVar(s) => s.name

    case s: SymSum if isNegative(s.sortedExprs(1)).isDefined =>
      s"${toLatex(s.sortedExprs.head)} ${toLatex(Sym.+++(s.sortedExprs.tail))}"
    case s: SymSum if s.sortedExprs(1).isInstanceOf[SymPM] =>
      s"${toLatex(s.sortedExprs.head)} ${toLatex(Sym.+++(s.sortedExprs.tail))}"
    case s: SymSum => s"${toLatex(s.sortedExprs.head)} + ${toLatex(Sym.+++(s.sortedExprs.tail))}"

    case p: SymProd =>
      p.sortedExprs.flatMap{ // Split up fractions into the top and bottom component
        case SymFrac(n, d) if n == 1 => Seq( ^(S(d), S(-1)) )
        case SymFrac(n, d) if d == 1 => Seq( S(n) )
        case SymFrac(n, d) => Seq( ^(S(d), S(-1)), S(n) )
        case other => Seq(other)
      }.partitionMap{ // Create 2 lists for factors on the top and bottom of the equation
        case SymPow(b, p) if isNegative(p).isDefined =>
          Right(SymPow(b, isNegative(p).get))
        case other => Left(other)
          // Turn the tuple of lists into a length 2 list of lists so it can be iterated over
      }.pipe{ case (ns: List[Sym], ds: List[Sym]) => List[List[Sym]](ns, ds) }
      // Add a minus sign to the beginning if -1 is in the factor list
        .map{ es => if (es contains SymInt(-1)) ("- ", es.filter(_ != SymInt(-1))) else ("", es) }
        .map{ case (str, es) => es match {
          // If there are no factors other than -1, add 1 to the string after the sign
          case List() => str + "1"
          // Concatenate all the factors separated by spaces
          case _ => str + ***(es).sortedExprs.map{
            case e: SymSum => s" \\quad ( ${toLatex(e)} ) \\quad "
            // On certain equations, the proper left and right brackets don't appear (mathquill issue)
            //case e: SymSum => s" \\left( ${toLatex(e)} \\right) "
            case e => toLatex(e)
          }.mkString(" ")
        }}.pipe{
          // If the denominator is 1 or -1, don't display as a fraction
          case List(n: String, "1") => n
          case List(n: String, "- 1") => "- " + n
          case List(n: String, d: String) =>
            if (n.startsWith("-")) s"- \\frac{${n.tail}}{$d}"
            else s"\\frac{$n}{$d}"
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
    case SymTan(expr) => s"\\tan ${wrappedLatex(expr)}"
    case SymASin(expr) => s"\\sin^{-1} ${wrappedLatex(expr)}"
    case SymACos(expr) => s"\\cos^{-1} ${wrappedLatex(expr)}"
    case SymATan(expr) => s"\\tan^{-1} ${wrappedLatex(expr)}"

    case SymPM(expr) => s"\\pm ${wrappedLatex(expr)}"

    case SymEquation(l, r) => s"${toLatex(l)} = ${toLatex(r)}"
    case SymVertical(x) => s"x = ${toLatex(x)}"

    // Can't use \int because it shows gray boxes for definite limits
    case SymIntegral(sub) => s"∫ ${wrappedLatex(sub)}"

    case SymPoint(x, y) =>
      ("(" + x.toLatex + ", \\quad \\quad " + y.toLatex + ")")
  }
}

/// Symbolic trait
trait Sym {
  def toLatex: String = Latex.toLatex(this)
  def size: Int = 1 + this.exprs.map(_.size).sum

  def exprs: Seq[Sym]
  def instance(args: Sym*): Sym

  def mapExprs(f: Sym => Sym): Sym = instance(exprs.map(f):_*)
  def replaceExpr(t: Sym, r: Sym) = Sym.replaceExpr(this, t, r)
  def isExplicit: Boolean = this match {
    case SymVar('x) => true
    case _: SymVar => false
    case _: SymEquation => false
    case e => e.exprs.find(!_.isExplicit).isEmpty
  }

  // Convert a function with multiple curves (eg plus-minus) to a list of single curves
  lazy val expanded: Seq[Sym] =
    exprs.map(_.expanded)
      .foldLeft(Seq(Seq[Sym]())){ (acc, seq: Seq[Sym]) =>
        acc.flatMap{a => seq.map{b => a :+ b}}
      }.map{es => this.instance(es:_*)}

  type Bind = (Symbol, Double)
  def approx(env: Bind*): Double
  def at(x: Double): Double = this.approx('x -> x)


  def isFinite: Boolean = true

  //lazy val simple: Sym = Simplify.simplify(this)
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

  def approx(env: Bind*) = constant
  def constant: Double
}


trait SymOp extends Sym {
  def operation(vs: Double*): Double

  def approx(env: Bind*): Double =
    this.operation({ exprs.map(_.approx(env:_*)) }:_*)
}

trait SymSpecial extends Sym {
  def approx(env: Bind*) = {
    throw new Error("Cannot approximate special value"); 0
  }
}

/// Special
//// Equation
case class SymEquation(left: Sym, right: Sym) extends SymSpecial {
  lazy val exprs = Seq(left, right)
  def instance(args: Sym*) = SymEquation(args(0), args(1))

  override def approx(env: Bind*) = ++(left, **(-1, right)).approx(env:_*)

  override def toString = left.toString + " = " + right.toString
}

//// Vertical Line
case class SymVertical(x: Sym) extends SymSpecial {
  lazy val exprs = Seq(x)
  def instance(args: Sym*) = SymVertical(args.head)

  override def toString = "x = " + x.toString
}

//// Integral
case class SymIntegral(expr: Sym) extends SymSpecial {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymIntegral(args.head)

  override def toString = f"Integral($expr)"
}

//// Point
case class SymPoint(x: Sym, y: Sym) extends SymSpecial {
  lazy val exprs = Seq(x, y)
  def instance(args: Sym*) = SymPoint(args(0), args(1))

  override def toString = f"($x, $y)"
}

/// Variables
case class SymVar(symbol: Symbol = 'x) extends Sym {
  lazy val exprs = Nil
  def instance(args: Sym*) = this
  override lazy val expanded = Seq(this)

  override def approx(env: Bind*): Double =
    env.find(_._1 == symbol) match {
      case Some((s, num)) => num
      case None => symbol match {
        case 'k => 0
        case _ => throw new Error("Variable not in bind") ; 0
      }
    }

  def s = this

  override def toString =
    symbol.name match {
      case "*" => "X"
      case a => a
    }
}

/// Constants
case class SymDecimal(decimal: BigDecimal) extends SymConstant {
  override def toString = decimal.toString

  lazy val constant = decimal.toDouble
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"

  lazy val constant = Math.PI
}

case class SymE() extends SymConstant {
  override def toString = "E"

  lazy val constant = Math.E
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

  lazy val constant = n.toDouble / d.toDouble

  def inverse: SymR = SymR(d, n)
  def negative: SymR = SymR(-n, d)
  def +(o: SymR): SymR = SymR((n * o.d) + (o.n * d), d * o.d)
  def -(o: SymR): SymR = this + o.negative
  def *(o: SymR): SymR = SymR(n * o.n, d * o.d)
  def /(o: SymR): SymR = this * o.inverse
  def ^(o: SymInt): SymR =
    if (o < 0) SymR(d.pow(-o.n.toInt), n.pow(-o.n.toInt))
    else SymR(n.pow(o.n.toInt), d.pow(o.n.toInt))

  def <(o: SymR): Boolean = (this.n*o.d) < (o.n*this.d)
  def >(o: SymR): Boolean = (this.n*o.d) > (o.n*this.d)
  def <=(o: SymR): Boolean = (this.n*o.d) <= (o.n*this.d)
  def >=(o: SymR): Boolean = (this.n*o.d) >= (o.n*this.d)
  def min(o: SymR): SymR = if (this > o) o else this
  def max(o: SymR): SymR = if (this < o) o else this
}

case class SymFrac(n: BigInt = 1, d: BigInt = 1) extends SymR

case class SymInt(n: BigInt = 1) extends SymR {
  override def toString = n.toString
  def d = BigInt(1)
  def ~(o: SymInt) = SymR(n, o.n)
  def s = this
  def toInt = n.toInt

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
  override def isFinite = false
}
case class SymPositiveInfinity() extends SymR {
  override def toString = "Inf"
  def n = 1
  def d = 0
  override def isFinite = false
}
case class SymNegativeInfinity() extends SymR {
  override def toString = "-Inf"
  def n = -1
  def d = 0
  override def isFinite = false
}

/// Operations
case class SymSum(set: Set[Sym]) extends SymOp {
  lazy val exprs = set.toSeq
  lazy val sortedExprs = exprs.sortWith{ (a, b) =>
    Latex.isNegative(a).isEmpty && !a.isInstanceOf[SymPM]
  }
  def instance(args: Sym*) = +++(args)

  def operation(vs: Double*) = vs.sum

  override def toString = f"(+ " + exprs.mkString(" ") + ")"
}

case class SymProd(set: Set[Sym]) extends SymOp {
  lazy val exprs = set.toSeq
  lazy val sortedExprs = exprs.groupBy{ _ match {
    case _: SymR => 1
    case _: SymConstant => 2
    case _: SymVar => 3
    case _: SymPow => 4
    case _: SymSum | _: SymProd => 6
    case _ => 5
  }}.toList.sortWith{ (a, b) => a._1 < b._1 }
    .map(_._2).flatten.toSeq

  def instance(args: Sym*) = ***(args)

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

  override def approx(env: Bind*) = expr.approx(env:_*)

  override lazy val expanded =
    expr.expanded ++ expr.expanded.map(**(_, -1.s))

  override def toString = f"(+- $expr)"
}

case class SymSin(expr: Sym) extends SymOp {
  override def toString = f"sin($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymSin(args.head)
  def operation(vs: Double*) = Math.sin(vs.head)
}

case class SymCos(expr: Sym) extends SymOp {
  override def toString = f"cos($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymCos(args.head)
  def operation(vs: Double*) = Math.cos(vs.head)
}

case class SymTan(expr: Sym) extends SymOp {
  override def toString = f"tan($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymTan(args.head)
  def operation(vs: Double*) = Math.tan(vs.head)
}

case class SymASin(expr: Sym) extends SymOp {
  override def toString = f"asin($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymASin(args.head)
  def operation(vs: Double*) = Math.asin(vs.head)
}

case class SymACos(expr: Sym) extends SymOp {
  override def toString = f"acos($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymACos(args.head)
  def operation(vs: Double*) = Math.acos(vs.head)
}

case class SymATan(expr: Sym) extends SymOp {
  override def toString = f"tan($expr)"
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymATan(args.head)
  def operation(vs: Double*) = Math.atan(vs.head)
}
