package sympany

import scala.util.chaining._

object Sym {
  def toMultiset[T](seq: Seq[T]): Map[T, Int] =
    seq.groupBy(identity).toList
      .map{ case (identity, list) => (identity, list.length) }
      .toMap
  
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

import Sym._

object Multiset {
  def toSeq[T](map: Map[T, Int]): Seq[T] =
    map.flatMap{ case (a, n) => Seq.fill(n)(a) }.toSeq

  def fromSeq[T](seq: Seq[T]): Map[T, Int] =
    seq.groupBy(identity).map{ case (k, vs) => (k, vs.length) }.toMap
}


trait Sym {
  def toLatex: String

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


  //def allHoles: Set[Sym] = exprHoles ++ extraHoles
  //def exprHoles: Set[Sym] = Set()
  //var extraHoles = Set[Sym] = Set()
  //def addHoles(newHoles: Set[Sym]): Unit =
  //  this.extraHoles = extraHoles ++ newHoles
  //def zeros: Set[Sym] = Set()
}

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


case class SymEquation(left: Sym = SymInt(0), right: Sym = SymInt(0)) extends Sym {
  lazy val exprs = Seq(left, right)
  def instance(args: Sym*) = SymEquation(args(0), args(1))

  override def toString = left.toString + " = " + right.toString
  def toLatex = left.toLatex + " = " + right.toLatex
}

//implicit class ImplicitSymVar(orig: Symbol) extends SymVar(orig)

case class SymDecimal(decimal: BigDecimal) extends SymConstant {
  override def toString = decimal.toString
  def toLatex = decimal.toString

  lazy val value = decimal.toDouble
}

case class SymVar(symbol: Symbol = 'x) extends Sym {
  lazy val exprs = Nil
  def instance(args: Sym*) = this
  override lazy val expand = Seq(this)
  override def approx(env: Bind*) = env.find(_._1 == symbol).map(_._2).toSeq

  override def toString = symbol.name
  
  def toLatex = symbol.name.indexOf('/') match {
    case -1 => symbol.name
    case n => s"\\frac{${symbol.name.substring(0, n)}}{${symbol.name.substring(n+1)}}"
  }
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

case class SymFrac(n: BigInt = 1, d: BigInt = 1) extends SymR {
  def toLatex = s"\\frac{${n.toString}}{${d.toString}}"
}

//implicit class ImplicitSymBigInt(original: BigInt) extends SymInt(original)
//implicit class ImplicitSymInt(original: Int) extends SymInt(BigInt(original))

case class SymInt(n: BigInt = 1) extends SymR {
  override def toString = n.toString
  def toLatex = n.toString
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
  def toLatex = "\\NaN"
  def n = 0
  def d = 0
}
case class SymPositiveInfinity() extends SymR {
  override def toString = "Inf"
  def toLatex = "\\infty"
  def n = 1
  def d = 0
}
case class SymNegativeInfinity() extends SymR {
  override def toString = "-Inf"
  def toLatex = "-\\infty"
  def n = -1
  def d = 0
}

case class SymSum(mset: Map[Sym, Int]) extends SymOp {
  lazy val exprs = Multiset.toSeq(mset)
  def instance(args: Sym*) = SymSum(Multiset.fromSeq(args))

  def operation(vs: Double*) = vs.sum

  override def toString = f"(+ " + exprs.mkString(" ") + ")"
  def toLatex = if (exprs.isEmpty) "" else {
    ("\\left(" + exprs.map(_.toLatex).map(noParens)
      .reduceLeft(_ + " + " + _) + "\\right)")
      .replace("+ \\pm", "\\pm")
  }
}

case class SymProd(mset: Map[Sym, Int]) extends SymOp {
  lazy val exprs = Multiset.toSeq(mset)
  def instance(args: Sym*) = SymProd(Multiset.fromSeq(args))

  def operation(vs: Double*) = vs.product

  override def toString = f"(* " + exprs.mkString(" ") + ")"
  
  // Split the positive and negative powers into the numerator and denominator
  def toLatex = if (exprs.isEmpty) "1" else if (exprs.length == 1) exprs(0).toLatex else {
    val part = exprs.partitionMap(_ match {
      case SymPow(b, SymInt(n)) if n.toInt == -1 => Right(b)
      case SymPow(b, SymInt(n)) if n < 0 => Right(SymPow(b, SymInt(-n)))
      case SymPow(b, p: SymProd) => {
        val es = p.exprs
        val op = es.collect{case si @ SymInt(n) if n < 0 => si}.headOption;
        val newEs = if (op.isEmpty) es else {
          es.updated(es.indexOf(op.get), SymInt(-op.get.n)).filter(_ != SymInt(1))
        }
        ^(b, ***(newEs)).pipe(if (op.isEmpty) Left(_) else Right(_))
      }
      case e => Left(e)
    })
    val strs = part.productIterator.toList.map{ in =>
      val l = in.asInstanceOf[Seq[Sym]]
      if (l.isEmpty) "1" else l.map(_.toLatex).reduceLeft(_ + " \\cdot " + _)
    }
    if (strs(1) == "1") s"\\left(${strs(0)}\\right)"
    else s"\\frac{${strs(0)}}{${strs(1)}}"
  }
}

case class SymPow(base: Sym = SymInt(1), expt: Sym = SymInt(1)) extends SymOp {
  lazy val exprs = Seq(base, expt)
  def instance(args: Sym*) = SymPow(args(0), args(1))

  def operation(vs: Double*) = Math.pow(vs(0), vs(1))

  override def toString = f"(^ $base $expt)"
  def toLatex = expt match {
    case SymFrac(top, root) if top == 1 && root == 2 => s"\\sqrt{${noParens(base.toLatex)}}"
    case SymFrac(top, root) if top == 1 => s"\\sqrt[${root.toInt}]{${noParens(base.toLatex)}}"
    case _ => s"${base.toLatex}^{${expt.toLatex}}"
  }
}

case class SymLog(pow: Sym = SymInt(1), base: Sym = SymE()) extends SymOp {
  lazy val exprs = Seq(pow, base)
  def instance(args: Sym*) = SymLog(args(0), args(1))

  def operation(vs: Double*) = Math.log(vs(0)) / Math.log(vs(1))

  override def toString = if (base == SymE()) f"(ln $pow)" else f"(log $pow $base)"
  def toLatex =
    if (base == SymE()) f"\\ln \\left(${pow.toLatex}\\right)"
    else f"\\log_{${pow.toLatex}} \\left(${base.toLatex}\\right)"
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
  def toLatex = expr match {
    case _: SymProd => s"\\pm ${expr.toLatex.pipe{s => s.substring(6, s.length-7)}}"
    case _ => s"\\pm ${expr.toLatex}"
  }
}

case class SymSin(expr: Sym) extends SymOp {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymSin(args.head)

  def operation(vs: Double*) = Math.sin(vs.head)

  def toLatex = f"sin${expr.toLatex}"
}

case class SymCos(expr: Sym) extends Sym {
  lazy val exprs = Seq(expr)
  def instance(args: Sym*) = SymCos(args.head)

  def operation(vs: Double*) = Math.cos(vs.head)

  def toLatex = f"cos${expr.toLatex}"
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"
  def toLatex = "\\pi"

  lazy val value = Math.PI
}

case class SymE() extends SymConstant {
  override def toString = "E"
  def toLatex = "e"

  lazy val value = Math.E
}
