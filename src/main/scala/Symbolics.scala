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
  
  def ++(es: Sym*) = SymSum(es:_*)
  def **(es: Sym*) = SymProd(es:_*)
  def #=(i: BigInt) = SymInt(i)
  def #=(n: BigInt, d: BigInt) = SymR(n, d)
  def ^(base: Sym, expt: Sym) = SymPow(base, expt)
  def log(pow: Sym, base: Sym = SymE()) = SymLog(pow, base)
  def +-(e: Sym) = SymPM(e)
  def Pi = SymPi()
  def E = SymE()
  def X = SymVar('X)
  def V(s: Symbol) = SymVar(s)
}

import Sym._

trait Sym {
  type Env = Map[Symbol, Double]
  def approx(implicit env: Env): Double
  def toLatex: String
  
  def exprs: Seq[Sym]
  def mapExprs(f: Sym => Sym): Sym
  def expand: Seq[Sym]
  def category: String
  
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
  def category = "constant"
  def exprs = Nil
  def mapExprs(f: Sym => Sym) = this
  def expand = Seq(this)
}

trait SymUnordered extends Sym

case class SymEquation(left: Sym = SymInt(0), right: Sym = SymInt(0)) extends Sym {
  def category = "equation"
  override def toString = left.toString + " = " + right.toString
  def toLatex = left.toLatex + " = " + right.toLatex
  def approx(implicit env: Env) = left.approx - right.approx
  def exprs = Seq(left, right)
  def mapExprs(f: Sym => Sym) = SymEquation(f(left), f(right))
  
  def expand = allCombos(left.expand, right.expand)
    .map{l => SymEquation(l(0), l(1))}
}

//implicit class ImplicitSymVar(orig: Symbol) extends SymVar(orig)

case class SymDecimal(decimal: BigDecimal) extends SymConstant {
  override def toString = decimal.toString
  def approx(implicit env: Env) = decimal.toDouble
  def toLatex = decimal.toString
}

case class SymVar(symbol: Symbol = 'x) extends Sym {
  def category = "variable"
  override def toString = symbol.name
  def exprs = Nil
  def mapExprs(f: Sym => Sym) = this
  def expand = Seq(this)
  def s = this
  
  def toLatex = symbol.name.indexOf('/') match {
    case -1 => symbol.name
    case n => s"\\frac{${symbol.name.substring(0, n)}}{${symbol.name.substring(n+1)}}"
  }
  
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
  override def approx(implicit env: Env) = Double.NaN
  def toLatex = "\\NaN"
  def n = 0
  def d = 0
}
case class SymPositiveInfinity() extends SymR {
  override def toString = "Inf"
  override def approx(implicit env: Env) = Double.PositiveInfinity
  def toLatex = "\\infty"
  def n = 1
  def d = 0
}
case class SymNegativeInfinity() extends SymR {
  override def toString = "-Inf"
  override def approx(implicit env: Env) = Double.NegativeInfinity
  def toLatex = "-\\infty"
  def n = -1
  def d = 0
}

case class SymSum(exprs: Sym*) extends SymUnordered {
  def category = "sum"
  override def toString = f"(+ " + exprs.mkString(" ") + ")"
  def toLatex = if (exprs.isEmpty) "" else {
    ("\\left(" + exprs.map(_.toLatex).map(noParens)
      .reduceLeft(_ + " + " + _) + "\\right)")
      .replace("+ \\pm", "\\pm")
  }
  
  override def id = (SymSum, toMultiset(exprs.map(_.id)))
  def approx(implicit env: Env) = exprs.map(_.approx).sum
  def mapExprs(f: Sym => Sym) = SymSum(exprs.map(f):_*)
  def expand = allCombos({ exprs.map(_.expand) }:_*).map{l => SymSum(l:_*)}
}

case class SymProd(exprs: Sym*) extends SymUnordered {
  def category = "product"
  override def toString = f"(* " + exprs.mkString(" ") + ")"
  
  // Split the positive and negative powers into the numerator and denominator
  def toLatex = if (exprs.isEmpty) "1" else if (exprs.length == 1) exprs(0).toLatex else {
    val part = exprs.partitionMap(_ match {
      case SymPow(b, SymInt(n)) if n.toInt == -1 => Right(b)
      case SymPow(b, SymInt(n)) if n < 0 => Right(SymPow(b, SymInt(-n)))
      case SymPow(b, SymProd(es @ _*)) => {
        val op = es.collect{case si @ SymInt(n) if n < 0 => si}.headOption;
        val newEs = if (op.isEmpty) es else {
          es.updated(es.indexOf(op.get), SymInt(-op.get.n)).filter(_ != SymInt(1))
        }
        SymPow(b, SymProd(newEs:_*)).pipe(if (op.isEmpty) Left(_) else Right(_))
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
  
  override def id = (SymProd, toMultiset(exprs.map(_.id)))
  def approx(implicit env: Env) = exprs.map(_.approx).product
  def mapExprs(f: Sym => Sym) = SymProd(exprs.map(f):_*)
  def expand = allCombos({ exprs.map(_.expand) }:_*).map{l => SymProd(l:_*)}
}

case class SymPow(base: Sym = SymInt(1), expt: Sym = SymInt(1)) extends Sym {
  def category = "power"
  override def toString = f"(^ $base $expt)"
  def toLatex = expt match {
    case SymFrac(top, root) if top == 1 && root == 2 => s"\\sqrt{${noParens(base.toLatex)}}"
    case SymFrac(top, root) if top == 1 => s"\\sqrt[${root.toInt}]{${noParens(base.toLatex)}}"
    case _ => s"${base.toLatex}^{${expt.toLatex}}"
  }
  
  def approx(implicit env: Env) = Math.pow(base.approx, expt.approx)
  def exprs = Seq(base, expt)
  def mapExprs(f: Sym => Sym) = SymPow(f(base), f(expt))
  def expand = allCombos(base.expand, expt.expand)
    .map{l => SymPow(l(0), l(1))}
}

case class SymLog(pow: Sym = SymInt(1), base: Sym = SymE()) extends Sym {
  def category = "log"
  override def toString = if (base == SymE()) f"(ln $pow)" else f"(log $pow $base)"
  def toLatex =
    if (base == SymE()) f"\\ln \\left(${pow.toLatex}\\right)"
    else f"\\log_{${pow.toLatex}} \\left(${base.toLatex}\\right)"
  
  def approx(implicit env: Env) = Math.log(pow.approx) / Math.log(base.approx)
  def exprs = Seq(pow, base)
  def mapExprs(f: Sym => Sym) = SymLog(f(pow), f(base))
  def expand = allCombos(pow.expand, base.expand)
    .map{l => SymLog(l(0), l(1))}
}

case class SymPM(expr: Sym = SymInt(1)) extends Sym {
  def category = "pm"
  override def toString = f"(+- $expr)"
  def toLatex = expr match {
    case _: SymProd => s"\\pm ${expr.toLatex.pipe{s => s.substring(6, s.length-7)}}"
    case _ => s"\\pm ${expr.toLatex}"
  }
  def approx(implicit env: Env) = expr.approx
  def exprs = Seq(expr)
  def mapExprs(f: Sym => Sym) = SymPM(f(expr))
  def expand = List(1, -1).flatMap{n => expr.expand.map(SymProd(SymInt(n), _))}
}

case class SymSin(expr: Sym) extends Sym {
  def category = "sin"
  def toLatex = f"sin${expr.toLatex}"
  def approx(implicit env: Env) = Math.sin(expr.approx)
  def exprs = Seq(expr)
  def mapExprs(f: Sym => Sym) = SymSin(f(expr))
  def expand = expr.expand.map(SymSin(_))
}

case class SymCos(expr: Sym) extends Sym {
  def category = "cos"
  def toLatex = f"cos${expr.toLatex}"
  def approx(implicit env: Env) = Math.cos(expr.approx)
  def exprs = Seq(expr)
  def mapExprs(f: Sym => Sym) = SymCos(f(expr))
  def expand = expr.expand.map(SymCos(_))
}

case class SymPi() extends SymConstant {
  override def toString = "Pi"
  def toLatex = "\\pi"
  def approx(implicit env: Env) = Math.PI
}

case class SymE() extends SymConstant {
  override def toString = "E"
  def toLatex = "e"
  def approx(implicit env: Env) = Math.E
}
