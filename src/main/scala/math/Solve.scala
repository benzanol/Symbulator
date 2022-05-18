package sympany.math

import scala.util.chaining._

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.symbolics._
import sympany.symbolics.Sym._
import sympany.patterns._
import sympany.patterns.Pattern._
import sympany.math.Simplify.simplify
import sympany.math.Derivative.derive

object Solve {
  val aRules = new Rules()
  
  def importantPoints(e: Sym, v: Symbol): Seq[Sym] = {
    e.exprs.map(importantPoints(_, v)).foldLeft(Seq[Sym]())(_ ++ _) ++
    solve(derive(e, v), v) ++
    (e match {
      case SymPow(b, SymFrac(p, root)) => solve(b, v)
      case SymPow(b, SymInt(n)) if n < 0 => solve(b, v)
      case _ => Nil
    })
  }
  
  def undefinedPoints(e: Sym, v: Symbol): Seq[Sym] = {
    e.exprs.map(undefinedPoints(_, v)).foldLeft(Seq[Sym]())(_ ++ _) ++
    (e match {
      case SymLog(p, _) => solve(p, v)
      case _ => Nil
    })
  }
  
  @JSExportTopLevel("solve")
  def solve(e: Sym, v: Symbol = X.symbol): Seq[Sym] =
    replaceExpr(e, SymVar(v), X)
      .pipe{expr => solve(Seq(expr), Nil)}
      .map{solution => replaceExpr(solution, X, SymVar(v))}
  
  def solve(es: Seq[Sym], old: Seq[Sym]): Seq[Sym] =
    (es.flatMap(zRules.all) // Seq[Sym]
      .map(simplify) ++ {
        es.flatMap{ e => aRules.all(e)
          .filter(!old.contains(_))
          .filter(!es.contains(_))
        }.pipe{ newEs => if (newEs.isEmpty) Nil else solve(newEs, old ++ es) }
      }).distinct
  
  val zRules = new Rules()
  
  zRules.+("Subtract from one side of equation"){
    @?('whole) @@ EquationP(@?('l), @?('r))
  }{ case (l: Sym, r: Sym, whole: Sym) =>
      solve(simplify(SymSum(l, SymProd(r, #=(-1))))).headOption.getOrElse(whole)
  }
  
  zRules.+("x^a = 0 >> 0"){ AsPowP(XP, __) }{ case () => #=(0) }
  
  zRules.+("u * a = 0 >> u = 0"){
    @?('whole) @@ ProdP(@?('e) @@ hasxP(), __*)
  }{ case (e: Sym, whole: Sym) =>
      solve(Seq(e), Seq(whole)).headOption.getOrElse(whole) }
  
  zRules.+("ax + b = 0 >> -b/a"){
    SumP(AsProdP(XP, @?('a) @@ Repeat(noxP())), @?('b) @@ Repeat(noxP()))
  }{ case (a: Seq[Sym], b: Seq[Sym]) =>
      SymProd(#=(-1), SymSum(b:_*), SymPow(SymProd(a:_*), #=(-1))) }
  
  zRules.+("x^p + a => x +- (-a)^(1/p)"){
    AsSumP(PowP(XP, @?('p) @@ noxP()), @?('rest) @@ Repeat(noxP()))
  }{ case (SymInt(n), r: Seq[Sym]) if (n % 2 == 0) => SymPM(SymPow(SymProd(#=(-1), SymSum(r:_*)), SymR(1, n)))
    case (p: Sym, r: Seq[Sym]) => SymPow(SymProd(#=(-1), SymSum(r:_*)), SymPow(p, #=(-1)))
  }
  
  zRules.+("Quadratic formula"){
    SumP(
      @?('as) @@ Repeat(AsProdP(PowP(XP, =#?(2)), Repeat(noxP())), min=1), // Any number of a*x^2
      @?('bs) @@ Repeat(AsProdP(XP, Repeat(noxP())), min=1), // Any number of b*x
      @?('cs) @@ Repeat(noxP(), min=1) // Any number of c
    )
  }{ case (aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]) =>
      quadraticFormula(aS, bS, cS)
  }
  
  def quadraticFormula(aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]): Sym = {
    val List(a, b, c) = List(aS, bS, cS).map{ es: Seq[Sym] =>
      val realEs = es.map(_ match {
        case SymProd(fs @ _*) => fs.filter(noX).pipe(SymProd(_ :_*))
        case f if hasX(f) => SymInt(1)
        case f => f
      })
      SymSum(realEs:_*).pipe(simplify)
    }
    **( ++( **(#=(-1), b), +-(^(++(^(b, #=(2)), **(#=(-4), a, c)), #=(1, 2)))), ^(**(#=(2), a), #=(-1)))
  }
}
