package sympany.math

import scala.util.chaining._

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math.Simplify.simplify
import sympany.math.Derivative.derive
import sympany.Sym._
import sympany.Pattern._

object Solve {
  val aRules = new Rules()
  
  def importantPoints(e: Sym, v: Symbol): Seq[Sym] = {
    e.exprs.map(importantPoints(_, v)).foldLeft(Seq[Sym]())(_ ++ _) ++
    undefinedPoints(derive(e, v), v) ++
    solve(derive(e, v), v) ++
    (e match {
      case SymPow(b, SymFrac(p, root)) => solve(b, v)
      case SymPow(b, SymInt(n)) if n < 0 => solve(b, v)
      case _ => Nil
    })
  }.distinct
  
  def undefinedPoints(e: Sym, v: Symbol): Seq[Sym] = {
    e.exprs.map(undefinedPoints(_, v)).foldLeft(Seq[Sym]())(_ ++ _) ++
    (e match {
      case SymLog(p, _) => solve(p, v)
      case SymPow(b, p: SymR) if (p.n*p.d) < 0 => solve(b, v)
      case _ => Nil
    })
  }.distinct
  
  @JSExportTopLevel("solve")
  def solve(e: Sym, v: Symbol = X.symbol): Seq[Sym] =
    replaceExpr(e.simple, SymVar(v), X)
      .pipe{expr => zRules.all(expr)}
      .map{solution => replaceExpr(solution, X, SymVar(v))}
      .map(_.simple).toSeq.distinct//.filter(_.isDefined)


  //def solve(e: Sym, v: Symbol = X.symbol): Seq[Sym] =
  //  replaceExpr(e, SymVar(v), X)
  //    .pipe{expr => solve(Seq(expr), Nil)}
  //    .map{solution => replaceExpr(solution, X, SymVar(v))}
  //
  //def solve(es: Seq[Sym], old: Seq[Sym]): Seq[Sym] =
  //  (es.flatMap(zRules.all) // Seq[Sym]
  //    .map(simplify) ++ {
  //      es.flatMap{ e => aRules.all(e)
  //        .filter(!old.contains(_))
  //        .filter(!es.contains(_))
  //      }.pipe{ newEs => if (newEs.isEmpty) Nil else solve(newEs, old ++ es) }
  //    }).distinct
  
  val zRules = new SeqRules()
  
  zRules.+("Subtract from one side of equation"){
    @?('whole) @@ EquationP(@?('l), @?('r))
  }{ case (l: Sym, r: Sym, whole: Sym) =>
      solve(simplify(++(l, **(r, S(-1)))))
  }

  zRules.+("x^3 + x^2 = x^2(x + 1)"){
    's @@ SumP(Repeat( AsProdP( AsPowP(XP, __), __*) ))
  }{ case s: SymSum =>

      val minExpt = s.exprs.flatMap{ e =>
        AsProdP( AsPowP(XP, 'p), __*).matches(e)
          .headOption.map(_.apply('p).asInstanceOf[SymInt].toInt)
      }.min

      val rule = new Rule("", AsProdP( AsPowP(XP, 'p), 'r @@ __*), {
        case (p: Sym, r: Seq[Sym]) =>
          ***( ^(X, ++(p, SymInt(-minExpt))) +: r ).simple
      })

      val divided = +++( s.exprs.map(rule.first(_).get) )
      println("Divided: ", divided)

      if (minExpt > 0) SymInt(0) +: solve( divided )
      else Nil
  }

  zRules.+("Plus Minus"){ PMP(@?('e)) }{ case e: Sym => solve(e) }

  // Good luck trying to understand this mess lol
  zRules.+("ax^p + b => x +- (-b/a)^(1/p)"){
    AsSumP(AsProdP(AsPowP(XP, @?('p) @@ noxP()), @?('a) @@ Repeat(noxP())), @?('rest) @@ Repeat(noxP()))
  }{ case (a: Seq[Sym], SymInt(n), r: Seq[Sym]) if (n % 2 == 0) => Seq(+-(^(**(S(-1), +++(r),
    if (a.isEmpty) S(1) else ^(+++(a), S(-1))), S(1, n))))
    case (a: Seq[Sym], p: Sym, r: Seq[Sym]) => Seq(^(**(S(-1), +++(r),
      if (a.isEmpty) S(1) else ^(+++(a), S(-1))), ^(p, S(-1))))
  }

  zRules.+("log 1 = 0"){
    LogP(@?('a) @@ hasxP(), __)
  }{ case a: Sym => solve( ++(a, S(-1)) ) }

  //  zRules.+("a^p => a = 0"){
  //    @?('whole) @@ PowP( @?('b), RatP( @?('p) |> { p: SymR => p.value > 0 } ) )
  //  }{ case (b: Sym, p: SymR, whole: Sym) => solve(b).headOption.getOrElse(whole) }

  zRules.+("Quadratic formula"){
    SumP(
      @?('as) @@ Repeat(AsProdP(PowP(XP, =#?(2)), Repeat(noxP())), min=1), // Any number of a*x^2
      @?('bs) @@ Repeat(AsProdP(XP, Repeat(noxP())), min=1), // Any number of b*x
      @?('cs) @@ Repeat(noxP()) // Any number of c
    )
  }{ case (aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]) =>
      Seq(quadraticFormula(aS, bS, cS))
  }

  def quadraticFormula(aS: Seq[Sym], bS: Seq[Sym], cS: Seq[Sym]): Sym = {
    val List(a, b, c) = List(aS, bS, cS).map{ es: Seq[Sym] =>
      val realEs = es.map(_ match {
        case p: SymProd => p.exprs.filter(noX).pipe(***)
        case f if hasX(f) => SymInt(1)
        case f => f
      })
      +++(realEs).pipe(simplify)
    }
    **( ++( **(S(-1), b), +-(^(++(^(b, S(2)), **(S(-4), a, c)), S(1, 2)))), ^(**(S(2), a), S(-1)))
  }
}
