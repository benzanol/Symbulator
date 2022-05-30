def check(expr: Sym)(simplified: Sym) =
  assert(if (simplify(expr) == simplified) true
  else { println(f"Failed on: $expr = $simplified") ; false })

/// Symbolic Expression Tests
// Equality regardless of factor order and assigned type (Sym vs SymProd)
assert( List[Sym](SymProd(2, Pi)).head == SymProd(Pi, 2) )

/// Pattern Matching Tests
// Pattern matching basics
assert{
  ProdP(Or('i @@ IntP(), 'a), __*).matches(**(2, 1~2)) == List(
    Map('i -> SymInt(2)),
    Map('a -> SymInt(2)),
    Map('a -> SymFrac(1, 2))
  )
}

// Pattern guards: |>
assert{ /?('a, 'b |> {(_:SymInt).n < 4}).matches(3~2).nonEmpty }
assert{ /?('a, 'b |> {(_:SymInt).n < 4}).matches(3~5).isEmpty }

// Assigned Vars
assert{ *?(First('i @@ #?(), ~~ &@ 'i -> 1.s), 'rest @@ __*).matches(**(Pi, 3, 4, E)).length == 2 }
assert{ *?(Or('i @@ #?(), ~~ &@ 'i -> 1.s), 'rest @@ __*).matches(**(Pi, 3, 4, E)).length == 3 }
assert{ *?(And('i @@ #?(), ~~ &@ 'a -> 1.s), 'rest @@ __*).matches(**(Pi, 3, 4, E)).length == 0 }

// Or/And/First
assert {
  Or(/?('n, 'd), 'u).matches(2~3) ==
  Seq(Map('n -> 2.s, 'd -> 3.s), Map('u -> 2~3))
}

assert {
  First(/?('n, 'd), 'u).matches(2~3) ==
  Seq(Map('n -> 2.s, 'd -> 3.s))
}

assert {
  And(/?('n, 'd), 'u).matches(2~3) ==
  Seq(Map('n -> 2.s, 'd -> 3.s, 'u -> 2~3))
}

// As Product
assert{ AsProdP(=?(8)).matches(8) == Seq(Map()) }
assert{ AsProdP(=?(8)).matches(**(8)) == Seq(Map()) }
assert{ AsProdP(=?(8)).matches(++(8)) == Nil }
assert{ AsProdP(First('a @@ #?(), ~~ &@ 'a->1.s), 'rest @@ __*).matches(**(E, 3, Pi, 4)).length == 2 }
assert{ AsProdP(First('a @@ #?(), ~~ &@ 'a->1.s), 'rest @@ __*).matches(**(E, Pi)).head('a) == 1.s }
assert{ AsProdP(First('a @@ #?(), ~~ &@ 'a->1.s), 'rest @@ __*).matches(Pi) ==
  Seq(Map('a -> SymInt(n = 1), 'rest -> List(SymPi())))
}
assert{ AsProdP(First('a @@ #?(), ~~ &@ 'a->1.s), 'rest @@ __*).matches(8) ==
  Seq(Map('a -> SymInt(n = 8), 'rest -> List()))
}

assert{ AsPowP('base, 'expt).matches(^(3, 4)) == Seq(Map('base -> 3.s, 'expt -> 4.s)) }
assert{ AsPowP('base, 'expt).matches(3) == Seq(Map('base -> 3.s, 'expt -> 1.s)) }
assert{ *?(AsPowP('base, 'e1), AsPowP('base, 'e2)).matches(**(3, ^(3, 4))).contains(
  Map('base -> 3.s, 'e1 -> 1.s, 'e2 -> 4.s) )
}
assert{ *?(AsPowP('base, 'e1), AsPowP('base, 'e2)).matches(**(3, ^(5, 4))).isEmpty }


/// Simplifying Rationals Tests
assert{ +6 ~ +4 == +3~2 }
assert{ -6 ~ -4 == +3~2 }
assert{ +6 ~ -4 == -3~2 }
assert{ -6 ~ +4 == -3~2 }
assert{ +8 ~ +2 ==  4.s }
assert{ +8 ~ -2 == -4.s }
assert{ +2 ~ +0 == SymPositiveInfinity() }
assert{ -3 ~ +0 == SymNegativeInfinity() }
assert{ +0 ~ +0 == SymUndefined() }

/// Simplifying Powers Tests
check{ ^(1, 100) }{ 1 }
check{ ^(0, 100) }{ 0 }
check{ ^(100, 0) }{ 1 }
check{ ^(100, 1) }{ 100 }
check{ ^(2, 3) }{ 8 }
check{ ^(3~2, 0) }{ 1 }
check{ ^(2, -1) }{ 1~2 }
check{ ^(2, -3) }{ 1~8 }
check{ ^(1~4, 3 ~ -2) }{ 8 }
check{ ^(4, 1~2) }{ 2 }
check{ ^(3~4, 2) }{ 9~16 }
check{ ^(12, 1~2) }{ **(2, ^(3, 1~2)) }
check{ ^(12~5, 2~3) }{ **(2, ^(18~25, 1~3)) }

// Simplifying Logs Tests
check{ log(^(2, 1~2)) }{ **(1~2, log(2)) }
check{ log(**(2, 3)) }{ log(6) }
check{ **(7, log(**(2, Pi), 10)) }{ **(log(2, 10), log(Pi, 10), 7) }

/// Simplifying Products Tests
// Multiplying rationals and rational roots
check{ **() }{ 1 }
check{ **(1, 1, Pi, 1, 1) }{ Pi }
check{ **(7, 3) }{ 21 }
check{ **(7~4, 10~3) }{ 35~6 }
check{ **(7, **(Pi, 2), E) }{ **(14, Pi, E) }
check{ **(3~2, 2~3, Pi, E) }{ **(Pi, E) }
check{ **(^(2, 1~2), ^(3, 1~3)) }{ ^(72, 1~6) }
check{
  **(3~2, ^(3, 2~3), ^(2, 1~3), ^(1024, 1~2))
}{ **(48, ^(18, 1~3)) }

// Combining similar bases
check{ **(E, ^(E, -1)) }{ 1 }
check{ **(E, E) }{ ^(E, 2) }
check{ **(E, 7, ^(E, 1~2)) }{ **(7, ^(E, 3~2)) }
check{ **(2, ^(E, 1~2), ^(E, 5~3)) }{ **(2, ^(E, 13~6)) }
check{ **(2, ^(E, 3), ^(Pi, 3)) }{ **(2, ^(E, 3), ^(Pi, 3)) }

// Distributive property
check{ **(2, ++(3, 4)) }{ 14 }
check{ **(2, ++(3, Pi)) }{ ++(6, **(2, Pi)) }
check{ **(E, ++(1, ^(2, 1~2))) }{ ++(E, **(E, ^(2, 1~2))) }

/// Simplifying Sums Tests
// Adding rationals
check{ ++(1, 2) }{ 3 }
check{ ++(1, 1~2) }{ 3~2 }
check{ ++(3~7, ++(Pi, 1~2)) }{ ++(Pi, 13~14) }

// Combining similar products
check{ ++(Pi, Pi) }{ **(Pi, 2) }
check{ ++(Pi, **(Pi, 3~2)) }{ **(Pi, 5~2) }
check{ ++(**(Pi, 3~2), **(Pi, -3~2)) }{ 0 }
check{ ++(**(Pi, E), **(Pi, E)) }{ **(Pi, E, 2) }
check{ ++(**(Pi, E), **(2, Pi, E)) }{ **(Pi, E, 3) }
check{
  ++(7, 6,
    **(E, Pi, 3), **(E, Pi, 4), **(E, Pi),
    Pi, **(Pi, -1),
    **(E, 3~2), **(E, -1~2))
}{ ++(13, **(E, 8, Pi), E) }
