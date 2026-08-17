# W220: the CABD system over `ZMod 4`

W220 determines the honest scalar ring of W219's finite additive system.  An ordinary
relative source class lies two two-central layers above the quotient cutoff, so its fourth
power vanishes.  The relative central defect row already has exponent two, while the
relative `C` class modulo exact neutral representatives has exponent dividing four.

Consequently `oneHandleBalancedCABDZModFourSystem` is the canonical `ZMod 4`-linear form of
the combined CABD map.  The theorem
`neutralityObstruction_eq_one_iff_mem_CABDZModFourSystem_range` restates the remaining
neutrality obstruction as membership of one explicit vector in this finite linear range.

This corrects the tempting but generally unjustified `ZMod 2` reduction: squaring an
ordinary relative `C` class deepens it by one layer, but need not make its exact continuous
character row vanish.  No rank, surjectivity, or obstruction-vanishing statement is asserted.
Every public declaration has exactly the standard axiom set `propext`, `Classical.choice`,
and `Quot.sound`.
