# W84 supplementary audit: OddFrame.lean headline versus statement

Recorded by the orchestrator; produced by a background audit the W84 house lane dispatched,
returning after that lane's branch merged.  All findings are PROSE-LEVEL (docstrings, section
headers, module doc); no statement is wrong, and the chain `clearing -> seam -> branch ->
general theorem` was separately verified end to end at degree one.  For the W85 house lane.

## Findings

1. **HIGH.** `OddFrame.lean:208` (and `:160`, `:190-191`): the section prose conflates the
   MOD-2 rows with the seam's EXACT `ℤ₂` rows.  "Only the split of the row sum is missing"
   is false: besides the bit, the entire lift out of `2ℤ₂` in each row is missing, and that
   lift is exactly what the model clearing pays for in §4.  The module doc's own T2 sentence
   (line 46) is careful; the regression is in the section headers and two docstrings.  The
   fix is to say "the two MOD-2 rows up to one shared bit" wherever the exact-row reading
   could be taken, and to keep "the ticket's target object" pointing at the exact-row frame
   (`:375`), not §2's mod-2 object.
2. **MEDIUM.** `OddFrame.lean:55` and `:227` cite `GammaLOddDegreeBridge` §9, which does not
   exist (that file has §1-§4 with primes).  The result is `PivotClimb` §9; the docstring at
   `:252` gets it right, so the file contradicts itself.
3. **MEDIUM-LOW.** `:56-62` "costs exactly the model-side clearing statement" contradicts the
   file's own `:318-320` ("overshoots by its marking quantifier").  Only one implication is
   proved; "costs at most" or "is bought by" is the honest phrase.
4. **LOW.** `:115-117` headlines "the dimension" over a cardinality statement (`Nat.card =
   2^(2h+3)`); the "i.e. odd dimension" step is unformalized.
5. **LOW.** The T1/T2 headline sentences say "unconditionally"/"at every oriented
   equivalence" while carrying the load-bearing data binder `FF : DyadicUnitFiltration K`
   (disclosed only once, at `:61`).
6. **LOW.** `oddFrame_candidate_equiv_galK_of_clear` has `{FF}` implicit where its seven §4
   siblings have it explicit, under a docstring whose word is "exactly".
7. **LOW.** `:438-439`: the §5 counterfactual is backwards (with `c₀` even the pivot argument
   concludes nothing, rather than pinning the rows).
8. **INFO.** Five unused-section-variable linter warnings; three theorems advertise a
   dependence on the absolute Galois group of `ℚ₂` they do not have (`[CompactSpace
   AbsGalQ2]`/`[TotallyDisconnectedSpace AbsGalQ2]` unused).

## Verified clean, for the record

All nine §6 axiom-pin bullets against the real `#print axioms` output (the file's distinct
axiom set is std-3 + {tateDualityAt, hilbertSymbol_normCriterion_finiteDyadic, B1, B7,
dyadicOrientation, peripheralCyclotomicAction}; no B5/B5-K anywhere); the cup-adapted Gram
identification exact; the two κ/ω-side row identities verified upstream; the presenting
frame's global relator kill; the iff's right-hand side precisely the clearing's conclusion
at the transported marking; the §4 consumers composing over `hclear` alone; PivotClimb §8's
strongest-unrefuted claim correctly cited with its liability located in PivotClimb.
