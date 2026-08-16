# W87-BLOCK lane note

Lane target: the bracket-square block at the three open mod-4 residues of `(A - 1, B)`,
decided against the graded supply; T3 if affirmative.  Module:
`GQ2/Dyadic/SqCore/GradedRowResidue.lean` (prefix `gRsd`, no collisions), green against the
mirror at base `1541635f`.  No sorry, no new axiom, no native_decide.

## Verdict up front

**The block is decided, POSITIVELY, at all three residues, and with them at every `(A, B)`
on the unit locus: rung 4 of the row ladder is a THEOREM** (`gRsd_nonempty_four`).  The
residual of the row ladder now starts at class FIVE, level with the M6 ladder after
`mpcBld_nonempty_four`.  The clearing `SqNuOrientedClearAtUnitPivot h` and the odd-degree
classification now rest on the rungs `k >= 5` alone (`gRsd_clearing_of_forall_class_five`,
`gRsd_supply_of_forall_class_five`, `gRsd_candidateEquiv_of_forall_class_five`).

> **[W88-HOUSE, as of `ad8c2b62`: "level with the M6 ladder" is stale.]**  W87-FIVE merged
> ahead of this lane in the same wave (`55c9173f` against this lane's `f56465a5`) and proved
> `mpcFv_nonempty_five : (mpcWordSet 5).Nonempty`, so the M6 ladder's residue starts at class
> SIX.  The two ladders are one rung apart with M6 ahead.  Everything else in this paragraph
> is exact.  Note the asymmetry the comparison hides: this lane's `k >= 5` chain is a
> PRODUCER, while the M6 side's sharp producer is still `mpcBld_shift_of_forall_class_five`
> and no class-six producer exists.

The decisive move is one Jacobi rotation.  The wave-86 note held that y-legged triples are
"reachable ONLY inside bundles", making the block a `sq(ker bY)`-membership question.  That
clause is FALSE for triples whose two inner letters are not `x_1`: Hall-Witt in `Q_4`
(`cfourDef_jacobi_solve`, committed since W72) rotates the guarding triple
`[zeta, Y] = [[sigma, x_0], x_1]` onto `[[X,Y],S] * [[S,Y],X]` (`gRsd_zeta_Y`), an s-legged
and an x-legged triple, which are slot costs of the engine.  So the bundle
`zeta^2 [zeta, Y]` closes the bracket square with no leftover, and the `sq(ker bY)`-framing
was needlessly pessimistic.  Per-clause honesty on the wave-86 map: the "triple brackets
with s/x legs are engine costs" clause was right; the "y-legged triples cancel among
themselves" clause was right where it was applied (the two-y triples and the y-squares do
pair off exactly); only the "reachable ONLY inside bundles" clause was wrong, and it was
exactly the clause that generated the open question.  Neither `gGen_record_one` nor the
`gDelta` functionals were needed: the decision is an explicit witness, not a basis
computation.  (The `gDelta` functionals could not have refuted here anyway: every atom in
sight has layer-bit reading `0` for every row, by the same `v_2`-bookkeeping as wave 74's
section 6.)

## The arithmetic seed

`gRsd_pivotExp_congr : 4 | sqPivotExp + 1`, i.e. `c_0 = 3 mod 4`.  From `X^{c_0} = S`,
`X = 5 mod 16`, `S = 13 mod 16`: were `c_0 = 1 mod 4`, `S X^{-1}` would be a `Z_2`-power of
`X^4` inside the closed subgroup `1 + 16 Z_2`, against `S - X = 8 * unit` exactly.  This
one bit makes the pivot split `W = S(XZ)` with `Z` CENTRAL in `Q_4` (`gRsd_W_split`), which
is what collapses every pivot-power bracket onto the two core letters and makes the whole
residue analysis five-atom finite.

## The per-residue table (all in the Lean)

Atoms: `zeta = [S,X]`, `ZX = [zeta,X]`, `ZS = [zeta,S]`, `xiS = [S,Y]`, `xiX = [X,Y]`,
the y-block `KillY = xiS^2 xiX^2 [[S,Y],X][[S,Y],S][[X,Y],X][[X,Y],S]`, the two-y pair
`YY = [[S,Y],Y][[X,Y],Y]`.  Write `A - 1 = B + 2t`.

| residue                | defect (proved)                   | witness `(e_0, e_1, e_2)`             |
|------------------------|-----------------------------------|---------------------------------------|
| `2 ∣ B`, `2 ∣ t`       | `1` (`gRsd_defect_even_even_t`)   | bare (`gRsd_nonempty_four_half`)      |
| `2 ∣ B`, `t` odd       | `KillE = zeta^2 ZX ZS`            | `(zeta xiS, zeta xiX, zeta)`          |
| `B` odd, `2 ∣ t`       | `KillO = ZX KillY YY`             | `(xiS xiX, zeta(xiS xiX), xiS xiX)`   |
| `B` odd, `t` odd       | `KillO' = zeta^2 ZS KillY YY`     | `(zeta xiS, xiX, zeta(xiS xiX))`      |

The witnesses are pure commutator words in the three letters, hence carrier elements with
no row bookkeeping (`gRsd_commP_mem_corr`); handle slots stay at `1` at every residue.
Each kill is `defect * cost = cost^2 = 1`: the cost lemma evaluates the engine cost of the
witness to EXACTLY the defect element, and everything in sight is a central involution of
`lambda_3/lambda_4` (`zLayer_sq` + `gLad_cost_mem` close the equation).

The ticket's three residues sit in the table as: scaling ray at `e = 3 mod 4` is row 2
(`B = 0`, `t` odd); translation ray at `c = 2 mod 4` is row 1 (`B = 2 mod 4`, `t` even),
so that residue is FREE with the bare frame, which wave 86 did not know; translation ray at
odd `c` is row 4 (`t = c(1 - c_0)/2` is odd because `c_0 = 3 mod 4`).  Rows 1 to 4
together cover the whole unit locus, beyond the ticket's rays.

## Two findings the wave-86 analysis did not have

1. **The half locus is free.**  On `2 ∣ B` every twist class of the bare defect dies and
   the lambda_2-part `[S,Q][Q,X]` cancels EXACTLY (at `B = 2 mod 4` the two factors are
   the same involution, `gRsd_S_Qeven` and `gRsd_Qeven_X` both equal `KillE`), so the
   even-locus defect is the excess cost alone (`gRsd_defect_even`).  The bare frame
   therefore solves rung 4 on all of `2 ∣ B`, `4 ∣ A - 1 - B`: the quarter locus of
   `gLad_defect_bare_quarter`, doubled.

2. **The even kill element is universal.**  The one nontrivial even-locus defect and the
   excess-cost contribution at every odd `t` are the SAME element
   `KillE = zeta^2 [zeta,X] [zeta,S]` (`gRsd_Zcost_odd_t`, at every `B`), and the
   odd-locus defects differ from each other by exactly it (`KillO' = KillE * KillO` up to
   the central order).

## What remains

Rungs `k >= 5`.  Nothing here decides them: each is a fresh linear-algebra question in
`lambda_{k-1}/lambda_k`, priced by the wave-86 engine (`gLad_step` at `j = k - 2`) as
`defect(solution one rung down) in image(gLadCost)`.  The residue of the odd route is now
`∀ A B on the unit locus, ∀ k >= 5, (gRowSet h A B k).Nonempty`, consumed by
`gRsd_clearing_of_forall_class_five`.  The natural W88 ticket: run THIS module's method one
level up on the rung-4 solutions just constructed (their class-5 defect is computable by
the same atom calculus, one letter deeper), and look for the uniform-in-`k` pattern; the
M6 ladder sits at the same threshold and the two should be compared per level.

## Pins (101 declarations, verified at gen time)

Everything through section 9, including `gRsd_pivotExp_congr`, the full atom table, the
four defect forms, the four kills, `gRsd_nonempty_four`, `gRsd_nonempty_of_le_four`,
`gRsd_pair_of_forall_class_five`, `gRsd_modelMove_of_forall_class_five`, and
`gRsd_clearing_of_forall_class_five`, prints **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset.  The two section-9b seam composites
(`gRsd_supply_of_forall_class_five`, `gRsd_candidateEquiv_of_forall_class_five`) print
std-3 plus the wave-83 seam's four census members
(`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`, the two `Foundations`
members).  No census axiom enters the rung-4 decision itself.  The census is unchanged.
