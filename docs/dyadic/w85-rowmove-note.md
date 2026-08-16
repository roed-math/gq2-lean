# W85-ROWMOVE lane note

Lane target: `GClearModelTranslate h c` and `GClearModelScale h d` at every h, composed to
`gRow_clearing (h) : SqNuOrientedClearAtUnitPivot h`, or the sharpest per-class reduction with
the obstruction in closed form. Module: `GQ2/Dyadic/SqCore/GradedRowMove.lean` (prefix `gRow`),
green against the mirror at base `76f21241`. No sorry, no new axiom, no native_decide.

## Verdict up front

The unconditional moves did NOT land, and the honest landing is the reduction the ticket named
as the fallback, pushed one rung further than planned: every clause of the row moves except
one word identity is DISCHARGED, the identity is put on the W84-WORD per-class ladder with a
compactness decision principle, and the ladder's rungs k <= 3 are PROVED on the unit locus.
The first class that can obstruct a row-moving automorphism is class four, the same threshold
at which the M6 ladder's residue starts. The odd route's last item now reads: solve one
explicit word to every class k >= 4 of the two-central tower, with corrections drawn from one
explicit closed carrier.

> **[W86-HOUSE, as of `f0de6ad5`:** "the same threshold at which the M6 ladder's residue starts"
> is stale, and was already stale when this note was written. This lane's own claim is exact and
> unaffected: the row-move residue starts at class four. But `Instances/MpcBuild.lean` merged
> into `dyadic` at `ee22161b`, earlier in the same wave, carrying
> `mpcBld_nonempty_four : (mpcWordSet 4).Nonempty`, so the M6 ladder's residue starts at class
> FIVE. The two ladders are one rung apart, not level. Corrected at both in-tree copies,
> `SqCore/GradedRowMove.lean`'s module doc item 5 and `gRow_pair_of_forall_class_four`.**]**

## The chain (all in the one module)

1. **The row pair.** `GRowPair h A B`: a lambda-preserving automorphism of `D_sq h` whose
   `nu_sq`-rows at `(sigma, x0)` are `(A, B)`. Two rows, no marking binder, no handle clause.
   `gRow_modelMove_of_pair` turns the pair at `(e(1 - c0 b), -(e b))`, with `d e = 1` and
   `d = a - c0 b`, into `GClearModelMove h a b` through wave 84's twist identity; the rays are
   the pairs `(1 - c0 c, -c)` (translate) and `(e, 0)` (scale). `gRow_pair_of_modelMove` is
   the CONVERSE: the pair is exactly as strong as the model move plus lambda-preservation, a
   change of coordinates on the same residual, not a strengthening. Confirmation:
   `gRow_pair_zero` realizes every unit-locus pair at h = 0 through the committed degree-one
   moves (B8 + B3c enter there and only there).

2. **The ansatz owes one equation.** `gRowMark h A B c`: slot i carries
   `gen_i * w^{e_i} * c_i`, `w` the chi-trivial pivot, exponent row `(A-1, B, 2B, 0, ..., 0)`.
   `gRow_pair_of_word`: corrections with trivial lambda-rows (and trivial `nu_sq`-rows at the
   two core slots), a spanning frame, and `sqRelWord (gRowMark h A B c) = 1` produce the pair,
   through the committed frame form `sqAutOfMark` (no inverse words, no composition
   identities). `gRow_modTwoIndep`: on the unit locus `IsUnit (A - c0 B)` any Frattini
   corrections leave the frame spanning; the proof recovers `sigma x0^{-1}`, then the pivot,
   then both letters, from the two twisted slots inside one index-two subgroup at a time,
   using that `A - 1 - B` is even exactly on the unit locus (`gRow_even_of_unit`). No case
   split on parities.

3. **The per-class criterion.** `gRowSet h A B k`: correction tuples in the carrier
   `gRowCorr = lambda_2 ⊓ ker(nuLam) ⊓ ker(nuSq)` whose frame kills the relator to class k.
   Nested, closed, compact; the tower separates (`lim_iInf_twoCentralSeries`);
   `gRow_pair_of_forall_class`: class-k solvability at every k gives the pair outright. If a
   row move is false it fails at a finite class, in a finite 2-group, no inverse limit.

4. **The per-class record.**
   - k <= 2: FREE for EVERY frame and every (A, B): `gRow_relWord_mem_two` exhibits the
     relator word on any marking as a product of squares, commutators and a conjugated
     commutator, all in lambda_2.
   - k = 3: FREE on the unit locus with the BARE frame (`gRow_relWord_bare_mem_three`). In
     the class-three quotient every commutator is central of order two (a private class-2
     calculus of exact laws: bilinearity, inversion rules, square-triviality, the
     `(x p)^4 = x^4` collapse); the twisted word equals the standard relator times the defect
     `[x0, w^B] * [w^B, sigma]`; even B makes `w^B` a square, hence class-three central; odd
     B expands `w^B = w * square` and `w = sigma * (x0 * square)^{-1}`, both defect factors
     read `[x0, sigma]`, and the product is a commutator square. This SUBSUMES the committed
     class-two balance (`PivotCoreMoves` module docstring, prose only, lower-central metric)
     one rung up and in Lean, in the two-central metric the ladder actually uses.
   - k >= 4: OPEN. The exact residue: `gRow_pair_of_forall_class_four`.

5. **Composition through the committed chain.** `gRow_clearing_of_forall_class_four` (and the
   `_of_forall_class` forms, plus per-ray forms): per-class solvability on the unit locus at
   k >= 4 discharges `SqNuOrientedClearAtUnitPivot h` outright through wave 84's
   `gClear_clearing_of_model`. The seam composites `gRow_supply_of_forall_class` and
   `gRow_candidateEquiv_of_forall_class` carry it to `SqMarkedForwardSupply B h` and the
   general theorem at every odd-degree field.

## What the elaboration found

- The wave-80 automorphism factory cannot produce row moves by composition: every factory map
  fixes the plane spanned by lambda and nu_sq in the character lattice pointwise in the only
  usable configuration. The relayed claim that nothing in the tree moves rows was verified,
  and the reduction had to be built from the frame side.
- The syllable-matching shortcut (conjugate the letters, twist sigma by a pivot power) fails
  EXACTLY: the required conjugator equation `[t, s] = w^{1-e}` has an abelianized obstruction
  (`w^{1-e}` is not in the closed derived subgroup unless e = 1). The defect it leaves is
  class-two, which is why the ladder genuinely starts working only at the graded level.
- At class three the defect is not merely solvable but ZERO with bare corrections: the
  lambda_2-carrier corrections are invisible mod lambda_3 (squares and brackets of
  lambda_2-elements die), so rung 3 is decided by the bare frame, and it passes. By the same
  invisibility, rung 4 is the first rung where the carrier corrections act at all: the
  residue's shape at k = 4 is exact linear algebra in `lambda_3/lambda_4` against the bare
  defect, with correction images `[c_i, gen]` and `c_i^2` from `lambda_2`.

## Sharpness, left open honestly

Whether `IsUnit (A - c0 B)` is NECESSARY for `GRowPair h A B` is not settled here, matching
the W84-CLEAR caution: the parity engine does not close because the pair leaves handle rows
free, and both parity cases of the mod-2 argument escape through a possibly-odd handle row of
`nuSq ∘ Psi`. A refutation off the unit locus would need a new invariant; a construction off
it would be a surprise the mod-2 cup form does not forbid on its own.

## Pins (all verified at gen time, 42 declarations)

std-3 (`propext`, `Classical.choice`, `Quot.sound`): `GRowPair`, `gRow_pair_one_zero`,
`gRow_modelMove_of_pair`, `gRow_pair_of_modelMove`, `GRowTranslate`, `GRowScale`,
`gRow_translate_of_pair`, `gRow_scale_of_pair`, `gRow_modelMove_of_ray_pairs`, `gRowExp`,
`gRowMark`, `gRowMark_id`, `gRow_pair_of_word`, `gRowFrat`, `gRow_lambdaTwo_le_frat`,
`gRow_modTwoIndep`, `gRowCorr`, `gRowSet`, `gRowSet_antitone`, `gRow_continuous`,
`gRow_isClosed_set`, `gRow_iInter_nonempty`, `gRow_pair_of_forall_class`,
`gRow_commP_mem_two`, `gRow_commP_mem_three`, `gRow_relWord_mem_two`,
`gRow_nonempty_of_le_two`, `gRow_even_of_unit`, `gRow_relWord_bare_mem_three`,
`gRow_nonempty_of_le_three`, `gRow_pair_of_forall_class_four`,
`gRow_modelMove_of_forall_class`, `gRow_translate_of_forall_class`,
`gRow_scale_of_forall_class`, `gRow_clearing_of_forall_class`,
`gRow_modelMove_of_forall_class_four`, `gRow_translate_of_forall_class_four`,
`gRow_scale_of_forall_class_four`, `gRow_clearing_of_forall_class_four`.
std-3 + {dyadicOrientation, peripheralCyclotomicAction}: `gRow_pair_zero`.
std-3 + {hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
Foundations.absGalQ2_isTopologicallyFinitelyGenerated,
Foundations.absGalQ2_localEulerCharacteristic}: `gRow_supply_of_forall_class`,
`gRow_candidateEquiv_of_forall_class`.

## What W86 needs

The class-four rung: for each (A, B) on the unit locus (the two rays suffice through
`gClear_modelMove_of_ray`), corrections in `gRowCorr` with
`sqRelWord (gRowMark h A B c) ∈ lambda_4`. The computation lives in `Q_4`, a class-three
calculus (commutators of commutators central, squares of commutators central but nontrivial);
the bare defect must be computed exactly and matched against the correction image
`[lambda_2 ∩ kers, gens] + (lambda_2 ∩ kers)^2` inside `lambda_3/lambda_4`. The W84-WORD
control result applies verbatim: greedy stalls carry no information, only exact per-rung
computations count. The M6 off-tree walk passed classes four to six with exact F2
computation; the analogous walk here has handle letters available in nothing (the carrier is
handle-free at degree one by design; if class four obstructs, the first weakening to try is
enlarging the carrier to `ker lambda ∩ ker nuSq`, which admits handle content and the torsion
letter, at the price of redoing generation with a determinant condition).
