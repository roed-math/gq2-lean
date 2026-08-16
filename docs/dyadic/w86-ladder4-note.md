# W86-LADDER4 lane note

Lane target: the row-move ladder at k >= 4, extending wave 85's record (k <= 3 proved), aiming
at `gLad_clearing (h) : SqNuOrientedClearAtUnitPivot h` or the sharpest per-rung record with
the first obstruction in closed form. Module: `GQ2/Dyadic/SqCore/GradedRowLadder.lean`
(prefix `gLad`), green against the mirror at base `f0de6ad5`. No sorry, no new axiom, no
native_decide.

## Verdict up front

The clearing did NOT land; what landed is the full increment engine (the ticket's named
deliverable, the M6 `mpcBld_incr_*` pattern at the square-commutator core, uniform in the
class), the class-4 defect of the class-3 solution in EXACT closed form with no parity split,
and the first quarter of rung 4 as a theorem: on `4 | A - 1`, `4 | B` the bare frame solves
rung 4 outright, which contains the scaling ray at every `e = 1 mod 4`. Off the quarter locus
rung 4 is now one explicit equation in the elementary abelian layer `lambda_3/lambda_4`
(defect times cost equals one), with both sides in closed form. The reachability analysis of
that equation (below) locates the first genuine obstruction candidate in the square-type
part of the defect; it is NOT discharged and NOT refuted here.

## The chain (all in the one module)

1. **The engine, uniform in the class.** In `Q_{j+2}`, a `lambda_j`-factor `eps` on one slot
   of `sqWord s x y = (x^s)^{-1} x^{-3} y^2 [y, y^s]` costs exactly one central element:

   - sigma slot: `[eps, x]` (`gLad_incr_s`);
   - `x0`-slot: `[s, eps]`, the fourth power `eps^{-4}` dies outright and the two conjugation
     brackets cancel in pairs (`gLad_incr_x`);
   - `x1`-slot: the knob bundle `eps^2 [eps, y]` (`gLad_incr_y`), the gTower bundle shape;
   - handle slots: single brackets (`gLad_incr_pair`, `gLad_incr_handle`).

   `gLad_relWord_incr` prices a full tuple as `gLadCost` (three slot costs then the handle
   brackets); `gLad_step` turns a rung-(j+1) solution of `gRowSet` plus a carrier tuple whose
   cost kills the defect into a rung-(j+2) solution. So EVERY rung is exact linear algebra in
   `lambda_{j+1}/lambda_{j+2}`: the defect is a central class (`gLad_defect_mem`), the
   reachable increments are bracket images against the letters as they stand plus the
   `x1`-bundles, and nothing else moves. This is the wave-84/85 control result built into the
   statements: there is no greedy search left to run, only per-rung linear algebra.

2. **The pivot twist, closed form, no parity.** `gLad_qtwist`: for ARBITRARY `s x y q` in
   `Q_4`,

   `sqWord (sq) (xq) (yq^2) = [s,q] [q,x] sqWord s x y * ([[x,q],q] [[q,s],q] [q,x]^2 [q^2,y] [y,[y,q]])`.

   Exactly. The proof pivots on `(xq)^4 = x^4 q^4 [q,x]^2` (`gLad_qtwist_four`) and on the
   commutator slot being blind up to `[y,[y,q]]` (`gLad_qtwist_commslot`). The identity
   `[x,q]^4 = 1` is consumed in the assembly: the `lambda_2`-part `[s,q][q,x]` is not central
   term by term, only as a product, and only on pivot powers.

3. **The class-4 defect, exactly.** `gLad_defect_bare`: with `A - 1 = B + 2t` and `Q` the
   `B`-th pivot power (`gLadQ h B`), the `Q_4`-residue of the bare relator word is

   `[S,Q] [Q,X] * ([[X,Q],Q] [[Q,S],Q] [Q,X]^2 [Q^2,Y] [Y,[Y,Q]] [(w^t)^2, X*Q])`.

   One formula for every point of the unit locus; wave 85's class-3 parity argument is its
   shadow one level down. `gLad_relWord_four` extends it to arbitrary carrier corrections:
   residue = defect times `gLadCost` on the bare marked letters.

4. **Rung 4 on the quarter locus.** `4 | A-1` and `4 | B` make `Q` a square of a square:
   every defect letter is then central or dead and the closed form collapses to `1`
   (`gLad_defect_bare_quarter`), so the BARE frame solves rung 4
   (`gLad_nonempty_four_quarter`); the scaling ray at `e = 1 mod 4` is an instance
   (`gLad_nonempty_four_scale`). `gLad_nonempty_four_of_kill` packages the general rung:
   nonemptiness follows from any carrier tuple whose cost kills the closed-form defect.

## The reachability analysis (prose, the honest map of what remains)

Off the quarter locus the defect reduces, by splitting `Q` through the parity of `B` and `t`
into pivot letters and squares, to three species in `lambda_3/lambda_4`:

- **triple brackets with s/x/handle legs** (`[[s,p],p]`-type): all reachable. The engine's
  bracket costs read `[eps, letters as they stand]`, and on the unit locus the mod-2
  determinant `A - c0 B` being a unit makes the twisted letters span the same brackets as the
  bare ones. Pivot legs split as `[eps, w] = [eps, s][eps, x]`-mod-dead, so every such term
  is a cost.
- **the y-legged triples** (`[e, y]`-type): reachable ONLY inside bundles `eps^2 [eps, y]`.
  Isolated y-triples produced by matching the squares (next item) must cancel among
  themselves. The one cancellation this lane verified in prose: bundle over
  `e_1 = [s,p], e_2 = [p,x]` leaves `[e_1 e_2, y]`, and `e_1 e_2` has trivial
  `lambda_2`-class exactly because the pivot's letter content is `s + x`, so that leftover
  dies. This is the same product-centrality that makes `[S,Q][Q,X]` central.
- **bracket squares** (`[s,p]^2`-type): the genuine question. Squares are reachable only
  through bundles, and a bundle pays `eps^2` AND `[eps, y]` together: pure squares are
  reachable iff the target square-class lies in `sq(ker bY)` where `bY` is the y-bracket
  functional on carrier classes. The candidates in `ker bY` found so far: `x1^2` (killing
  `y^4`-terms, since powers of `y` commute), and total relation-classes. Whether
  `[s,p]^2`-type targets lie in that image is EXACTLY the first linear-algebra question the
  graded supply machinery (the `gGen_record` generation of the layer, and the `gDelta`
  functionals for membership decisions) should decide; the wave-80 kill `gGen_killAt` gives
  the defect's membership in knobs times towers once its readers vanish, and the tower part
  is the non-cost part. If the answer is negative at some residue of `(A, B) mod 4`, that is
  a refutation of the corresponding row move with the present carrier, and the
  carrier-enlargement fallback (`ker lambda ∩ ker nuSq`, with handle content and the torsion
  letter, at the price of redoing generation with a determinant condition) activates.

⚠ **[W87-BLOCK, as of the wave-87 merge: DECIDED, positively, at all three residues, and the
y-legged clause above is FALSE as stated.**  Triples with both inner letters distinct from
`x₁` are reachable OUTSIDE bundles: Hall-Witt in `Q₄` (the committed `cfourDef_jacobi_solve`)
rotates the guarding triple `[ζ,Y] = [[σ,x₀],x₁]` onto `[[X,Y],S]·[[S,Y],X]` (`gRsd_zeta_Y`),
which are slot costs, and the bundle `ζ²[ζ,Y]` then closes the square with no leftover.  The
other two species clauses were right.  Neither `gGen_record_one` nor the `gDelta` functionals
were needed (the functionals are provably blind at the layer bit); the decision is by explicit
witness, with the new arithmetic `4 ∣ sqPivotExp + 1` (`gRsd_pivotExp_congr`) splitting the
pivot as `W = S(XZ)`, `Z` central.  The defect is `1` on the HALF locus `2∣B, 2∣t` (doubling
the quarter locus), and killed by pure commutator words elsewhere: `gRsd_nonempty_four` on the
whole unit locus.  The residual starts at class five; the chain to the clearing is
`gRsd_clearing_of_forall_class_five`.  See `GradedRowResidue.lean` and
`docs/dyadic/w87-block-note.md`.]

## What W87 needs

Either (a) decide `defect in image(gLadCost)` at the three remaining mod-4 residue classes of
`(A - 1, B)` on the two rays, using `gLad_defect_bare` + parity splits of `Q` and the engine
costs, with the square-block decided against the graded supply (`gGen_record_one` generates
`lambda_3/lambda_4`; the `gDelta` functionals decide membership); a positive answer at all
three plus the quarter locus closes rung 4 outright, and the engine then reduces rung 5 to
the same shape one level up (the defect of the rung-4 solution, priced by `gLadCost` at
`j = 3`). Or (b) a proven empty intersection at some residue, which refutes the move for this
carrier and forces the enlargement. The compactness criterion needs no coherence between
rungs: each `gRowSet h A B k` may be solved from scratch.

## Pins (all verified at gen time, 57 declarations)

All of: `gLad_swap`, `gLad_commP_inv`, `gLad_conjP_eq`, `gLad_conjP_mul`,
`gLad_conjP_conjP`, `gLad_zmove4`, `gLad_commP_mem_two`, `gLad_vanish`, `gLad_vanish'`,
`gLad_zLayer_le`, `gLad_le_two`, `gLad_sq_mem_zLayer`, `gLad_pow_four`,
`gLad_commP_zLayer_right`, `gLad_commP_inv_left`, `gLad_commP_inv_right`,
`gLad_commP_cube_left`, `gLad_commP_absorb_right`, `gLad_commP_conj`, `gLad_incr_s`,
`gLad_incr_x`, `gLad_incr_y`, `gLad_incr_pair`, `gLadCost`, `gLad_incr_handle`,
`gLad_sqWord_incr`, `gLad_cost_mem`, `gLad_relWord_incr`, `gLad_mark_mul`,
`gLad_defect_mem`, `gLad_step`, `gLad_sq_mem_two`, `gLad_vanish4`, `gLad_two_comm`,
`gLad_commP_mul_left_two`, `gLad_commP_self_absorb`, `gLad_commP_conj_self`,
`gLad_qtwist_four`, `gLad_qtwist_comm`, `gLad_qtwist_sqslot`, `gLad_qtwist_commslot`,
`gLad_qtwist`, `gLadS`, `gLadX`, `gLadY`, `gLadQ`, `gLadQ_two_mul`, `gLadQ_sq_mem`,
`gLad_defect_bare`, `gLadQ_mem_zLayer_of_four`, `gLad_defect_bare_quarter`,
`gLad_nonempty_four_quarter`, `gLad_nonempty_four_scale`, `gLad_bare_mem_three`,
`gLad_nonempty_four_of_kill`, `gLad_mark_eq_bare_mul`, `gLad_relWord_four` print **std-3**
(`propext`, `Classical.choice`, `Quot.sound`) or a subset of it (the five exact word
identities print `propext` alone or nothing). No census axioms enter anywhere.
