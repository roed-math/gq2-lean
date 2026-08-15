# W82-SEAM lane note

Lane target: the two residues wave 81 left on the odd row. T1: the absent model computation
`demushkinQ (D_sq h) = 2`. T2: the marked forward supply `SqMarkedForwardSupply B h`, attacked
through the halved relator clause. New module: `GQ2/Dyadic/Instances/OddSeam.lean`, prefix
`oddSeam`, based at `a45bc557`; gen'd green against the mirror. No new axiom, no sorry, no
native_decide; `B` is a binder in every pin (no B5, no B5-K).

## T1: `demushkinQ (D_sq h) = 2` at every h, std-3 (DONE)

`SqCore/DsqDemushkin.lean` recorded the value as absent from the tree. The lane built the
abelianization frame in the `NFrameExists.lean` pattern: the abelianized relator is
`rho_sq = -4x0 + 2x1` (`sqRelWord_comm`), Smith form `D_sq(h)^ab = Z/2 + Z2^(2+2h)` with
torsion generator `t = x1 - 2x0`. Two differences from the N clone, both forced by the
relator: the free `x0`-coordinate is the TWO-SLOT functional `x0 -> 1, x1 -> 2` (the relation
vector pairs the two wild letters), and the torsion coordinate sits at `x1`, not at the marked
letter. Key declarations:

- `oddSeamAbEquiv : D_sq(h)^ab as a group = Z/2 x Z2 x Z2 x Z2^(2h)` (bare MulEquiv; the
  generic count `MarkedCore.demushkinQ_of_torsionEquivZMod` needs no continuity, so none is
  proved).
- `oddSeam_demushkinQ_DSq (h) : demushkinQ (D_sq h) = 2`. **std-3.** The odd row's third
  Demushkin invariant, previously absent, now axiom-free.
- `oddSeam_torsionPremise`: at every `[K : Q2] = 2h + 1` over the bundle,
  `MaxProTwoAbTorsionGeneratedByFieldRoots B` holds, via wave 81's relocation
  `oddId_torsionPremise_iff_model`. {B1, B6, B7, B11a}. The per-field local-CFT torsion
  premise of `DemushkinQRamifiedI.lean` is DISCHARGED at every odd-degree field at once.
- `oddSeam_demushkinQ_galK`: `demushkinQ (G_K(2)) = 2` at every odd degree. Same census. With
  `oddId_chiCycKTwo_surjective` and `oddId_demushkinRank` the odd invariant triple
  `(im chi, rank, q) = (Z2^x, [K : Q2] + 2, 2)` is complete over the bundle.
- Stress pin: `demushkinQ (D_sq h) /= demushkinQ (D_N 1 h)` (2 vs 4): the q-invariant
  separates the square core from the alpha = 1 N core at every handle count.

## T2: the seam calculus (three exact statements; the seam itself stays open at h >= 1)

- **Wave 80 self-improves the seam, std-3.** `oddSeam_supply_iff_fullMarking`: the supply's
  two selected rows are equivalent to an oriented equivalence carrying the WHOLE standard
  marking `nu_sq` on all `3 + 2h` generators. Proof: pull the field marking back, correct by
  `SqCore.gOdd_markedMatching` (the wave-80 chi-preserving matcher at exact rows), compose.
  Consequences, both std-3: the live bridge
  `exists_orientedEquiv_fullNu_of_orientedClearAtUnitPivot` holds with its model binder
  `SqNuOrientedClearAtUnitPivot h` DELETED (and without the filtration input), and the L-row
  pro-2 block `MarkedCoreRealization (D_sq h) (lNu h)` costs the supply alone
  (`oddSeam_realization_of_supply`): no chi-free clearing binder, no frame residual, where the
  committed route `markedCoreRealization_oddDegree` consumed both.
- **The frame form is exact.** `oddSeam_supply_iff_cupAdaptedFrame` (at `hdeg`): the supply is
  equivalent to ONE cup-adapted Frattini frame killing the improved relator and carrying the
  two nu-rows at slots 0, 1. Forward is `frameOfOrientedEquiv` on the full-marking equivalence
  plus the committed `isCupAdapted_frameOfOrientedEquiv` ({B1, B6} for the frame direction);
  backward is odd-degree Demushkin rigidity `sqMarkedForwardSupply_of_presentingFrame`, which
  does NOT consume cup-adaptation ({B1, B6, B7} for the iff). Reading: the halved relator
  clause `SqCupAdaptedFrameRelator K` (same conclusion at EVERY cup-adapted frame) overshoots
  the seam by exactly its quantifier; the seam IS its exists-row-marked instance.
- **The relator clause produces the seam, h-explicitly.** `oddSeam_supply_of_relator`:
  `SqCupAdaptedFrameRelator K` implies `SqMarkedForwardSupply B h` at `[K : Q2] = 2h + 1`,
  through `sqCupAdaptedFramePresentation_of_relator` and the committed nu-endpoint wiring.
  {B1, B6, B7, B11a}.

NOT done, stated honestly: neither `SqCupAdaptedFrameRelator K` nor the seam is discharged at
`h >= 1`. The two nu-rows are arithmetic (PivotNu section 5: a marking
interface-indistinguishable from the standard one carries the opposite pivot row, so no
orientation-plus-interface argument supplies them; exact rows reduce to mod-2 shadows and the
pivot parity is a target invariant), and the relator above level three is the stage lane's
open problem. The wave-80 dividend used here is exactly the model-side transitivity; per the
wave-81 prediction it cannot reach the rows themselves, and this lane confirms that boundary:
mark transitivity converts rows-once-held into everything, it does not create them.

## T3: acceptance composites (all {B1, B6, B7, B11a})

- `oddSeam_genAsmBranch_L_of_relator`: over the halved relator clause, every odd-degree `K`
  sits on the `L h` row of the general assembly.
- `oddSeam_realization_of_relator`: the L-row pro-2 block over the clause, no clearing binder.
- `oddSeam_candidate_equiv_galK_of_relator`: over the clause, what
  `genAsm_candidate_equiv_galK` still needs at odd degree is exactly the two record blocks,
  `GenAsmFieldInputs` (structural) plus `GenAsmRowResidual` (exactLifting, stokes,
  determinant, cand). The record blocks are the whole remaining distance.
- Degree-one floor pins (section 5): at `[K : Q2] = 1` the seam is the committed theorem, so
  the full marking, the cup-adapted row-marked presenting frame, the `h = 0` pro-2 block, and
  the torsion premise are all unconditional over bundle plus filtration.

## Where the seam now sits

One Prop at `h >= 1`, unchanged in name: `SqMarkedForwardSupply B h`. Its exact worth is now
maximal (full marked oriented identification, hence the pro-2 block, std-3 from it). Its exact
cost is now minimal-frame-shaped: one cup-adapted presenting frame with the two nu-rows. Its
cheapest committed producer is unchanged: `SqCupAdaptedFrameRelator K`, whose gap is entirely
above level three on the frame's own generators.

## What W83 needs

1. **The relator clause, or the single frame.** Either discharge `SqCupAdaptedFrameRelator K`
   (kill the relator above level three on every cup-adapted frame), or produce ONE cup-adapted
   frame with relator plus rows directly; by `oddSeam_supply_iff_cupAdaptedFrame` the latter
   is the seam on the nose. The row half is arithmetic (mod-2 shadows suffice by PivotNu
   section 2; the ramified-i hypothesis makes nu-bar an independent direction per PivotNu
   section 5), so a frame ticket can now aim at: cup-adapted frame + relator + two MOD-2 rows.
2. **The record blocks at the L row**: ASK exactLifting + stokes wiring, the determinant
   wiring flagged by W79-HOUSE, and the CAND `WordCertificate` over `D_sq h` (no producer at
   free `h`). T1's abelianization frame (`oddSeamAbEquiv`, with word calculus
   `oddSeamAbWord`, coordinate homs and `oddSeam_topAb_coord`) is new tooling a CAND lane can
   consume.
3. **Housekeeping**: register `GQ2.Dyadic.Instances.OddSeam` in `GQ2.lean` (this lane does not
   edit it); `SqCore/DsqDemushkin.lean`'s "not proved anywhere in the tree" sentence about
   `demushkinQ (D_sq h) = 2` is now stale and should cite `oddSeam_demushkinQ_DSq`.
