# W85-BLOCKS: the record's remaining blocks

Lane note for `claude/w85-blocks`, based on `76f21241`.  One new module,
`GQ2/Dyadic/Instances/RecordBlocks.lean` (prefix `recBl`), 24 declarations, 23 of them std-3.

W84-CLAUSES measured the `ℚ₂(√5)` row down to four things and queued them as W85-A..D.  This
lane worked all four.  Two closed, one closed as far as the architecture allows, and one turned
out to be a **correction to the ticket** rather than a discharge.

---

## §1 What the row costs now

| W83-RECORDS obligation | after W84-CLAUSES | after this lane |
| --- | --- | --- |
| `cand` `exactLifting` at `Γ_R` | `askCStageVanishing` at `Γ_R`, an equivalence | unchanged; §4 narrows how it could be refuted |
| `cand` `scalar` at `Γ_R` | discharged | discharged |
| `cand` `stokes` at `Γ_R` | **open**, "the lane did not narrow it" | **discharged**: `recBl_mCand_stokes`, unconditional at `2 ≤ α` |
| `cand` `determinant` at `Γ_R` | **open**, "no candidate-side Gauss-`Z` supplier exists anywhere outside the `L` row" | reduced to `recBlWordPhaseSupply`, two even-degree wall-handle phase computations |
| `ASK` `exactLifting` at `G_K` | `askCStageVanishing` at `G_K` | unchanged |
| `ASK` `stokes` at `G_K` | discharged | discharged |

The acceptance statement is `recBl_candidate_equiv_galK_sqrtFive`, which is
`rowCl_candidate_equiv_galK_sqrtFive` with the `candStokes` binder **removed outright** and the
`candDeterminant` binder **replaced by the word-phase supply**.  The two coefficient `Prop`s are
untouched.

Per clause, per row, read off the Lean:

| clause | `M0 2 0` (`√5`) | `M0 3 0` (`√2`) | `N0 2 0` (`√-2`) | `Mpc 2 1 false 1 0` (`√10`) |
| --- | --- | --- | --- | --- |
| `exactLifting` | `askCStageVanishing` at `Γ_R` | same | same | **same, new this lane** (§2) |
| `scalar` | theorem (W84) | theorem | theorem | theorem |
| `stokes` | **theorem** (§3) | **theorem** (§3, same `α`-generic statement) | not attempted here | not attempted here |
| `determinant` | word-phase supply (§5) | word-phase supply (§5) | open | open |

§3 and §5 are stated at general `(α, h, q)` with `2 ≤ α`, `q ≠ 0`, `Even q`, so both frozen `M0`
rows get them at once.  The `N0` twin was not transcribed; it is mechanical (the resolver
`Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis` and `NCompact.uniformPushedHsimp` both
exist) and is the obvious first W86 item.

---

## §2 W85-D, the `Mpc` bundle: closed, and the note's obstruction was stale

W84-CLAUSES §2 narrowed "the residue is uniform across the four rows" to three, because
`MProcyclicExact` had no `exactLiftingRN_unconditional`.  The reason it looked hard is
`MpcPairings.lean:72`, which records `MProcyclicExact.RamifiedNormalPairingSeparates` as **not**
proved there with a precise obstruction: on the ramified reading neither commutator base is
trivial, so `EvenHeisPure.heisCommR_of_trivial_right` does not apply and a fully general
commutator law is needed first.

That obstruction was subsequently removed and the docstring was never revisited.
`MpcRamifiedRow.lean:988` proves `MProcyclicExact.ramifiedNormalPairingSeparates` at `1 ≤ α` for
**every** display, unconditionally.  `MpcSelectedScalar.lean:206` already reduced
`UniformPushedHsimp` to exactly that one input.  Composing them is the whole ticket:

* `recBl_mpc_uniformPushedHsimp`
* `recBl_mpc_exactLiftingRN`

**Honest caveat on the word "unconditional".**  `MCompact` quantifies over `(α, h, q)` and
nothing else, so its bundle is unconditional literally.  The `Mpc` carrier is indexed by a
*display* of the field unit `η`, and the reduction needs the display to be well formed and to
represent `η`.  Both are fields of `MpcDisplayFor η`, which is what the field seam presents, so
the honest form is **unconditional given the display package**.  `1 ≤ r` is carried too, supplied
at the seam by `FieldBranchSelection.valid`.

**Correction owed to `MpcPairings.lean:72`**: its obstruction paragraph should be marked
superseded, with a pointer to `MpcRamifiedRow.lean:988`.  A housekeeping lane should do it; this
lane may not edit existing modules.

---

## §3 W85-B, the Stokes conjuncts: closed, and cheaper than the original

W84-CLAUSES declined this one on the grounds that the `L` row's four conjuncts are 470 lines with
`maxHeartbeats 1200000` on one of them, and that "that is a lane, not a section".  On inspection
`GammaLAnalyticLeaves` uses nothing about the `L` word except five things, and the compact-`M`
row has all five:

| what the `L` proof needs | `M` counterpart |
| --- | --- |
| uniform Heisenberg resolver + Stokes endpoint | `Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis` |
| admissible marked presentation | `isAdmissibleMarkedPresentation_gammaR (2 + 2*h) q (mCompactW α h)` |
| a degree identity | `MCompact.degree` |
| a surjective datum map | `MCompact.datumRho_surjective` |
| the word residue | `MCompact.uniformPushedHsimp`, **unconditional at `2 ≤ α`** |

So it is a transcription.  Landed: `recBl_mCand_tcocycle`, `recBl_mCand_hsep`,
`recBl_mCand_hrsep`, `recBl_mCand_hpartial`, `recBl_mCand_hZcard`, packed as
`recBl_mCand_stokes_of_uniformPushed` and then, with no new hypothesis at all, as
`recBl_mCand_stokes`.

Three things are genuinely different from the `L` transcription and are recorded in the module:

1. **The degree is even.**  `MCompact.degree` feeds the count suppliers `n = 2*h + 2`; the row
   records spell the same number `2 + 2*h`.  These are not defeq as `Nat` and `SourceNumerics` is
   indexed by the degree, so the lane carries `recBl_stokes_standard_congr`.  **No Stokes twin of
   `rowCl_scalar_standard_congr` existed in the tree**; this is it.  `recBl_determinant_standard_congr`
   is the same thing for the determinant.
2. **`hpartial` carries `1 ≤ α` and `q ≠ 0`**, which the `L` twin does not, because
   `MCompact.cardH2_of_uniformPushed` does.  Everything downstream inherits them.  At `2 ≤ α`
   they are free.
3. **No raised heartbeats.**  The five `L` originals carry `1200000` or `1600000`; every `M`
   transcription elaborates inside the default budget.

Nothing here touches Tate duality or a local Euler characteristic.  The alternative producer
`KAnalytic.stokesDualityCertificate_of_localDualityG` takes both, and neither is available at an
abstract candidate carrier.

---

## §4 W85-A, the coefficient frame: the ticket's starting point is refuted

This was the note's sharpest item, and the answer is a **correction**, not a discharge.

W84-CLAUSES proposed building the refuting frame at `MCompact.datumRho`, "a handle-uniform
surjection onto a nontrivial finite 2-group".  It cannot be done there, and the reason is
structural rather than about `datumRho`.

The refutation handle `rowCl_mCand_isEmpty_boundaryLifts` is gated on a
`SectionSeven.MinimalBlock` with `1 < #Φ(K)`.  `MinimalBlock.nontrivial_action` demands a `y` and
a `p ∈ P` with `y p y⁻¹ p⁻¹ ∉ S`: the chief factor `P/S` must be a **nontrivial** `Y`-module.  A
nilpotent `Y` has no such factor.  Proved as `recBl_minimalBlock_isEmpty_of_nilpotent`:

> For `Y` nilpotent and any `L : Subgroup Y`, `MinimalBlock L` is empty.

Proof shape, since it needed one piece of new API: mathlib's `Subgroup.lowerCentralSeries P` is
the lower central series of `P` **as a group in its own right** (`⁅Pₙ, P⁆`) and does not see the
outer action, so the module defines the `Y`-lower central series `P₀ = P`, `Pₙ₊₁ = ⁅Y, Pₙ⁆`
directly and bounds it by mathlib's series on `⊤`.  At each step the chief dichotomy gives
`S ⊔ Pₙ = P` or `S ⊔ Pₙ = S`; the second makes all of `P` central mod `S`, contradicting
`nontrivial_action`.  Nilpotency drives `Pₙ` to `⊥` and the last step reads `S = P`, against
`S < P`.  The step conclusion is carried by `centralMod S`, the preimage of `Z(Y/S)`, which is
what avoids having to split the join `S ⊔ Pₙ` into a product.

Corollaries: `recBl_minimalBlock_isEmpty_of_isPGroup` (every finite `p`-group) and
`recBl_minimalBlock_isEmpty_of_sq` (every exponent-2 group).  `datumRho`'s target
`Base ⧸ datum.M` has exponent 2 by `SqrtNeg2.datumQuot_sq`, so it is dead twice over.

**Consequence for the ticket.**  Any refuting frame must have a target `Y` that is **not
nilpotent**: one whose odd part acts nontrivially on a 2-group chief factor.  The smallest shape
that can work has `L_Y = Q₈`, `S = Z(Q₈)`, `P = K = Q₈` and `H = Y/Q₈` of order 3, where
`Φ(K) = Z(Q₈)` has order 2.  Nothing in the `M` row's resolver package produces a boundary-framed
surjection of the candidate group onto such a `Y`, and this lane did not build one.

So `askCStageVanishing` at the candidate carrier is **still open**, the cheap route to refuting
it is closed, and the owner call still rests where W81-ASK left it: restate the records against
`ExactLiftingSemanticsRN`, which `rowCl_rn_both_carriers_sqrtFive` already supports at both
carriers with no residue on either.

---

## §5 W85-C, the candidate determinant: the reduction lands, the supply does not

Two routes exist and only one is legitimate.

**The route not taken.**  `GQ2.Dyadic.affineDeterminant_galK` (`GaussZ/FinalDK.lean:915`)
discharges both Gauss-`Z` clauses internally, through `gaussZResidueDK_unramified` and
`gaussZResidueDK_ramified`.  Each takes `D : TateDualityG ↥U 2`, produced only by
`FieldData.tateDualityGalK`, which is gated on `IsLocalDualizingGroup` and hence on an open
finite-index embedding into the absolute Galois group.  A word group has no such embedding
without the presentation theorem this campaign is trying to prove, so using it here is circular;
`GammaLDualityBoundary`'s module docstring already says exactly this about `GammaL`.  The
ramified branch additionally wants a `RamifiedCertificate` indexed by the field.  **No
declaration in the new module takes any of the three.**  (`recBl_candidate_equiv_galK_sqrtFive`
does pin the `tateDualityAt` *axiom*, but through the general theorem and the row's arithmetic
inputs, exactly as `rowCl_candidate_equiv_galK_sqrtFive` already did, not through §5.)

**The route taken.**  `LSquare.gaussZResidueK_of_wordPhase` takes no duality at all: only
finiteness of the cocycle group, absence of nonzero fixed vectors, and a `WordPhaseResidueK`.
`recBl_mCand_determinant_of_wordPhaseSupply` is the compact-`M` twin of
`LSquare.affineDeterminantCertificate_of_wordPhaseSupply`, with `recBlWordPhaseSupply` the
binder-for-binder `M` analogue of `DeterminantWordPhaseSupply`.  Note that
`DeterminantWordPhaseSupply` is **not** word-agnostic despite what W84-CLAUSES §1 says: its
`tame` binder has type `ContinuousMonoidHom (gamma h q) (Tq q)` with `gamma h q = GammaR (2*h+1) q (lSqW h)`,
so the `L` word and the odd degree are baked into the type of every field.  A fresh definition was
required, not an instantiation.

The finiteness step is where §3 pays for itself: the `L` proof calls
`hZcard_of_uniformPushed`, and no `M` counterpart existed until this lane built
`recBl_mCand_hZcard`.

**What is still missing, precisely.**  The `L` supply producers
`wordPhaseResidueK_unramified_lSq` and `wordPhaseResidueK_ramified_lSq` run through
`lSqWallHandlePhase_gaussSum_standardUnram` / `…Ram`, which exist only at odd degree `2h + 1`.
The compact-`M` word offers only the unsigned magnitude
(`Certificates.MCompact.mCompact_gauss_pow`), and there are no even-degree sign pins.  So the
row's residual moved from "the whole determinant certificate, with no supplier anywhere" to "two
even-degree wall-handle phase computations", which is strictly smaller and purely combinatorial.

**The two `n = 2` numerics lemmas: confirmed absent, and routed around.**
`Recursion/Numerics.lean` has a `section NEqOne` with six lemmas and there is no `NEqTwo`;
`standardNumerics_two_*` does not exist anywhere in the tree.  What is genuinely missing is the
even-degree sign collapse `(-1)^(2h+2) = 1` that would reduce `gaussUnram m` to `+2^(n*m)`
(`Even.neg_one_pow` is never used anywhere under `GQ2/`).  This lane routes around it: `gaussUnram`
and `gaussRam` are carried symbolically as `(standardNumerics (2*h+2)).gauss…` and never
evaluated, so no numerics fact is needed at the bridge layer.  Whoever builds the supply will
need both.

---

## §6 Axioms

24 declarations pinned in the file.

* **23 std-3** (`propext`, `Classical.choice`, `Quot.sound`): everything this lane proves.
* **1 with campaign axioms**: `recBl_candidate_equiv_galK_sqrtFive`, carrying std-3 plus
  `{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic,
  hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction,
  relativeStiefelWhitney_dyadic}`.  Term for term the set already on
  `rowCl_candidate_equiv_galK_sqrtFive` and on W83-RECORDS' §5 union.  **Discharging the row's
  `stokes` clause and reducing its `determinant` clause adds no axiom to the row's record.**

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options.  The one
option set is `linter.unusedVariables`, on `recBlWordPhaseSupply`, for the same reason the `L`
structure sets it.

---

## §7 What W86 should pick up

1. **The `N0` Stokes and determinant twins.**  §3 and §5 transcribe with `nCompactFam` for
   `mCompactFam`, `NCompact.uniformPushedHsimp` for `MCompact.uniformPushedHsimp`, and
   `Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis`.  All three exist.  That would put
   three of the four rows on the same footing.
2. **The even-degree wall-handle phase**, `recBlWordPhaseSupply`'s two clauses.  This is now the
   single largest analytic item on the `M` rows, and it is combinatorial: an even-degree twin of
   `GammaLUnramifiedPhase`/`GammaLRamifiedPhase`, plus the `n = 2` numerics sign collapse.
3. **A non-nilpotent frame**, if anyone still wants to refute the frozen coefficient by
   counterexample.  §4 says what shape it must have; the hard part is the boundary equation, not
   the block.  The alternative, and W81-ASK's and W84-CLAUSES' shared recommendation, is to
   restate the records against `ExactLiftingSemanticsRN` and stop carrying the frozen coefficient
   at all.
4. **Housekeeping**, none of which this lane could do:
   * `MpcPairings.lean:72`'s obstruction paragraph is stale (superseded by
     `MpcRamifiedRow.lean:988`); mark it.
   * `SqrtNeg2.lean:893`'s "no candidate-side supplier in the repository" is now stale for the
     `L` row and, after §5, for the `M` rows' *reduction*.  It remains accurate for the two
     Gauss-`Z` clauses at `nCompactW`, `mpcW`, `npcW`.
   * W84-CLAUSES §2's "the residue is uniform across three rows, not four" should go back to
     **four**: §2 of this lane supplies the missing `Mpc` bundle.
   * W84-CLAUSES §1's description of `DeterminantWordPhaseSupply` as "word-agnostic in its
     statement" is wrong; see §5.
   * `GQ2/Dyadic/Instances/RecordBlocks.lean` needs registering in `GQ2.lean`, after
     `GQ2.Dyadic.Instances.RowClauses`, `…MpcRamifiedRow` and `…MpcSelectedScalar`.
