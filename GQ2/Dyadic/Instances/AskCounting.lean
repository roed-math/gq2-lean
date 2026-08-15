/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.RStage
import GQ2.Dyadic.Instances.KExactLiftingGalK

/-!
# The ASK counting pack at `G_K`: the surviving residue  (lane W81-ASK)

The lane opened on the premise that the two arithmetic counting bundles at `G_K` are unowned.
They are not.  This file records what is actually true at this tree, and isolates the one
statement that is still open.

## What the tree already proves, verified here

| bundle at `galKProfinite K` | status | supplier |
|---|---|---|
| `StokesDualityCertificate` (all four clauses) | **theorem**, hypothesis `hdeg` only | `stokesDualityCertificate_galK` |
| `ExactLiftingSemanticsRN` (all three clauses) | **theorem** at every degree | `exactLiftingSemanticsRN_galK` |
| `AffineDeterminantCertificate` | **theorem** given the packet's `ramifiedData` | `affineDeterminant_galK` |
| `ExactLiftingSemantics` (frozen) | theorem at `[K : ℚ₂] = 1` **only** | `exactLiftingSemantics_galK` |

The K-analogue of `RadicalEdgeLocal.exists_good_twist` that `KSupply.lean` §4 names as the one
owed existential is `Count.exists_nonzero_varCoc_of_tateDualityG`
(`GQ2/Dyadic/Instances/KExactLiftingVar.lean`), and its consumer at `G_K` is
`lem86_galK_of_noDescent`.  Both are landed.  §1 below re-derives the two bundles at the shape
the row records ask for, so that the claim is checked and not merely cited.

## The residue: one coefficient, and it is not a missing clone

`KSupply.exactLifting`, `GenAsmRowResidual.exactLifting` and all five `Main.lean` row records
ask for the **frozen** `ExactLiftingSemantics`, whose third conjunct pins the equation-(136)
coefficient to `RecursionFrame.zR = #R² · #D_R`.  The R-cocycle count at `G_K` is
`zRN RF (standardNumerics n) = #R^{n+1} · #D_R` (`correctedRStage_hZcount_galK`).  The two agree
exactly when `#R = 1` or `n = 1`.  **Every live row sits at `n = 2`.**

So the gap between what is proved and what is asked is not a counting theorem at all.  It is the
difference between two coefficients on the same identity, and §2 measures it exactly:

* `askCStageVanishing` (§2) is the named Prop: the (136) alternating sum vanishes on every frame
  whose Frattini block `R` is nontrivial.
* `askC_exactLiftingSemantics_galK` proves the frozen bundle at **every** degree from it.
* `askC_stageVanishing_of_exactLifting` proves it is **necessary** at `2 ≤ n`.
* `askC_exactLifting_iff_stageVanishing` is therefore an equivalence at `2 ≤ n`: at the degree
  the campaign runs at, the frozen bundle and `askCStageVanishing` are the same statement.

The necessity direction is the sharp half, and it is a warning rather than a convenience.  At
`2 ≤ n` the frozen field forces `e_Γ(B) = 0` on every nontrivial-`R` frame
(`askC_exactImageCount_eq_zero_of_exactLifting`), and that count is `#BoundaryLiftsK`, which is
finite because `G_K` is topologically finitely generated.  So the frozen field asserts that
`G_K` admits **no** boundary-framed surjection whatever onto any marked target with a nontrivial
Frattini block (`askC_isEmpty_boundaryLifts_of_exactLifting`).  The recursion exists to count
those surjections.

The lane's recommendation therefore is to restate the row records against
`ExactLiftingSemanticsRN`, which `askC_exactLiftingRN_galK` proves at every degree with nothing
carried.  This file does not make that statement change; it prices it.

## What §3 delivers

The record consequence.  With `askCStageVanishing` in hand the whole `KSupply` record at general
degree costs the four marked-core pro-`2` data, the degree pin, the two `params` pins and the
packet's `ramifiedData` input; its `exactLifting`, `stokes` and `determinant` fields cost
nothing further.  Without it, `stokes` and `determinant` are still free and `exactLifting` alone
survives, which is the honest one-block record.

## Axioms

Per-declaration `#print axioms` output is recorded in §4, with the honest split.  §1 and §3
inherit B6/B7/B1 from the `G_K` instantiations they route through; §2's two implications are
parametrized over the hypothesis and add nothing beyond what `correctedRStageSemantics_galK`
already carries.  No `sorry`, no new axiom, no `native_decide`.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open LiftingDualityG

/-! ## §1 The two bundles at `G_K`, re-derived at the row shape

Neither theorem below is new mathematics: each is the already-landed `G_K` supplier, restated at
the numerics slot the five row records use.  They exist so the lane's central claim, that the
ASK Stokes bundle and the ASK half-torsor clause are closed, is *checked* against the Lean and
not taken from a memo. -/

section Verified

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The Stokes bundle at `G_K` is closed.**  All four clauses (`tcocycle_card`, `hsep`,
`hpartial`, `hZcard`) at the arithmetic carrier, from the degree pin alone.  This is
`stokesDualityCertificate_galK`; the restatement fixes `q := qOf K FF`, which is the spelling
`KSupply.stokes` and `GenAsmRowResidual.stokes` are written at. -/
theorem askC_stokes_galK {n : ℕ} {FF : DyadicUnitFiltration K}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    StokesDualityCertificate (galKProfinite K) n (qOf K FF) P nuP
      (standardNumerics n) (smulZmod2GalK K) :=
  stokesDualityCertificate_galK K hdeg

/-- **The half-torsor clause at `G_K` is closed.**  This is the conjunct `KSupply.lean` §4
narrows the whole `exactLifting` bundle to, and calls "the `K` analogue of
`RadicalEdgeLocal.exists_good_twist`, unowned".  It is owned: the variation witness is
`Count.exists_nonzero_varCoc_of_tateDualityG` and the count is `Count.lem86N`. -/
theorem askC_halfTorsor_galK {Bg : Type} [Group Bg] [TopologicalSpace Bg]
    [DiscreteTopology Bg] [Finite Bg] (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom (GalK K) (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  lem86_galK_of_noDescent K D hedge ρ hρ

/-- **The corrected exact-lifting bundle at `G_K` is closed at every degree.**  All three
conjuncts, at the row's numerics slot.  Only the *frozen* bundle's third conjunct is open, and
§2 is exactly that gap. -/
theorem askC_exactLiftingRN_galK {n : ℕ} {FF : DyadicUnitFiltration K}
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    ExactLiftingSemanticsRN (galKProfinite K) n (qOf K FF) P nuP (standardNumerics n) :=
  exactLiftingSemanticsRN_galK hdeg

end Verified

/-! ## §2 The frozen coefficient gap, measured

The frozen and corrected R-stage clauses are the same identity with two different coefficients,
`RF.zR = #R² · #D_R` and `zRN RF (standardNumerics n) = #R^{n+1} · #D_R`.  They coincide when
`#R = 1`, in every degree.  When `#R > 1` and `2 ≤ n` they are different numbers, so, the
corrected clause being a theorem at `G_K`, the frozen one holds if and only if the sum it
multiplies is zero. -/

section Gap

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The coefficients agree when the Frattini block is trivial**, in every degree.  This is the
half of the `n = 1` coincidence that survives to all `n`, and it is why `askCStageVanishing`
only has to speak about frames with `1 < #R`. -/
theorem askC_zRN_eq_zR_of_card_one (RF : RecursionFrame T Blk) {n : ℕ}
    (h1 : Nat.card ↥Blk.frattiniK = 1) :
    zRN RF (standardNumerics n) = RF.zR := by
  show (standardNumerics n).tMult (Nat.card ↥Blk.frattiniK) * Nat.card RF.DR
    = Nat.card ↥Blk.frattiniK ^ 2 * Nat.card RF.DR
  rw [h1]
  show (1 : ℕ) ^ (n + 1) * Nat.card RF.DR = 1 ^ 2 * Nat.card RF.DR
  rw [one_pow, one_pow]

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The coefficients differ whenever the Frattini block is nontrivial and `2 ≤ n`.**  The
`#D_R` factor needs no hypothesis: a `RecursionFrame` supplies `zeroDR`, so its finite carrier is
automatically nonempty.  This is `Count.standardNumerics_tMult_ne_sq` read at the frame. -/
theorem askC_zRN_ne_zR (RF : RecursionFrame T Blk) {n : ℕ} (hn : 2 ≤ n)
    (hR : 1 < Nat.card ↥Blk.frattiniK) :
    zRN RF (standardNumerics n) ≠ RF.zR := by
  letI : Nonempty RF.DR := ⟨RF.zeroDR⟩
  show (standardNumerics n).tMult (Nat.card ↥Blk.frattiniK) * Nat.card RF.DR
    ≠ Nat.card ↥Blk.frattiniK ^ 2 * Nat.card RF.DR
  exact Count.standardNumerics_tMult_ne_sq hn hR Nat.card_pos

end Gap

section Residual

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **The lane's residual Prop.**  On every recursion frame whose Frattini block `R` is
nontrivial, the equation-(136) alternating sum vanishes.

The binder list is byte-for-byte the frozen third conjunct's, the same `hE2`, `hRK`, `hR2`, `b`,
`F`, with `1 < #R` added and the identity replaced by the vanishing of its right-hand factor.
That is deliberate: it is what makes §2's two implications both directions of one equivalence
rather than a lemma and a near-converse. -/
def askCStageVanishing (Γ : ProfiniteGrp) (q : ℕ) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E),
    1 < Nat.card ↥Blk.frattiniK →
      ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) = 0

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The reduction (ticket T1).**  `askCStageVanishing` is enough for the frozen
`ExactLiftingSemantics` at `G_K` in **every** degree.

Two cases, and neither of them is arithmetic.  If `#R = 1` the frozen and corrected coefficients
are equal (`askC_zRN_eq_zR_of_card_one`) and the corrected clause *is* the frozen one.  If
`#R > 1` the hypothesis kills the sum, so both sides of the frozen identity are zero, and the
corrected clause, which is a theorem, supplies the left-hand side.

The first two conjuncts are not touched: they are `liftsOver_card_galK` and
`lem86_galK_of_noDescent`, already theorems. -/
theorem askC_exactLiftingSemantics_galK {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n)
    (hvan : askCStageVanishing (galKProfinite K) q P nuP) :
    ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n) := by
  refine exactLiftingSemantics_galK_of_stageR136 hdeg ?_
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
  have hRN := correctedRStageSemantics_galK (K := K) hdeg hE2 hRK hR2 b F
  rcases lt_or_ge 1 (Nat.card ↥Blk.frattiniK) with hR | hR
  · rw [hvan hE2 hRK hR2 b F hR, mul_zero] at hRN ⊢
    exact hRN
  · have h1 : Nat.card ↥Blk.frattiniK = 1 := le_antisymm hR Nat.card_pos
    rw [← askC_zRN_eq_zR_of_card_one (n := n) (blockFrameImpl T Blk hE2) h1]
    exact hRN

/-- **The necessity (ticket T1, the sharp half).**  At `2 ≤ n` the frozen bundle *implies*
`askCStageVanishing`.

Both clauses evaluate the same left-hand side `#D_R · e_Γ(B)`, so their right-hand sides agree:
`zR · S = zRN · S` in `ℤ`.  At `2 ≤ n` with `1 < #R` the two coefficients are distinct naturals
(`askC_zRN_ne_zR`), and `ℤ` has no zero divisors, so `S = 0`. -/
theorem askC_stageVanishing_of_exactLifting {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n) (hn : 2 ≤ n)
    (hfroz : ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n)) :
    askCStageVanishing (galKProfinite K) q P nuP := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F hR
  have hfr := hfroz.2.2 hE2 hRK hR2 b F
  have hRN := correctedRStageSemantics_galK (K := K) hdeg hE2 hRK hR2 b F
  have hcoeff : ((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun hc => askC_zRN_ne_zR (blockFrameImpl T Blk hE2) hn hR
      (Nat.cast_injective (R := ℤ) hc.symm)
  have hzero : (((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ))
      * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) = 0 := by
    rw [sub_mul, ← hfr, ← hRN, sub_self]
  rcases mul_eq_zero.mp hzero with hc | hs
  · exact absurd hc hcoeff
  · exact hs

/-- **The equivalence at the campaign's degree.**  At `2 ≤ n`, and every live row is at `n = 2`,
the frozen `ExactLiftingSemantics` at `G_K` and `askCStageVanishing` are the same statement.
There is no third possibility and no smaller residue: this is the whole of the frozen bundle
that the corrected one does not already give. -/
theorem askC_exactLifting_iff_stageVanishing {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n) (hn : 2 ≤ n) :
    ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n)
      ↔ askCStageVanishing (galKProfinite K) q P nuP :=
  ⟨askC_stageVanishing_of_exactLifting hdeg hn,
   askC_exactLiftingSemantics_galK hdeg⟩

/-- **What the frozen field costs, stated without the residual Prop.**  Carrying
`ExactLiftingSemantics` at `2 ≤ n` is not a neutral binder: it forces the boundary-framed exact
image count of the target to vanish on every frame with a nontrivial Frattini block.

This is the finding the row records should be read against.  It is derived, not conjectured: the
vanishing sum of `askC_stageVanishing_of_exactLifting` feeds back into the corrected identity,
whose left-hand side is `#D_R · e_Γ(B)` with `#D_R > 0`. -/
theorem askC_exactImageCount_eq_zero_of_exactLifting {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n) (hn : 2 ≤ n)
    (hfroz : ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n))
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (hR : 1 < Nat.card ↥Blk.frattiniK) :
    exactImageCountK b F T = 0 := by
  have hvan := askC_stageVanishing_of_exactLifting hdeg hn hfroz hE2 hRK hR2 b F hR
  have hRN := correctedRStageSemantics_galK (K := K) hdeg hE2 hRK hR2 b F
  rw [hvan, mul_zero] at hRN
  letI : Nonempty (blockFrameImpl T Blk hE2).DR := ⟨(blockFrameImpl T Blk hE2).zeroDR⟩
  have hd : (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr Nat.card_pos.ne'
  rcases mul_eq_zero.mp hRN with hc | hx
  · exact absurd hc hd
  · exact Nat.cast_eq_zero.mp hx

/-- **The finding in its sharpest form.**  `exactImageCountK b F T` is `#BoundaryLiftsK b F T`,
the number of boundary-framed surjections `G_K ↠ Y` (`Recursion/Frame.lean`), and `G_K` is
topologically finitely generated, so that count is finite.  A finite count of zero is emptiness.

So carrying the frozen `ExactLiftingSemantics` at `2 ≤ n` asserts that `G_K` admits **no**
boundary-framed surjection at all onto any marked target whose Frattini block is nontrivial.
The recursion exists to count exactly those surjections, so this is not a harmless binder: on
every nontrivial-`R` frame it makes the object being counted empty.

This is stated, not resolved.  It is the reason the lane's recommendation is to restate the row
records against `ExactLiftingSemanticsRN`, which `askC_exactLiftingRN_galK` already proves at
every degree with nothing carried. -/
theorem askC_isEmpty_boundaryLifts_of_exactLifting {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n) (hn : 2 ≤ n)
    (hfroz : ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n))
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (hR : 1 < Nat.card ↥Blk.frattiniK) :
    IsEmpty (BoundaryLiftsK b F T) := by
  haveI : Finite (BoundaryLiftsK b F T) :=
    finite_boundaryLiftsK b F T (tfg_galK K)
  have hzero : Nat.card (BoundaryLiftsK b F T) = 0 :=
    askC_exactImageCount_eq_zero_of_exactLifting hdeg hn hfroz hE2 hRK hR2 b F hR
  rcases Nat.card_eq_zero.mp hzero with he | hi
  · exact he
  · exact absurd hi (not_infinite_iff_finite.mpr inferInstance)

end Residual

/-! ## §3 The record consequence  (ticket T3)

With §2's Prop the whole arithmetic supply record closes at general degree.  Without it, §1 still
removes two of the record's three ASK fields. -/

section Records

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **`KExactSupply` at general degree from the marked-core block and the residual Prop.**

The degree-one restriction of `kExactSupply_of_markedCore_degreeOne` was not an artefact of that
lemma: it is exactly `askCStageVanishing`, which is free at `n = 1` because the coefficients
coincide there.  At general `n` this constructor is the same statement with the residue made an
argument. -/
noncomputable def askCKExactSupply_of_markedCore {T : OrientedTameQuotientK B FF} {n : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n)
    (hvan : askCStageVanishing (galKProfinite K) (qOf K FF) P nuP)
    (pro2 : ContinuousMonoidHom (GalK K) P) (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)) :
    KExactSupply T n P hP nuP where
  hdeg := hdeg
  pro2 := pro2
  hpro2 := hpro2
  ker_pro2 := ker_pro2
  nu_compat := nu_compat
  exactLifting := askC_exactLiftingSemantics_galK hdeg hvan

/-- **`KSupply` at general degree, ASK block included.**

The end of the arithmetic chain.  Its nine fields now cost: the degree pin, the four marked-core
pro-`2` data (workstream CLASS), the two `params` pins, the packet's `ramifiedData` input, and
`askCStageVanishing`.  Ledger fields 4 and 6 (`stokes` and `determinant`) cost nothing; ledger
field 5 was already a theorem (`scalarHilbert_galK`); and ledger field 3 costs exactly the one
Prop of §2. -/
noncomputable def askCKSupply_of_markedCore {T : OrientedTameQuotientK B FF} {n : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n)
    (hvan : askCStageVanishing (galKProfinite K) (qOf K FF) P nuP)
    (pro2 : ContinuousMonoidHom (GalK K) P) (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g))
    (params : FieldParameters) (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    KSupply T n P hP nuP (standardNumerics n) :=
  (askCKExactSupply_of_markedCore hdeg hvan pro2 hpro2 ker_pro2 nu_compat).toKSupply
    params params_n params_qK ramifiedData

end Records

/-! ## §4 Acceptance and the axiom census

The acceptance tests are at the quadratic slot `n = 2`, which is where all five committed rows
sit (`docs/dyadic/w74-critical-path.md` §0: every row core has `2 + 2 * 0` for its degree).  The
`example`s below produce the row records' field types on the nose. -/

section Acceptance

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Acceptance: at the quadratic slot the `stokes` field of every `M` row and the pilot's
`hstokes` are free. -/
example {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = 2) :
    StokesDualityCertificate (galKProfinite K) 2 (qOf K FF) P nuP
      (standardNumerics 2) (smulZmod2GalK K) :=
  askC_stokes_galK (FF := FF) hdeg

/-- Acceptance: at the quadratic slot the pilot's `hexact` and every `M` row's `exactLifting`
cost exactly `askCStageVanishing`, and nothing else. -/
example {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (hvan : askCStageVanishing (galKProfinite K) (qOf K FF) P nuP) :
    ExactLiftingSemantics (galKProfinite K) 2 (qOf K FF) P nuP (standardNumerics 2) :=
  askC_exactLiftingSemantics_galK hdeg hvan

/-- Acceptance: and conversely, at the quadratic slot that cost is unavoidable. -/
example {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = 2) :
    ExactLiftingSemantics (galKProfinite K) 2 (qOf K FF) P nuP (standardNumerics 2)
      ↔ askCStageVanishing (galKProfinite K) (qOf K FF) P nuP :=
  askC_exactLifting_iff_stageVanishing hdeg (le_refl 2)

end Acceptance

/-! ### Axiom census

Measured at this tree with `scripts/mirror.sh check`, transcribed from the `#print axioms` output
below.  `std-3` abbreviates `propext, Classical.choice, Quot.sound`.

| declaration | beyond std-3 |
|---|---|
| `askCStageVanishing` (the residual `Prop`) | **nothing** |
| `askC_zRN_eq_zR_of_card_one` | **nothing** |
| `askC_zRN_ne_zR` | **nothing** |
| `askC_stokes_galK` | `tateDualityAt`, `Foundations.absGalQ2_localEulerCharacteristic` |
| `askC_halfTorsor_galK` | `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` |
| `askC_exactLiftingRN_galK` | the union of the two rows above |
| `askC_exactLiftingSemantics_galK` | same union |
| `askC_stageVanishing_of_exactLifting` | same union |
| `askC_exactLifting_iff_stageVanishing` | same union |
| `askC_exactImageCount_eq_zero_of_exactLifting` | same union |
| `askC_isEmpty_boundaryLifts_of_exactLifting` | same union |
| `askCKExactSupply_of_markedCore` | same union |
| `askCKSupply_of_markedCore` | same union **plus** `hilbertSymbol_normCriterion_finiteDyadic`, `relativeStiefelWhitney_dyadic` |

Three readings worth recording.

* The two coefficient lemmas print **std-3 and nothing else**.  That is the measurement behind
  the headline: the gap between the frozen and corrected bundles is not arithmetic at all, and
  the file's own §2 says so in a form with no field in it.
* `askC_halfTorsor_galK` prints B6 and B1 but **not** B7, exactly as
  `KExactLiftingGalK.lean` predicted: the half-torsor clause is degree-free, so it never reaches
  the local Euler characteristic.
* The last row's two extra axioms arrive through `KExactSupply.toKSupply`'s call to
  `affineDeterminant_galK`, i.e. through the *determinant* field, not through anything this file
  proves.  They are the price of ledger field 6, and they are already paid at head.

No declaration in this file introduces an axiom of its own, and none of the thirteen uses
`sorry` or `native_decide`. -/

#print axioms askC_stokes_galK
#print axioms askC_halfTorsor_galK
#print axioms askC_exactLiftingRN_galK
#print axioms askCStageVanishing
#print axioms askC_zRN_eq_zR_of_card_one
#print axioms askC_zRN_ne_zR
#print axioms askC_exactLiftingSemantics_galK
#print axioms askC_stageVanishing_of_exactLifting
#print axioms askC_exactLifting_iff_stageVanishing
#print axioms askC_exactImageCount_eq_zero_of_exactLifting
#print axioms askC_isEmpty_boundaryLifts_of_exactLifting
#print axioms askCKExactSupply_of_markedCore
#print axioms askCKSupply_of_markedCore

end GQ2.Dyadic
