/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Terminal
import GQ2.Dyadic.Recursion.Recursion

/-!
# §9 terminal count, `M`-stage partition and recursion solver at the `K`-boundary (SD-R2)

Clone of the **`b`-typed layer** of `GQ2/SectionNine/Induction.lean` (606 ln), re-typed at the
general `K`-boundary and consuming SD-R1's numerically parameterized `ClosedRecursionK`.

## What is reused rather than cloned

Boundary-free, hence never cloned: `IsEquivariantFactorSet.comap` (:92) and `.comapHom` (:124)
— the two datum-transport lemmas, consumed by import in `GQ2/Dyadic/Recursion/Kappa.lean` —
`zmod_two_cases` (:164, `private` anyway), and `blockFrame` (:236), which is target-side.

Note this file does **not** import `GQ2.SectionNine.Induction` at all: everything it reuses
comes from `GQ2.SectionNine.Terminal` (via the clone) and `GQ2.SectionEight.Recursion` (via
SD-R1's).  The model file's own contribution is entirely `b`-typed or SEAM B.

`ActsThroughTame` (:155) and `kappa0_exists` (:196) are **not** cloned here: they are SEAM B and
live in `GQ2/Dyadic/Recursion/Kappa.lean` as `ActsThroughTameQ` / `kappa0_existsK`, because the
Block productions need them one import earlier.

## The two-sided flip of the terminal count

`terminal_count_eq` (:34) is the one place in this file where the model is *one-sided*: it
fixes the second source to `G_ℚ₂` through `B : BoundaryMaps`, the `AbsGalQ2` instance binders,
and `ker_pro2A`/`B.ker_pro2F`.  Per SD1 memo §3.1 all of that **disappears** from the
degree-`n` statement: `terminal_count_eqK` takes the two sources symmetrically, each supplying
the four leaves the proof actually consumes —

`b`, `Function.Surjective b`, `pro2`, `Function.Surjective pro2`,
`∀ γ, (b γ).val.2 = pro2 γ`, `pro2.ker = proPKernel 2 Γ`

— which are exactly the `SourceDataN` fields `surj`/`pro2`/`compat`/`ker_pro2` (memo §1.2), so
SD2/SD3 feed it from the record with no glue.  The model's derivation of `pro2A`-surjectivity
from `B.surjA` + `nuT_surjective` becomes the hypothesis `hnuP` (memo §2.2), shared by both
sources since they share the slot.

## Parameterization delta versus the `ℚ₂` model

| model | clone |
|---|---|
| `boundarySubgroup`, `BoundaryFrame` | `boundarySubgroupQ q nuP`, `BoundaryFrameK q P H E` |
| `exactImageCount`, `exactImageCountOn` | `exactImageCountK`, `exactImageCountOnK` (SD-R1) |
| `BoundaryLifts`, `IsBoundaryLift` | `BoundaryLiftsK`, `IsBoundaryLiftK` (SD-R1) |
| `ClosedRecursion RF b F μ G0 DT phase` | `ClosedRecursionK … cS mM vH` (SD-R1's three opaque numerics) |
| `head_two_nilpotent` | `head_two_nilpotentK` (needs `q ≠ 0`, `Even q`) |
| `RF.mJOn`, `RF.mJ`, `RF.zBC`, `RF.mB`, `RF.nPhase` | `mJOnK`, `mJK`, `zBCK`, `mBK`, `nPhaseK` (SD-R1) |

`RecursionFrame` and its whole derived layer are the model's own (SD-R1's finding), so no
transport is ever needed between the two spines.

## ⚠ The one predicted `omega` seam — found and fixed

The SD1 memo §4.1(a) predicted exactly one cancellation seam in this file, at
`GQ2/SectionNine/Induction.lean:539`, and it is where it was predicted.  The model derives

```
h8 : 8 * RF.mJ b₁ F l hl J hJ = 8 * RF.mJ b₂ F l hl J hJ
⊢ RF.mJ b₁ F l hl J hJ = RF.mJ b₂ F l hl J hJ
```

and closes it with `omega`, which works only because the coefficient is the **literal** `8`.
With the coefficient a variable `cS` the goal becomes `cS * x = cS * y ⊢ x = y`, which `omega`
cannot do (it is nonlinear) — the verbatim error is quoted at the fix site below.  The fix is
the memo's positivity-cancels pattern: `Nat.eq_of_mul_eq_mul_left` at `0 < cS`, which is why
`SourceNumerics` carries the `homScalar_pos` field (`GQ2/Dyadic/Recursion/Numerics.lean`) and
why `count_eq_of_closedRecursionK` gains the single hypothesis `hcS : 0 < cS`.

The file's other two cancellations do **not** move: `2 * zBC b₁ … = 2 * zBC b₂ …` (model :562)
keeps its `omega` because the `2` of (139) is the half-torsor index, degree-independent
(memo §4.1 "non-movers"), and the `2 * #D_T` cancel at :558 already goes through
`mul_left_cancel₀` on a nonzero `ℤ`.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionNine

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## The terminal regime, two-sided -/

/-- **The terminal case at the `K`-boundary** (§9.1), stated two-sidedly: if every chief factor
of `L_Y` is scalar, the exact-image problems of *any two* sources over the same slot are
identical.  Clone of `GQ2.SectionNine.terminal_count_eq` (`GQ2/SectionNine/Induction.lean:34`)
with the `G_ℚ₂` side replaced by a second abstract source (SD1 memo §3.1; the removal list is
the module docstring's).

Lemma 9.2 (`lemma_9_2_core`) and the whole `L92` bundle are the model's — only the head's
2-nilpotency (`head_two_nilpotentK`, hence `q ≠ 0`/`Even q`) and the two correspondence steps
move to the `K`-boundary. -/
theorem terminal_count_eqK (hq0 : q ≠ 0) (hqe : Even q) (hP : IsProP 2 P)
    (hnuP : Function.Surjective nuP) (F : BoundaryFrameK q P H E)
    {Γ₁ : Type} [Group Γ₁] [TopologicalSpace Γ₁] [IsTopologicalGroup Γ₁] [CompactSpace Γ₁]
    [T2Space Γ₁] [TotallyDisconnectedSpace Γ₁]
    {Γ₂ : Type} [Group Γ₂] [TopologicalSpace Γ₂] [IsTopologicalGroup Γ₂] [CompactSpace Γ₂]
    [T2Space Γ₂] [TotallyDisconnectedSpace Γ₂]
    (b₁ : ContinuousMonoidHom Γ₁ ↥(boundarySubgroupQ q nuP)) (hb₁ : Function.Surjective b₁)
    (pro2₁ : ContinuousMonoidHom Γ₁ P) (hpro2₁ : Function.Surjective pro2₁)
    (hbpro2₁ : ∀ γ, (b₁ γ).val.2 = pro2₁ γ)
    (hker₁ : pro2₁.toMonoidHom.ker = proPKernel 2 Γ₁)
    (b₂ : ContinuousMonoidHom Γ₂ ↥(boundarySubgroupQ q nuP)) (hb₂ : Function.Surjective b₂)
    (pro2₂ : ContinuousMonoidHom Γ₂ P) (hpro2₂ : Function.Surjective pro2₂)
    (hbpro2₂ : ∀ γ, (b₂ γ).val.2 = pro2₂ γ)
    (hker₂ : pro2₂.toMonoidHom.ker = proPKernel 2 Γ₂)
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (hstack : SectionSeven.IsScalarStack T.LY) :
    exactImageCountK b₁ F T = exactImageCountK b₂ F T := by
  obtain ⟨M, hMn, hModd, hMtwo⟩ := head_two_nilpotentK hq0 hqe F
  obtain ⟨Ntil, hNn, hNodd, hNQ2, hNL, _hNcomm, hmapM, hNLsup⟩ :=
    lemma_9_2_core T.piY T.piY_surjective T.LY T.ker_piY T.isPGroup_two hstack M hModd hMtwo
  set D : L92 H Y := ⟨T.piY, T.piY_surjective, T.LY, T.ker_piY, M, hMn, hModd, Ntil, hNn,
    hNodd, hNL, hmapM, hNLsup, hNQ2⟩ with hD
  have hDpi : D.piY = T.piY := by rw [hD]
  show Nat.card (BoundaryLiftsK b₁ F T) = Nat.card (BoundaryLiftsK b₂ F T)
  calc Nat.card (BoundaryLiftsK b₁ F T)
      = Nat.card (QLiftsK F T hE2 D b₁) :=
        boundaryLiftsK_equiv_qliftsK F T hE2 D hDpi b₁ hb₁ hnuP
    _ = Nat.card (CommonLiftsK F T hE2 D nuP) :=
        qliftsK_equiv_commonLiftsK hP F T hE2 D b₁ hb₁ pro2₁ hpro2₁ hbpro2₁ hker₁
    _ = Nat.card (QLiftsK F T hE2 D b₂) :=
        (qliftsK_equiv_commonLiftsK hP F T hE2 D b₂ hb₂ pro2₂ hpro2₂ hbpro2₂ hker₂).symm
    _ = Nat.card (BoundaryLiftsK b₂ F T) :=
        (boundaryLiftsK_equiv_qliftsK F T hE2 D hDpi b₂ hb₂ hnuP).symm

/-! ## The elementary `M`-stage partition

The model's `mStage_partition` is **already multiplicity-generic** (it takes `mult : ℕ` as a
parameter, `Induction.lean:474`), so no numeric parameterization happens here: SD3 instantiates
`mult := SN.mMult (Nat.card ↥RF.MB)` from both records' `liftsOver_card` fields.  Only the
boundary types move. -/

section MStage

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]

/-- **All `B`-lifts over a lower exact-image map `ρ : Γ ↠ C`** at the `K`-boundary.  Clone of
`GQ2.SectionEight.RecursionFrame.LiftsOver` (`GQ2/RadicalEdge/Bridge.lean:71`).

⚠ Budget note for SD-R3: this two-line definition belongs, by the memo's §4.3 table, to the
`RadicalEdge/Bridge.lean` clone that SD-R3 owns, but `mStage_partitionK` below cannot be stated
without it, so it lands here.  SD-R3 should **import it** rather than redefine it (its Bridge
clone sits below this file in the `ℚ₂` dependency order, so if the reuse is awkward, moving the
definition down into the Bridge clone and importing that from here is the alternative — either
way there must be exactly one `LiftsOverK`). -/
def LiftsOverK (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) : Type :=
  {m : ContinuousMonoidHom Γ RF.YB // ∀ γ : Γ, RF.piBC (m γ) = ρ.1.1 γ}

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] in
/-- At `n = 1` the lift set **is** the model's — `rfl`. -/
theorem liftsOverK_eq (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    LiftsOverK RF b F ρ = RF.LiftsOver b F.toBoundaryFrame ρ := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Stages (A)+(B) of `mStage_partitionK`.  Clone of the `private`
`GQ2.SectionNine.mStage_Mset_card_eq_mult` (`GQ2/SectionNine/Induction.lean:253`). -/
private theorem mStage_Mset_card_eq_multK (RF : RecursionFrame T Blk)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (mult : ℕ)
    (hmult : ∀ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) = mult) :
    Nat.card {m : ContinuousMonoidHom Γ RF.YB //
        IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)}
      = mult * exactImageCountK b F RF.TC := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TC) := Fintype.ofFinite _
  have hheadBC : RF.TC.piY.comp RF.piBC = RF.TB.piY := RF.headBC
  have hthetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY := RF.thetaBC
  set Mset := {m : ContinuousMonoidHom Γ RF.YB //
    IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)} with hMsetdef
  haveI : Finite Mset := Subtype.finite
  -- (A) the `LiftsOver`-fibration collapses by `hmult` (the `half139_of` pattern)
  have hmultsum : ∑ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ)
      = mult * exactImageCountK b F RF.TC := by
    rw [Finset.sum_congr rfl (fun ρ _ => hmult ρ), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, exactImageCountK, Nat.card_eq_fintype_card]
    exact mul_comm _ _
  -- (B) `Mset` fibres over the `C`-image `ρ`, the fibre being `LiftsOver ρ`
  have eUnion : Nat.card Mset
      = ∑ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) := by
    set Φ : Mset → BoundaryLiftsK b F RF.TC := fun m =>
      ⟨⟨⟨RF.piBC.comp m.1.toMonoidHom,
          (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun⟩, m.2.2⟩,
        fun γ => by
          show (RF.TC.piY (RF.piBC (m.1 γ)), RF.TC.thetaY (RF.piBC (m.1 γ))) = F.frameMap (b γ)
          have h1 : RF.TC.piY (RF.piBC (m.1 γ)) = RF.TB.piY (m.1 γ) := by
            rw [show RF.TC.piY (RF.piBC (m.1 γ)) = (RF.TC.piY.comp RF.piBC) (m.1 γ) from rfl,
              hheadBC]
          have h2 : RF.TC.thetaY (RF.piBC (m.1 γ)) = RF.TB.thetaY (m.1 γ) := by
            rw [show RF.TC.thetaY (RF.piBC (m.1 γ)) = (RF.TC.thetaY.comp RF.piBC) (m.1 γ)
              from rfl, hthetaBC]
          rw [h1, h2]
          exact m.2.1 γ⟩ with hΦdef
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv Φ).symm, Nat.card_sigma]
    refine Finset.sum_congr rfl (fun ρ _ => Nat.card_congr ?_)
    exact
      { toFun := fun mm =>
          ⟨mm.1.1, fun γ => congrArg (fun x : BoundaryLiftsK b F RF.TC => x.1.1 γ) mm.2⟩
        invFun := fun n =>
          ⟨⟨n.1, isBoundaryLiftK_of_over RF b F n.1 ρ n.2,
              by rw [show (⇑RF.piBC ∘ ⇑n.1) = ⇑ρ.1.1 from funext n.2]; exact ρ.1.2⟩,
            Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ => n.2 γ))⟩
        left_inv := fun mm => Subtype.ext (Subtype.ext rfl)
        right_inv := fun n => Subtype.ext rfl }
  rw [eUnion]; exact hmultsum

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] in
/-- Stage (C), `C`-onto head-surjective stratum.  Clone of the `private`
`GQ2.SectionNine.mStage_stratum_fiber_card` (`Induction.lean:309`). -/
private theorem mStage_stratum_fiber_cardK (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (J : Subgroup RF.YB) (hJc : J.map RF.piBC = ⊤)
    (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J}
      = exactImageCountK b F (RF.TB.stratum J hJh) := by
  classical
  rw [exactImageCountK]
  have hmem : ∀ (m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)}),
      m.1.toMonoidHom.range = J → ∀ γ, m.1 γ ∈ J := by
    intro m hm γ
    have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
    rwa [hm] at this
  refine Nat.card_congr ⟨fun m =>
    ⟨⟨cmhCodRestrict m.1.1 J (hmem m.1 m.2), fun j => ?_⟩, fun γ => ?_⟩,
    fun f => ⟨⟨cmhInclude J f.1.1, fun γ => f.2 γ, ?_⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ => Subtype.ext rfl))⟩
  · -- corestriction surjective onto `↥J`
    have hj : (j : RF.YB) ∈ m.1.1.toMonoidHom.range := by rw [m.2]; exact j.2
    obtain ⟨γ, hγ⟩ := hj
    exact ⟨γ, Subtype.ext hγ⟩
  · -- stratum boundary equation (definitional transport)
    exact m.1.2.1 γ
  · -- `C`-surjectivity of the included map, from `J ↠ C`
    intro c
    have hc : c ∈ J.map RF.piBC := by rw [hJc]; trivial
    obtain ⟨y, hyJ, hyc⟩ := Subgroup.mem_map.mp hc
    obtain ⟨γ, hγ⟩ := f.1.2 ⟨y, hyJ⟩
    exact ⟨γ, by show RF.piBC ((f.1.1 γ : RF.YB)) = c; rw [hγ, hyc]⟩
  · -- the included map has range exactly `J`
    have h1 : (cmhInclude J f.1.1).toMonoidHom.range
        = f.1.1.toMonoidHom.range.map J.subtype := MonoidHom.range_comp _ _
    rw [h1, MonoidHom.range_eq_top.mpr f.1.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] in
/-- Stage (C), `C`-missing stratum.  Clone of the `private`
`GQ2.SectionNine.mStage_fiber_empty_of_not_onto` (`Induction.lean:352`). -/
private theorem mStage_fiber_empty_of_not_ontoK (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (J : Subgroup RF.YB) (hJc : J.map RF.piBC ≠ ⊤) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J} = 0 := by
  classical
  have hE : IsEmpty {m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
      m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJc
    rw [← hm, ← MonoidHom.range_comp, MonoidHom.range_eq_top]
    intro c
    obtain ⟨γ, hγ⟩ := m.2.2 c
    exact ⟨γ, hγ⟩
  exact Nat.card_of_isEmpty

omit [TopologicalSpace Y] [DiscreteTopology Y] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] in
/-- Stage (C), head-missing stratum.  Clone of the `private`
`GQ2.SectionNine.mStage_fiber_empty_of_not_head` (`Induction.lean:376`). -/
private theorem mStage_fiber_empty_of_not_headK (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) (J : Subgroup RF.YB)
    (hJh : ¬ Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J} = 0 := by
  classical
  have hE : IsEmpty {m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLiftK b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
      m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJh
    intro hh
    obtain ⟨γ, hγ⟩ := hhead hh
    have hmemJ : m.1 γ ∈ J := by
      have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
      rwa [hm] at this
    refine ⟨⟨m.1 γ, hmemJ⟩, ?_⟩
    show RF.TB.piY (m.1 γ) = hh
    have hbd := m.2.1 γ
    have := congrArg Prod.fst hbd
    simpa [hγ] using this
  exact Nat.card_of_isEmpty

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Stage (C) of `mStage_partitionK`.  Clone of the `private`
`GQ2.SectionNine.mStage_Mset_card_eq_finsum` (`Induction.lean:408`). -/
private theorem mStage_Mset_card_eq_finsumK (RF : RecursionFrame T Blk)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) :
    Nat.card {m : ContinuousMonoidHom Γ RF.YB //
        IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)}
      = ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤}, exactImageCountOnK b F RF.TB J := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (Subgroup RF.YB) :=
    Finite.of_injective (fun J : Subgroup RF.YB => (J : Set RF.YB)) SetLike.coe_injective
  haveI : Fintype (Subgroup RF.YB) := Fintype.ofFinite _
  set Mset := {m : ContinuousMonoidHom Γ RF.YB //
    IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)} with hMsetdef
  -- stratify `Mset` by the exact image `range m`
  have e2 : Nat.card Mset
      = ∑ J : Subgroup RF.YB, Nat.card {m : Mset // m.1.toMonoidHom.range = J} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun m : Mset => m.1.toMonoidHom.range)).symm, Nat.card_sigma]
  set fib : Subgroup RF.YB → ℕ :=
    fun J => Nat.card {m : Mset // m.1.toMonoidHom.range = J} with hfibdef
  set S : Finset (Subgroup RF.YB) :=
    Finset.univ.filter (fun J => J.map RF.piBC = ⊤) with hSdef
  -- assemble: restrict to `S`, match `fib` to `exactImageCountOnK`, convert to `finsum`
  have hStep : (∑ J : Subgroup RF.YB, fib J) = ∑ J ∈ S, fib J := by
    rw [hSdef, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun J => J.map RF.piBC = ⊤) fib]
    have hz : ∑ J ∈ Finset.univ.filter (fun J => ¬ J.map RF.piBC = ⊤), fib J = 0 :=
      Finset.sum_eq_zero (fun J hJ =>
        mStage_fiber_empty_of_not_ontoK RF b F J (Finset.mem_filter.mp hJ).2)
    rw [hz, add_zero]
  have hmatch : ∀ J ∈ S, fib J = exactImageCountOnK b F RF.TB J := by
    intro J hJ
    rw [hSdef, Finset.mem_filter] at hJ
    obtain ⟨_, hJc⟩ := hJ
    by_cases hJh : Function.Surjective (RF.TB.piY.comp J.subtype)
    · simp only [exactImageCountOnK, dif_pos hJh]
      exact mStage_stratum_fiber_cardK RF b F J hJc hJh
    · simp only [exactImageCountOnK, dif_neg hJh]
      exact mStage_fiber_empty_of_not_headK RF b F hhead J hJh
  have hsetconv : {J : Subgroup RF.YB | J.map RF.piBC = ⊤} = ↑S := by
    rw [hSdef]; ext J; simp
  have hfinsum : ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤},
        exactImageCountOnK b F RF.TB J
      = ∑ J ∈ S, exactImageCountOnK b F RF.TB J := by
    rw [hsetconv, finsum_mem_coe_finset]
  rw [e2, hStep, Finset.sum_congr rfl hmatch]
  exact hfinsum.symm

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The `M`-stage partition** (§9.2) at the `K`-boundary.  Clone of
`GQ2.SectionNine.mStage_partition` (`Induction.lean:467`) — verbatim, and already
multiplicity-generic in the model (`mult : ℕ`), so no numeric parameterization is needed:
`mult · e_Γ(C) = Σ_{J ↠ C} e_Γ(stratum J)`. -/
theorem mStage_partitionK (RF : RecursionFrame T Blk)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (mult : ℕ)
    (hmult : ∀ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) = mult) :
    mult * exactImageCountK b F RF.TC
      = ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤},
          exactImageCountOnK b F RF.TB J := by
  classical
  rw [← mStage_Mset_card_eq_multK RF hfg b F mult hmult]
  exact mStage_Mset_card_eq_finsumK RF hfg b F hhead

end MStage

/-! ## The recursion solver -/

/-- **Solving the closed recursion** at the `K`-boundary (the §9.3 bookkeeping).  Clone of
`GQ2.SectionNine.count_eq_of_closedRecursion` (`GQ2/SectionNine/Induction.lean:503`): two
sources satisfying SD-R1's numerically parameterized boxed system (136)–(140) for the *same*
frame, the *same* shared data `(μ, G⁰, D_T, phase)` **and the same numerics `(cS, mM, vH)`**
have equal exact-image counts at the top, given the strictly-smaller ingredient counts.

Sharing one numeric triple between the two sources is the definitional realization of the
ledger's "the recursion consumes only equality of the two sources' leaves" (memo §3.2): no
equality side condition between the sources' numerics can arise.

The single new hypothesis versus the model is `hcS : 0 < cS` — the positivity that replaces the
literal `8`'s `omega` cancellation (module docstring; memo §4.1(a)).  SD3 supplies it from
`SourceNumerics.homScalar_pos`. -/
theorem count_eq_of_closedRecursionK {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    {Γ₁ : Type} [Group Γ₁] [TopologicalSpace Γ₁]
    {Γ₂ : Type} [Group Γ₂] [TopologicalSpace Γ₂]
    (b₁ : ContinuousMonoidHom Γ₁ ↥(boundarySubgroupQ q nuP))
    (b₂ : ContinuousMonoidHom Γ₂ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (cS mM vH : ℕ) (hcS : 0 < cS)
    (h₁ : ClosedRecursionK RF b₁ F μ G0 DT phase cS mM vH)
    (h₂ : ClosedRecursionK RF b₂ F μ G0 DT phase cS mM vH)
    (hDT : Nat.card DT ≠ 0)
    (hTB : exactImageCountK b₁ F RF.TB = exactImageCountK b₂ F RF.TB)
    (hTC : exactImageCountK b₁ F RF.TC = exactImageCountK b₂ F RF.TC)
    (hpull : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J' : Subgroup (RF.scalarCover l h).cover),
      J'.map (RF.scalarCover l h).p ≠ ⊤ → (J'.map (RF.scalarCover l h).p).map RF.piBC = ⊤ →
      exactImageCountOnK b₁ F ((RF.scalarCover l h).pullTarget RF.TB) J'
        = exactImageCountOnK b₂ F ((RF.scalarCover l h).pullTarget RF.TB) J')
    (hphase : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (ζ : DT),
      nPhaseK RF b₁ F (phase l h ζ) = nPhaseK RF b₂ F (phase l h ζ)) :
    exactImageCountK b₁ F T = exactImageCountK b₂ F T := by
  classical
  -- (138) + `hpull`: the proper `C`-onto stratum counts `m_J` agree (cancel the scalar `cS`),
  -- hence so do `mJOn` (only these instances are consumed by (137) below)
  have hmJOn : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR) (J : Subgroup RF.YB),
      J ≠ ⊤ → J.map RF.piBC = ⊤ →
      mJOnK RF b₁ F l hl J = mJOnK RF b₂ F l hl J := by
    intro l hl J hJne hJC
    simp only [mJOnK]
    by_cases hJ : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJ, dif_pos hJ]
      have hcs : cS * mJK RF b₁ F l hl J hJ = cS * mJK RF b₂ F l hl J hJ := by
        rw [h₁.eq138 l hl J hJ, h₂.eq138 l hl J hJ]
        refine finsum_mem_congr rfl (fun J' hJ' => ?_)
        have hJ'' : J'.map (RF.scalarCover l hl).p = J := hJ'
        exact hpull l hl J' (by rw [hJ'']; exact hJne) (by rw [hJ'']; exact hJC)
      -- ⚠ THE PREDICTED SEAM (memo §4.1(a); model `Induction.lean:539` closed this by `omega`).
      -- With `cS` a variable rather than the literal `8`, `omega` reports (verbatim, verified
      -- in-session by swapping the tactic back):
      --   omega could not prove the goal:
      --   a possible counterexample may satisfy the constraints
      --     g ≥ 1, f ≥ 0, e ≥ 0, e - f ≥ 1, d ≥ 0, c ≥ 0, b ≥ 0, a ≥ 1
      --   where
      --    a := ↑cS
      --    d := ↑cS * ↑(mJK RF b₂ F l hl J hJ)
      --    e := ↑(mJK RF b₂ F l hl J hJ)
      --    f := ↑(mJK RF b₁ F l hl J hJ)
      -- i.e. `omega` atomizes the nonlinear product `cS * mJK …` (`d`) and so cannot relate it
      -- to `e`; the counterexample `e - f ≥ 1` is exactly the un-cancelled coefficient.
      -- Positivity cancels instead.
      exact Nat.eq_of_mul_eq_mul_left hcS hcs
    · rw [dif_neg hJ, dif_neg hJ]
  -- (139)/(140): the compatible-lift counts `zBC` agree (case split on the descent-∃)
  have hzBC : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR),
      zBCK RF b₁ F l hl = zBCK RF b₂ F l hl := by
    intro l hl
    by_cases hdesc : ∃ N : Subgroup (RF.scalarCover l hl).cover, N.Normal ∧
        N.map (RF.scalarCover l hl).p = RF.TBsub ∧ (RF.scalarCover l hl).z ∉ N
    · -- descent: (140), cancel `2·#DT ≠ 0`
      have hns : (∑ᶠ ζ : DT,
            (2 * (nPhaseK RF b₁ F (phase l hl ζ) : ℤ) - (exactImageCountK b₁ F RF.TC : ℤ)))
          = ∑ᶠ ζ : DT,
            (2 * (nPhaseK RF b₂ F (phase l hl ζ) : ℤ) - (exactImageCountK b₂ F RF.TC : ℤ)) :=
        finsum_congr (fun ζ => by rw [hphase l hl ζ, hTC])
      have hcancel : 2 * (Nat.card DT : ℤ) * (zBCK RF b₁ F l hl : ℤ)
          = 2 * (Nat.card DT : ℤ) * (zBCK RF b₂ F l hl : ℤ) := by
        rw [h₁.eq140 l hl hdesc, h₂.eq140 l hl hdesc, hns, hTC]
      have hne : (2 : ℤ) * (Nat.card DT : ℤ) ≠ 0 :=
        mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hDT)
      exact_mod_cast mul_left_cancel₀ hne hcancel
    · -- no descent: (139), cancel `2` — the half-torsor index, degree-independent, so this
      -- `omega` is the model's own and does **not** become a positivity-cancel
      have hcancel : 2 * zBCK RF b₁ F l hl = 2 * zBCK RF b₂ F l hl := by
        rw [h₁.eq139 l hl hdesc, h₂.eq139 l hl hdesc, hTC]
      omega
  -- (137) + `mB(0) = e(T_B)`: the top-stratum counts `m_B` agree
  have hmB : ∀ l : RF.DR, mBK RF b₁ F l = mBK RF b₂ F l := by
    intro l
    by_cases hl : l = RF.zeroDR
    · subst hl
      simp only [mBK]
      exact hTB
    · have hsum : (∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (mJOnK RF b₁ F l hl J : ℤ))
          = ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (mJOnK RF b₂ F l hl J : ℤ) :=
        finsum_mem_congr rfl (fun J hJmem => by
          obtain ⟨hJne, hJC⟩ := hJmem
          rw [hmJOn l hl J hJne hJC])
      have hz : (zBCK RF b₁ F l hl : ℤ) = (zBCK RF b₂ F l hl : ℤ) := by rw [hzBC l hl]
      have hcast : (mBK RF b₁ F l : ℤ) = (mBK RF b₂ F l : ℤ) := by
        have h137 : (mBK RF b₁ F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (mJOnK RF b₁ F l hl J : ℤ)
            = (mBK RF b₂ F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (mJOnK RF b₂ F l hl J : ℤ) := by
          rw [← h₁.eq137 l hl, ← h₂.eq137 l hl, hz]
        rw [hsum] at h137
        exact add_right_cancel h137
      exact_mod_cast hcast
  -- (136): the top counts `e(T)` agree (cancel `#D_R ≠ 0`)
  have hDRne : (Nat.card RF.DR : ℤ) ≠ 0 := by
    have h : Nat.card RF.DR ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨RF.zeroDR⟩, inferInstance⟩
    exact_mod_cast h
  have hrhs : (RF.zR : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b₁ F l : ℤ) - exactImageCountK b₁ F RF.TB)
      = (RF.zR : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b₂ F l : ℤ) - exactImageCountK b₂ F RF.TB) := by
    congr 1
    exact finsum_congr (fun l => by rw [hmB l, hTB])
  have hcast : (exactImageCountK b₁ F T : ℤ) = (exactImageCountK b₂ F T : ℤ) := by
    refine mul_left_cancel₀ hDRne ?_
    rw [h₁.eq136, h₂.eq136, hrhs]
  exact_mod_cast hcast

end GQ2.Dyadic
