/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Partition
import GQ2.SectionEight.Recursion

/-!
# §8 closed recursion at the `K`-boundary (dyadic campaign, ticket SD-R1)

Clone of the **`b`-typed layer** of `GQ2/SectionEight/Recursion.lean` (887 ln), re-typed at the
`K`-boundary and with the three degree-carrying literals replaced by opaque parameters.

## Finding: `RecursionFrame`, its derived layer, and `Enrichment` are boundary-free

`GQ2.SectionEight.RecursionFrame` (`Recursion.lean:50`) is parameterized only by
`(T : MarkedTarget H E Y)` and `(Blk : MinimalBlock T.LY)`; **no field mentions a boundary
object**.  The same holds for its whole derived layer (`MB_normal`, `MB_elem`, `MB_comm`,
`TBsub_eq_mapKS`, `TBsub_normal`, `TBsub_le_MB`, `ker_piBC`, `piBC_surj`, `headBC`, `thetaBC`,
:201-280), for `zR` (:114), for `Enrichment` (:308) and for `Enrichment.radData` (:361).

All of it is therefore **consumed by import**, and the degree-`n` spine shares one target-side
frame object with the `ℚ₂` spine — strictly better than cloning, because SD2/SD3 and the
`n = 1` regression need no transport between two copies of the frame.  What is cloned below is
exactly the layer that mentions `b`: the five counts, `liftB`, the boxed system, the (137)
partition, the input bundle, and the two assembly steps.

This is the "finer split" the SD1 memo's §4.3 closing note anticipated ("reuse the target-side
`RecursionFrame` fields, clone only the `b`-typed count layer").

## Numeric parameterization  (memo §4.1, §4.2's Plan-B row for `ClosedRecursion`)

`ClosedRecursionK` and `RecursionInputsK` gain three opaque `ℕ` parameters:

| parameter | replaces | model site | memo |
|---|---|---|---|
| `cS` | the literal `8` | `eq138` (:407), `prop_8_9_aux`'s `hscalar` (:744) | §4.1(a) |
| `mM` | `(Nat.card ↥RF.MB) ^ 2` | `eq139` (:417), `half139` (:721) | §4.1(b) |
| `vH` | `Nat.card ↥RF.MB / Nat.card ↥RF.TBsub` | `eq140` (:429), `phase140` (:728) | §4.1(c) |

SD3 instantiates `cS := SN.homScalar`, `mM := SN.mMult (Nat.card ↥RF.MB)`,
`vH := SN.h1Mult (Nat.card En.Vmod)`.  Note `vH` is the **inner** `|V|` factor (`#H¹`), the
one that moves with the degree; the *outer* `|V|` normalizing `GaussZResidue` is `#B¹` and
stays put (memo §1.3) — it does not occur in this file.  `RF.zR`, eq. (136)'s `2`, eq. (140)'s
`2 · #D_T` and `μ`/`G0`/`DT`/`phase` are degree-independent or already opaque, and are
untouched.

**Every proof in this file is verbatim modulo the substitutions above.**  No `omega` seam
arises here: the two positivity-cancels the memo predicts (§4.1(a)) live at the *cancellation*
sites — `Induction.lean:534-539` (SD-R2) and `ThmFourTwo.lean:285` (SD-R3) — not at any
carrier in §8.  `homScalar_pos` is correspondingly not needed by this file.

Axioms: none beyond std-3; each clone's print equals its model's.
-/

open scoped Pointwise

namespace GQ2.Dyadic

open GQ2.SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

section Recursion

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)

/-! ## The five `b`-typed counts

`RecursionFrame.zR` (`Recursion.lean:114`) is boundary-free and is **not** cloned; it is used
below as `RF.zR`, the model's own. -/

open scoped Classical in
/-- `m_{Γ,λ}(B)`.  Clone of `GQ2.SectionEight.RecursionFrame.mB` (`Recursion.lean:120`). -/
noncomputable def mBK (l : RF.DR) : ℕ :=
  if h : l = RF.zeroDR then exactImageCountK b F RF.TB
  else Nat.card {f : BoundaryLiftsK b F RF.TB //
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = f.1.1 γ}

open scoped Classical in
/-- `m_{Γ,λ}(J)` for a proper stratum `J < B`.  Clone of `RecursionFrame.mJ`
(`Recursion.lean:129`). -/
noncomputable def mJK (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
    (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)) : ℕ :=
  liftableCountK b F RF.TB (RF.scalarCover l h) J hJ

open scoped Classical in
/-- `m_{Γ,λ}(J)`, totalized over all subgroups.  Clone of `RecursionFrame.mJOn`
(`Recursion.lean:136`). -/
noncomputable def mJOnK (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB) : ℕ :=
  if hJ : Function.Surjective (RF.TB.piY.comp J.subtype) then mJK RF b F l h J hJ else 0

/-- `Z_{Γ,λ}(B/C)`.  Clone of `RecursionFrame.zBC` (`Recursion.lean:151`), including its
encoding-correction docstring: the datum is the `B`-lift `m` with the **existence** of a cover
lift, not the cover-valued lift itself. -/
noncomputable def zBCK (l : RF.DR) (h : l ≠ RF.zeroDR) : ℕ :=
  Nat.card {pr : BoundaryLiftsK b F RF.TC × ContinuousMonoidHom Γ RF.YB //
    (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧
      IsBoundaryLiftK b F RF.TB pr.2 ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ}

/-- `n_{Γ,0}(ζ)` for a phase cover `C_ζ ↠ C`.  Clone of `RecursionFrame.nPhase`
(`Recursion.lean:160`). -/
noncomputable def nPhaseK (Cζ : CentralCover RF.YC) : ℕ :=
  Nat.card {f : BoundaryLiftsK b F RF.TC //
    ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ}

/-- **The `B`-stage projection of a boundary lift**.  Clone of `RecursionFrame.liftB`
(`Recursion.lean:168`) — verbatim; the spec fields `TB_head`/`TB_theta` are the model's. -/
noncomputable def liftBK (f : BoundaryLiftsK b F T) : BoundaryLiftsK b F RF.TB :=
  ⟨⟨⟨RF.piB.comp f.1.1.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑RF.piB)).comp f.1.1.continuous_toFun⟩,
    RF.piB_surj.comp f.1.2⟩,
   fun γ => by
     show (RF.TB.piY (RF.piB (f.1.1 γ)), RF.TB.thetaY (RF.piB (f.1.1 γ))) = F.frameMap (b γ)
     have h1 : RF.TB.piY (RF.piB (f.1.1 γ)) = T.piY (f.1.1 γ) :=
       DFunLike.congr_fun RF.TB_head (f.1.1 γ)
     have h2 : RF.TB.thetaY (RF.piB (f.1.1 γ)) = T.thetaY (f.1.1 γ) :=
       DFunLike.congr_fun RF.TB_theta (f.1.1 γ)
     rw [h1, h2]
     exact f.2 γ⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Boundary-framing rides free over `ρ`**.  Clone of `RecursionFrame.isBoundaryLift_of_over`
(`Recursion.lean:289`) — verbatim; `headBC`/`thetaBC` are the model's derived layer. -/
theorem isBoundaryLiftK_of_over (f : ContinuousMonoidHom Γ RF.YB)
    (ρ : BoundaryLiftsK b F RF.TC) (hover : ∀ γ, RF.piBC (f γ) = ρ.1.1 γ) :
    IsBoundaryLiftK b F RF.TB f := by
  intro γ
  have h1 : RF.TB.piY (f γ) = RF.TC.piY (ρ.1.1 γ) := by
    rw [← hover γ]; exact (DFunLike.congr_fun RF.headBC (f γ)).symm
  have h2 : RF.TB.thetaY (f γ) = RF.TC.thetaY (ρ.1.1 γ) := by
    rw [← hover γ]; exact (DFunLike.congr_fun RF.thetaBC (f γ)).symm
  rw [h1, h2]
  exact ρ.2 γ

end Recursion

open scoped Classical in
/-- **The boxed system of Prop 8.9** at the `K`-boundary, numerically parameterized.  Clone of
`GQ2.SectionEight.ClosedRecursion` (`Recursion.lean:383`).

The three literals become the opaque `(cS mM vH : ℕ)` of the module docstring's table; every
other datum (`μ`, `G0`, `DT`, `phase`, `RF.zR`, the `2`s of (136) and (140)) is unchanged. -/
structure ClosedRecursionK {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (cS mM vH : ℕ) : Prop where
  /-- **(136)**, multiplied out. -/
  eq136 : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)
  /-- **(137)**, additively (with the model's index-set correction: the sum runs over the
  proper strata surjecting onto `C`). -/
  eq137 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (zBCK RF b F l h : ℤ) = mBK RF b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (mJOnK RF b F l h J : ℤ)
  /-- **(138)**: the eight-lift partition at the `λ`-cover, with the scalar `cS`. -/
  eq138 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
      (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)),
    cS * mJK RF b F l h J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup (RF.scalarCover l h).cover |
          J'.map (RF.scalarCover l h).p = J},
          exactImageCountOnK b F ((RF.scalarCover l h).pullTarget RF.TB) J'
  /-- **(139)**: the nonzero-edge half-torsor value, with the multiplicity `mM`. -/
  eq139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC
  /-- **(140)–(142)**, folded: the zero-edge constrained-Gauss value over the per-`λ` phase
  family, with the `#H¹`-factor `vH`. -/
  eq140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * zBCK RF b F l h
        = μ * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (nPhaseK RF b F (phase l h ζ) : ℤ) - exactImageCountK b F RF.TC))

section Partition137

open scoped Classical

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  (RF : RecursionFrame T Blk)
  (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
  (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- The set of `B`-level lifts underlying `Z_{Γ,λ}(B/C)`.  Clone of `partition137Set`
(`Recursion.lean:446`). -/
private abbrev partition137SetK : Type :=
  {m : ContinuousMonoidHom Γ RF.YB //
    (IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)) ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m γ}

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), pair elimination**.  Clone of `partition137_zBC_eq_card`
(`Recursion.lean:456`) — verbatim. -/
private theorem partition137K_zBC_eq_card :
    zBCK RF b F l h = Nat.card (partition137SetK RF b F l h) := by
  refine Nat.card_congr ⟨fun pr => ⟨pr.1.2, ⟨pr.2.2.1, ?_⟩, pr.2.2.2⟩,
    fun m => ⟨(⟨⟨⟨RF.piBC.comp m.1.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun⟩,
      m.2.1.2⟩,
      fun γ => by
        show (RF.TC.piY (RF.piBC (m.1 γ)), RF.TC.thetaY (RF.piBC (m.1 γ)))
          = F.frameMap (b γ)
        have h1 : RF.TC.piY (RF.piBC (m.1 γ)) = RF.TB.piY (m.1 γ) :=
          DFunLike.congr_fun RF.headBC (m.1 γ)
        have h2 : RF.TC.thetaY (RF.piBC (m.1 γ)) = RF.TB.thetaY (m.1 γ) :=
          DFunLike.congr_fun RF.thetaBC (m.1 γ)
        rw [h1, h2]
        exact m.2.1.1 γ⟩, m.1), fun γ => rfl, m.2.1.1, m.2.2⟩,
    fun pr => ?_, fun m => ?_⟩
  · have hfun : ⇑RF.piBC ∘ ⇑pr.1.2 = ⇑pr.1.1.1.1 := funext fun γ => pr.2.1 γ
    rw [hfun]
    exact pr.1.1.1.2
  · obtain ⟨⟨f, m⟩, hcompat, hbd, hg⟩ := pr
    refine Subtype.ext (Prod.ext ?_ rfl)
    refine Subtype.ext (Subtype.ext ?_)
    apply ContinuousMonoidHom.ext
    intro γ
    exact hcompat γ
  · exact Subtype.ext rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), top stratum**.  Clone of `partition137_card_fiber_top` (`Recursion.lean:486`) —
verbatim. -/
private theorem partition137K_card_fiber_top :
    Nat.card {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = ⊤}
      = mBK RF b F l := by
  rw [mBK, dif_neg h]
  refine Nat.card_congr ⟨fun m => ⟨⟨⟨m.1.1, fun y => ?_⟩, m.1.2.1.1⟩, m.1.2.2⟩,
    fun f => ⟨⟨f.1.1.1, ⟨f.1.2, RF.piBC_surj.comp f.1.1.2⟩, f.2⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  · have hy : y ∈ m.1.1.toMonoidHom.range := by rw [m.2]; trivial
    exact hy
  · rw [MonoidHom.range_eq_top]
    exact f.1.1.2

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), proper stratum**.  Clone of `partition137_card_fiber_stratum`
(`Recursion.lean:502`) — verbatim. -/
private theorem partition137K_card_fiber_stratum (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC = ⊤)
    (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = J}
      = mJK RF b F l h J hJh := by
  rw [mJK, liftableCountK]
  have hmem : ∀ (m : partition137SetK RF b F l h), m.1.toMonoidHom.range = J →
      ∀ γ, m.1 γ ∈ J := by
    intro m hm γ
    have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
    rwa [hm] at this
  refine Nat.card_congr ⟨fun m =>
    ⟨⟨⟨cmhCodRestrict m.1.1 J (hmem m.1 m.2), fun j => ?_⟩, fun γ => ?_⟩, ?_⟩,
    fun f => ⟨⟨cmhInclude J f.1.1.1, ⟨fun γ => f.1.2 γ, ?_⟩, ?_⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (Subtype.ext (by
      apply ContinuousMonoidHom.ext
      intro γ
      exact Subtype.ext rfl)))⟩
  · have hj : (j : RF.YB) ∈ m.1.1.toMonoidHom.range := by rw [m.2]; exact j.2
    obtain ⟨γ, hγ⟩ := hj
    exact ⟨γ, Subtype.ext hγ⟩
  · exact m.1.2.1.1 γ
  · obtain ⟨g, hg⟩ := m.1.2.2
    exact ⟨g, fun γ => hg γ⟩
  · intro c
    have hc : c ∈ J.map RF.piBC := by rw [hJc]; trivial
    obtain ⟨y, hyJ, hyc⟩ := Subgroup.mem_map.mp hc
    obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hyJ⟩
    exact ⟨γ, by
      show RF.piBC ((f.1.1.1 γ : RF.YB)) = c
      rw [hγ, hyc]⟩
  · obtain ⟨g, hg⟩ := f.2
    exact ⟨g, fun γ => hg γ⟩
  · have h1 : (cmhInclude J f.1.1.1).toMonoidHom.range
        = f.1.1.1.toMonoidHom.range.map J.subtype := MonoidHom.range_comp _ _
    rw [h1, MonoidHom.range_eq_top.mpr f.1.1.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), `C`-missing strata are empty**.  Clone of
`partition137_card_fiber_eq_zero_of_not_map` (`Recursion.lean:550`) — verbatim. -/
private theorem partition137K_card_fiber_eq_zero_of_not_map (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC ≠ ⊤) :
    Nat.card {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = J} = 0 := by
  have hE : IsEmpty {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJc
    rw [← hm, ← MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top]
    intro c
    obtain ⟨γ, hγ⟩ := m.2.1.2 c
    exact ⟨γ, hγ⟩
  exact Nat.card_of_isEmpty

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **(137), head-missing strata are empty**.  Clone of
`partition137_card_fiber_eq_zero_of_not_head` (`Recursion.lean:567`) — verbatim. -/
private theorem partition137K_card_fiber_eq_zero_of_not_head
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) (J : Subgroup RF.YB)
    (hJh : ¬ Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = J} = 0 := by
  have hE : IsEmpty {m : partition137SetK RF b F l h // m.1.toMonoidHom.range = J} := by
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
    have hbd := m.2.1.1 γ
    have := congrArg Prod.fst hbd
    simpa [hγ] using this
  exact Nat.card_of_isEmpty

end Partition137

open scoped Classical in
/-- **The (137) partition**, derived outright.  Clone of `GQ2.SectionEight.partition137_of`
(`Recursion.lean:596`) — verbatim modulo the `K`-boundary retype. -/
theorem partition137_ofK {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    (zBCK RF b F l h : ℤ) = mBK RF b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (mJOnK RF b F l h J : ℤ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLiftsK b F RF.TB) := finite_boundaryLiftsK b F RF.TB hfg
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Finite (Subgroup RF.YB) :=
    Finite.of_injective (fun J : Subgroup RF.YB => (J : Set RF.YB)) SetLike.coe_injective
  haveI : Fintype (Subgroup RF.YB) := Fintype.ofFinite _
  -- ===== Step 1: eliminate the pair =====
  set Mset := partition137SetK RF b F l h with hMsetdef
  haveI : Finite Mset := Subtype.finite
  have e1 : zBCK RF b F l h = Nat.card Mset := partition137K_zBC_eq_card RF b F l h
  -- ===== Step 2: stratify by the exact image =====
  have e2 : Nat.card Mset
      = ∑ J : Subgroup RF.YB, Nat.card {m : Mset // m.1.toMonoidHom.range = J} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun m : Mset => m.1.toMonoidHom.range)).symm, Nat.card_sigma]
  -- ===== Step 3: the fibres =====
  have htop : Nat.card {m : Mset // m.1.toMonoidHom.range = ⊤} = mBK RF b F l :=
    partition137K_card_fiber_top RF b F l h
  have hstr : ∀ (J : Subgroup RF.YB) (_hJc : J.map RF.piBC = ⊤)
      (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)),
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = mJK RF b F l h J hJh :=
    fun J hJc hJh => partition137K_card_fiber_stratum RF b F l h J hJc hJh
  have hemptyC : ∀ (J : Subgroup RF.YB), J.map RF.piBC ≠ ⊤ →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 :=
    fun J hJc => partition137K_card_fiber_eq_zero_of_not_map RF b F l h J hJc
  have hemptyH : ∀ (J : Subgroup RF.YB),
      ¬ Function.Surjective (RF.TB.piY.comp J.subtype) →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 :=
    fun J hJh => partition137K_card_fiber_eq_zero_of_not_head RF b F l h hhead J hJh
  -- ===== Step 4: assemble =====
  set fib : Subgroup RF.YB → ℕ :=
    fun J => Nat.card {m : Mset // m.1.toMonoidHom.range = J} with hfibdef
  set S : Finset (Subgroup RF.YB) :=
    ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
      (fun J => J.map RF.piBC = ⊤) with hSdef
  have hsplit : ∑ J : Subgroup RF.YB, fib J
      = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ ⊤)]
  have hrest : ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J
      = ∑ J ∈ S, fib J := by
    rw [hSdef,
      ← Finset.sum_filter_add_sum_filter_not
        ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤)
        (fun J => J.map RF.piBC = ⊤) fib]
    have hz : ∑ J ∈ ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
          (fun J => ¬ J.map RF.piBC = ⊤), fib J = 0 := by
      refine Finset.sum_eq_zero fun J hJ => ?_
      exact hemptyC J (Finset.mem_filter.mp hJ).2
    rw [hz, add_zero]
  have hmatch : ∀ J ∈ S, fib J = mJOnK RF b F l h J := by
    intro J hJ
    rw [hSdef] at hJ
    obtain ⟨hJne, hJc⟩ := Finset.mem_filter.mp hJ
    rw [mJOnK]
    by_cases hJh : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJh]
      exact hstr J hJc hJh
    · rw [dif_neg hJh]
      exact hemptyH J hJh
  have hsetconv : {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤} = ↑S := by
    rw [hSdef]
    ext J
    simp [Finset.mem_erase, and_comm]
  have hfinsum : ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
        (mJOnK RF b F l h J : ℤ)
      = ∑ J ∈ S, (mJOnK RF b F l h J : ℤ) := by
    rw [hsetconv, finsum_mem_coe_finset]
  have hnat : zBCK RF b F l h = mBK RF b F l + ∑ J ∈ S, mJOnK RF b F l h J := by
    calc zBCK RF b F l h = Nat.card Mset := e1
      _ = ∑ J : Subgroup RF.YB, fib J := e2
      _ = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := hsplit
      _ = mBK RF b F l + ∑ J ∈ S, fib J := by
          have htop' : fib ⊤ = mBK RF b F l := htop
          rw [htop', hrest]
      _ = mBK RF b F l + ∑ J ∈ S, mJOnK RF b F l h J := by
          rw [Finset.sum_congr rfl hmatch]
  rw [hfinsum, hnat]
  push_cast
  ring

open scoped Classical in
/-- **The source-side input bundle** at the `K`-boundary, numerically parameterized.  Clone of
`GQ2.SectionEight.RecursionInputs` (`Recursion.lean:706`).  The displays (137) and (138) are
*not* inputs — `prop_8_9_auxK` discharges them from `partition137_ofK` and `lemma_8_3K`. -/
structure RecursionInputsK {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (mM vH : ℕ) : Prop where
  /-- The (136)-stage identity. -/
  stageR136 : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)
  /-- The (139) half count, at the multiplicity `mM`. -/
  half139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC
  /-- The (140) constrained-Gauss value, at the `#H¹`-factor `vH`. -/
  phase140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * zBCK RF b F l h
        = μ * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (nPhaseK RF b F (phase l h ζ) : ℤ) - exactImageCountK b F RF.TC))

open scoped Classical in
/-- **The Prop 8.9 assembly step** at the `K`-boundary.  Clone of
`GQ2.SectionEight.prop_8_9_aux` (`Recursion.lean:738`) — verbatim; **(138) is discharged from
`lemma_8_3K`** at the scalar `cS`, exactly as the model discharges it from `lemma_8_3` at `8`.
-/
theorem prop_8_9_auxK {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (cS : ℕ) (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = cS)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (mM vH : ℕ)
    (inp : RecursionInputsK RF b F μ G0 DT phase mM vH) :
    ClosedRecursionK RF b F μ G0 DT phase cS mM vH where
  eq136 := inp.stageR136
  eq137 := partition137_ofK RF hfg b F hhead
  eq138 := fun l h => lemma_8_3K hfg b F RF.TB (RF.scalarCover l h) cS hscalar
  eq139 := inp.half139
  eq140 := inp.phase140

open scoped Classical in
/-- **The (136) stage, combinatorial core** at the `K`-boundary.  Clone of
`GQ2.SectionEight.stageR136_of` (`Recursion.lean:771`) — verbatim; the Fourier engine
`lemma_8_4` is boundary-free and is the model's, by import. -/
theorem stageR136_ofK {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (o : BoundaryLiftsK b F RF.TB → W)
    (e : RF.DR ≃ Module.Dual (ZMod 2) W)
    (he0 : e RF.zeroDR = 0)
    (hmB : ∀ (l : RF.DR), l ≠ RF.zeroDR →
      mBK RF b F l = Nat.card {g : BoundaryLiftsK b F RF.TB // e l (o g) = 0})
    (hobs : ∀ g : BoundaryLiftsK b F RF.TB,
      o g = 0 ↔ ∃ f : BoundaryLiftsK b F T, liftBK RF b F f = g)
    (hfib : ∀ g : BoundaryLiftsK b F RF.TB, o g = 0 →
      Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
  classical
  haveI : Finite (BoundaryLiftsK b F T) := finite_boundaryLiftsK b F T hfg
  haveI : Finite (BoundaryLiftsK b F RF.TB) := finite_boundaryLiftsK b F RF.TB hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TB) := Fintype.ofFinite _
  -- Step 1 (fibration): `e_Γ(Y) = z_R · #{o = 0}`.
  have h1 : exactImageCountK b F T
      = RF.zR * Nat.card {g : BoundaryLiftsK b F RF.TB // o g = 0} := by
    have hsig : exactImageCountK b F T
        = ∑ g : BoundaryLiftsK b F RF.TB,
            Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g} := by
      rw [exactImageCountK,
        Nat.card_congr (Equiv.sigmaFiberEquiv (liftBK RF b F)).symm, Nat.card_sigma]
    rw [hsig]
    have hterm : ∀ g : BoundaryLiftsK b F RF.TB,
        Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g}
          = if o g = 0 then RF.zR else 0 := by
      intro g
      by_cases hg : o g = 0
      · rw [if_pos hg]
        exact hfib g hg
      · rw [if_neg hg]
        have hempty : IsEmpty {f : BoundaryLiftsK b F T // liftBK RF b F f = g} := by
          constructor
          rintro ⟨f, hf⟩
          exact hg ((hobs g).mpr ⟨f, hf⟩)
        exact Nat.card_of_isEmpty
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 2 (Fourier): `lemma_8_4` at the obstruction map.
  have h2 := lemma_8_4 (X := BoundaryLiftsK b F RF.TB) (W := W) o
  haveI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod 2) W => (φ : W → ZMod 2))
      DFunLike.coe_injective
  haveI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  -- Step 3 (reindex the character sum along `e`, matching `m_B`).
  have h3 : ∑ᶠ φ : Module.Dual (ZMod 2) W,
        (2 * (Nat.card {g : BoundaryLiftsK b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLiftsK b F RF.TB))
      = ∑ᶠ l : RF.DR, (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Equiv.sum_comp e (fun φ =>
        2 * (Nat.card {g : BoundaryLiftsK b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLiftsK b F RF.TB))]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = RF.zeroDR
    · subst hl
      rw [he0]
      have hall : Nat.card {g : BoundaryLiftsK b F RF.TB //
          (0 : Module.Dual (ZMod 2) W) (o g) = 0} = Nat.card (BoundaryLiftsK b F RF.TB) := by
        refine Nat.card_congr (Equiv.subtypeUnivEquiv fun g => ?_)
        simp
      have hmB0 : mBK RF b F RF.zeroDR = exactImageCountK b F RF.TB := by
        rw [mBK, dif_pos rfl]
      rw [hall, hmB0, exactImageCountK]
    · rw [hmB l hl]
      rfl
  -- Assemble in `ℤ`.
  have hcardDR : (Nat.card RF.DR : ℤ) = Nat.card (Module.Dual (ZMod 2) W) := by
    exact_mod_cast Nat.card_congr e
  calc (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = (Nat.card RF.DR : ℤ)
        * (RF.zR * Nat.card {g : BoundaryLiftsK b F RF.TB // o g = 0}) := by
        rw [h1]; push_cast; ring
    _ = RF.zR * ((Nat.card (Module.Dual (ZMod 2) W) : ℤ)
        * Nat.card {g : BoundaryLiftsK b F RF.TB // o g = 0}) := by
        rw [← hcardDR]; ring
    _ = RF.zR * ∑ᶠ φ : Module.Dual (ZMod 2) W,
          (2 * (Nat.card {g : BoundaryLiftsK b F RF.TB // φ (o g) = 0} : ℤ)
            - Nat.card (BoundaryLiftsK b F RF.TB)) := by
        rw [h2]
    _ = RF.zR * ∑ᶠ l : RF.DR, (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
        rw [h3]

end GQ2.Dyadic
