/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Covers
import GQ2.SectionEight.Partition

/-!
# §8 Lemma 8.3 at the `K`-boundary, scalar-parameterized (dyadic campaign, ticket SD-R1)

Clone of the Lemma 8.3 layer of `GQ2/SectionEight/Partition.lean:31-268`, re-typed at the
`K`-boundary and with the literal `8` replaced by an opaque scalar parameter `cS`.

## The numeric parameterization  (memo §4.1(a))

`lemma_8_3` (`Partition.lean:209`) carries the scalar as the hypothesis
`hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8` and as the
coefficient of its conclusion.  The proof was **already value-generic**: it counts the
projection fibres as `Nat.card (ContinuousMonoidHom Γ 𝔽₂)` (via `fiberLiftEquiv`) and only
then rewrites by `hscalar`.  Replacing `8` by a variable `cS` is therefore **verbatim** — no
proof step changes, confirming the memo's claim at this carrier.

`cS` is a bare `ℕ`, not a `SourceNumerics` projection: the recursion layer consumes opaque
shared constants and never inspects a formula (memo Q3).  SD3 instantiates `cS :=
SN.homScalar` at the two-sided theorem; `SN.homScalar_pos` is *not* needed here — positivity
is consumed only where the coefficient is **cancelled**, which is SD-R2's `Induction.lean`
solver and SD-R3's `rStage_phase` (memo §4.1(a)).

## What is reused rather than cloned

`stratum_surj` (`Partition.lean:58`) is boundary-free and is consumed by import.  So are
`CentralCover.pullTarget`, the corestriction layer, and `fiberLiftEquiv` (see
`GQ2/Dyadic/Recursion/Covers.lean`'s finding note).  The file's Lemma 8.6 half-torsor block
(`lemma_8_6_gammaA` :291, `lemma_8_6_local` :304) is **not** spine: those are the `Γ_A`/`G_ℚ₂`
instantiations, whose `K`-analogues belong to the §3.3 supply package (ticket ASK).

Axioms: none beyond std-3; the clone's print equals its model's.
-/

open scoped Pointwise

namespace GQ2.Dyadic

open GQ2.SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## Lemma 8.3: the eight-lift partition  (display (124)) -/

section Lemma83

variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
  (T : MarkedTarget H E Y) (C : CentralCover Y) (J : Subgroup Y)

/-- The master set of Lemma 8.3.  Clone of `GQ2.SectionEight.masterLifts`
(`Partition.lean:48`). -/
abbrev masterLiftsK : Type :=
  {g : ContinuousMonoidHom Γ C.cover //
    (C.pCont.comp g).toMonoidHom.range = J ∧ IsBoundaryLiftK b F T (C.pCont.comp g)}

end Lemma83

section Lemma83Fibres

variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
  (T : MarkedTarget H E Y) (C : CentralCover Y) (J : Subgroup Y)
  (hJ : Function.Surjective (T.piY.comp J.subtype))

/-- The **image-stratum lifts** of Lemma 8.3.  Clone of `masterLiftsImage`
(`Partition.lean:80`). -/
private abbrev masterLiftsImageK : Type :=
  {f : BoundaryLiftsK b F (T.stratum J hJ) //
    ∃ g : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (g γ) = (f.1.1 γ : Y)}

omit [DiscreteTopology Y] in
/-- Any master lift projects into `J`.  Clone of `masterLifts_pComp_mem`
(`Partition.lean:86`). -/
private theorem masterLiftsK_pComp_mem (g : masterLiftsK b F T C J) :
    ∀ γ : Γ, C.p (g.1 γ) ∈ J := fun γ => by
  have hmem : (C.pCont.comp g.1).toMonoidHom γ ∈ (C.pCont.comp g.1).toMonoidHom.range := ⟨γ, rfl⟩
  rw [g.2.1] at hmem; exact hmem

/-- **The projection fibration map** `g ↦ p∘g`.  Clone of `masterLiftsProjB`
(`Partition.lean:93`). -/
private noncomputable def masterLiftsProjBK :
    masterLiftsK b F T C J → masterLiftsImageK b F T C J hJ :=
  fun g =>
    ⟨⟨⟨cmhCodRestrict (C.pCont.comp g.1) J (masterLiftsK_pComp_mem b F T C J g), fun y => by
        have hy : (y : Y) ∈ (C.pCont.comp g.1).toMonoidHom.range := by rw [g.2.1]; exact y.2
        obtain ⟨γ, hγ⟩ := hy
        exact ⟨γ, Subtype.ext hγ⟩⟩, g.2.2⟩, g.1, fun γ => rfl⟩

/-- **The image fibration map** `g ↦ g.range`.  Clone of `masterLiftsImageMap`
(`Partition.lean:103`). -/
private noncomputable def masterLiftsImageMapK :
    masterLiftsK b F T C J → {J' : Subgroup C.cover // J'.map C.p = J} :=
  fun g => ⟨g.1.toMonoidHom.range, by
    have hrange : (C.pCont.comp g.1).toMonoidHom.range = g.1.toMonoidHom.range.map C.p :=
      MonoidHom.range_comp _ _
    rw [← hrange]; exact g.2.1⟩

omit [DiscreteTopology Y] in
/-- **Projection fibre = torsor of `Hom_cont(Γ,𝔽₂)`**.  Clone of `masterLifts_projFibre`
(`Partition.lean:113`) — verbatim; `fiberLiftEquiv` is the model's, by import. -/
private theorem masterLiftsK_projFibre (f : masterLiftsImageK b F T C J hJ) :
    Nat.card {g : masterLiftsK b F T C J // masterLiftsProjBK b F T C J hJ g = f}
      = Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) := by
  obtain ⟨g₀, hg₀⟩ := f.2
  refine Nat.card_congr (Equiv.trans ?_ (fiberLiftEquiv C g₀).symm)
  refine
    { toFun := fun g => ⟨g.1.1, fun γ => ?_⟩
      invFun := fun g' => ⟨⟨g'.1, ?_, ?_⟩, ?_⟩
      left_inv := fun g => ?_
      right_inv := fun g' => ?_ }
  · have h1 : C.p (g.1.1 γ) = (f.1.1.1 γ : Y) :=
      congrArg (fun w : masterLiftsImageK b F T C J hJ => (w.1.1.1 γ : Y)) g.2
    rw [h1, ← hg₀]
  · show (C.pCont.comp g'.1).toMonoidHom.range = J
    apply le_antisymm
    · rintro _ ⟨γ, rfl⟩
      show C.p (g'.1 γ) ∈ J
      rw [g'.2 γ, hg₀]; exact (f.1.1.1 γ).2
    · intro y hy
      obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hy⟩
      refine ⟨γ, ?_⟩
      show C.p (g'.1 γ) = y
      rw [g'.2 γ, hg₀, hγ]
  · have heq : C.pCont.comp g'.1 = C.pCont.comp g₀ := by ext γ; exact g'.2 γ
    rw [heq]
    intro γ
    show (T.piY (C.p (g₀ γ)), T.thetaY (C.p (g₀ γ))) = F.frameMap (b γ)
    rw [hg₀ γ]
    exact f.1.2 γ
  · apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    ext γ
    show C.p (g'.1 γ) = (f.1.1.1 γ : Y)
    rw [g'.2 γ, hg₀]
  · rfl
  · rfl

omit [DiscreteTopology Y] in
include hJ in
/-- **Image fibre = boundary lifts of the pullback stratum**.  Clone of
`masterLifts_imageFibre` (`Partition.lean:158`) — verbatim; `stratum_surj` is the model's, by
import (it is boundary-free). -/
private theorem masterLiftsK_imageFibre
    (J' : {J' : Subgroup C.cover // J'.map C.p = J}) :
    Nat.card {g : masterLiftsK b F T C J // masterLiftsImageMapK b F T C J g = J'}
      = exactImageCountOnK b F (C.pullTarget T) J'.1 := by
  have hrange : ∀ (g : ContinuousMonoidHom Γ C.cover),
      (C.pCont.comp g).toMonoidHom.range = g.toMonoidHom.range.map C.p := fun g =>
    MonoidHom.range_comp _ _
  have hsurj := stratum_surj hJ J'.2
  rw [exactImageCountOnK, dif_pos hsurj, exactImageCountK]
  apply Nat.card_congr
  refine
    { toFun := fun g => ?_
      invFun := fun gt => ?_
      left_inv := fun g => ?_
      right_inv := fun gt => ?_ }
  · have hrgK : g.1.1.toMonoidHom.range = J'.1 := congrArg Subtype.val g.2
    have hmemK : ∀ γ, g.1.1 γ ∈ J'.1 := fun γ => hrgK ▸ ⟨γ, rfl⟩
    refine ⟨⟨cmhCodRestrict g.1.1 J'.1 hmemK, ?_⟩, ?_⟩
    · rintro ⟨y, hy⟩
      rw [← hrgK] at hy
      obtain ⟨γ, hγ⟩ := hy
      exact ⟨γ, Subtype.ext hγ⟩
    · intro γ
      show ((C.pullTarget T).piY (g.1.1 γ), (C.pullTarget T).thetaY (g.1.1 γ)) = F.frameMap (b γ)
      exact g.1.2.2 γ
  · have hsurj_gt : Function.Surjective ⇑gt.1.1.toMonoidHom := gt.1.2
    have hincl : (cmhInclude J'.1 gt.1.1).toMonoidHom.range = J'.1 := by
      show (J'.1.subtype.comp gt.1.1.toMonoidHom).range = J'.1
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hsurj_gt, ← MonoidHom.range_eq_map J'.1.subtype,
        Subgroup.range_subtype]
    refine ⟨⟨cmhInclude J'.1 gt.1.1, ?_, ?_⟩, ?_⟩
    · rw [hrange, hincl]; exact J'.2
    · intro γ
      show (T.piY (C.p (gt.1.1 γ : C.cover)), T.thetaY (C.p (gt.1.1 γ : C.cover)))
        = F.frameMap (b γ)
      exact gt.2 γ
    · exact Subtype.ext hincl
  · apply Subtype.ext; apply Subtype.ext; ext γ; rfl
  · apply Subtype.ext; apply Subtype.ext; ext γ; rfl

end Lemma83Fibres

/-- **Central-cover exact-image transform** at the `K`-boundary, with the scalar as a
parameter.  Clone of `GQ2.SectionEight.lemma_8_3` (`GQ2/SectionEight/Partition.lean:209`).

Parameterization delta: the literal `8` becomes the opaque `cS` (hypothesis `hscalar` and
conclusion coefficient).  **The proof is verbatim** — the model already counted the projection
fibres as `Nat.card (ContinuousMonoidHom Γ 𝔽₂)` and rewrote by `hscalar` afterwards, so no
step depends on the value (memo §4.1(a)).  SD3 instantiates `cS := SN.homScalar`. -/
theorem lemma_8_3K
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y) (cS : ℕ)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = cS)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    cS * liftableCountK b F T C J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
          exactImageCountOnK b F (C.pullTarget T) J' := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ C.cover) := finite_continuousMonoidHom hfg C.cover
  haveI : Finite (masterLiftsK b F T C J) := Subtype.finite
  haveI : Finite (BoundaryLiftsK b F (T.stratum J hJ)) :=
    finite_boundaryLiftsK b F (T.stratum J hJ) hfg
  set L := masterLiftsImageK b F T C J hJ with hLdef
  haveI : Finite L := Subtype.finite
  haveI : Fintype L := Fintype.ofFinite L
  -- **Projection fibration** (fibres are `Hom_cont(Γ,𝔽₂)`-torsors).
  set projB := masterLiftsProjBK b F T C J hJ with hprojBdef
  have hfibB : ∀ f : L, Nat.card {g : masterLiftsK b F T C J // projB g = f}
      = Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) :=
    masterLiftsK_projFibre b F T C J hJ
  have hB : Nat.card (masterLiftsK b F T C J) = cS * liftableCountK b F T C J hJ := by
    calc Nat.card (masterLiftsK b F T C J)
        = Nat.card (Σ f : L, {g : masterLiftsK b F T C J // projB g = f}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv projB)).symm
      _ = ∑ f : L, Nat.card {g : masterLiftsK b F T C J // projB g = f} := Nat.card_sigma
      _ = ∑ _f : L, cS := Finset.sum_congr rfl (fun f _ => (hfibB f).trans hscalar)
      _ = cS * Nat.card L := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            smul_eq_mul, mul_comm]
  -- **Image fibration** (→ RHS; fibres are pullback-stratum lifts).
  haveI : Finite (Subgroup C.cover) :=
    Finite.of_injective (fun H : Subgroup C.cover => (H : Set C.cover)) SetLike.coe_injective
  haveI : Fintype (Subgroup C.cover) := Fintype.ofFinite _
  set imageMap := masterLiftsImageMapK b F T C J with himapdef
  haveI : Fintype {J' : Subgroup C.cover // J'.map C.p = J} := Fintype.ofFinite _
  have hfibA : ∀ J' : {J' : Subgroup C.cover // J'.map C.p = J},
      Nat.card {g : masterLiftsK b F T C J // imageMap g = J'}
        = exactImageCountOnK b F (C.pullTarget T) J'.1 :=
    masterLiftsK_imageFibre b F T C J hJ
  have hsumeq : ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
      exactImageCountOnK b F (C.pullTarget T) J'
      = ∑ J' : {J' : Subgroup C.cover // J'.map C.p = J},
          exactImageCountOnK b F (C.pullTarget T) J'.1 := by
    have hset : {J' : Subgroup C.cover | J'.map C.p = J}
        = ↑(Finset.univ.filter (fun J' : Subgroup C.cover => J'.map C.p = J)) := by
      ext J'; simp
    rw [hset, finsum_mem_coe_finset]
    exact Finset.sum_subtype _ (fun J' => by simp) _
  rw [hsumeq, ← hB, ← Nat.card_congr (Equiv.sigmaFiberEquiv imageMap), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun J' _ => hfibA J')

/-- **The `n = 1` regression for Lemma 8.3**: at `q = 2` with the `ℚ₂` slot and `cS := 8` the
clone's statement **is** the model's, and the model discharges it. -/
theorem lemma_8_3K_eq_lemma_8_3
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    8 * liftableCountK b F T C J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
          exactImageCountOnK b F (C.pullTarget T) J' :=
  lemma_8_3 hfg b F.toBoundaryFrame T C hscalar J hJ

end GQ2.Dyadic
