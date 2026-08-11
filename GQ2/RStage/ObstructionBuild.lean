/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.RStage.Obstruction
import GQ2.CentralObstruction

/-!
# §8 R-stage obstruction module — Option-A construction

Builds the obstruction datum `obs`/`hmB`/`hobs`/`hfib` consumed by
`GQ2.SectionEight.stageR136_ofObstruction` (`GQ2/RStageObstruction.lean`), from the **Option-A
compatibility structure** `RCoverData`: the datum, absent from the bare
`RecursionFrame` + `Enrichment`, that each scalar cover `p_λ = (scalarCover l).p` really is a
quotient of the single radical extension `Y ↠ B = Y/R` — a hom family
`coverMap_λ : Y →* (scalarCover l).cover` with `p_λ ∘ coverMap_λ = π_B`.

The compatibility datum remains a separate structure rather than a field of `Enrichment`, keeping
the generic recursion frame independent of this particular cover realization.  This file proves
the obstruction bridge, fibre count, separation-based lift construction, and the resulting
`stageR136_ofRSepData` interface consumed by the recursion splice.
-/

namespace GQ2

namespace SectionEight

open SectionSeven

/-- **A finite `𝔽₂`-module of cardinality 2 is `ZMod 2`** (linearly).  Used to turn the
scalar obstruction class `homOb ∈ H²(Γ,𝔽₂)` into an `𝔽₂` value once the source numeric
`#H²(Γ,𝔽₂) = 2` is available (`prop_5_16`/`prop_5_15`), so `obs` lands in `D_Rᵛ`. -/
noncomputable def cardTwoLinEquiv {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Nat.card M = 2) : M ≃ₗ[ZMod 2] ZMod 2 := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : FiniteDimensional (ZMod 2) M := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) M = 1 := by
    have h : Fintype.card M = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) M :=
      Module.card_eq_pow_finrank
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hM] at h
    have h2 : (2 : ℕ) ^ 1 = 2 ^ Module.finrank (ZMod 2) M := by rw [pow_one]; exact h
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  exact (Module.finBasisOfFinrankEq (R := ZMod 2) (M := M) hfr).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (ZMod 2))

/-- **The trivial (`M = ⊥`) radical-cover datum** wrapping a bare central cover.  All the
`GQ2.SectionEight.CentralObstruction` engine (the kernel-sign calculus, the obstruction class,
`central_iff_ob_eq_zero`) is stated over a `RadicalCoverData`, but its lifting content uses only
the cover `C`; this reduces "a hom lifts through the central cover `C`" to the engine's
`MLifts.Central`/`ob` at `M = ⊥` (the square form is vacuous). -/
def trivialRCD {Bg : Type} [Group Bg] [Finite Bg] (C : CentralCover Bg) :
    RadicalCoverData Bg where
  C := C
  M := ⊥
  hM := Subgroup.normal_bot
  T := ⊥
  hT := Subgroup.normal_bot
  hTM := le_refl _
  helem := fun m hm => by rw [Subgroup.mem_bot.mp hm]; group
  hcomm := fun m hm m' hm' => by
    rw [Subgroup.mem_bot.mp hm, Subgroup.mem_bot.mp hm']
  q := fun _ => 0
  hq := fun x hx => by
    rw [ZMod.val_zero, pow_zero]
    exact C.sq_eq_one_of_mem_ker (MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hx))
  hrad := fun t ht m hm => by simp [polarMul]
  hTzero := fun t ht => rfl


variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-! ## Step 1 — the `mB ⟺ ob` bridge (via `trivialRCD` + `central_iff_ob_eq_zero`) -/

section Bridge

open ContCoh CentralObstruction

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- `ρ = mk : Bg → Bg/⊥`, precomposed with `g`; the lower map making `g` an `M`-lift of
`trivialRCD C` (`M = ⊥`). -/
noncomputable def trivialRho (g : ContinuousMonoidHom Γ Bg) :
    ContinuousMonoidHom Γ (Bg ⧸ (⊥ : Subgroup Bg)) :=
  ⟨(QuotientGroup.mk' ⊥).comp g.toMonoidHom,
    (continuous_quotient_mk').comp g.continuous_toFun⟩

/-- `g` itself as the `M`-lift of `trivialRCD C` over `trivialRho g`. -/
def trivialMLift (C : CentralCover Bg) (g : ContinuousMonoidHom Γ Bg) :
    MLifts (trivialRCD C) (trivialRho g) :=
  ⟨g, fun _ => rfl⟩

/-- **The scalar obstruction of a hom `g` through a bare central cover `C`** — the
`CentralObstruction.ob` of `g` viewed as an `M = ⊥` lift. -/
noncomputable def homOb (C : CentralCover Bg) (g : ContinuousMonoidHom Γ Bg)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) : H2 Γ (ZMod 2) :=
  ob (trivialRCD C) (trivialRho g) htriv (trivialMLift C g)

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Step 1**: `g` lifts through the central cover `C` iff its scalar obstruction vanishes. -/
theorem liftsThroughCover_iff_homOb (C : CentralCover Bg) (g : ContinuousMonoidHom Γ Bg)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    (∃ h : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (h γ) = g γ)
      ↔ homOb C g htriv = 0 :=
  central_iff_ob_eq_zero (trivialRCD C) (trivialRho g) htriv (trivialMLift C g)

end Bridge

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-- **Option-A compatibility datum (the Prop. 8.9 assembly)**: the missing link between the frame's abstract scalar
covers and the single radical extension `Y ↠ B`.  For each nonzero scalar character `λ`, a
homomorphism `coverMap λ : Y →* (scalarCover λ).cover` realizing `scalarCover λ` as a quotient of
`Y` over `B`: `p_λ ∘ coverMap λ = π_B`.  (This is the frame-level content of "`p_λ` is the pushout
`Y/ker λ ↠ Y/R`", which the `RecursionFrame`/`Enrichment` document but do not carry.) -/
structure RCoverData {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) where
  /-- `coverMap λ : Y →* B_λ`, the realization of the scalar cover as a quotient of `Y`. -/
  coverMap : (l : RF.DR) → (h : l ≠ RF.zeroDR) → Y →* (RF.scalarCover l h).cover
  /-- `p_λ ∘ coverMap λ = π_B`: the cover projects `coverMap λ` back to the `B`-stage map. -/
  coverMap_lifts : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (RF.scalarCover l h).p.comp (coverMap l h) = RF.piB

namespace RCoverData

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  {RF : RecursionFrame T Blk}

/-- `coverMap λ` bundled as a `ContinuousMonoidHom` (free: `Y` is discrete). -/
noncomputable def coverMapC (D : RCoverData RF) (l : RF.DR) (h : l ≠ RF.zeroDR) :
    ContinuousMonoidHom Y (RF.scalarCover l h).cover :=
  ⟨D.coverMap l h, continuous_of_discreteTopology⟩

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **Easy `hobs` direction**: if a `B`-stage boundary lift `f` lifts all the way to `Y` (is
`RF.liftB` of some `Y`-lift `F`), then it lifts through **every** scalar cover `p_λ` — compose the
`Y`-lift with `coverMap λ`.  (The converse — "lifts through every `p_λ` ⟹ lifts to `Y`" — is the
hard separation, using `R`-elementary-abelianness and the Frattini structure.) -/
theorem lifts_scalarCover_of_liftB (D : RCoverData RF)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (fY : BoundaryLifts b F T) :
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = (RF.liftB b F fY).1.1 γ := by
  refine ⟨(D.coverMapC l h).comp fY.1.1, fun γ => ?_⟩
  show (RF.scalarCover l h).p (D.coverMap l h (fY.1.1 γ)) = RF.piB (fY.1.1 γ)
  rw [← MonoidHom.comp_apply, D.coverMap_lifts l h]

end RCoverData

/-! ## Step 2 — the obstruction map `obs`, its linearity, and `hmB` -/

section Obstruction

open ContCoh CentralObstruction

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **The R-stage obstruction datum** (Option A, extended): the compat covers `RCoverData`
together with the `𝔽₂`-module realization of the scalar-character index `D_R` and the
`D_R ≃ (R^∨)^C` **pairing** `pair` (a linear map `D_Rmod → (R →+ 𝔽₂)`), pinned to the covers by
`pair_coverMap` (`pair d = zsign ∘ coverMap_{λ}` on `R`, for `λ = toDR d ≠ 0`).  This is exactly
what the concrete `𝒴`-frame (the Prop. 8.9 assembly/d6) supplies; from it the obstruction map, its linearity, and
`hmB` follow. -/
structure RObstructionData (RF : RecursionFrame T Blk) extends RCoverData RF where
  /-- The `𝔽₂`-module realization of the scalar-character index `D_R`. -/
  DRmod : Type
  [addCommGroup : AddCommGroup DRmod]
  [moduleZMod : Module (ZMod 2) DRmod]
  [finiteDRmod : Finite DRmod]
  /-- `D_Rmod ≃ D_R`. -/
  toDR : DRmod ≃ RF.DR
  /-- … sending `0 ↦ zeroDR`. -/
  h0 : toDR.symm RF.zeroDR = 0
  /-- The `D_R ≃ (R^∨)^C` pairing: `pair d` is a `𝔽₂`-functional on the radical `R = Blk.frattiniK`,
  linear in `d`. -/
  pair : DRmod →ₗ[ZMod 2] (Additive ↥Blk.frattiniK →+ ZMod 2)
  /-- The pairing is `zsign ∘ coverMap_λ` on `R` (`λ = toDR d ≠ 0`): the scalar character `d`
  reads off the `λ`-cover's kernel sign of a radical element. -/
  pair_coverMap : ∀ (d : DRmod) (h : toDR d ≠ RF.zeroDR) (r : ↥Blk.frattiniK),
    pair d (Additive.ofMul r)
      = zsign (trivialRCD (RF.scalarCover (toDR d) h))
          (coverMap (toDR d) h (r : Y))

attribute [instance] RObstructionData.addCommGroup RObstructionData.moduleZMod
  RObstructionData.finiteDRmod

variable (RF : RecursionFrame T Blk)

/-- A set-theoretic section of `π_B : Y ↠ B`. -/
noncomputable def slift (x : RF.YB) : Y := Function.surjInv RF.piB_surj x

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
@[simp] theorem piB_slift (x : RF.YB) : RF.piB (slift RF x) = x :=
  Function.surjInv_eq RF.piB_surj x

/-- **The `R`-valued section defect** of a `B`-stage map `g : Γ → B` for the single set-lift
`slift`: `Obs^s_g(γ,δ) = s(gγ)·s(gδ)·s(g(γδ))⁻¹ ∈ R = ker π_B`. -/
noncomputable def rDefect (g : ContinuousMonoidHom Γ RF.YB) (γ δ : Γ) : ↥Blk.frattiniK :=
  ⟨slift RF (g γ) * slift RF (g δ) * (slift RF (g (γ * δ)))⁻¹, by
    rw [← RF.ker_piB, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      piB_slift, piB_slift, piB_slift, map_mul]
    group⟩

section Cohomology

open ContCoh CentralObstruction

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- `H²(Γ,𝔽₂)` is a `ZMod 2`-module (it has exponent 2, being a quotient of `𝔽₂`-cochains). -/
instance instModuleH2 : Module (ZMod 2) (H2 Γ (ZMod 2)) :=
  AddCommGroup.zmodModule (fun x => by
    obtain ⟨c, rfl⟩ := H2mk_surjective x
    rw [← map_nsmul]
    have hc : (2 : ℕ) • c = 0 := by
      ext gd
      show (2 : ℕ) • (c.1 gd) = 0
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [hc, map_zero])

/-- The lift family of `g` into the `λ`-cover built from the single set-section: `x ↦
coverMap_λ (slift (g x))`. -/
noncomputable def obsLiftFam (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) : Γ → (RF.scalarCover (D.toDR d) h).cover :=
  fun x => D.coverMap (D.toDR d) h (slift RF (g x))

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace Y] [DiscreteTopology Y] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
private theorem obsLiftFam_p (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) (x : Γ) :
    (RF.scalarCover (D.toDR d) h).p (obsLiftFam RF D g d h x) = g x := by
  show (RF.scalarCover (D.toDR d) h).p (D.coverMap (D.toDR d) h (slift RF (g x))) = g x
  rw [← MonoidHom.comp_apply, D.coverMap_lifts (D.toDR d) h, piB_slift]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace Y] [DiscreteTopology Y] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
private theorem obsLiftFam_cont (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) : Continuous (obsLiftFam RF D g d h) := by
  show Continuous ((fun y => D.coverMap (D.toDR d) h (slift RF y)) ∘ (g : Γ → RF.YB))
  exact continuous_of_discreteTopology.comp (map_continuous g)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace Y] [DiscreteTopology Y] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
/-- **The pointwise obstruction identity**: the obstruction cochain of the lift family equals
`pair d` applied to the `R`-valued defect. -/
theorem obCocOf_obsLiftFam (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) (γ δ : Γ) :
    obCocOf (trivialRCD (RF.scalarCover (D.toDR d) h)) (obsLiftFam RF D g d h) (γ, δ)
      = D.pair d (Additive.ofMul (rDefect RF g γ δ)) := by
  rw [D.pair_coverMap d h (rDefect RF g γ δ)]
  show zsign (trivialRCD (RF.scalarCover (D.toDR d) h))
      (obsLiftFam RF D g d h γ * obsLiftFam RF D g d h δ * (obsLiftFam RF D g d h (γ * δ))⁻¹)
    = zsign (trivialRCD (RF.scalarCover (D.toDR d) h))
        (D.coverMap (D.toDR d) h ((rDefect RF g γ δ : ↥Blk.frattiniK) : Y))
  congr 1
  simp only [obsLiftFam]
  rw [show ((rDefect RF g γ δ : ↥Blk.frattiniK) : Y)
        = slift RF (g γ) * slift RF (g δ) * (slift RF (g (γ * δ)))⁻¹ from rfl]
  simp only [map_mul, map_inv]

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
theorem pairDefect_mem_Z2 (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) :
    (fun gd : Γ × Γ => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2))) ∈ Z2 Γ (ZMod 2) := by
  have hmem := obCocOf_mem_Z2 (trivialRCD (RF.scalarCover (D.toDR d) h)) (trivialRho g) htriv
    (obsLiftFam_cont RF D g d h) (f := trivialMLift (RF.scalarCover (D.toDR d) h) g)
    (fun x => obsLiftFam_p RF D g d h x)
  convert hmem using 1
  funext gd
  exact (obCocOf_obsLiftFam RF D g d h gd.1 gd.2).symm

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
/-- **The connection** (step 2 core): the scalar obstruction `homOb` of `g` through the `λ`-cover
is the class of `pair d ∘ rDefect` — so it is `H2mk` of a cochain **linear in `d`**. -/
theorem homOb_eq_H2mk_pair (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) :
    homOb (RF.scalarCover (D.toDR d) h) g htriv
      = H2mk Γ (ZMod 2)
          ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
           pairDefect_mem_Z2 RF D htriv g d h⟩ := by
  rw [homOb, ob_eq_of_liftFam (trivialRCD (RF.scalarCover (D.toDR d) h)) (trivialRho g) htriv
      (trivialMLift (RF.scalarCover (D.toDR d) h) g) (obsLiftFam_cont RF D g d h)
      (fun x => obsLiftFam_p RF D g d h x)]
  exact congrArg _ (Subtype.ext (funext fun gd => obCocOf_obsLiftFam RF D g d h gd.1 gd.2))

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
/-- The obstruction cochain lies in `Z²` for **every** `d` (the `toDR d = 0` case is the zero
cochain, since `pair 0 = 0`). -/
theorem pairDefect_mem_Z2_all (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) :
    (fun gd : Γ × Γ => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2))) ∈ Z2 Γ (ZMod 2) := by
  by_cases h : D.toDR d = RF.zeroDR
  · have hd0 : d = 0 := by rw [← D.h0, ← h, Equiv.symm_apply_apply]
    subst hd0
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact (Z2 Γ (ZMod 2)).zero_mem
  · exact pairDefect_mem_Z2 RF D htriv g d h

/-- **The obstruction map** (additive) `obsMapAdd g : D_Rmod →+ H²(Γ,𝔽₂)`,
`d ↦ [pair d ∘ rDefect]` — additive in `d` (`pair` is linear), and equal to
`homOb(scalarCover λ) g` at `λ = toDR d ≠ 0` (`homOb_eq_H2mk_pair`). -/
noncomputable def obsMapAdd (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) : D.DRmod →+ H2 Γ (ZMod 2) :=
  AddMonoidHom.mk'
    (fun d => H2mk Γ (ZMod 2)
      ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
       pairDefect_mem_Z2_all RF D htriv g d⟩)
    (by
      intro d d'
      rw [← map_add]
      congr 1
      ext gd
      show D.pair (d + d') _ = D.pair d _ + D.pair d' _
      rw [map_add]; rfl)

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
private theorem obsMapAdd_apply (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) :
    obsMapAdd RF D htriv g d = H2mk Γ (ZMod 2)
      ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
       pairDefect_mem_Z2_all RF D htriv g d⟩ := rfl

/-- **The obstruction functional** `obs g : D_Rmod →ₗ 𝔽₂ = D_Rᵛ`: compose the additive
`obsMapAdd` with the linear iso `H²(Γ,𝔽₂) ≃ 𝔽₂` (from the source numeric `#H² = 2`).  Linearity
in the scalar `c ∈ 𝔽₂` is the two-value case split. -/
noncomputable def obs (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (g : ContinuousMonoidHom Γ RF.YB) : D.DRmod →ₗ[ZMod 2] ZMod 2 :=
  haveI : Finite (H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  { toFun := fun d => cardTwoLinEquiv hcard (obsMapAdd RF D htriv g d)
    map_add' := fun d d' => by rw [map_add, map_add]
    map_smul' := fun c d => by
      rw [RingHom.id_apply]
      rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) c with rfl | rfl
      · rw [zero_smul, map_zero, map_zero, zero_smul]
      · rw [one_smul, one_smul] }

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
/-- `obsMapAdd g d` is the scalar obstruction of `g` through the `λ`-cover (`λ = toDR d ≠ 0`). -/
theorem obsMapAdd_eq_homOb (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) :
    obsMapAdd RF D htriv g d = homOb (RF.scalarCover (D.toDR d) h) g htriv :=
  (obsMapAdd_apply RF D htriv g d).trans (homOb_eq_H2mk_pair RF D htriv g d h).symm

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
/-- **`obs g d = 0 ⟺ g lifts through the `λ`-cover** (`λ = toDR d ≠ 0`): the `hmB` pointwise
identity. -/
theorem obs_zero_iff_lifts (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) :
    obs RF D htriv hcard g d = 0
      ↔ ∃ gc : ContinuousMonoidHom Γ (RF.scalarCover (D.toDR d) h).cover,
          ∀ γ, (RF.scalarCover (D.toDR d) h).p (gc γ) = g γ := by
  haveI : Finite (H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  show cardTwoLinEquiv hcard (obsMapAdd RF D htriv g d) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, obsMapAdd_eq_homOb RF D htriv g d h]
  exact (liftsThroughCover_iff_homOb (RF.scalarCover (D.toDR d) h) g htriv).symm

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] [ContinuousSMul Γ (ZMod 2)] in
/-- **`obs` at the `𝔽₂`-cochain level** (for the d6 separation discharge): `obs g d = 0` iff the
`𝔽₂`-valued defect cochain `pair d ∘ rDefect` is a coboundary (`H2mk = 0` in `H²(Γ,𝔽₂)`).  This is
the cochain-level face of `obs_zero_iff_lifts`; it pairs with `homLift_of_split` — from `obs g = 0`,
d6 gets every `pair d ∘ rDefect` a coboundary, assembles the concrete `R`-splitting cochain (the
`(R^∨)^C`-separation of `H²(Γ,R)`), and produces the hom lift. -/
theorem obs_zero_iff_pairClass_zero (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (g : ContinuousMonoidHom Γ RF.YB) (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) :
    obs RF D htriv hcard g d = 0 ↔
      H2mk Γ (ZMod 2) ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
        pairDefect_mem_Z2 RF D htriv g d h⟩ = 0 := by
  haveI : Finite (H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  show cardTwoLinEquiv hcard (obsMapAdd RF D htriv g d) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, obsMapAdd_eq_homOb RF D htriv g d h,
    homOb_eq_H2mk_pair RF D htriv g d h]

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace Y] [DiscreteTopology Y]
  [ContinuousSMul Γ (ZMod 2)] in
/-- **`hmB`** (step 2 payoff): `m_{Γ,λ}(B)` counts the `B`-lifts whose obstruction vanishes at the
scalar character `λ`.  Matches `stageR136_ofObstruction`'s `hmB` hypothesis. -/
theorem hmB_holds (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    RF.mB b F l = Nat.card {f : BoundaryLifts b F RF.TB //
      obs RF D htriv hcard f.1.1 (D.toDR.symm l) = 0} := by
  have hne : D.toDR (D.toDR.symm l) ≠ RF.zeroDR := by
    rw [Equiv.apply_symm_apply]; exact h
  rw [RecursionFrame.mB, dif_neg h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_).symm
  rw [obs_zero_iff_lifts RF D htriv hcard f.1.1 (D.toDR.symm l) hne]
  have hcov : RF.scalarCover (D.toDR (D.toDR.symm l)) hne = RF.scalarCover l h := by
    congr 1; exact Equiv.apply_symm_apply _ _
  rw [hcov]

/-! ## Step 5 — assemble: (136) modulo the two hard classical cores -/
omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) from an `RObstructionData`, modulo the two hard classical cores.**  The obstruction map
`obs`, its `𝔽₂`-linearity, the counting identity `hmB`, and the *easy* direction of `hobs` (a lift
to `Y` kills the obstruction) are all discharged here; the (136) display of Prop 8.9 then follows
from `stageR136_ofObstruction` once the two remaining classical facts are supplied as hypotheses:

* `hsep` — the **hard separation** (the ⟹ of `hobs`): a `B`-stage boundary lift whose obstruction
  functional vanishes lifts all the way to `Y`.  Classically this uses `R`-elementary-abelianness
  (`lemma_7_2`), the Frattini surjectivity `eq_top_of_map_frattini_quotient_top`, and the pushout
  link between the scalar covers and the single radical extension `Y ↠ B`.
* `hfib` — the **`z_R` torsor count**: every liftable fibre of `RF.liftB` has size `z_R`, the
  twisted-`Z¹(Γ,R)`-torsor count `#Z¹(Γ,R) = z_R` (the 5.15/5.16 numeric; B6/B7 enter here).

So the whole (136) numeric is reduced to exactly `hsep` + `hfib`, with the entire obstruction-theory
machinery in between discharged. -/
theorem stageR136_ofRObstructionData (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hsep : ∀ g : BoundaryLifts b F RF.TB,
      obs RF D htriv hcard g.1.1 = 0 → ∃ f : BoundaryLifts b F T, RF.liftB b F f = g)
    (hfib : ∀ g : BoundaryLifts b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
  refine stageR136_ofObstruction RF hfg b F D.DRmod D.toDR D.h0
    (fun g => obs RF D htriv hcard g.1.1) ?_ ?_ hfib
  · -- `hmB` — the obstruction-count identity, proved above
    exact hmB_holds RF D htriv hcard b F
  · -- `hobs` — the liftability biconditional
    intro g
    refine ⟨hsep g, ?_⟩
    -- ⟸ : a lift to `Y` kills the obstruction (compose the `Y`-lift with every scalar cover)
    rintro ⟨f, hf⟩
    show obs RF D htriv hcard g.1.1 = 0
    refine LinearMap.ext fun d => ?_
    rw [LinearMap.zero_apply]
    by_cases h : D.toDR d = RF.zeroDR
    · -- `d = 0`: the functional is linear, so it vanishes at `0`
      have hd : d = 0 := by rw [← D.toDR.symm_apply_apply d, h, D.h0]
      rw [hd]; exact map_zero _
    · -- `d ≠ 0`: `g` lifts through the `λ`-cover because it lifts to `Y`
      rw [obs_zero_iff_lifts RF D htriv hcard g.1.1 d h]
      obtain ⟨gc, hgc⟩ :=
        RCoverData.lifts_scalarCover_of_liftB D.toRCoverData b F (D.toDR d) h f
      exact ⟨gc, fun γ => by rw [hgc γ, hf]⟩

end Cohomology

end Obstruction

/-! ## Step 4 — `hfib`: the `R`-stage `liftB`-fibre is a `Z¹(Γ, R)`-torsor

The fibre of `RF.liftB` over a `B`-stage lift `g` is `{f : Γ ↠ Y // π_B ∘ f = g}` (framing is
automatic, `TB_head`/`TB_theta`).  Two such lifts `f, f₀` differ by `c γ := f γ · (f₀ γ)⁻¹ ∈ R`
(`ker π_B = R`), a **crossed 1-cocycle** for the `f₀`-conjugation action of `Γ` on `R`; conversely
each cocycle twists `f₀` to another fibre element (a homomorphism by the cocycle law, surjective by
the Frattini argument `eq_top_of_map_frattini_quotient_top`, framed because `R ≤ ker(π_Y, θ_Y)`).
So the fibre is a `Z¹(Γ, R)`-torsor; `#Z¹(Γ, R) = z_R` is the source numeric (5.15/5.16, d6). -/

section RFibre

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable (RF : RecursionFrame T Blk)

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `R = Φ(K) ≤ K ≤ P ≤ L_Y = ker π_Y`: `R`-twists preserve the head framing. -/
theorem R_le_ker_piY : Blk.frattiniK ≤ T.piY.ker := by
  rw [T.ker_piY]
  exact (frattiniLike_le Blk.K).trans (Blk.hKP.trans Blk.hPL)

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `R = Φ(K) ≤ ker θ_Y` when `E` is elementary-2 (`lemma_7_3`): `R`-twists preserve the scalar
framing.  This is exactly the `thm_4_2` decoration hypothesis (harmless downstream: §10 uses
`E = 0`), and the one point flagged in `docs/orchestration/p16d2-plan.md` for the fibre count. -/
theorem R_le_ker_thetaY (hE2 : ∀ e : E, e ^ 2 = 1) : Blk.frattiniK ≤ T.thetaY.ker :=
  (frattiniLike_le Blk.K).trans (lemma_7_3 Blk hE2 T.thetaY)

/-- **The R-stage torsor group** `Z¹_{Γ,ρ}(R)`: continuous crossed 1-cocycles `Γ → R = ker π_B`
for the `f₀`-conjugation action of `Γ` on `R`, `f₀` a fixed reference `Y`-lift.  (Multiplicative
crossed-hom convention, as `GQ2.SectionEight.TCocycle`; the fibre of `liftB` over a liftable `g`
is a torsor under this group with basepoint `f₀`.) -/
structure RCocycle (RF : RecursionFrame T Blk) (f₀ : ContinuousMonoidHom Γ Y) where
  /-- The cocycle map. -/
  u : Γ → Y
  /-- Values lie in the radical `R = ker π_B`. -/
  mem : ∀ γ, u γ ∈ Blk.frattiniK
  /-- Continuity. -/
  cont : Continuous u
  /-- The twisted (crossed) cocycle law `u(γδ) = u γ · (f₀ γ · u δ · f₀ γ⁻¹)`. -/
  crossed : ∀ γ δ, u (γ * δ) = u γ * (f₀ γ * u δ * (f₀ γ)⁻¹)

namespace RCocycle

variable {RF} {f₀ : ContinuousMonoidHom Γ Y}

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [DiscreteTopology Y] in
/-- Extensionality: only the underlying map matters. -/
theorem ext {c c' : RCocycle RF f₀} (h : c.u = c'.u) : c = c' := by
  cases c; cases c'; subst h; rfl

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [DiscreteTopology Y] in
/-- Cocycles are normalized: `u 1 = 1` (from `crossed` at `(1,1)`, `f₀ 1 = 1`). -/
theorem u_one (c : RCocycle RF f₀) : c.u 1 = 1 := by
  have h := c.crossed 1 1
  rw [mul_one, map_one, one_mul, inv_one, mul_one] at h
  -- `h : c.u 1 = c.u 1 * c.u 1`; cancel on the left
  exact left_eq_mul.mp h

/-- The reference lift `f₀` twisted by a cocycle `c`: `(c ⋆ f₀) γ = c.u γ · f₀ γ`, a continuous
homomorphism `Γ → Y` (homomorphism by `crossed`, continuous since `Y` is discrete). -/
def twistHom (c : RCocycle RF f₀) : ContinuousMonoidHom Γ Y :=
  ⟨{ toFun := fun γ => c.u γ * f₀ γ
     map_one' := by rw [u_one, map_one, one_mul]
     map_mul' := fun γ δ => by
       show c.u (γ * δ) * f₀ (γ * δ) = c.u γ * f₀ γ * (c.u δ * f₀ δ)
       rw [c.crossed γ δ, map_mul]; group },
   c.cont.mul f₀.continuous_toFun⟩

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] in
@[simp] private theorem twistHom_apply (c : RCocycle RF f₀) (γ : Γ) : c.twistHom γ = c.u γ * f₀ γ := rfl

end RCocycle

variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `π_B` kills the radical: `r ∈ R = ker π_B ⟹ π_B r = 1`. -/
theorem piB_eq_one_of_mem_R {r : Y} (hr : r ∈ Blk.frattiniK) : RF.piB r = 1 := by
  rw [← MonoidHom.mem_ker, RF.ker_piB]; exact hr

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [DiscreteTopology Y] in
/-- **Frattini surjectivity** (`eq_top_of_map_frattini_quotient_top`, `R = Φ(K)`, `K` a 2-group):
a continuous hom `φ : Γ → Y` whose `π_B`-composite is onto `B` is itself onto `Y`. -/
theorem surj_of_piB_surj {φ : ContinuousMonoidHom Γ Y}
    (hφ : Function.Surjective (fun γ => RF.piB (φ γ))) : Function.Surjective φ := by
  have h2K : IsPGroup 2 ↥Blk.K := Blk.h2L.to_le (le_trans Blk.hKP Blk.hPL)
  haveI : (frattiniLike Blk.K).Normal := frattiniLike_normal Blk.K Blk.hK
  have hJtop : Subgroup.map RF.piB φ.toMonoidHom.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨γ, hγ⟩ := hφ y
    exact ⟨φ γ, ⟨γ, rfl⟩, hγ⟩
  have hrange : φ.toMonoidHom.range = ⊤ :=
    eq_top_of_map_frattini_quotient_top RF.piB h2K RF.ker_piB (frattiniLike_le Blk.K) hJtop
  exact MonoidHom.range_eq_top.mp hrange

/-- **The R-stage fibre torsor** (`hfib` core): fixing a lift `f₀` of `g`, the fibre of `RF.liftB`
over `g` is a torsor under `RCocycle RF f₀.1.1` — every `Y`-lift of `g` is a unique cocycle-twist
of `f₀`.  The forward map lands in `BoundaryLifts` by Frattini surjectivity (`surj_of_piB_surj`)
and `R ≤ ker(π_Y, θ_Y)` framing (needs `hE2`); the backward map reads off the `R`-valued
difference `f · f₀⁻¹`. -/
noncomputable def fibreCocycleEquiv (hE2 : ∀ e : E, e ^ 2 = 1)
    (g : BoundaryLifts b F RF.TB) (f₀ : BoundaryLifts b F T) (hf₀ : RF.liftB b F f₀ = g) :
    RCocycle RF f₀.1.1 ≃ {f : BoundaryLifts b F T // RF.liftB b F f = g} where
  toFun c :=
    ⟨⟨⟨c.twistHom, by
        apply surj_of_piB_surj RF
        have hfun : (fun γ => RF.piB (c.twistHom γ)) = fun γ => g.1.1 γ := by
          funext γ
          rw [RCocycle.twistHom_apply, map_mul, piB_eq_one_of_mem_R RF (c.mem γ), one_mul]
          exact congrArg (fun z : BoundaryLifts b F RF.TB => z.1.1 γ) hf₀
        rw [hfun]; exact g.1.2⟩,
      by
        intro γ
        have hpi : T.piY (c.twistHom γ) = T.piY (f₀.1.1 γ) := by
          rw [RCocycle.twistHom_apply, map_mul, MonoidHom.mem_ker.mp (R_le_ker_piY (c.mem γ)),
            one_mul]
        have hth : T.thetaY (c.twistHom γ) = T.thetaY (f₀.1.1 γ) := by
          rw [RCocycle.twistHom_apply, map_mul,
            MonoidHom.mem_ker.mp (R_le_ker_thetaY hE2 (c.mem γ)), one_mul]
        rw [hpi, hth]; exact f₀.2 γ⟩,
    by
      apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
      intro γ
      show RF.piB (c.twistHom γ) = g.1.1 γ
      rw [RCocycle.twistHom_apply, map_mul, piB_eq_one_of_mem_R RF (c.mem γ), one_mul]
      exact congrArg (fun z : BoundaryLifts b F RF.TB => z.1.1 γ) hf₀⟩
  invFun f :=
    { u := fun γ => f.1.1.1 γ * (f₀.1.1 γ)⁻¹
      mem := by
        intro γ
        have hf2 : RF.piB (f.1.1.1 γ) = g.1.1 γ :=
          congrArg (fun z : BoundaryLifts b F RF.TB => z.1.1 γ) f.2
        have hf0' : RF.piB (f₀.1.1 γ) = g.1.1 γ :=
          congrArg (fun z : BoundaryLifts b F RF.TB => z.1.1 γ) hf₀
        rw [← RF.ker_piB, MonoidHom.mem_ker, map_mul, map_inv, hf2, hf0', mul_inv_cancel]
      cont := f.1.1.1.continuous_toFun.mul f₀.1.1.continuous_toFun.inv
      crossed := by
        intro γ δ
        show f.1.1.1 (γ * δ) * (f₀.1.1 (γ * δ))⁻¹
          = f.1.1.1 γ * (f₀.1.1 γ)⁻¹ *
              (f₀.1.1 γ * (f.1.1.1 δ * (f₀.1.1 δ)⁻¹) * (f₀.1.1 γ)⁻¹)
        rw [map_mul, map_mul]; group }
  left_inv c := by
    apply RCocycle.ext
    funext γ
    show c.twistHom γ * (f₀.1.1 γ)⁻¹ = c.u γ
    rw [RCocycle.twistHom_apply]; group
  right_inv f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
    intro γ
    show f.1.1.1 γ * (f₀.1.1 γ)⁻¹ * f₀.1.1 γ = f.1.1.1 γ
    group

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **`hfib`** (step 4 payoff): the `liftB`-fibre over a liftable `g` has size `z_R`, reduced to the
source `Z¹`-count `#RCocycle = z_R` (the 5.15/5.16 numeric + `card_DR`, supplied by d6).  The
abstract torsor identification is `fibreCocycleEquiv`. -/
theorem hfib_holds (hE2 : ∀ e : E, e ^ 2 = 1)
    (g : BoundaryLifts b F RF.TB) (f₀ : BoundaryLifts b F T) (hf₀ : RF.liftB b F f₀ = g)
    (hcount : Nat.card (RCocycle RF f₀.1.1) = RF.zR) :
    Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} = RF.zR := by
  rw [← Nat.card_congr (fibreCocycleEquiv RF b F hE2 g f₀ hf₀), hcount]

/-! ### `hsep` wrapper: a bare homomorphism lift upgrades to a fibre element -/
omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **Frattini/framing wrapper for `hsep`**: a bare homomorphism lift `φ : Γ → Y` of `g`
(`π_B ∘ φ = g`) already lands in the `liftB`-fibre — it is surjective by `surj_of_piB_surj`
(Frattini) and boundary-framed because the framing factors through `π_B` (`TB_head`/`TB_theta`).
So `hsep` reduces to producing *any* homomorphism lift of `g` to `Y`; that existence is the
separation core (`obs g = 0 ⟹ the radical obstruction dies ⟹ `g` lifts to `Y`). -/
theorem liftB_fibre_nonempty_of_homLift
    (g : BoundaryLifts b F RF.TB) (φ : ContinuousMonoidHom Γ Y)
    (hφ : ∀ γ, RF.piB (φ γ) = g.1.1 γ) :
    ∃ f : BoundaryLifts b F T, RF.liftB b F f = g := by
  refine ⟨⟨⟨φ, surj_of_piB_surj RF (by rw [funext hφ]; exact g.1.2)⟩, ?_⟩, ?_⟩
  · intro γ
    have h1 : T.piY (φ γ) = RF.TB.piY (g.1.1 γ) := by
      rw [← RF.TB_head, MonoidHom.comp_apply, hφ γ]
    have h2 : T.thetaY (φ γ) = RF.TB.thetaY (g.1.1 γ) := by
      rw [← RF.TB_theta, MonoidHom.comp_apply, hφ γ]
    rw [h1, h2]; exact g.2 γ
  · apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
    intro γ; exact hφ γ

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] in
/-- **Constructive coboundary → hom lift** (`hsep` interior): a continuous `R`-valued cochain `c`
splitting the section defect `rDefect` (the twisted-coboundary equation) assembles the set-section
`slift ∘ g` into a genuine continuous homomorphism `φ γ = c γ · slift(g γ)` lifting `g`.  This is
the abstractly-provable half of the separation: it turns "`[rDefect] = 0 ∈ H²(Γ,R)`" (a splitting
cochain) into the hom lift that `liftB_fibre_nonempty_of_homLift` then upgrades to a fibre element.
(`slift` is continuous because `B = Y/R` is discrete, so `φ` is genuinely continuous.) -/
theorem homLift_of_split (g : ContinuousMonoidHom Γ RF.YB)
    (c : Γ → ↥Blk.frattiniK) (hc : Continuous fun γ => ((c γ : Y)))
    (hsplit : ∀ γ δ, (c (γ * δ) : Y)
        = (c γ : Y) * (slift RF (g γ) * (c δ : Y) * (slift RF (g γ))⁻¹) * (rDefect RF g γ δ : Y)) :
    ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g γ := by
  have hscont : Continuous fun γ => slift RF (g γ) :=
    (continuous_of_discreteTopology (f := slift RF)).comp g.continuous_toFun
  refine ⟨⟨MonoidHom.mk' (fun γ => (c γ : Y) * slift RF (g γ)) (fun γ δ => ?_),
      hc.mul hscont⟩, fun γ => ?_⟩
  · -- homomorphism: the split equation collapses the defect
    have hrd : (rDefect RF g γ δ : Y)
        = slift RF (g γ) * slift RF (g δ) * (slift RF (g (γ * δ)))⁻¹ := rfl
    show (c (γ * δ) : Y) * slift RF (g (γ * δ))
      = (c γ : Y) * slift RF (g γ) * ((c δ : Y) * slift RF (g δ))
    rw [hsplit, hrd]; group
  · -- lifts `g`: `π_B` kills `c γ ∈ R` and `π_B (slift (g γ)) = g γ`
    show RF.piB ((c γ : Y) * slift RF (g γ)) = g γ
    rw [map_mul, piB_eq_one_of_mem_R RF (c γ).2, one_mul, piB_slift]

section Assemble

open ContCoh CentralObstruction

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136), fully discharged modulo the two irreducible concrete inputs** (`hsep_hom` + `hZcount`).
Every abstractly-provable ingredient is proven here — the obstruction map, `hmB`, the easy `hobs`,
the `hfib` fibre-torsor, and `hsep`'s Frattini/framing wrapper — so a caller (the concrete
`𝒴`-frame, the Prop. 8.9 assembly) supplies only:

* `hsep_hom` — the **radical-obstruction separation**: `obs g = 0 ⟹ g` has a homomorphism lift to
  `Y`.  (Not provable in the bare abstract frame — it is the `(R^∨)^C`-detection of `H²(Γ,R)`, a
  property of the concrete `R` + `C`-action.  d6 discharges it, optionally via `homLift_of_split`.)
* `hZcount` — the **source `Z¹`-count** `#RCocycle = z_R` (5.15/5.16 numeric + `card_DR`).

and `hE2` (`E` elementary-2, the `thm_4_2` decoration hypothesis).  This is the finish line of the
abstract R-stage obstruction module: (136) reduced to exactly the source-arithmetic residues. -/
theorem stageR136_ofRSepData (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hsep_hom : ∀ g : BoundaryLifts b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLifts b F T, Nat.card (RCocycle RF f₀.1.1) = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
  refine stageR136_ofRObstructionData RF D htriv hcard hfg b F ?_ ?_
  · -- `hsep`: separation hom lift, upgraded to a fibre element by the wrapper
    intro g hg
    obtain ⟨φ, hφ⟩ := hsep_hom g hg
    exact liftB_fibre_nonempty_of_homLift RF b F g φ hφ
  · -- `hfib`: same lift as basepoint, then the fibre-torsor count
    intro g hg
    obtain ⟨φ, hφ⟩ := hsep_hom g hg
    obtain ⟨f₀, hf₀⟩ := liftB_fibre_nonempty_of_homLift RF b F g φ hφ
    exact hfib_holds RF b F hE2 g f₀ hf₀ (hZcount f₀)

end Assemble

end RFibre

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 8.9 = ⟦thm-closedrecursion⟧ (= theorem 8.17 in current tex)
-/
