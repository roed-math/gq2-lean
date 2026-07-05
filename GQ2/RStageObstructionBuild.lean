import GQ2.RStageObstruction
import GQ2.CentralObstruction

/-!
# §8 R-stage obstruction module — Option-A construction  (P-16d2)

Builds the obstruction datum `obs`/`hmB`/`hobs`/`hfib` consumed by
`GQ2.SectionEight.stageR136_ofObstruction` (`GQ2/RStageObstruction.lean`), from the **Option-A
compatibility structure** `RCoverData` (user-approved 2026-07-05): the datum, absent from the bare
`RecursionFrame` + `Enrichment`, that each scalar cover `p_λ = (scalarCover l).p` really is a
quotient of the single radical extension `Y ↠ B = Y/R` — a hom family
`coverMap_λ : Y →* (scalarCover l).cover` with `p_λ ∘ coverMap_λ = π_B`.

Kept self-contained here (own file, no edit to the co-owned `Enrichment`); a later refactor may
fold `RCoverData` into `Enrichment` as a field.  See `docs/p16d2-plan.md` for the full route.

Build status (see the per-lemma notes): the compatibility structure and the "lifts to `Y` ⟹ lifts
through every `p_λ`" direction are std-3; the obstruction-linearity, the hard separation, and the
`z_R` torsor count are the remaining cores (each needs the twisted-cocycle layer for the
`R`-extension — tracked).
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
    have hx1 : C.p x = 1 := Subgroup.mem_bot.mp hx
    rw [show ((0 : ZMod 2)).val = 0 from rfl, pow_zero]
    exact C.sq_eq_one_of_mem_ker (MonoidHom.mem_ker.mpr hx1)
  hrad := fun t ht m hm => by simp [polarMul]
  hTzero := fun t ht => rfl

@[simp] theorem trivialRCD_C {Bg : Type} [Group Bg] [Finite Bg] (C : CentralCover Bg) :
    (trivialRCD C).C = C := rfl

@[simp] theorem trivialRCD_M {Bg : Type} [Group Bg] [Finite Bg] (C : CentralCover Bg) :
    (trivialRCD C).M = ⊥ := rfl

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

/-- **Option-A compatibility datum (P-16d2)**: the missing link between the frame's abstract scalar
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
what the concrete `𝒴`-frame (P-16d5/d6) supplies; from it the obstruction map, its linearity, and
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
  /-- The `D_R ≃ (R^∨)^C` pairing: `pair d` is a `𝔽₂`-functional on the radical `R = Blk.R`,
  linear in `d`. -/
  pair : DRmod →ₗ[ZMod 2] (Additive ↥Blk.R →+ ZMod 2)
  /-- The pairing is `zsign ∘ coverMap_λ` on `R` (`λ = toDR d ≠ 0`): the scalar character `d`
  reads off the `λ`-cover's kernel sign of a radical element. -/
  pair_coverMap : ∀ (d : DRmod) (h : toDR d ≠ RF.zeroDR) (r : ↥Blk.R),
    pair d (Additive.ofMul r)
      = zsign (trivialRCD (RF.scalarCover (toDR d) h))
          (coverMap (toDR d) h (r : Y))

attribute [instance] RObstructionData.addCommGroup RObstructionData.moduleZMod
  RObstructionData.finiteDRmod

variable (RF : RecursionFrame T Blk)

/-- A set-theoretic section of `π_B : Y ↠ B`. -/
noncomputable def slift (x : RF.YB) : Y := Function.surjInv RF.piB_surj x

@[simp] theorem piB_slift (x : RF.YB) : RF.piB (slift RF x) = x :=
  Function.surjInv_eq RF.piB_surj x

/-- **The `R`-valued section defect** of a `B`-stage map `g : Γ → B` for the single set-lift
`slift`: `Obs^s_g(γ,δ) = s(gγ)·s(gδ)·s(g(γδ))⁻¹ ∈ R = ker π_B`. -/
noncomputable def rDefect (g : ContinuousMonoidHom Γ RF.YB) (γ δ : Γ) : ↥Blk.R :=
  ⟨slift RF (g γ) * slift RF (g δ) * (slift RF (g (γ * δ)))⁻¹, by
    rw [← RF.ker_piB, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      piB_slift, piB_slift, piB_slift, map_mul]
    group⟩

section Cohomology

open ContCoh CentralObstruction

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- The lift family of `g` into the `λ`-cover built from the single set-section: `x ↦
coverMap_λ (slift (g x))`. -/
noncomputable def obsLiftFam (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) : Γ → (RF.scalarCover (D.toDR d) h).cover :=
  fun x => D.coverMap (D.toDR d) h (slift RF (g x))

theorem obsLiftFam_p (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) (x : Γ) :
    (RF.scalarCover (D.toDR d) h).p (obsLiftFam RF D g d h x) = g x := by
  show (RF.scalarCover (D.toDR d) h).p (D.coverMap (D.toDR d) h (slift RF (g x))) = g x
  rw [← MonoidHom.comp_apply, D.coverMap_lifts (D.toDR d) h, piB_slift]

theorem obsLiftFam_cont (D : RObstructionData RF) (g : ContinuousMonoidHom Γ RF.YB)
    (d : D.DRmod) (h : D.toDR d ≠ RF.zeroDR) : Continuous (obsLiftFam RF D g d h) := by
  have he : obsLiftFam RF D g d h
      = (fun y => D.coverMap (D.toDR d) h (slift RF y)) ∘ (g : Γ → RF.YB) := rfl
  rw [he]
  exact continuous_of_discreteTopology.comp (map_continuous g)

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
        (D.coverMap (D.toDR d) h ((rDefect RF g γ δ : ↥Blk.R) : Y))
  congr 1
  simp only [obsLiftFam]
  rw [show ((rDefect RF g γ δ : ↥Blk.R) : Y)
        = slift RF (g γ) * slift RF (g δ) * (slift RF (g (γ * δ)))⁻¹ from rfl]
  simp only [map_mul, map_inv]

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
  apply congrArg
  apply Subtype.ext
  funext gd
  exact obCocOf_obsLiftFam RF D g d h gd.1 gd.2

end Cohomology

end Obstruction

end SectionEight

end GQ2
