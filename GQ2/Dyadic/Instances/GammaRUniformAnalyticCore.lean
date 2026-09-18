/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformExactLifting
import GQ2.Dyadic.Instances.SourceBoundaryReplacementRN

/-!
# The analytic core of an arbitrary uniformly Stokes word

All corrected analytic certificates are supplied by the same finite-target Stokes interface.
The affine determinant is intentionally not included: it remains boundary and phase dependent.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.RowActionImage
attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

section Frames
variable (S : UniformStokesSupply n q R wOf)
  {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
  {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
  [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
  {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
  (b : ContinuousMonoidHom ((GammaR n q R) : Type) ↥(boundarySubgroupQ q nuP))
  (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR) (hl : l ≠ RF.zeroDR)

include S

/-- The T-cocycle clause is independent of the form of the branch word. -/
theorem tcocycle (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      (standardNumerics n).tMult (Nat.card (Additive ↥(En.radData l hl).T)) *
        Nat.card (fixedPts (RF.YB ⧸ (En.radData l hl).M)
          (ElemDual (Additive ↥(En.radData l hl).T))) := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI : TopologicalSpace (Additive ↥D.T) := ⊥
  letI : DiscreteTopology (Additive ↥D.T) := ⟨rfl⟩
  letI : DistribMulAction ((GammaR n q R) : Type) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : ContinuousSMul ((GammaR n q R) : Type) (Additive ↥D.T) :=
    continuousSMul_of_comp_finite rho (fun _ _ ↦ rfl)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  exact tcocycle_cardN rho (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R) (S.resolvesWord (radT_add_self D))
    (radT_add_self D)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ ↦ rfl))
    (rhoPrimeK_surjective RF b F D rfl ρ) degree
    (S.stokes _ rho _ (radT_add_self D)) (S.endpoint _)

/-- Vanishing of all invariant-character obstructions supplies a T-lift. -/
theorem hsep (Dsc : Descent (En.radData l hl)) (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((GammaR n q R) : Type)
      ∀ chi : ↥(TCharC (En.radData l hl)),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l hl Dsc) c := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((GammaR n q R) : Type)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  exact hsep_field_goal_marking b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR n q R) (fun _ ↦ rfl)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ ↦ rfl))
    (S.resolvesWord (by decide : ∀ a : ZMod 2, a + a = 0))
    (S.resolvesWord (radT_add_self D)) (S.stokes _ rho _ (radT_add_self D))
    (S.endpoint _) c hvan

/-- The descent module has right-separating continuous cohomology. -/
theorem hrsep (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((GammaR n q R) : Type)
    letI : TopologicalSpace (En.descData l hl).Vmod := ⊥
    letI : DiscreteTopology (En.descData l hl).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((GammaR n q R) : Type) (En.descData l hl).Vmod :=
      DistribMulAction.compHom (En.descData l hl).Vmod
        (rho0 (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l hl).Vmod) := ⊥
    letI : DiscreteTopology (ElemDual (En.descData l hl).Vmod) := ⟨rfl⟩
    IsRightSeparating ((GammaR n q R) : Type) (En.descData l hl).Vmod := by
  let D := En.radData l hl
  let DD := En.descData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((GammaR n q R) : Type)
  letI := scalarActionZmodTwo_continuousSMul ((GammaR n q R) : Type)
  letI : TopologicalSpace DD.Vmod := ⊥
  letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((GammaR n q R) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rho)
  letI : TopologicalSpace (ElemDual DD.Vmod) := ⊥
  letI : DiscreteTopology (ElemDual DD.Vmod) := ⟨rfl⟩
  letI : TopologicalSpace DD.C0 := ⊥
  letI : DiscreteTopology DD.C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo DD.C0
  let theta := Count.rho0Continuous DD rho
  have hcompat : ∀ (g : ((GammaR n q R) : Type)) (a : DD.Vmod), g • a = theta g • a :=
    fun _ _ ↦ rfl
  letI : ContinuousSMul ((GammaR n q R) : Type) (ElemDual DD.Vmod) :=
    continuousSMul_of_comp_finite theta (elemDual_compat theta hcompat)
  have hsurj : Function.Surjective theta :=
    LSquare.rho0Continuous_surjective DD rho (rhoPrimeK_surjective RF b F D rfl ρ)
  have hwild := isWildTwo_of_gammaGen theta hsurj (fun _ ↦ rfl)
  have hd := S.stokes DD.C0 theta DD.Vmod (Vmod_exp2 DD)
  have hresP := S.resolvesWord (C := DD.C0) (Vmod_exp2 DD)
  have hsd : IsSelfDualN n (fun g ↦ theta (gammaGen n q R g))
      (wOf (4 * Monoid.exponent DD.C0)) DD.Vmod :=
    isSelfDualN_of_stokesDuality degree hd
      (lower_rel theta (fun _ ↦ rfl) (isAdmissibleMarkedPresentation_gammaR n q R) hresP)
      (S.endpoint _)
  exact isRightSeparating_of_selfDualN theta hcompat (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R) hwild
    (S.resolvesWord (by decide : ∀ a : ZMod 2, a + a = 0)) hresP
    (S.resolvesWord (fun lam : ElemDual DD.Vmod ↦ lam.add_self_eq_zero))
    (S.level.heis (Vmod_exp2 DD)) hsd (S.endpoint _) (Vmod_exp2 DD)

/-- A nonzero character gives a genuinely varying obstruction. -/
theorem hpartial (hspec : TameSpec.TameSpecializes n q R)
    (Dsc : Descent (En.radData l hl)) (ρ : BoundaryLiftsK b F RF.TC)
    (chi : ↥(TCharC (En.radData l hl))) (hchi : chi ≠ 0) :
    letI := scalarActionZmodTwo ((GammaR n q R) : Type)
    ∃ c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
      betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c ≠
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi
          (0 : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) :=
  hpartial_field_goal b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (S.cardH2 hspec) (S.hrsep b F En l hl ρ) chi hchi

/-- The simple nontrivial descent cocycle count depends only on n. -/
theorem hZcard
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      Nat.card En.Vmod * (standardNumerics n).h1Mult (Nat.card En.Vmod) := by
  let DD := En.descData l hl
  letI : TopologicalSpace DD.Vmod := ⊥
  letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC DD.Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction ((GammaR n q R) : Type) DD.Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  letI : ContinuousSMul ((GammaR n q R) : Type) DD.Vmod :=
    continuousSMul_of_comp_finite ρ.1.1 (fun _ _ ↦ rfl)
  letI := scalarActionZmodTwo RF.YC
  have hsimple' : IsSimpleModTwo RF.YC DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact hZcardN ρ.1.1
    (fun g v ↦ congrArg (fun c : RF.YC ↦ c • v) (rho0_descData_rhoPrimeK b F En l hl ρ g))
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R) (S.resolvesWord (Vmod_exp2 DD))
    (Vmod_exp2 DD) (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ ↦ rfl)) ρ.1.2
    degree (S.stokes RF.YC ρ.1.1 DD.Vmod (Vmod_exp2 DD)) (S.endpoint _) hsimple' hnt

end Frames

/-- The complete corrected Stokes certificate at an arbitrary intrinsic word. -/
theorem stokesCertificate (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (GammaR n q R) n q P nuP (standardNumerics n)
      (scalarActionZmodTwo ((GammaR n q R) : Type)) :=
  ⟨fun b F En l hl ρ ↦ S.tcocycle b F En l hl ρ,
   fun b F En l hl Dsc ρ c hvan ↦ S.hsep b F En l hl Dsc ρ c hvan,
   fun b F En l hl Dsc ρ chi hchi ↦ S.hpartial b F En l hl hspec Dsc ρ chi hchi,
   fun b F En l hl hsimple hVne hnt ρ ↦ S.hZcard b F En l hl hsimple hVne hnt ρ⟩

/-- All boundary-independent corrected clauses, with no word-specific analytic residue. -/
def analyticCore (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R)
    (P : ProfiniteGrp) (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) :
    Instances.SourceBoundaryReplacementRN.SourceAnalyticCoreRN n q P hP nuP
      (standardNumerics n) where
  Γ := GammaR n q R
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  exactLifting := S.exactLiftingRN hspec nuP
  stokes := S.stokesCertificate hspec
  scalar := S.scalar hspec

/-- Once the boundary-dependent affine determinant is known, all flexible certificate leaves
are supplied by the normalized core and the uniform Stokes theorem. -/
def certificateLeaves (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : Instances.FieldFamilyFlexibleCertificate.FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q)
    (hdet : AffineDeterminantCertificate (GammaR n q R) n q P nuP (standardNumerics n)
      (TameSpec.tameOfSpec n q R hspec) (C.pro2 hq0 hqe) (C.compat hq0 hqe hspec)
      (scalarActionZmodTwo _)) :
    Instances.FieldFamilyFlexibleCertificate.FlexibleCertificateLeavesRN n q R P hP nuP
      (standardNumerics n) hq0 hqe where
  tameSpecialization := hspec
  core := C
  exactLifting := S.exactLiftingRN hspec nuP
  stokes := S.stokesCertificate hspec
  scalar := S.scalar hspec
  determinant := hdet

#print axioms tcocycle
#print axioms hsep
#print axioms hrsep
#print axioms hpartial
#print axioms hZcard
#print axioms stokesCertificate
#print axioms analyticCore
#print axioms certificateLeaves

end
end GQ2.Dyadic.UniformStokesSupply
