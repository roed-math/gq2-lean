/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Compare
import GQ2.Dyadic.Count.Separation

/-!
# Local-duality suppliers for the dyadic Stokes counts

This file joins two already-landed generic layers:

* `tcocycleEquivZ1` / `vcocycleEquivZ1`, which put the recursion's cocycles in continuous
  cohomology; and
* `LiftingDualityG.card_Z1_eqG`, which evaluates that cohomology from a
  `TateDualityG` bundle and a degree-`d` local Euler characteristic.

The resulting exponents are `d + 1`.  In particular, none of the statements below imports the
degree-one `#Z¹ = #A² · #fixedPts` formula from the `G_ℚ₂` source.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction GQ2.SectionEight.AffineTLift
open GQ2.SectionEight.RadicalEdgeGammaA
open LiftingDualityG

section TCocycle

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}
  {Gam : Type} [Group Gam] [TopologicalSpace Gam] [IsTopologicalGroup Gam]
  [DistribMulAction Gam (MuN 2)] [ContinuousSMul Gam (MuN 2)]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Gam (Additive ↥D.T)] [ContinuousSMul Gam (Additive ↥D.T)]

/-- The local-duality count of crossed `T`-cocycles.  Surjectivity is essential: it is what
identifies `Gam`-invariants with invariants under the displayed finite quotient. -/
theorem tcocycle_card_of_localDualityG {d : ℕ}
    (Dl : TateDualityG Gam 2) (hE : LocalEulerChar Gam d)
    (rho : ContinuousMonoidHom Gam (Bg ⧸ D.M)) (hrho : Function.Surjective rho)
    (hcomp : ∀ (gam : Gam) (a : Additive ↥D.T), gam • a = rho gam • a) :
    Nat.card (TCocycle D rho) =
      Nat.card (Additive ↥D.T) ^ (d + 1) *
        Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :=
  (Nat.card_congr (tcocycleEquivZ1 rho hcomp)).trans
    (card_Z1_eqG hrho hcomp Dl hE (radT_add_self D))

/-- `tcocycle_card_of_localDualityG` in the exact `SourceDataN.tcocycle_card` numeric shape. -/
theorem tcocycle_card_standard_of_localDualityG {d : ℕ}
    (Dl : TateDualityG Gam 2) (hE : LocalEulerChar Gam d)
    (rho : ContinuousMonoidHom Gam (Bg ⧸ D.M)) (hrho : Function.Surjective rho)
    (hcomp : ∀ (gam : Gam) (a : Additive ↥D.T), gam • a = rho gam • a) :
    Nat.card (TCocycle D rho) =
      (standardNumerics d).tMult (Nat.card (Additive ↥D.T)) *
        Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :=
  tcocycle_card_of_localDualityG Dl hE rho hrho hcomp

end TCocycle

section VCocycle

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Gam : Type} [Group Gam] [TopologicalSpace Gam] [IsTopologicalGroup Gam]
  [DistribMulAction Gam (MuN 2)] [ContinuousSMul Gam (MuN 2)]
  {E : Type} [Group E] [TopologicalSpace E]
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction E DD.Vmod] [DistribMulAction Gam DD.Vmod] [ContinuousSMul Gam DD.Vmod]
  {rho : ContinuousMonoidHom Gam (Bg ⧸ D.M)}

/-- The local-duality count of `V`-cocycles when the finite acting group acts nontrivially on a
simple mod-two module.  The fixed-point factor in `card_Z1_eqG` is then one. -/
theorem vcocycle_card_of_localDualityG {d : ℕ}
    (Dl : TateDualityG Gam 2) (hE : LocalEulerChar Gam d)
    (theta : ContinuousMonoidHom Gam E) (htheta : Function.Surjective theta)
    (hround : ∀ (gam : Gam) (v : DD.Vmod), rho0 DD rho gam • v = theta gam • v)
    (hact : ∀ (gam : Gam) (v : DD.Vmod), gam • v = theta gam • v)
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho) = Nat.card DD.Vmod ^ (d + 1) := by
  rw [Nat.card_congr (vcocycleEquivZ1 theta hround hact),
    card_Z1_eqG htheta hact Dl hE (Vmod_exp2 (DD := DD)),
    card_fixedPts_elemDual_eq_one_of_nontrivial hsimple hnt, mul_one]

/-- `vcocycle_card_of_localDualityG` in the exact `SourceDataN.hZcard` outer/inner shape. -/
theorem vcocycle_card_standard_of_localDualityG {d : ℕ}
    (Dl : TateDualityG Gam 2) (hE : LocalEulerChar Gam d)
    (theta : ContinuousMonoidHom Gam E) (htheta : Function.Surjective theta)
    (hround : ∀ (gam : Gam) (v : DD.Vmod), rho0 DD rho gam • v = theta gam • v)
    (hact : ∀ (gam : Gam) (v : DD.Vmod), gam • v = theta gam • v)
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho) =
      Nat.card DD.Vmod * (standardNumerics d).h1Mult (Nat.card DD.Vmod) := by
  rw [vcocycle_card_of_localDualityG Dl hE theta htheta hround hact hsimple hnt, pow_succ]
  exact Nat.mul_comm _ _

end VCocycle

/-! ## The two count fields in recursion vocabulary -/

private theorem continuousSMul_of_comp_discrete {G C A : Type}
    [Monoid G] [TopologicalSpace G] [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A] [SMul G A]
    (theta : ContinuousMonoidHom G C) (hcomp : ∀ (g : G) (a : A), g • a = theta g • a) :
    ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A => p.1 • p.2) =
      (fun p : C × A => p.1 • p.2) ∘ (fun p : G × A => (theta p.1, p.2)) := by
    funext p
    exact hcomp p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

private theorem elemDual_smul_eq_of_comp {G C A : Type} [Group G] [TopologicalSpace G]
    [Group C] [TopologicalSpace C] [AddCommGroup A]
    [DistribMulAction C A] [DistribMulAction G A]
    (theta : ContinuousMonoidHom G C)
    (hcomp : ∀ (g : G) (a : A), g • a = theta g • a)
    (g : G) (lam : ElemDual A) : g • lam = theta g • lam := by
  ext a
  rw [ElemDual.smul_apply, ElemDual.smul_apply]
  congr 1
  rw [hcomp, map_inv]

private theorem dualEval_equivariant_of_trivial {G A : Type} [Group G]
    [AddCommGroup A] [DistribMulAction G A] [DistribMulAction G (ZMod 2)]
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (g : G) (a : A) (lam : ElemDual A) :
    dualEval A (g • a) (g • lam) = g • dualEval A a lam := by
  rw [dualEval_apply, ElemDual.smul_apply, inv_smul_smul, dualEval_apply, htriv]

/-- The descent lower map, with the continuity already present in `rho` retained. -/
noncomputable def rho0Continuous {Bg : Type} [Group Bg] [TopologicalSpace Bg]
    [DiscreteTopology Bg] [Finite Bg] {D : RadicalCoverData Bg} (DD : DescData D)
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {G : Type} [Group G] [TopologicalSpace G] (rho : ContinuousMonoidHom G (Bg ⧸ D.M)) :
    ContinuousMonoidHom G DD.C0 :=
  ⟨rho0 DD rho,
    (continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => liftC0 DD x)).comp
      rho.continuous_toFun⟩

section FieldCounts

variable {Gam : ProfiniteGrp} {d q : ℕ} {P : ProfiniteGrp}
  {nuP : ContinuousMonoidHom P Ztwo}
  [DistribMulAction (Gam : Type) (MuN 2)] [ContinuousSMul (Gam : Type) (MuN 2)]

/-- The first `StokesDualityCertificate` field, in the recursion's exact vocabulary. -/
theorem tcocycle_field_of_localDualityG
    (Dl : TateDualityG (Gam : Type) 2) (hE : LocalEulerChar (Gam : Type) d)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (rho : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)) =
      (standardNumerics d).tMult (Nat.card (Additive ↥(En.radData l h).T)) *
        Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
          (ElemDual (Additive ↥(En.radData l h).T))) := by
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
  letI : DistribMulAction (Gam : Type) (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom _
      (rhoPrimeK RF b F (En.radData l h) rfl rho).toMonoidHom
  haveI : ContinuousSMul (Gam : Type) (Additive ↥(En.radData l h).T) :=
    continuousSMul_of_comp_discrete (rhoPrimeK RF b F (En.radData l h) rfl rho)
      (fun _ _ => rfl)
  exact tcocycle_card_standard_of_localDualityG Dl hE
    (rhoPrimeK RF b F (En.radData l h) rfl rho)
    (rhoPrimeK_surjective RF b F (En.radData l h) rfl rho) (fun _ _ => rfl)

/-- The fourth `StokesDualityCertificate` field, in the recursion's exact outer/inner numeric
shape. -/
theorem hZcard_field_of_localDualityG
    (Dl : TateDualityG (Gam : Type) 2) (hE : LocalEulerChar (Gam : Type) d)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (rho : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)) =
      Nat.card En.Vmod * (standardNumerics d).h1Mult (Nat.card En.Vmod) := by
  letI : TopologicalSpace (En.descData l h).Vmod := ⊥
  haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction (Gam : Type) (En.descData l h).Vmod :=
    DistribMulAction.compHom _ rho.1.1.toMonoidHom
  haveI : ContinuousSMul (Gam : Type) (En.descData l h).Vmod :=
    continuousSMul_of_comp_discrete rho.1.1 (fun _ _ => rfl)
  have hsimple' : IsSimpleModTwo RF.YC (En.descData l h).Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact vcocycle_card_standard_of_localDualityG Dl hE rho.1.1 rho.1.2
    (fun gam v => congrArg (fun g : RF.YC => g • v)
      (rho0_descData_rhoPrimeK b F En l h rho gam))
    (fun _ _ => rfl) hsimple' hnt

/-- The second `StokesDualityCertificate` field, supplied by Tate `(2,0)` separation. -/
theorem hsep_field_of_localDualityG
    (Dl : TateDualityG (Gam : Type) 2) (hE : LocalEulerChar (Gam : Type) d)
    (smulZ2 : DistribMulAction (Gam : Type) (ZMod 2))
    (_contZ2 : letI := smulZ2; ContinuousSMul (Gam : Type) (ZMod 2))
    (htriv : letI := smulZ2; ∀ (gam : (Gam : Type)) (m : ZMod 2), gam • m = m)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (rho : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho))
    (hc : letI := smulZ2
      ∀ chi : ↥(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l h Dsc) c := by
  letI := smulZ2
  haveI : ContinuousSMul (Gam : Type) (ZMod 2) := _contZ2
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
  letI : DistribMulAction (Gam : Type) (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom _
      (rhoPrimeK RF b F (En.radData l h) rfl rho).toMonoidHom
  haveI : ContinuousSMul (Gam : Type) (Additive ↥(En.radData l h).T) :=
    continuousSMul_of_comp_discrete (rhoPrimeK RF b F (En.radData l h) rfl rho)
      (fun _ _ => rfl)
  letI : TopologicalSpace (ElemDual (Additive ↥(En.radData l h).T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥(En.radData l h).T)) := ⟨rfl⟩
  have hcompD : ∀ (gam : (Gam : Type))
      (lam : ElemDual (Additive ↥(En.radData l h).T)),
      gam • lam = rhoPrimeK RF b F (En.radData l h) rfl rho gam • lam :=
    elemDual_smul_eq_of_comp (rhoPrimeK RF b F (En.radData l h) rfl rho)
      (fun _ _ => rfl)
  haveI : ContinuousSMul (Gam : Type) (ElemDual (Additive ↥(En.radData l h).T)) :=
    continuousSMul_of_comp_discrete (rhoPrimeK RF b F (En.radData l h) rfl rho) hcompD
  exact hsep_field_goal b F En l h Dsc rho smulZ2
    (isTwoSeparating_of_tateDualityG Dl hE (radT_add_self (En.radData l h)) htriv
      (dualEval_equivariant_of_trivial htriv)) c hc

/-- The third `StokesDualityCertificate` field, supplied by Tate `(1,1)` right separation and
the invariant-map count `#H²(Gam, 𝔽₂) = 2`. -/
theorem hpartial_field_of_localDualityG
    (Dl : TateDualityG (Gam : Type) 2)
    (smulZ2 : DistribMulAction (Gam : Type) (ZMod 2))
    (_contZ2 : letI := smulZ2; ContinuousSMul (Gam : Type) (ZMod 2))
    (htriv : letI := smulZ2; ∀ (gam : (Gam : Type)) (m : ZMod 2), gam • m = m)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (rho : BoundaryLiftsK b F RF.TC)
    (chi : ↥(TCharC (En.radData l h))) (hchi : chi ≠ 0) :
    letI := smulZ2
    ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi c ≠
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi
          (0 : VCocycle (En.descData l h)
            (rhoPrimeK RF b F (En.radData l h) rfl rho)) := by
  letI := smulZ2
  haveI : ContinuousSMul (Gam : Type) (ZMod 2) := _contZ2
  letI : TopologicalSpace (En.descData l h).Vmod := ⊥
  haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
  letI : DistribMulAction (Gam : Type) (En.descData l h).Vmod :=
    DistribMulAction.compHom (En.descData l h).Vmod
      (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho))
  letI : TopologicalSpace (ElemDual (En.descData l h).Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual (En.descData l h).Vmod) := ⟨rfl⟩
  letI : TopologicalSpace (En.descData l h).C0 := ⊥
  haveI : DiscreteTopology (En.descData l h).C0 := ⟨rfl⟩
  have hcomp : ∀ (gam : (Gam : Type)) (v : (En.descData l h).Vmod),
      gam • v = rho0Continuous (En.descData l h)
        (rhoPrimeK RF b F (En.radData l h) rfl rho) gam • v := fun _ _ => rfl
  haveI : ContinuousSMul (Gam : Type) (En.descData l h).Vmod :=
    continuousSMul_of_comp_discrete
      (rho0Continuous (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)) hcomp
  have hcompD : ∀ (gam : (Gam : Type)) (lam : ElemDual (En.descData l h).Vmod),
      gam • lam = rho0Continuous (En.descData l h)
        (rhoPrimeK RF b F (En.radData l h) rfl rho) gam • lam :=
    elemDual_smul_eq_of_comp
      (rho0Continuous (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)) hcomp
  haveI : ContinuousSMul (Gam : Type) (ElemDual (En.descData l h).Vmod) :=
    continuousSMul_of_comp_discrete
      (rho0Continuous (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)) hcompD
  exact hpartial_field_goal b F En l h Dsc rho smulZ2 htriv
    (card_H2_zmod2_eq_twoG Dl htriv)
    (isRightSeparating_of_tateDualityG Dl (Vmod_exp2 (DD := En.descData l h)) htriv
      (dualEval_equivariant_of_trivial htriv)) chi hchi

end FieldCounts

end GQ2.Dyadic.Count
