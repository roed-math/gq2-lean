/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceActionImage
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves

/-!
# A word-independent analytic supply interface

The finite-target Stokes theorem and its level resolver are the entire word-dependent input
to the counting pipeline. This file packages that input for an arbitrary `GammaR` word and
provides the scalar and variation consumers. Tame specialization supplies the fixed nonzero
variation witness through its unramified order-two quotient; no displayed core coordinates
or particular branch are needed.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN GQ2.Dyadic.RowActionImage
open GQ2.CardH2GammaA DihedralGroup

attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

/-- Coefficient-independent finite Stokes data for an arbitrary branch word. -/
structure UniformStokesSupply (n q : ℕ) (R : PWord (Generator n))
    (wOf : ℕ → Fin 2 → FreeGroup (Generator n)) : Prop where
  level : LevelResolver n q R wOf
  stokes : ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
    (∀ a : A, a + a = 0) →
    StokesDuality (fun g ↦ rho (gammaGen n q R g)) (wOf (4 * Monoid.exponent C)) A

namespace UniformStokesSupply
variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

theorem of_simple (hlv : LevelResolver n q R wOf)
    (hsimp : SimpleActionImageStokes n q R wOf) : UniformStokesSupply n q R wOf :=
  ⟨hlv, fun _ _ _ _ _ rho A _ _ _ hA₂ ↦
    uniformPushedStokesDuality_of_actionImage hlv hsimp rho A hA₂⟩

theorem endpoint (S : UniformStokesSupply n q R wOf) (C : Type) [Group C] [Finite C] :
    IsStokesEndpoint (wOf (4 * Monoid.exponent C)) :=
  S.level.endpoint _ (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2

theorem resolvesWord (S : UniformStokesSupply n q R wOf)
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
    (hA₂ : ∀ a : A, a + a = 0) :
    ResolvesAt (gammaFam n q R) (wOf (4 * Monoid.exponent C)) (WordLift A C) :=
  S.level.resolves _ _ (fourMulExponent_ne_zero_and_even C).1
    (fun x ↦ (WordLift.orderOf_dvd_two_mul hA₂
      (fun c : C ↦ Monoid.order_dvd_exponent c) x).trans ⟨2, by ring⟩)

/-- Every intrinsic two-relator family has deficiency n. -/
theorem degree : Nat.card (Generator n) = Nat.card (Fin 2) + (n + 1) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Generator.card_generator,
    Fintype.card_fin]
  omega

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩
local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-- The fixed order-two variation quotient is reached through the tame sigma coordinate. -/
def datumRho (hspec : TameSpec.TameSpecializes n q R) :
    ContinuousMonoidHom ((GammaR n q R) : Type) (Base ⧸ datum.M) :=
  (tqClassify q (ProfiniteGrp.of (Base ⧸ datum.M))
    (a := QuotientGroup.mk (r 1)) (b := 1) (by simp [conjP])).comp
    (TameSpec.tameOfSpec n q R hspec)

@[simp] theorem datumRho_sigma (hspec : TameSpec.TameSpecializes n q R) :
    datumRho hspec (gammaGen n q R .sigma) = QuotientGroup.mk (r 1) := by
  change tqClassify q (ProfiniteGrp.of (Base ⧸ datum.M))
    (a := QuotientGroup.mk (r 1)) (b := 1) (by simp [conjP])
      (TameSpec.tameOfSpec n q R hspec (gammaGen n q R .sigma)) = _
  rw [TameSpec.tameOfSpec_gammaGen]
  exact tqClassify_tqSigma q (ProfiniteGrp.of (Base ⧸ datum.M)) (by simp [conjP])

theorem datumRho_surjective (hspec : TameSpec.TameSpecializes n q R) :
    Function.Surjective (datumRho hspec) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rcases quotient_cases b with h1 | hr
  · exact ⟨1, (map_one _).trans h1.symm⟩
  · exact ⟨gammaGen n q R .sigma, (datumRho_sigma hspec).trans hr.symm⟩

/-- Scalar H2 has order two, for every tame-specializing word with uniform Stokes supply. -/
theorem cardH2 (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R) :
    letI := scalarActionZmodTwo ((GammaR n q R) : Type)
    Nat.card (H2 ((GammaR n q R) : Type) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((GammaR n q R) : Type)
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  let rho := datumRho hspec
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  letI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((GammaR n q R) : Type) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((GammaR n q R) : Type) (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : ContinuousSMul ((GammaR n q R) : Type) (ElemDual (Additive ↥datum.T)) :=
    continuousSMul_of_comp_finite rho (fun _ _ ↦ rfl)
  exact cardH2_of_variation (tComplement_nonempty datum).some rho
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R) (fun V ↦ hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho (datumRho_surjective hspec) (fun _ ↦ rfl))
    (S.resolvesWord (by decide : ∀ a : ZMod 2, a + a = 0))
    (S.resolvesWord (radT_add_self datum))
    (S.resolvesWord (fun lam : ElemDual (Additive ↥datum.T) ↦ lam.add_self_eq_zero))
    (S.level.heis (radT_add_self datum))
    (S.stokes _ rho _ (radT_add_self datum))
    (S.stokes _ rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    (S.endpoint _) datum_noDescent (datumRho_surjective hspec)

/-- The scalar character count is determined by the degree of the alphabet. -/
theorem homCard (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R) :
    Nat.card (ContinuousMonoidHom ((GammaR n q R) : Type) (Multiplicative (ZMod 2))) =
      (standardNumerics n).homScalar := by
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  let rho := datumRho hspec
  exact homCard_field_goal rho (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R)
    (S.resolvesWord (by decide : ∀ a : ZMod 2, a + a = 0))
    (isWildTwo_of_gammaGen rho (datumRho_surjective hspec) (fun _ ↦ rfl)) degree
    (S.stokes _ rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)) (S.endpoint _)

/-- Both scalar certificate clauses are supplied without a branch-specific core argument. -/
theorem scalar (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R) :
    ScalarHilbertCertificate (GammaR n q R) n (standardNumerics n)
      (scalarActionZmodTwo ((GammaR n q R) : Type)) :=
  ⟨S.homCard hspec, S.cardH2 hspec⟩

/-- The universal half-torsor identity is another word-independent Stokes consumer. -/
theorem lem86 (S : UniformStokesSupply n q R wOf)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho) := by
  letI := scalarActionZmodTwo ((GammaR n q R) : Type)
  letI := scalarActionZmodTwo (Bg ⧸ D.M)
  letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
  letI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
  letI : DistribMulAction ((GammaR n q R) : Type) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((GammaR n q R) : Type) (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : ContinuousSMul ((GammaR n q R) : Type) (ElemDual (Additive ↥D.T)) :=
    continuousSMul_of_comp_finite rho (fun _ _ ↦ rfl)
  exact lem86_of_variation (tComplement_nonempty D).some rho
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R) (fun V ↦ hwildLevel_gammaR V)
    (isWildTwo_of_gammaGen rho hrho (fun _ ↦ rfl))
    (S.resolvesWord (by decide : ∀ a : ZMod 2, a + a = 0))
    (S.resolvesWord (radT_add_self D))
    (S.resolvesWord (fun lam : ElemDual (Additive ↥D.T) ↦ lam.add_self_eq_zero))
    (S.level.heis (radT_add_self D))
    (S.stokes _ rho _ (radT_add_self D))
    (S.stokes _ rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    (S.endpoint _) hedge hrho

#print axioms of_simple
#print axioms resolvesWord
#print axioms datumRho_surjective
#print axioms cardH2
#print axioms homCard
#print axioms scalar
#print axioms lem86

end UniformStokesSupply
end
end GQ2.Dyadic
