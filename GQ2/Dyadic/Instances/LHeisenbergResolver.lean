/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleMixed
import GQ2.Dyadic.Instances.LSourceComposition
import GQ2.Dyadic.Instances.LScalarTrace

/-!
# The L Heisenberg resolver and degree-one representatives

The mixed comparison square needs the L relators resolved in `HeisLift A C`, not merely in its
primal and dual split slices.  The canonical target-local choice is the `omega2Exp` of the
Heisenberg exponent.  At that exponent the generic frozen L resolver theorem applies directly.

For an arbitrary preselected exponent parameter `e`, the exact additional condition exposed here
is equality with that canonical `omega2Exp`; the primal and dual split resolvers alone do not
control the Heisenberg central coordinate.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

section Resolver

variable {A C : Type} [AddCommGroup A] [Group C] [DistribMulAction C A]
  [Finite A] [Finite C]

local instance lHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance lHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The canonical L word resolves every marking in the Heisenberg target. -/
theorem resolvesAt_lSqFam_heisExponent (h q : ℕ) :
    ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q
        (omega2Exp (Monoid.exponent (HeisLift A C))))
      (HeisLift A C) :=
  resolvesAt_lSqFam heisExponent_ne_zero orderOf_heisLift_dvd h q

/-- At even `q`, the same canonical word simultaneously resolves the Heisenberg target and is a
Stokes endpoint. -/
theorem resolvesAt_and_endpoint_lSqFam_heisExponent (h : ℕ) {q : ℕ} (hq : Even q) :
    ResolvesAt
        (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (Monoid.exponent (HeisLift A C))))
        (HeisLift A C) ∧
      IsStokesEndpoint
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (Monoid.exponent (HeisLift A C)))) :=
  resolvesAt_and_endpoint_lSqFam heisExponent_ne_zero
    heisLevel_ne_zero_and_even.2 orderOf_heisLift_dvd hq

/-- Minimal equality criterion for reusing an arbitrary displayed L exponent at the Heisenberg
target. -/
theorem resolvesAt_lSqFam_heis_of_eq {h q e : ℕ}
    (he : e = omega2Exp (Monoid.exponent (HeisLift A C))) :
    ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e)
      (HeisLift A C) := by
  subst e
  exact resolvesAt_lSqFam_heisExponent h q

end Resolver

section Representatives

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-- The representative-level map underlying the L source `H¹` equivalence. -/
noncomputable abbrev lSourceZ1Map
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hres : ResolvesAt WL wL (WordLift A C)) :
    Z1 GammaL A →+ ↥(heisD1 (A := A) (fun i ↦ rho (genL i)) wL).ker :=
  Count.toZ1w rho hcompat (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hres

@[simp] theorem lSourceZ1Map_coe
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hres : ResolvesAt WL wL (WordLift A C)) (z : Z1 GammaL A) :
    (lSourceZ1Map rho hcompat hres z : Generator (2 * h + 1) → A) =
      fun i ↦ z.1 (genL i) := rfl

/-- Representative regression for the actual range-based L source `H¹` equivalence. -/
@[simp] theorem lSourceH1Equiv_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C)) (z : Z1 GammaL A) :
    lSourceH1Equiv rho hcompat hA₂ hres (H1mk GammaL A z) =
      stokesH1Mk _ _ (lSourceZ1Map rho hcompat hres z) := by
  exact Count.h1Equiv_gammaR_range_H1mk rho hcompat hres hA₂ z

end Representatives

section MixedSquare

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)]
  [ContinuousSMul ((gamma h q : Type)) (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
  [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
  [DistribMulAction C (ZMod 2)]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

local instance lComparisonHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance lComparisonHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The source and represented scalar actions agree automatically: every group action on
`ZMod 2` is trivial. -/
theorem lSource_scalar_compatible (rho : ContinuousMonoidHom GammaL C) :
    ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s := by
  intro g s
  rw [Count.smul_zmod2, Count.smul_zmod2]

/-- The L `(1,1)` comparison square with the canonical scalar trace orientation.  For a
preselected word exponent the one genuinely mixed input is the Heisenberg resolver; the primal
and dual split resolvers do not determine its central coordinate. -/
theorem lSquare11_commutes_of_heisResolver
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hresDual : ResolvesAt WL wL (WordLift (ElemDual A) C))
    (hresHeis : ResolvesAt WL wL (HeisLift A C))
    (hq : Even q) (he : Odd e) (D : TateDualityG GammaL 2) :
    ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC1
            (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i)))
            (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))
          (wordH1_target_uc (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho hres))).trans
        (scalarDualTransport
          (lSourceH1Equiv rho hcompatDual
            (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual)
          (lScalarH2TraceEquiv rho (lSource_scalar_compatible rho) hq he
            (lSource_rel_death rho hres) D Count.smul_zmod2)))
          (stokesH1Map
            (stokes_square₀ (A := A) (fun i ↦ rho (genL i)) wL
              (lSource_rel_death rho hres)
              (Certificates.LSqStokes.lSq_isStokesEndpoint hq he))
            (stokes_square₁ (A := A) (fun i ↦ rho (genL i)) wL
              (lSource_rel_death rho hres)
              (Certificates.LSqStokes.lSq_isStokesEndpoint hq he)) x)
        = sourceCup11
            (lSource_dualEval_equivariant rho hcompatA hcompatDual Count.smul_zmod2)
            ((lSourceH1Equiv rho hcompatA hA₂ hres).symm x) := by
  exact square11_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatDual
    (lSource_scalar_compatible rho) (lSource_rel_death rho hres)
    (Certificates.LSqStokes.lSq_isStokesEndpoint hq he) hresHeis
    (lSource_dualEval_equivariant rho hcompatA hcompatDual Count.smul_zmod2)
    (lSourceH1Equiv rho hcompatA hA₂ hres)
    (lSourceH1Equiv rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual)
    (lSourceZ1Map rho hcompatA hres)
    (lSourceZ1Map rho hcompatDual hresDual)
    (lSourceZ1Map_coe rho hcompatA hres)
    (lSourceZ1Map_coe rho hcompatDual hresDual)
    (lSourceH1Equiv_mk rho hcompatA hA₂ hres)
    (lSourceH1Equiv_mk rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual)
    (lScalarH2TraceEquiv rho (lSource_scalar_compatible rho) hq he
      (lSource_rel_death rho hres) D Count.smul_zmod2)
    (lScalarTraceCompatible rho (lSource_scalar_compatible rho) hq he
      (lSource_rel_death rho hres) D Count.smul_zmod2)

end MixedSquare

section CanonicalSource

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)]
  [ContinuousSMul ((gamma h q : Type)) (ElemDual A)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]
  [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
  [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eHeis" => omega2Exp (Monoid.exponent (HeisLift A C))
local notation "wHeis" => Certificates.LSqStokes.lSqFam h q eHeis

local instance lCanonicalHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance lCanonicalHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The canonical Heisenberg exponent is odd, exactly the parity required by the improved L
endpoint and scalar trace. -/
theorem lCanonicalHeisenbergExponent_odd : Odd eHeis :=
  odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2

/-- At the target-local Heisenberg exponent, the sole field of
`LFlexibleEulerTateSquares` is discharged by the generic finite-target L resolver. -/
noncomputable def lCanonicalFlexibleEulerTateSquares :
    LFlexibleEulerTateSquares (h := h) (q := q) (e := eHeis) (C := C) (A := A) where
  hresHeis := resolvesAt_lSqFam_heisExponent (A := A) (C := C) h q

/-- Fully canonical one-target source comparison for the improved L presentation.

The displayed exponent is chosen from the common Heisenberg target.  Hence the common resolver,
its primal and dual restrictions, the endpoint, scalar triviality, and all three comparison
squares are constructed internally. -/
noncomputable def sourceComparisonPackage_lCanonical
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2) (hq : Even q) :
    SourceComparisonPackage (fun i ↦ rho (genL i)) wHeis
      (lSource_rel_death rho lCanonicalFlexibleEulerTateSquares.hres)
      (Certificates.LSqStokes.lSq_isStokesEndpoint hq lCanonicalHeisenbergExponent_odd)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual Count.smul_zmod2)
      (lSourceH0Equiv rho hcompatA)
      (lSourceH1Equiv rho hcompatA hA₂ lCanonicalFlexibleEulerTateSquares.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero)
        lCanonicalFlexibleEulerTateSquares.hresDual) :=
  sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality rho hcompatA hcompatDual hA₂ hE D
    Count.smul_zmod2 hq lCanonicalHeisenbergExponent_odd
    lCanonicalFlexibleEulerTateSquares

/-- Canonical one-target source comparison with the exact two non-scalar `H²` cardinal
hypotheses exposed.  It is the no-`LocalEulerChar` counterpart of
`sourceComparisonPackage_lCanonical`; the Heisenberg resolver, endpoint, scalar trace, all
three cup bijectivities, and all comparison squares are still constructed internally. -/
noncomputable def sourceComparisonPackage_lCanonical_of_card
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hcardA : Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wHeis A))
    (hcardDual : Nat.card (H2 GammaL (ElemDual A)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wHeis (ElemDual A)))
    (D : TateDualityG GammaL 2) (hq : Even q) :
    SourceComparisonPackage (fun i ↦ rho (genL i)) wHeis
      (lSource_rel_death rho lCanonicalFlexibleEulerTateSquares.hres)
      (Certificates.LSqStokes.lSq_isStokesEndpoint hq lCanonicalHeisenbergExponent_odd)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual Count.smul_zmod2)
      (lSourceH0Equiv rho hcompatA)
      (lSourceH1Equiv rho hcompatA hA₂ lCanonicalFlexibleEulerTateSquares.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero)
        lCanonicalFlexibleEulerTateSquares.hresDual) :=
  sourceComparisonPackage_of_lFlexibleH2_card_tateDuality rho hcompatA hcompatDual hA₂
    hcardA hcardDual D Count.smul_zmod2 hq lCanonicalHeisenbergExponent_odd
    lCanonicalFlexibleEulerTateSquares

/-- Canonical no-Euler regression: the two explicit non-scalar `H²` cardinal equalities and
Tate duality suffice for all three Stokes cohomology bijections. -/
theorem stokesCohomologyBijections_lCanonical_of_card
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hcardA : Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wHeis A))
    (hcardDual : Nat.card (H2 GammaL (ElemDual A)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wHeis (ElemDual A)))
    (D : TateDualityG GammaL 2) (hq : Even q) :
    StokesCohomologyBijections (fun i ↦ rho (genL i)) wHeis A
      (lSource_rel_death rho lCanonicalFlexibleEulerTateSquares.hres)
      (Certificates.LSqStokes.lSq_isStokesEndpoint hq lCanonicalHeisenbergExponent_odd) :=
  (sourceComparisonPackage_lCanonical_of_card rho hcompatA hcompatDual hA₂
    hcardA hcardDual D hq).stokesCohomologyBijections

/-- Canonical regression: the target-local constructor reaches all three Stokes cohomology
bijections with no resolver, endpoint, scalar-triviality, or comparison-square hypothesis. -/
theorem stokesCohomologyBijections_lCanonical
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2) (hq : Even q) :
    StokesCohomologyBijections (fun i ↦ rho (genL i)) wHeis A
      (lSource_rel_death rho lCanonicalFlexibleEulerTateSquares.hres)
      (Certificates.LSqStokes.lSq_isStokesEndpoint hq lCanonicalHeisenbergExponent_odd) :=
  (sourceComparisonPackage_lCanonical rho hcompatA hcompatDual hA₂ hE D hq).stokesCohomologyBijections

end CanonicalSource

end

end GQ2.Dyadic.LSquare
