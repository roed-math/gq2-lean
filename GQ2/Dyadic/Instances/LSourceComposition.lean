/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LSourceEulerCard
import GQ2.Dyadic.Instances.LSourceDualityAdapter

/-!
# The composed continuous source interface for the L presentation

This file composes the independent reductions already available for the improved L row:

* the target-local flexible resolver construction gives injective module-valued `H²` maps;
* `LocalEulerChar GammaL (2h+1)` upgrades the primal and dual maps to equivalences;
* `TateDualityG GammaL 2` orients scalar `H²` and proves the three continuous cup maps
  bijective;
* `h0Equiv` and `h1Equiv_gammaR_range` supply the degree-zero and degree-one comparisons.

Consequently the only fields left in `LFlexibleEulerTateSquares` are the three comparison
squares.  Neither analytic bundle is asserted for the abstract group `GammaL`; both remain
honest hypotheses on that source group.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

section LComposition

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
  [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
  [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-! ## Canonical comparison maps and pairings -/

/-- Relator death at the represented target follows from the target-local primal resolver. -/
theorem lSource_rel_death
    (rho : ContinuousMonoidHom GammaL C)
    (hres : ResolvesAt WL wL (WordLift A C)) :
    ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1 := fun k ↦
  lower_rel (A := A) rho (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hres k

/-- The proved degree-zero source comparison for the represented L presentation. -/
noncomputable abbrev lSourceH0Equiv
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a) :
    H0 GammaL A ≃+ ↥(heisD0 (A := A) (fun i ↦ rho (genL i))).ker :=
  Count.h0Equiv rho hcompat (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))

/-- The proved degree-one source comparison, using only the target-local resolver. -/
noncomputable abbrev lSourceH1Equiv
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C)) :
    H1 GammaL A ≃+ WordH1 (fun i ↦ rho (genL i)) wL A :=
  Count.h1Equiv_gammaR_range rho hcompat hres hA₂

/-- The evaluation pairing is equivariant for compatible primal and contragredient actions. -/
theorem lSource_dualEval_equivariant
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m) :
    ∀ (g : GammaL) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam := by
  intro g a lam
  rw [hcompatA, hcompatDual, dualEval_apply, ElemDual.smul_apply, inv_smul_smul,
    dualEval_apply, htriv]

/-! ## H² equivalences supplied by Euler characteristic and Tate duality -/

/-- Local Euler characteristic upgrades the concrete flexible L `H²` map to an equivalence. -/
noncomputable def lModuleH2EquivFlexible_of_localEulerChar
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hE : LocalEulerChar GammaL (2 * h + 1)) :
    H2 GammaL A ≃+ WordH2 (fun i ↦ rho (genL i)) wL A :=
  lModuleH2EquivFlexible_of_card_eq rho hcompat hA₂ hres
    (l_card_H2_eq_WordH2_of_localEulerChar rho hcompat hA₂ hres hE)

/-- Tate duality supplies the scalar orientation required by the source package. -/
noncomputable def lScalarH2Equiv_of_tateDuality
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m) :
    H2 GammaL (ZMod 2) ≃+ ZMod 2 :=
  sourceScalarH2Equiv_of_card_eq
    (scalar_card_H2_eq_card_zmodTwo_of_tateDuality D htriv)

/-! ## The exact three-square residue -/

/--
After composing the proved algebraic comparisons with the two named analytic bundles, these
are exactly the three remaining source obligations for one L target.
-/
structure LFlexibleEulerTateSquares
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hresDual : ResolvesAt WL wL (WordLift (ElemDual A) C))
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hend : IsStokesEndpoint wL) : Prop where
  /-- The `(0,2)` continuous cup/Stokes comparison square. -/
  square02_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC0 (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))
        (stokesUC0_bijective
          (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))).trans
      (scalarDualTransport
        (lModuleH2EquivFlexible_of_localEulerChar rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual hE)
        (lScalarH2Equiv_of_tateDuality D htriv)))
        (stokesH0Map
          (stokes_square₀ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho hres) hend) x)
      = sourceCup02 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lSourceH0Equiv rho hcompatA).symm x)
  /-- The `(1,1)` continuous cup/Stokes comparison square. -/
  square11_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC1
          (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i)))
          (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))
        (wordH1_target_uc (A := A) (fun i ↦ rho (genL i)) wL
          (lSource_rel_death rho hres))).trans
      (scalarDualTransport
        (lSourceH1Equiv rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual)
        (lScalarH2Equiv_of_tateDuality D htriv)))
        (stokesH1Map
          (stokes_square₀ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho hres) hend)
          (stokes_square₁ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho hres) hend) x)
      = sourceCup11 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lSourceH1Equiv rho hcompatA hA₂ hres).symm x)
  /-- The `(2,0)` continuous cup/Stokes comparison square. -/
  square20_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC2 (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i))))
        (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
          (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i))))).trans
      (scalarDualTransport
        (lSourceH0Equiv rho hcompatDual)
        (lScalarH2Equiv_of_tateDuality D htriv)))
        (stokesH2Map
          (stokes_square₁ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho hres) hend) x)
      = sourceCup20 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lModuleH2EquivFlexible_of_localEulerChar rho hcompatA hA₂ hres hE).symm x)

/--
The strongest current one-target source constructor for the improved L presentation.

It uses only the two target-local resolvers, `LocalEulerChar` and `TateDualityG` on the actual
source `GammaL`, the trivial scalar action, and the three fields of
`LFlexibleEulerTateSquares`.  In particular there is no all-level fixed-word resolver and no
separate `H²` cardinality, cup-bijectivity, relator-death, pairing, `H⁰`, or `H¹` hypothesis.
-/
noncomputable def sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hresDual : ResolvesAt WL wL (WordLift (ElemDual A) C))
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hend : IsStokesEndpoint wL)
    (S : LFlexibleEulerTateSquares rho hcompatA hcompatDual hA₂ hres hresDual
      hE D htriv hend) :
    SourceComparisonPackage (fun i ↦ rho (genL i)) wL (lSource_rel_death rho hres) hend
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA) (lSourceH1Equiv rho hcompatA hA₂ hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual) where
  h2A := lModuleH2EquivFlexible_of_localEulerChar rho hcompatA hA₂ hres hE
  h2Dual := lModuleH2EquivFlexible_of_localEulerChar rho hcompatDual
    (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresDual hE
  h2Scalar := lScalarH2Equiv_of_tateDuality D htriv
  cup02_bijective := bijective_cup02_dualEvalG D hE hA₂ htriv
    (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
  cup11_bijective := bijective_cup11_dualEvalG D hE hA₂ htriv
    (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
  cup20_bijective := bijective_cup20_dualEvalG D hE hA₂ htriv
    (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
  square02_commutes := S.square02_commutes
  square11_commutes := S.square11_commutes
  square20_commutes := S.square20_commutes

/-- Regression: the composed constructor reaches the exact three Stokes bijections. -/
theorem stokesCohomologyBijections_of_lFlexibleH2_euler_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hresDual : ResolvesAt WL wL (WordLift (ElemDual A) C))
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hend : IsStokesEndpoint wL)
    (S : LFlexibleEulerTateSquares rho hcompatA hcompatDual hA₂ hres hresDual
      hE D htriv hend) :
    StokesCohomologyBijections (fun i ↦ rho (genL i)) wL A
      (lSource_rel_death rho hres) hend :=
  (sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality rho hcompatA hcompatDual
    hA₂ hres hresDual hE D htriv hend S).stokesCohomologyBijections

end LComposition

end

end GQ2.Dyadic.LSquare
