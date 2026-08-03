/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LSourceComparison

/-!
# Tate-duality adapter for the L source-comparison package

`SourceComparisonPackage` deliberately records all three continuous cup-product
bijectivities.  They are not independent inputs once the source group carries local Tate
duality and the local Euler characteristic: the generic theorems in
`LiftingDualityG` prove them for the evaluation pairing.

This file supplies that adapter.  Its constructor leaves exactly six comparison inputs:
three degree-two comparison equivalences and the three comparison-square identities.  In
particular, it assumes Tate duality and Euler characteristic for the actual source `Γ`; it
does not transfer either hypothesis to a finite quotient or to `GammaR` by fiat.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes

section Generic

variable {Γ C A : Type}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group C] [Finite C]
  [AddCommGroup A] [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Γ (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  {ι rel : Type*} [Fintype ι] [DecidableEq ι] [Fintype rel]

variable (c : ι → C) (w : rel → FreeGroup ι) [DistribMulAction C A]
  (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
  (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
    dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam)

/--
Local Tate duality discharges all three perfectness fields of a source-comparison package.

The remaining arguments are precisely the comparison data: `H²` comparison for the primal,
dual, and scalar coefficients, and commutativity of the three Stokes/cup squares.  The
degree-zero and degree-one comparisons remain arbitrary here so that this constructor can be
used both with the L target adapters and with future presentations.
-/
noncomputable def sourceComparisonPackage_of_tateDuality
    (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1A : H1 Γ A ≃+ WordH1 c w A)
    (h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker)
    (h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A))
    (h2A : H2 Γ A ≃+ WordH2 c w A)
    (h2Dual : H2 Γ (ElemDual A) ≃+ WordH2 c w (ElemDual A))
    (h2Scalar : H2 Γ (ZMod 2) ≃+ ZMod 2)
    (square02_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC0 (heisD1 (A := ElemDual A) c w))
          (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
        (scalarDualTransport h2Dual h2Scalar))
          (stokesH0Map (stokes_square₀ (A := A) c w hr hend) x)
        = sourceCup02 hpair (h0A.symm x))
    (square11_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
          (wordH1_target_uc (A := A) c w hr)).trans
        (scalarDualTransport h1Dual h2Scalar))
          (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
            (stokes_square₁ (A := A) c w hr hend) x)
        = sourceCup11 hpair (h1A.symm x))
    (square20_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC2 (heisD0 (A := ElemDual A) c))
          (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
            (heisD0 (A := ElemDual A) c))).trans
        (scalarDualTransport h0Dual h2Scalar))
          (stokesH2Map (stokes_square₁ (A := A) c w hr hend) x)
        = sourceCup20 hpair (h2A.symm x)) :
    SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual where
  h2A := h2A
  h2Dual := h2Dual
  h2Scalar := h2Scalar
  cup02_bijective := bijective_cup02_dualEvalG D hE hA₂ htriv hpair
  cup11_bijective := bijective_cup11_dualEvalG D hE hA₂ htriv hpair
  cup20_bijective := bijective_cup20_dualEvalG D hE hA₂ htriv hpair
  square02_commutes := square02_commutes
  square11_commutes := square11_commutes
  square20_commutes := square20_commutes

/-- The same adapter with its final word-cohomology conclusion already assembled. -/
theorem stokesCohomologyBijections_of_tateDuality
    (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1A : H1 Γ A ≃+ WordH1 c w A)
    (h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker)
    (h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A))
    (h2A : H2 Γ A ≃+ WordH2 c w A)
    (h2Dual : H2 Γ (ElemDual A) ≃+ WordH2 c w (ElemDual A))
    (h2Scalar : H2 Γ (ZMod 2) ≃+ ZMod 2)
    (square02_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC0 (heisD1 (A := ElemDual A) c w))
          (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
        (scalarDualTransport h2Dual h2Scalar))
          (stokesH0Map (stokes_square₀ (A := A) c w hr hend) x)
        = sourceCup02 hpair (h0A.symm x))
    (square11_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
          (wordH1_target_uc (A := A) c w hr)).trans
        (scalarDualTransport h1Dual h2Scalar))
          (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
            (stokes_square₁ (A := A) c w hr hend) x)
        = sourceCup11 hpair (h1A.symm x))
    (square20_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC2 (heisD0 (A := ElemDual A) c))
          (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
            (heisD0 (A := ElemDual A) c))).trans
        (scalarDualTransport h0Dual h2Scalar))
          (stokesH2Map (stokes_square₁ (A := A) c w hr hend) x)
        = sourceCup20 hpair (h2A.symm x)) :
    StokesCohomologyBijections c w A hr hend := by
  exact (sourceComparisonPackage_of_tateDuality c w hr hend hpair D hE hA₂ htriv
    h0A h1A h0Dual h1Dual h2A h2Dual h2Scalar square02_commutes square11_commutes
    square20_commutes).stokesCohomologyBijections

end Generic

end

end GQ2.Dyadic.LSquare
