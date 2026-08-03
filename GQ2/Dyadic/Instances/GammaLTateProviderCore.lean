/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.Instances.GammaLRelatorRealization
import GQ2.Dyadic.Instances.LSourceComposition

/-!
# A relation-theoretic precursor to the direct L Tate provider

This file removes `TateDualityG` and `LocalEulerChar` from the construction of the
continuous-to-word comparison core.  Surjectivity upgrades the three already-constructed
injective flexible `H²` maps (primal, dual, and scalar) to equivalences.  The scalar equivalence
is followed by the explicit two-relator trace.  Its representative formula is exactly the one
compatibility needed by all three comparison squares.

The resulting constructor isolates two genuinely independent inputs which are not consequences
of map-level `H²` surjectivity alone:

* one common Heisenberg resolver, needed by the mixed `(1,1)` square; and
* agreement of the target-dependent scalar trace equivalence with the one common scalar
  orientation used by a uniform Tate provider.

No cup-product perfectness, Tate duality, Euler characteristic, or field realization is used.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

/-! ## The scalar flexible map from surjectivity alone -/

section ScalarSurjectivity

variable {h q e : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
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
local notation "wL" => lSqFam h q e

/-- The scalar flexible map is bijective as soon as its only open map-level condition,
surjectivity, is supplied.  Injectivity is unconditional. -/
theorem lScalarH2WordFlexible_bijective_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he)) :
    Function.Bijective (lScalarH2WordFlexible rho hcompatScalar he) :=
  ⟨lScalarH2WordFlexible_injective rho hcompatScalar he, hsurj⟩

/-- The canonical scalar continuous-to-word map, upgraded to an equivalence without Tate
duality. -/
noncomputable def lScalarModuleH2EquivFlexible_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he)) :
    H2 GammaL (ZMod 2) ≃+
      WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2) :=
  AddEquiv.ofBijective (lScalarH2WordFlexible rho hcompatScalar he)
    (lScalarH2WordFlexible_bijective_of_surjective rho hcompatScalar he hsurj)

@[simp] theorem lScalarModuleH2EquivFlexible_of_surjective_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he))
    (f : Z2 GammaL (ZMod 2)) :
    lScalarModuleH2EquivFlexible_of_surjective rho hcompatScalar he hsurj
        (H2mk GammaL (ZMod 2) f) =
      QuotientAddGroup.mk'
        (heisD1 (A := ZMod 2) (fun i ↦ rho (genL i)) wL).range
        (moduleObsFam WL genL rho hcompatScalar f) := rfl

/-- The scalar orientation obtained from map-level surjectivity followed by the explicit L
word trace. -/
noncomputable def lScalarH2TraceEquiv_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he)) :
    H2 GammaL (ZMod 2) ≃+ ZMod 2 :=
  (lScalarModuleH2EquivFlexible_of_surjective rho hcompatScalar he hsurj).trans
    (lWordH2TraceEquiv (fun i ↦ rho (genL i)) hq he hr)

/-- The surjectivity-built scalar orientation has the exact representative formula required by
the comparison squares. -/
@[simp] theorem lScalarH2TraceEquiv_of_surjective_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he))
    (f : Z2 GammaL (ZMod 2)) :
    lScalarH2TraceEquiv_of_surjective rho hcompatScalar hq he hr hsurj
        (H2mk GammaL (ZMod 2) f) =
      ∑ k, moduleObsFun WL genL rho hcompatScalar f k := rfl

/-- Thus scalar trace compatibility is a theorem from scalar map surjectivity, not an
additional square hypothesis. -/
theorem lScalarTraceCompatible_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (hsurj : Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he)) :
    ScalarTraceCompatible WL genL rho hcompatScalar
      (lScalarH2TraceEquiv_of_surjective rho hcompatScalar hq he hr hsurj) :=
  fun f ↦ lScalarH2TraceEquiv_of_surjective_mk rho hcompatScalar hq he hr hsurj f

end ScalarSurjectivity

/-! ## A no-Tate, no-Euler source-comparison core -/

section Core

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
local notation "wL" => lSqFam h q e

/-- Surjectivity of the three canonical flexible `H²` maps and a common Heisenberg resolver
construct the complete noncircular source comparison core.  The scalar trace formula proves all
three comparison squares. -/
noncomputable def sourceComparisonCore_of_lFlexibleH2_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A))
    (hsurjA : Function.Surjective
      (lModuleH2WordFlexible rho hcompatA hA₂ S.hres))
    (hsurjDual : Function.Surjective
      (lModuleH2WordFlexible rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual))
    (hsurjScalar : Function.Surjective
      (lScalarH2WordFlexible rho hcompatScalar he)) :
    SourceComparisonCore (fun i ↦ rho (genL i)) wL
      (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA)
      (lSourceH1Equiv rho hcompatA hA₂ S.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual) := by
  let hr := lSource_rel_death rho S.hres
  let h2A := lModuleH2EquivFlexible_of_surjective
    rho hcompatA hA₂ S.hres hsurjA
  let h2Dual := lModuleH2EquivFlexible_of_surjective rho hcompatDual
    (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual hsurjDual
  let h2Scalar := lScalarH2TraceEquiv_of_surjective
    rho hcompatScalar hq he hr hsurjScalar
  refine
    { h2A := h2A
      h2Dual := h2Dual
      h2Scalar := h2Scalar
      square02_commutes := ?_
      square11_commutes := ?_
      square20_commutes := ?_ }
  · simpa only [h2Dual, h2Scalar] using
      square02_commutes_of_scalarTrace WL genL rho wL hcompatDual hcompatScalar
        hr (lSq_isStokesEndpoint hq he)
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH0Equiv rho hcompatA) (fun _ ↦ rfl) h2Dual (fun _ ↦ rfl)
        h2Scalar
        (lScalarTraceCompatible_of_surjective rho hcompatScalar hq he hr hsurjScalar)
  · let za := Count.toZ1w rho hcompatA (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hres
    let zb := Count.toZ1w rho hcompatDual (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hresDual
    simpa only [h2Scalar] using
      square11_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatDual hcompatScalar
        hr (lSq_isStokesEndpoint hq he) S.hresHeis
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH1Equiv rho hcompatA hA₂ S.hres)
        (lSourceH1Equiv rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual)
        za zb (fun _ ↦ rfl) (fun _ ↦ rfl)
        (Count.h1Equiv_gammaR_range_H1mk rho hcompatA S.hres hA₂)
        (Count.h1Equiv_gammaR_range_H1mk rho hcompatDual S.hresDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
        h2Scalar
        (lScalarTraceCompatible_of_surjective rho hcompatScalar hq he hr hsurjScalar)
  · simpa only [h2A, h2Scalar] using
      square20_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatScalar
        hr (lSq_isStokesEndpoint hq he)
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH0Equiv rho hcompatDual) (fun _ ↦ rfl) h2A (fun _ ↦ rfl)
        h2Scalar
        (lScalarTraceCompatible_of_surjective rho hcompatScalar hq he hr hsurjScalar)

end Core

end

end GQ2.Dyadic.LSquare
