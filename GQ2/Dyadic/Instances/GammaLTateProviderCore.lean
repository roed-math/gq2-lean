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
* word-level Stokes duality.

There is no separate scalar-orientation compatibility input: any two additive equivalences
from `H²(GammaL, ZMod 2)` to `ZMod 2` are equal, so target-independence is automatic.

No cup-product perfectness, Tate duality, Euler characteristic, or field realization is used.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

/-! ## Uniqueness of a scalar orientation -/

/-- There is at most one additive equivalence from any additive group to `ZMod 2`.

Both equivalences send zero to zero.  If the first sends `x` to one, then `x` is nonzero, so
injectivity prevents the second from sending it to zero; `ZMod.eq_zero_or_eq_one` finishes. -/
theorem addEquiv_zmodTwo_unique
    {A : Type*} [AddCommGroup A] (e₁ e₂ : A ≃+ ZMod 2) : e₁ = e₂ := by
  ext x
  rcases ZMod.eq_zero_or_eq_one (e₁ x) with h₁ | h₁
  · have hx : x = 0 := e₁.injective (by simpa using h₁)
    subst x
    simp
  · rcases ZMod.eq_zero_or_eq_one (e₂ x) with h₂ | h₂
    · have hx : x = 0 := e₂.injective (by simpa using h₂)
      subst x
      simp at h₁
    · exact h₁.trans h₂.symm

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

/-- Scalar trace orientations built through any two finite action targets agree.  No comparison
of chosen finite factorizations is needed: additive equivalences into `ZMod 2` are unique. -/
theorem lScalarH2TraceEquiv_of_surjective_target_independent
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    [DistribMulAction D (ZMod 2)]
    (rhoC : ContinuousMonoidHom GammaL C)
    (rhoD : ContinuousMonoidHom GammaL D)
    (hcompatC : ∀ (g : GammaL) (s : ZMod 2), g • s = rhoC g • s)
    (hcompatD : ∀ (g : GammaL) (s : ZMod 2), g • s = rhoD g • s)
    (hq : Even q) (he : Odd e)
    (hrC : ∀ k, FreeGroup.lift (fun i ↦ rhoC (genL i)) (wL k) = 1)
    (hrD : ∀ k, FreeGroup.lift (fun i ↦ rhoD (genL i)) (wL k) = 1)
    (hsurjC : Function.Surjective (lScalarH2WordFlexible rhoC hcompatC he))
    (hsurjD : Function.Surjective (lScalarH2WordFlexible rhoD hcompatD he)) :
    lScalarH2TraceEquiv_of_surjective rhoC hcompatC hq he hrC hsurjC =
      lScalarH2TraceEquiv_of_surjective rhoD hcompatD hq he hrD hsurjD :=
  addEquiv_zmodTwo_unique _ _

omit [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)] in
/-- Finite-extension asphericity supplies scalar map surjectivity.  The specialized scalar
flexible resolver is available at every odd L word, so no fixed-target scalar resolver is an
extra hypothesis. -/
theorem lScalarH2WordFlexible_surjective_of_extensionAsphericity
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e)
    (hasph : LModuleFiniteExtensionAsphericity (A := ZMod 2) rho) :
    Function.Surjective (lScalarH2WordFlexible rho hcompatScalar he) := by
  let hresolve := lScalarFlexibleResolverSystem rho he
  let hreal := moduleRelatorRealization_of_extensionAsphericity WL genL rho
    (fun i ↦ rho (genL i)) wL hresolve hasph
  exact globalModuleH2WordFlexible_surjective_of_relatorRealization
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompatScalar (fun V ↦ hwildLevel_gammaR V) (by decide) hresolve hreal

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

/-! ## Coefficient-wise and uniform precursor packages -/

section Precursor

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

/-- The strongest coefficient-wise precursor obtained from the current relation-theoretic
machinery.

The first four fields are finite presentation data: a common Heisenberg resolver and
surjectivity of the three canonical continuous-to-word maps.  Scalar-orientation
target-independence is automatic by `addEquiv_zmodTwo_unique`.  Word Stokes duality remains an
independent algebraic input. -/
structure LModuleTatePrecursor
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (he : Odd e) where
  /-- One resolver simultaneously supplies the primal, dual, and mixed comparison data. -/
  squares : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)
  /-- Surjectivity of the canonical primal `H²` comparison. -/
  h2A_surjective : Function.Surjective
    (lModuleH2WordFlexible rho hcompatA hA₂ squares.hres)
  /-- Surjectivity of the canonical dual `H²` comparison. -/
  h2Dual_surjective : Function.Surjective
    (lModuleH2WordFlexible rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) squares.hresDual)
  /-- Surjectivity of the canonical scalar `H²` comparison. -/
  h2Scalar_surjective : Function.Surjective
    (lScalarH2WordFlexible rho hcompatScalar he)
  /-- Independent word-complex duality; no continuous cup perfectness is assumed. -/
  stokes : StokesDuality (fun i ↦ rho (genL i)) wL A

/-- A coefficient-wise precursor produces the complete noncircular comparison core. -/
noncomputable def LModuleTatePrecursor.core
    {rho : ContinuousMonoidHom GammaL C}
    {hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a}
    {hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam}
    {hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s}
    {htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s}
    {hA₂ : ∀ a : A, a + a = 0}
    {hq : Even q} {he : Odd e}
    (D : LModuleTatePrecursor rho hcompatA hcompatDual hcompatScalar
      htriv hA₂ hq he) :
    SourceComparisonCore (fun i ↦ rho (genL i)) wL
      (lSource_rel_death rho D.squares.hres) (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA)
      (lSourceH1Equiv rho hcompatA hA₂ D.squares.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) D.squares.hresDual) :=
  sourceComparisonCore_of_lFlexibleH2_surjective rho hcompatA hcompatDual
    hcompatScalar htriv hA₂ hq he D.squares D.h2A_surjective
      D.h2Dual_surjective D.h2Scalar_surjective

/-- Finite-extension asphericity for the primal, dual, and scalar modules constructs the three
surjectivity fields of `LModuleTatePrecursor`.  Word Stokes duality is the remaining independent
hypothesis. -/
noncomputable def LModuleTatePrecursor.ofExtensionAsphericity
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A))
    (hasphA : LModuleFiniteExtensionAsphericity (A := A) rho)
    (hasphDual : LModuleFiniteExtensionAsphericity (A := ElemDual A) rho)
    (hasphScalar : LModuleFiniteExtensionAsphericity (A := ZMod 2) rho)
    (hstokes : StokesDuality (fun i ↦ rho (genL i)) wL A) :
    LModuleTatePrecursor rho hcompatA hcompatDual hcompatScalar
      htriv hA₂ hq he where
  squares := S
  h2A_surjective :=
    lModuleH2WordFlexible_surjective_of_relatorRealization rho hcompatA hA₂ S.hres
      (lModuleRelatorRealization_of_extensionAsphericity rho S.hres hasphA)
  h2Dual_surjective :=
    lModuleH2WordFlexible_surjective_of_relatorRealization rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual
      (lModuleRelatorRealization_of_extensionAsphericity rho S.hresDual hasphDual)
  h2Scalar_surjective :=
    lScalarH2WordFlexible_surjective_of_extensionAsphericity
      rho hcompatScalar he hasphScalar
  stokes := hstokes

/-- The coefficient-wise relation/asphericity input before conversion to map surjectivity.
The only fields not finite-extension statements are the common resolver and independent word
Stokes duality. -/
structure LModuleTateAsphericityData
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (he : Odd e) where
  /-- A common resolver for the primal, dual, and mixed square. -/
  squares : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)
  /-- Finite-extension asphericity for the primal module. -/
  asphericityA : LModuleFiniteExtensionAsphericity (A := A) rho
  /-- Finite-extension asphericity for the elementary dual. -/
  asphericityDual : LModuleFiniteExtensionAsphericity (A := ElemDual A) rho
  /-- Finite-extension asphericity for the scalar coefficient. -/
  asphericityScalar : LModuleFiniteExtensionAsphericity (A := ZMod 2) rho
  /-- Independent word-level Stokes duality. -/
  stokes : StokesDuality (fun i ↦ rho (genL i)) wL A

/-- Finite-extension data supplies the coefficient-wise surjectivity precursor. -/
noncomputable def LModuleTateAsphericityData.toPrecursor
    {rho : ContinuousMonoidHom GammaL C}
    {hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a}
    {hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam}
    {hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s}
    {htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s}
    {hA₂ : ∀ a : A, a + a = 0}
    {hq : Even q} {he : Odd e}
    (D : LModuleTateAsphericityData rho hcompatA hcompatDual hcompatScalar
      htriv hA₂ hq he) :
    LModuleTatePrecursor rho hcompatA hcompatDual hcompatScalar
      htriv hA₂ hq he :=
  LModuleTatePrecursor.ofExtensionAsphericity rho hcompatA hcompatDual
    hcompatScalar htriv hA₂ hq he D.squares D.asphericityA
      D.asphericityDual D.asphericityScalar D.stokes

end Precursor

section UniformPrecursor

variable {h q e : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- Compatibility of the source contragredient action with the canonical finite action target. -/
theorem finiteActionHom_elemDual_smul
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction GammaL M] [ContinuousSMul GammaL M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    (g : GammaL) (lam : ElemDual M) :
    g • lam = finiteActionHom (G := GammaL) (M := M) g • lam := by
  apply ElemDual.ext
  intro m
  rw [ElemDual.smul_apply, ElemDual.smul_apply]
  change lam (g⁻¹ • m) = lam (finiteActionHom (G := GammaL) (M := M) g⁻¹ • m)
  rfl

/-- The coefficient-wise precursor specialized to the canonical finite action target used by
`LNoCupTateProvider`.  The target scalar action is installed canonically. -/
noncomputable abbrev LFiniteActionModuleTatePrecursor
    (hq : Even q) (he : Odd e)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction GammaL M] [ContinuousSMul GammaL M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul GammaL (ElemDual M)]
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction GammaL (ZMod 2)] [ContinuousSMul GammaL (ZMod 2)]
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hM₂ : ∀ m : M, m + m = 0) : Prop := by
  let C := Multiplicative (AddAut M)
  let rho : ContinuousMonoidHom GammaL C := finiteActionHom
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatM : ∀ (g : GammaL) (m : M), g • m = rho g • m := fun _ _ ↦ rfl
  let hcompatDual : ∀ (g : GammaL) (lam : ElemDual M), g • lam = rho g • lam :=
    finiteActionHom_elemDual_smul
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  exact LModuleTatePrecursor rho hcompatM hcompatDual hcompatScalar
    htriv hM₂ hq he

/-- The finite-extension/asphericity version of the canonical action-target module data. -/
noncomputable abbrev LFiniteActionModuleTateAsphericityData
    (hq : Even q) (he : Odd e)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction GammaL M] [ContinuousSMul GammaL M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul GammaL (ElemDual M)]
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction GammaL (ZMod 2)] [ContinuousSMul GammaL (ZMod 2)]
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (hM₂ : ∀ m : M, m + m = 0) : Prop := by
  let C := Multiplicative (AddAut M)
  let rho : ContinuousMonoidHom GammaL C := finiteActionHom
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatM : ∀ (g : GammaL) (m : M), g • m = rho g • m := fun _ _ ↦ rfl
  let hcompatDual : ∀ (g : GammaL) (lam : ElemDual M), g • lam = rho g • lam :=
    finiteActionHom_elemDual_smul
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  exact LModuleTateAsphericityData rho hcompatM hcompatDual hcompatScalar
    htriv hM₂ hq he

/-- A uniform all-module precursor for the direct L Tate provider.

For every finite exponent-two source module, it supplies the three map-level surjectivity
statements, a common Heisenberg resolver, and independent word Stokes duality.  Scalar
target-independence is automatic. -/
structure LNoCupTateSurjectiveProviderCore (h q e : ℕ) (hq : Even q) (he : Odd e)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)] where
  /-- The one common scalar orientation. -/
  invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2
  /-- Triviality of the source scalar action. -/
  htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s
  /-- Uniform coefficient-wise relation/source precursors. -/
  modulePrecursor : ∀ (M : Type) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul ((gamma h q : Type)) (ElemDual M)],
    (hM₂ : ∀ m : M, m + m = 0) →
      LFiniteActionModuleTatePrecursor hq he M htriv hM₂

/-- The uniform finite-extension/asphericity precursor.  It makes the relation-theoretic input
visible before conversion to canonical-map surjectivity. -/
structure LNoCupTateAsphericityProviderCore (h q e : ℕ) (hq : Even q) (he : Odd e)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)] where
  /-- The one common scalar orientation. -/
  invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2
  /-- Triviality of the source scalar action. -/
  htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s
  /-- Uniform finite-extension, resolver, and word-duality data. -/
  moduleAsphericity : ∀ (M : Type) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul ((gamma h q : Type)) (ElemDual M)],
    (hM₂ : ∀ m : M, m + m = 0) →
      LFiniteActionModuleTateAsphericityData hq he M htriv hM₂

/-- The public uniform precursor fixes the source scalar topology and action canonically. -/
noncomputable abbrev LNoCupTateSurjectiveProvider
    (h q e : ℕ) (hq : Even q) (he : Odd e)
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)] : Type _ := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  exact LNoCupTateSurjectiveProviderCore h q e hq he

/-- Public finite-extension/asphericity provider with canonical scalar structures. -/
noncomputable abbrev LNoCupTateAsphericityProvider
    (h q e : ℕ) (hq : Even q) (he : Odd e)
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)] : Type _ := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  exact LNoCupTateAsphericityProviderCore h q e hq he

/-- Uniform finite-extension/asphericity data supplies the all-module map-surjectivity
precursor. -/
noncomputable def LNoCupTateAsphericityProviderCore.toSurjectiveProviderCore
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateAsphericityProviderCore h q e hq he) :
    LNoCupTateSurjectiveProviderCore h q e hq he where
  invZ := P.invZ
  htriv := P.htriv
  modulePrecursor := by
    intro M _ _ _ _ _ _ _ _ _ hM₂
    let C := Multiplicative (AddAut M)
    let rho : ContinuousMonoidHom (gamma h q : Type) C := finiteActionHom
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m :=
      fun _ _ ↦ rfl
    let hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
        g • lam = rho g • lam := finiteActionHom_elemDual_smul
    let hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
        g • s = rho g • s :=
      fun g s ↦ (P.htriv g s).trans (smul_zmod2 (rho g) s).symm
    let D := P.moduleAsphericity M hM₂
    change LModuleTateAsphericityData rho hcompatM hcompatDual hcompatScalar
      P.htriv hM₂ hq he at D
    exact D.toPrecursor

/-- The all-module surjectivity precursor produces the established no-cup provider.  The scalar
orientation comparison with the provider's chosen `invZ` follows from uniqueness. -/
noncomputable def lNoCupTateProviderCore_of_surjectiveProviderCore
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateSurjectiveProviderCore h q e hq he) :
    LNoCupTateProviderCore h q e hq he where
  invZ := P.invZ
  htriv := P.htriv
  moduleData := by
    intro M _ _ _ _ _ _ _ _ _ _ _ _ _ hM₂
    let C := Multiplicative (AddAut M)
    let rho : ContinuousMonoidHom (gamma h q : Type) C := finiteActionHom
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatM : ∀ (g : (gamma h q : Type)) (m : M), g • m = rho g • m :=
      fun _ _ ↦ rfl
    let hcompatDual : ∀ (g : (gamma h q : Type)) (lam : ElemDual M),
        g • lam = rho g • lam := finiteActionHom_elemDual_smul
    let hcompatScalar : ∀ (g : (gamma h q : Type)) (s : ZMod 2),
        g • s = rho g • s :=
      fun g s ↦ (P.htriv g s).trans (smul_zmod2 (rho g) s).symm
    let D := P.modulePrecursor M hM₂
    change LModuleTatePrecursor rho hcompatM hcompatDual hcompatScalar
      P.htriv hM₂ hq he at D
    let core := D.core
    exact
      { relator_death := lSource_rel_death rho D.squares.hres
        h0M := lSourceH0Equiv rho hcompatM
        h1M := lSourceH1Equiv rho hcompatM hM₂ D.squares.hres
        h0Dual := lSourceH0Equiv rho hcompatDual
        h1Dual := lSourceH1Equiv rho hcompatDual
          (fun lam : ElemDual M ↦ lam.add_self_eq_zero) D.squares.hresDual
        core := core
        scalar_eq := addEquiv_zmodTwo_unique core.h2Scalar P.invZ
        stokes := D.stokes }

/-- Public wrapper: all-module map surjectivity, one common scalar orientation, and independent
word Stokes duality produce `LNoCupTateProvider`.  Orientation compatibility is automatic. -/
noncomputable def lNoCupTateProvider_of_surjectiveProvider
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateSurjectiveProvider h q e hq he) :
    LNoCupTateProvider h q e hq he := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  change LNoCupTateSurjectiveProviderCore h q e hq he at P
  exact lNoCupTateProviderCore_of_surjectiveProviderCore P

/-- Uniform finite-extension/asphericity data, together with its common orientation and
word-Stokes fields, produces the established no-cup provider. -/
noncomputable def lNoCupTateProviderCore_of_extensionAsphericityProviderCore
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateAsphericityProviderCore h q e hq he) :
    LNoCupTateProviderCore h q e hq he :=
  lNoCupTateProviderCore_of_surjectiveProviderCore P.toSurjectiveProviderCore

/-- Public wrapper from the finite-extension/asphericity provider to `LNoCupTateProvider`. -/
noncomputable def lNoCupTateProvider_of_extensionAsphericityProvider
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateAsphericityProvider h q e hq he) :
    LNoCupTateProvider h q e hq he := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  change LNoCupTateAsphericityProviderCore h q e hq he at P
  exact lNoCupTateProviderCore_of_extensionAsphericityProviderCore P

/-- End-to-end no-field, no-Euler regression through the existing direct assembly. -/
noncomputable def tateDualityG_of_lNoCupTateSurjectiveProvider
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateSurjectiveProvider h q e hq he) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_lNoCupTateProvider
    (lNoCupTateProvider_of_surjectiveProvider P)

/-- End-to-end direct Tate duality from uniform finite-extension/asphericity, common scalar
orientation equality, and independent word Stokes duality. -/
noncomputable def tateDualityG_of_lNoCupTateAsphericityProvider
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateAsphericityProvider h q e hq he) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_lNoCupTateProvider
    (lNoCupTateProvider_of_extensionAsphericityProvider P)

end UniformPrecursor

end

end GQ2.Dyadic.LSquare
