/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LSourceEulerCard
import GQ2.Dyadic.Instances.LSourceDualityAdapter
import GQ2.Dyadic.Instances.LScalarTrace
import GQ2.Dyadic.Count.HTwoModuleMixed

/-!
# The composed continuous source interface for the L presentation

This file composes the independent reductions already available for the improved L row:

* the target-local flexible resolver construction gives injective module-valued `H²` maps;
* `LocalEulerChar GammaL (2h+1)` upgrades the primal and dual maps to equivalences;
* the flexible scalar map followed by the explicit two-relator trace canonically orients
  scalar `H²`, while `TateDualityG GammaL 2` proves the three continuous cup maps bijective;
* `h0Equiv` and `h1Equiv_gammaR_range` supply the degree-zero and degree-one comparisons.

Coefficient naturality proves the two edge squares, and the mixed cup/Heisenberg identity proves
the middle square.  Consequently `LFlexibleEulerTateSquares` now contains just the common
Heisenberg-target resolver from which all three squares follow.  Neither analytic bundle is
asserted for the abstract group `GammaL`; both remain honest hypotheses on that source group.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

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
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

local instance lSourceHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance lSourceHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

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

/-! ## A common Heisenberg resolver and the three H² equivalences -/

/-- A resolver in the common Heisenberg target restricts to the primal split target. -/
theorem lSource_resolves_primal_of_heis
    (hresHeis : ResolvesAt WL wL (HeisLift A C)) :
    ResolvesAt WL wL (WordLift A C) := by
  let incl : ContinuousMonoidHom (WordLift A C) (HeisLift A C) :=
    ⟨Count.heisPrim (A := A) (C := C), continuous_of_discreteTopology⟩
  exact hresHeis.pullback incl Count.heisPrim_injective

/-- A resolver in the common Heisenberg target restricts to the dual split target. -/
theorem lSource_resolves_dual_of_heis
    (hresHeis : ResolvesAt WL wL (HeisLift A C)) :
    ResolvesAt WL wL (WordLift (ElemDual A) C) := by
  let incl : ContinuousMonoidHom (WordLift (ElemDual A) C) (HeisLift A C) :=
    ⟨Count.heisDual (A := A) (C := C), continuous_of_discreteTopology⟩
  exact hresHeis.pullback incl Count.heisDual_injective

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

/-- Tate duality upgrades the flexible scalar map, while the explicit L word trace fixes its
orientation.  The target action on `ZMod 2` is installed canonically and compatibility follows
from the assumed trivial source action. -/
noncomputable def lScalarH2Equiv_of_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m) :
    H2 GammaL (ZMod 2) ≃+ ZMod 2 :=
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  lScalarH2TraceEquiv rho hcompatScalar hq he hr D htriv

/-! ## The exact mixed-resolver residue -/

/-- After scalar trace compatibility, coefficient naturality, and the mixed Heisenberg identity,
the complete three-square residue is exactly one target-local resolver in the common Heisenberg
target. -/
structure LFlexibleEulerTateSquares : Prop where
  /-- The sole remaining target-local datum. -/
  hresHeis : ResolvesAt WL wL (HeisLift A C)

/-- The primal split resolver extracted from the common Heisenberg resolver. -/
theorem LFlexibleEulerTateSquares.hres (S : LFlexibleEulerTateSquares (h := h) (q := q)
    (e := e) (C := C) (A := A)) : ResolvesAt WL wL (WordLift A C) :=
  lSource_resolves_primal_of_heis S.hresHeis

/-- The dual split resolver extracted from the common Heisenberg resolver. -/
theorem LFlexibleEulerTateSquares.hresDual (S : LFlexibleEulerTateSquares (h := h) (q := q)
    (e := e) (C := C) (A := A)) : ResolvesAt WL wL (WordLift (ElemDual A) C) :=
  lSource_resolves_dual_of_heis S.hresHeis

/-- The `(0,2)` square is forced by the canonical scalar trace orientation. -/
theorem LFlexibleEulerTateSquares.square02_commutes
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC0 (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))
        (stokesUC0_bijective
          (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))).trans
      (scalarDualTransport
        (lModuleH2EquivFlexible_of_localEulerChar rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual hE)
        (lScalarH2Equiv_of_tateDuality rho hq he (lSource_rel_death rho S.hres) D htriv)))
        (stokesH0Map
          (stokes_square₀ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)) x)
      = sourceCup02 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lSourceH0Equiv rho hcompatA).symm x) := by
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  simpa only [lScalarH2Equiv_of_tateDuality] using
    square02_commutes_of_scalarTrace WL genL rho wL hcompatDual hcompatScalar
      (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA) (fun _ ↦ rfl)
      (lModuleH2EquivFlexible_of_localEulerChar rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual hE)
      (fun _ ↦ rfl)
      (lScalarH2TraceEquiv rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)
      (lScalarTraceCompatible rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)

/-- The `(1,1)` square is forced by the same scalar trace and the common Heisenberg resolver. -/
theorem LFlexibleEulerTateSquares.square11_commutes
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC1
          (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i)))
          (heisD1 (A := ElemDual A) (fun i ↦ rho (genL i)) wL))
        (wordH1_target_uc (A := A) (fun i ↦ rho (genL i)) wL
          (lSource_rel_death rho S.hres))).trans
      (scalarDualTransport
        (lSourceH1Equiv rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual)
        (lScalarH2Equiv_of_tateDuality rho hq he (lSource_rel_death rho S.hres) D htriv)))
        (stokesH1Map
          (stokes_square₀ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he))
          (stokes_square₁ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)) x)
      = sourceCup11 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lSourceH1Equiv rho hcompatA hA₂ S.hres).symm x) := by
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  let za := Count.toZ1w rho hcompatA (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hres
  let zb := Count.toZ1w rho hcompatDual (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hresDual
  simpa only [lScalarH2Equiv_of_tateDuality] using
    square11_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatDual hcompatScalar
      (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he) S.hresHeis
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH1Equiv rho hcompatA hA₂ S.hres)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual)
      za zb (fun _ ↦ rfl) (fun _ ↦ rfl)
      (Count.h1Equiv_gammaR_range_H1mk rho hcompatA S.hres hA₂)
      (Count.h1Equiv_gammaR_range_H1mk rho hcompatDual S.hresDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
      (lScalarH2TraceEquiv rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)
      (lScalarTraceCompatible rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)

/-- The `(2,0)` square is forced by the canonical scalar trace orientation. -/
theorem LFlexibleEulerTateSquares.square20_commutes
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC2 (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i))))
        (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
          (heisD0 (A := ElemDual A) (fun i ↦ rho (genL i))))).trans
      (scalarDualTransport
        (lSourceH0Equiv rho hcompatDual)
        (lScalarH2Equiv_of_tateDuality rho hq he (lSource_rel_death rho S.hres) D htriv)))
        (stokesH2Map
          (stokes_square₁ (A := A) (fun i ↦ rho (genL i)) wL
            (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)) x)
      = sourceCup20 (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        ((lModuleH2EquivFlexible_of_localEulerChar rho hcompatA hA₂ S.hres hE).symm x) := by
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
    fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
  simpa only [lScalarH2Equiv_of_tateDuality] using
    square20_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatScalar
      (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatDual) (fun _ ↦ rfl)
      (lModuleH2EquivFlexible_of_localEulerChar rho hcompatA hA₂ S.hres hE)
      (fun _ ↦ rfl)
      (lScalarH2TraceEquiv rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)
      (lScalarTraceCompatible rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)

/--
The exact no-Euler source constructor for the improved L presentation.

Compared with `sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality`, the full
`LocalEulerChar` bundle is replaced by the two coefficient-wise cardinal equalities which it
was used to prove.  The flexible injections make both source `H²` groups finite, the existing
`H¹` comparisons make both source `H¹` groups finite, and the three Tate cup maps are therefore
bijective by the `_of_finite` lemmas.  Scalar `H²` is still constructed from Tate duality alone.

The two displayed cardinal hypotheses are genuine: the current presentation theory gives
injections into the two word `H²` groups, but does not force their common possible excess to
vanish. -/
noncomputable def sourceComparisonPackage_of_lFlexibleH2_card_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hcardA : Nat.card (H2 GammaL A) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL A))
    (hcardDual : Nat.card (H2 GammaL (ElemDual A)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL (ElemDual A)))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) :
    SourceComparisonPackage (fun i ↦ rho (genL i)) wL (lSource_rel_death rho S.hres)
      (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA) (lSourceH1Equiv rho hcompatA hA₂ S.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual) := by
  let h2A := lModuleH2EquivFlexible_of_card_eq rho hcompatA hA₂ S.hres hcardA
  let h2Dual := lModuleH2EquivFlexible_of_card_eq rho hcompatDual
    (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual hcardDual
  let h2Scalar :=
    lScalarH2Equiv_of_tateDuality rho hq he (lSource_rel_death rho S.hres) D htriv
  letI : Finite (H1 GammaL A) :=
    Finite.of_equiv _ (lSourceH1Equiv rho hcompatA hA₂ S.hres).symm.toEquiv
  letI : Finite (H1 GammaL (ElemDual A)) := Finite.of_equiv _
    (lSourceH1Equiv rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual).symm.toEquiv
  letI : Finite (H2 GammaL A) := Finite.of_equiv _ h2A.symm.toEquiv
  letI : Finite (H2 GammaL (ElemDual A)) := Finite.of_equiv _ h2Dual.symm.toEquiv
  refine
    { h2A := h2A
      h2Dual := h2Dual
      h2Scalar := h2Scalar
      cup02_bijective := bijective_cup02_dualEvalG_of_finite D hA₂ htriv
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      cup11_bijective := bijective_cup11_dualEvalG_of_finite D hA₂ htriv
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      cup20_bijective := bijective_cup20_dualEvalG_of_finite D hA₂ htriv
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      square02_commutes := ?_
      square11_commutes := ?_
      square20_commutes := ?_ }
  · letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
      fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
    simpa only [h2Dual, h2Scalar, lScalarH2Equiv_of_tateDuality] using
      square02_commutes_of_scalarTrace WL genL rho wL hcompatDual hcompatScalar
        (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH0Equiv rho hcompatA) (fun _ ↦ rfl) h2Dual (fun _ ↦ rfl)
        (lScalarH2TraceEquiv rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)
        (lScalarTraceCompatible rho hcompatScalar hq he
          (lSource_rel_death rho S.hres) D htriv)
  · letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
      fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
    let za := Count.toZ1w rho hcompatA (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hres
    let zb := Count.toZ1w rho hcompatDual (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) S.hresDual
    simpa only [h2Scalar, lScalarH2Equiv_of_tateDuality] using
      square11_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatDual hcompatScalar
        (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he) S.hresHeis
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH1Equiv rho hcompatA hA₂ S.hres)
        (lSourceH1Equiv rho hcompatDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual)
        za zb (fun _ ↦ rfl) (fun _ ↦ rfl)
        (Count.h1Equiv_gammaR_range_H1mk rho hcompatA S.hres hA₂)
        (Count.h1Equiv_gammaR_range_H1mk rho hcompatDual S.hresDual
          (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
        (lScalarH2TraceEquiv rho hcompatScalar hq he
          (lSource_rel_death rho S.hres) D htriv)
        (lScalarTraceCompatible rho hcompatScalar hq he
          (lSource_rel_death rho S.hres) D htriv)
  · letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    let hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s :=
      fun g s ↦ (htriv g s).trans (smul_zmod2 (rho g) s).symm
    simpa only [h2A, h2Scalar, lScalarH2Equiv_of_tateDuality] using
      square20_commutes_of_scalarTrace WL genL rho wL hcompatA hcompatScalar
        (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he)
        (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
        (lSourceH0Equiv rho hcompatDual) (fun _ ↦ rfl) h2A (fun _ ↦ rfl)
        (lScalarH2TraceEquiv rho hcompatScalar hq he (lSource_rel_death rho S.hres) D htriv)
        (lScalarTraceCompatible rho hcompatScalar hq he
          (lSource_rel_death rho S.hres) D htriv)

/--
The strongest current one-target source constructor for the improved L presentation.

It uses one common Heisenberg resolver, `LocalEulerChar` and `TateDualityG` on the actual source
`GammaL`, the trivial scalar action, and the parity of the improved L presentation.  The three
comparison squares are theorems.  In particular there is no all-level fixed-word resolver and
no separate `H²` cardinality, cup-bijectivity, relator-death, pairing, `H⁰`, `H¹`, or square
hypothesis.
-/
noncomputable def sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) :
    SourceComparisonPackage (fun i ↦ rho (genL i)) wL (lSource_rel_death rho S.hres)
      (lSq_isStokesEndpoint hq he)
      (lSource_dualEval_equivariant rho hcompatA hcompatDual htriv)
      (lSourceH0Equiv rho hcompatA) (lSourceH1Equiv rho hcompatA hA₂ S.hres)
      (lSourceH0Equiv rho hcompatDual)
      (lSourceH1Equiv rho hcompatDual
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual) :=
  sourceComparisonPackage_of_lFlexibleH2_card_tateDuality rho hcompatA hcompatDual hA₂
    (l_card_H2_eq_WordH2_of_localEulerChar rho hcompatA hA₂ S.hres hE)
    (l_card_H2_eq_WordH2_of_localEulerChar rho hcompatDual
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) S.hresDual hE)
    D htriv hq he S

/-- Regression: the composed constructor reaches the exact three Stokes bijections. -/
theorem stokesCohomologyBijections_of_lFlexibleH2_euler_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : GammaL) (lam : ElemDual A), g • lam = rho g • lam)
    (hA₂ : ∀ a : A, a + a = 0)
    (hE : LocalEulerChar GammaL (2 * h + 1))
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (m : ZMod 2), g • m = m)
    (hq : Even q) (he : Odd e)
    (S : LFlexibleEulerTateSquares (h := h) (q := q) (e := e) (C := C) (A := A)) :
    StokesCohomologyBijections (fun i ↦ rho (genL i)) wL A
      (lSource_rel_death rho S.hres) (lSq_isStokesEndpoint hq he) :=
  (sourceComparisonPackage_of_lFlexibleH2_euler_tateDuality rho hcompatA hcompatDual
    hA₂ hE D htriv hq he S).stokesCohomologyBijections

end LComposition

end

end GQ2.Dyadic.LSquare
