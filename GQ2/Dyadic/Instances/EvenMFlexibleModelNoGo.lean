/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMAdaptedBoundaryNoGo
import GQ2.Dyadic.Instances.SourceAnalyticCoreTransportRN

/-!
# Equivalent even-M model sources preserve the pivot obstruction

W341 showed that changing the tame/pro-2 boundary on the standard compact-M or Mpc source
cannot evade the distinguished-`C` pivot.  W342 made it possible to transport the entire
boundary-independent analytic core to another, equivalent source group before attaching a new
boundary.  This module closes that apparent escape route as well.

Any `FlexibleModelSourceRN` for the standard compact-M or displayed-Mpc candidate transports
back along its source equivalence to an adapted boundary on the standard candidate group.
Pro-`p` kernels are preserved by this transport, so W341 applies.  Thus an arbitrary equivalent
model source still forces the compact-M unit pivot or the Mpc exact-level pivot.

Consequently neither boundary replacement, presentation rewrites, nor an equivalent source
model can repair a missing field pivot while retaining the same standard candidate group.  A
general repair must instead exclude the obstructed selector case or change the actual candidate
group selected for that field.
-/

namespace GQ2.Dyadic.Instances.EvenMFlexibleModelNoGo

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.EvenMAdaptedBoundaryNoGo
open GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
open GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
open GQ2.Dyadic.Instances.EvenMMobileSourceModel
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc

/-- Precomposition by a continuous group equivalence preserves a pro-`p` kernel. -/
theorem isProP_ker_comp_continuousMulEquiv
    {p : ℕ} {A B C : Type*}
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    (e : ContinuousMulEquiv A B) (f : ContinuousMonoidHom B C)
    (h : IsProP p f.toMonoidHom.ker) :
    IsProP p (f.comp (e : ContinuousMonoidHom A B)).toMonoidHom.ker := by
  let phi : ContinuousMonoidHom f.toMonoidHom.ker
      (f.comp (e : ContinuousMonoidHom A B)).toMonoidHom.ker :=
    { toFun := fun x => ⟨e.symm x.1, by
          change f (e (e.symm x.1)) = 1
          rw [e.apply_symm_apply]
          exact x.2⟩
      map_one' := by ext; exact map_one e.symm
      map_mul' := fun x y => by ext; exact map_mul e.symm x.1 y.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact e.symm.continuous_toFun.comp continuous_subtype_val }
  have hsurj : Function.Surjective phi := by
    intro y
    let x : f.toMonoidHom.ker := ⟨e y.1, y.2⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact e.symm_apply_apply y.1
  exact SectionThree.isProP_of_surjective phi.toMonoidHom phi.continuous_toFun hsurj h

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Even a presentation-independent compact-M model source forces the canonical field pivot. -/
theorem mCompact_flexibleModelSource_forces_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)))
    (F : FlexibleModelSourceRN (2 + 2 * h) (qOf K FF) (mCompactW alpha h)
      (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
      (fieldCoreNuZtwo B) (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha 0 h := by
  let S0 := F.source.transport F.equivCandidate
    (scalarActionZmodTwo (GammaR (2 + 2 * h) (qOf K FF) (mCompactW alpha h)))
    (scalarActionZmodTwo_continuousSMul
      (GammaR (2 + 2 * h) (qOf K FF) (mCompactW alpha h)))
    (scalarActionZmodTwo_triv
      (GammaR (2 + 2 * h) (qOf K FF) (mCompactW alpha h)))
  let A := mCompactAnalyticCoreRN (alpha := alpha) (h := h) (q := qOf K FF)
    halpha (qOf_ne_zero K FF) (even_qOf K FF)
    (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)
  let D : SourceAnalyticBoundaryRN A :=
    { tame := S0.tame
      pro2 := S0.pro2
      compat := S0.compat
      surj := S0.surj
      ker_pro2 := S0.ker_pro2
      determinant := S0.determinant }
  have hwild : IsProP 2 D.tame.toMonoidHom.ker :=
    isProP_ker_comp_continuousMulEquiv F.equivCandidate F.source.tame
      F.wild_isProP
  exact mCompact_mobileBoundary_forces_cPivot B FF halpha e0 D hwild

/-- The same presentation-independent statement holds for arbitrary displayed Mpc data. -/
theorem mpc_flexibleModelSource_forces_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)))
    (F : FlexibleModelSourceRN (2 + 2 * h) (qOf K FF)
      (mpcW alpha r (p epsilon r) d.display h)
      (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
      (fieldCoreNuZtwo B) (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha r h := by
  let R := mpcW alpha r (p epsilon r) d.display h
  let S0 := F.source.transport F.equivCandidate
    (scalarActionZmodTwo (GammaR (2 + 2 * h) (qOf K FF) R))
    (scalarActionZmodTwo_continuousSMul (GammaR (2 + 2 * h) (qOf K FF) R))
    (scalarActionZmodTwo_triv (GammaR (2 + 2 * h) (qOf K FF) R))
  let A := mpcAnalyticCoreRN (alpha := alpha) (r := r) (h := h) (q := qOf K FF)
    (epsilon := epsilon) d halpha hr (even_qOf K FF)
    (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)
  let D : SourceAnalyticBoundaryRN A :=
    { tame := S0.tame
      pro2 := S0.pro2
      compat := S0.compat
      surj := S0.surj
      ker_pro2 := S0.ker_pro2
      determinant := S0.determinant }
  have hwild : IsProP 2 D.tame.toMonoidHom.ker :=
    isProP_ker_comp_continuousMulEquiv F.equivCandidate F.source.tame
      F.wild_isProP
  exact mpc_mobileBoundary_forces_cPivot B FF d halpha hr e0 D hwild

#print axioms isProP_ker_comp_continuousMulEquiv
#print axioms mCompact_flexibleModelSource_forces_cPivot
#print axioms mpc_flexibleModelSource_forces_cPivot

end

end GQ2.Dyadic.Instances.EvenMFlexibleModelNoGo
