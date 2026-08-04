/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxAdjoint
import GQ2.Dyadic.Count.H3UniversalRelationLift
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# From the finite adjoint identity to the universal degree-three interface

The canonical bar contraction is not equivariant, so its raw adjoint bar defect need not vanish
on three-cocycles.  The correct object to factor through `d³` is the combined reconstruction
residual after choosing the universal relation coefficient.  This file defines that residual,
identifies it with the three explicit terms in the transposed chain identity, and constructs
`SqFiniteInputUniversalDegreeThreeComparisonAt` from precisely its `d³`-factorization.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

private abbrev SqAdjointInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

private abbrev SqAdjointInputFour (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup)

/-- The combined fixed-quotient residual that must factor through `d³`.  It contains the
refined input, the `d²H₂†` term, and the finite-support universal correction chosen by the
compatible universal syzygy. -/
def sqFiniteInputUniversalAdjointReconstructionResidual
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    SqAdjointInputThree h V →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup) :=
  let m := sqOpenQuotientMarking h W
  let heval := sqOpenQuotientFreeEvaluation_surjective h W
  sqFiniteModTwoBarRefineThree h hWV +
    (finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)).comp
      ((finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval).toAddMonoidHom.comp
        (sqFiniteModTwoBarRefineThree h hWV)) +
    (finiteUniversalRelationThreeFiniteSupportCorrection m heval).toAddMonoidHom.comp
      (U.universalSyzygy.coordinate W)

/-- The combined residual is exactly the sum of the `H₃†d³` term, the raw non-invariance
defect, and the universal finite-support defect.  In particular, truncating the unrestricted
universal adjoint kills only the last term; it does not make the raw bar defect factor through
`d³`. -/
theorem sqFiniteInputUniversalAdjointReconstructionResidual_eq_explicitDefects
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : SqAdjointInputThree h V) :
    sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c =
      finiteBarForwardReverseHomotopyThreeCochainAdjoint
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (finiteModTwoBarDThree ((DSq h : Type) ⧸ W.toSubgroup)
            (sqFiniteModTwoBarRefineThree h hWV c)) +
        finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) := by
  let m := sqOpenQuotientMarking h W
  let heval := sqOpenQuotientFreeEvaluation_surjective h W
  let cW := sqFiniteModTwoBarRefineThree h hWV c
  let u := U.universalSyzygy.coordinate W c
  have hid := finiteBarForwardReverseHomotopyThree_cochain_identity_with_defects
    m heval cW u
  funext a
  have ha := congrFun hid a
  simp only [sqFiniteInputUniversalAdjointReconstructionResidual,
    AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
  let A : ZMod 2 := finiteBarForwardReverseHomotopyThreeCochainAdjoint m heval
    (finiteModTwoBarDThree ((DSq h : Type) ⧸ W.toSubgroup) cW) a
  let D : ZMod 2 := finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval cW) a
  let F : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval u a
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect m heval cW a
  let T : ZMod 2 := finiteUniversalThreeAdjointFiniteSupportDefect m heval cW u a
  let C : ZMod 2 := cW a
  change C + D + F = A + B + T
  change A + D + F + B + T = C at ha
  calc
    C + D + F = (A + D + F + B + T) + D + F := by rw [ha]
    _ = A + B + T + (D + D) + (F + F) := by abel
    _ = A + B + T := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp

/-- On an input three-cocycle, the `H₃†d³` term vanishes after refinement.  The combined
residual is therefore exactly the raw bar defect plus the universal finite-support defect. -/
theorem sqFiniteInputUniversalAdjointReconstructionResidual_of_cocycle
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : SqAdjointInputThree h V)
    (hc : finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0) :
    sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c =
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) := by
  rw [sqFiniteInputUniversalAdjointReconstructionResidual_eq_explicitDefects]
  have hrefine := DFunLike.congr_fun (finiteModTwoBarDThree_refine h hWV) c
  simp only [AddMonoidHom.comp_apply] at hrefine
  rw [hc, map_zero] at hrefine
  rw [hrefine, map_zero, zero_add]

/-- The exact quotient-coordinate condition needed from a compatible universal syzygy: on
three-cocycles, its universal defect cancels the raw non-invariance defect.  Requiring the
universal defect itself to vanish would be too strong in the wrong direction unless the raw bar
defect also vanished. -/
def SqFiniteInputUniversalAdjointCocycleCancellationAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) : Prop :=
  ∀ c : SqAdjointInputThree h V,
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) = 0

/-- Cocycle cancellation is precisely enough for the kernel inclusion required by the linear
factorization constructor. -/
theorem sqFiniteInputUniversalAdjoint_ker_le_ker_of_cocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV) :
    LinearMap.ker
        ((finiteModTwoBarDThree
          ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2) ≤
      LinearMap.ker
        ((sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : finiteModTwoBarDThree
      ((DSq h : Type) ⧸ V.toSubgroup) c = 0 := by
    simpa using hc
  simpa using (sqFiniteInputUniversalAdjointReconstructionResidual_of_cocycle
    U W hWV c hc').trans (hcancel c hc')

/-- The exact residual factorization needed by the existing universal degree-three comparison
interface.  The field is deliberately named for its role in that interface; it need not equal
the raw non-invariance defect of `H₂†`. -/
structure SqFiniteInputUniversalAdjointResidualFactorizationAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) where
  barDefect :
    SqAdjointInputFour h V →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  factor : ∀ c,
    barDefect (finiteModTwoBarDThree _ c) =
      sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c

/-- Linear algebra turns the kernel criterion for the combined residual into the required
factorization.  First descend through `C³ / ker d³ ≃ range d³`, then extend the resulting map
from `range d³` to all of `C⁴`. -/
noncomputable def
    SqFiniteInputUniversalAdjointResidualFactorizationAt.of_ker_le_ker
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hker :
      LinearMap.ker
          ((finiteModTwoBarDThree
            ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2) ≤
        LinearMap.ker
          ((sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2)) :
    SqFiniteInputUniversalAdjointResidualFactorizationAt U W hWV := by
  let d := (finiteModTwoBarDThree
    ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2
  let E :=
    (sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2
  let onRange : LinearMap.range d →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup) :=
    ((LinearMap.ker d).liftQ E hker).comp
      d.quotKerEquivRange.symm.toLinearMap
  let hExtend := LinearMap.exists_extend onRange
  let D := Classical.choose hExtend
  have hD := Classical.choose_spec hExtend
  refine {
    barDefect := D.toAddMonoidHom
    factor := fun c => ?_
  }
  change D (d c) = E c
  let dc : LinearMap.range d := ⟨d c, ⟨c, rfl⟩⟩
  calc
    D (d c) = D ((LinearMap.range d).subtype dc) := rfl
    _ = onRange dc := LinearMap.congr_fun hD dc
    _ = E c := by
      simp [onRange, dc]

/-- A factorization of the combined residual through `d³` fills all fields of
`SqFiniteInputUniversalDegreeThreeComparisonAt` at the chosen finite quotient. -/
def SqFiniteInputUniversalDegreeThreeComparisonAt.ofAdjointResidualFactorization
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (F : SqFiniteInputUniversalAdjointResidualFactorizationAt U W hWV) :
    SqFiniteInputUniversalDegreeThreeComparisonAt h V where
  W := W
  le := hWV
  homotopyTwo :=
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)).toAddMonoidHom.comp
        (sqFiniteModTwoBarRefineThree h hWV)
  universalSyzygy := U.universalSyzygy
  universalRelationError :=
    (finiteUniversalRelationThreeFiniteSupportCorrection
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)).toAddMonoidHom
  boundaryDefect := U.boundaryDefect
  barDefect := F.barDefect
  boundary_universalSyzygy := U.boundary_universalSyzygy
  reconstruct c := by
    rw [F.factor]
    funext a
    simp only [sqFiniteInputUniversalAdjointReconstructionResidual,
      AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
    let C : ZMod 2 := sqFiniteModTwoBarRefineThree h hWV c a
    let D : ZMod 2 := finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)
      (finiteBarForwardReverseHomotopyTwoCochainAdjoint
        (sqOpenQuotientMarking h W)
        (sqOpenQuotientFreeEvaluation_surjective h W)
        (sqFiniteModTwoBarRefineThree h hWV c)) a
    let R : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)
      (U.universalSyzygy.coordinate W c) a
    change D + R + (C + D + R) = C
    calc
      D + R + (C + D + R) = C + (D + D) + (R + R) := by abel
      _ = C := by
        rw [ZModModule.add_self, ZModModule.add_self]
        simp

/-- Final fixed-quotient constructor: a compatible universal syzygy whose coordinate cancels
the raw bar defect on cocycles automatically supplies the residual factorization and hence the
full existing degree-three comparison interface. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.ofAdjointCocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV) :
    SqFiniteInputUniversalDegreeThreeComparisonAt h V :=
  .ofAdjointResidualFactorization U W hWV
    (.of_ker_le_ker U W hWV
      (sqFiniteInputUniversalAdjoint_ker_le_ker_of_cocycleCancellation
        U W hWV hcancel))

end

end GQ2.Dyadic.Count
