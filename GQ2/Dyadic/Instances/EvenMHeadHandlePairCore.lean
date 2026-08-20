/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
import GQ2.Dyadic.Instances.GammaRCorePresentationNielsen

/-!
# The pro-2 core of the strict-handle pair source

The full pair exchange from W346 is an involutive Nielsen transformation at the pro-2
presentation level, even though it is deliberately not wild-preserving at the corrected source
level.  Consequently the pair-swapped word presents the same Demushkin core `DM alpha h`.

The transported marking sends the new tame head to the chosen `U`-handle, the displaced
`U`-wild letter to the old `C`, and the old `x₂` letter to the chosen `V`-handle.  This is the
precise structural effect required by the strict handle normal form.

The final constructor records the remaining normalization honestly.  The promoted `U` row must
be the unramified generator and every transported wild row must vanish.  This is one uniform
all-wild condition; it does not fix a nilpotency class, a field, or a handle count.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairCore

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.EvenMHeadHandleSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.GammaRPWordNielsen
open GQ2.Dyadic.Instances.GammaRPWordNielsenElementary
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-- The simultaneous pair exchange as one alphabet equivalence. -/
def headHandlePairSwap {h : ℕ} (j : Fin h) :
    Generator (2 + 2 * h) ≃ Generator (2 + 2 * h) :=
  (headHandleSwap j).trans (tailHandleSwap j)

/-- The pair exchange as a syntactic Nielsen pair. -/
def headHandlePairNielsen {h : ℕ} (j : Fin h) :
    PWordNielsenPair (2 + 2 * h) :=
  PWordNielsenPair.ofEquiv (headHandlePairSwap j)

@[simp] theorem headHandlePairSwap_tau {h : ℕ} (j : Fin h) :
    headHandlePairSwap j .tau = .tau := by
  simp [headHandlePairSwap]

@[simp] theorem headHandlePairSwap_sigma {h : ℕ} (j : Fin h) :
    headHandlePairSwap j .sigma = handleU j := by
  simp [headHandlePairSwap]

@[simp] theorem headHandlePairSwap_handleU_self {h : ℕ} (j : Fin h) :
    headHandlePairSwap j (handleU j) = .sigma := by
  simp [headHandlePairSwap]

@[simp] theorem headHandlePairSwap_coreTwo {h : ℕ} (j : Fin h) :
    headHandlePairSwap j (coreLetter h 2) = handleV j := by
  simp [headHandlePairSwap]

@[simp] theorem headHandlePairSwap_handleV_self {h : ℕ} (j : Fin h) :
    headHandlePairSwap j (handleV j) = coreLetter h 2 := by
  simp [headHandlePairSwap]

theorem headHandlePairSwap_involutive {h : ℕ} (j : Fin h) :
    Function.Involutive (headHandlePairSwap j) := by
  intro g
  cases g with
  | sigma => simp
  | tau => simp
  | wild i =>
      by_cases hU : Generator.wild i = handleU j
      · rw [hU]
        simp
      · by_cases hV : Generator.wild i = handleV j
        · rw [hV]
          simp
        · by_cases hC : Generator.wild i = coreLetter h 2
          · rw [hC]
            simp
          · have hSigma : Generator.wild i ≠ Generator.sigma := by simp
            have hh : headHandleSwap j (Generator.wild i) = Generator.wild i := by
              exact Equiv.swap_apply_of_ne_of_ne hSigma hU
            have ht : tailHandleSwap j (Generator.wild i) = Generator.wild i := by
              exact Equiv.swap_apply_of_ne_of_ne hC hV
            rw [headHandlePairSwap]
            change tailHandleSwap j
                (headHandleSwap j (tailHandleSwap j (headHandleSwap j (.wild i)))) = .wild i
            rw [hh, ht, hh, ht]

theorem headHandlePairSwap_symm {h : ℕ} (j : Fin h) :
    (headHandlePairSwap j).symm = headHandlePairSwap j := by
  ext g
  apply (headHandlePairSwap j).injective
  rw [(headHandlePairSwap j).apply_symm_apply]
  exact (headHandlePairSwap_involutive j g).symm

@[simp] theorem headHandlePairNielsen_forward_tau {h : ℕ} (j : Fin h) :
    (headHandlePairNielsen j).forward .tau = .gen .tau := by
  change PWord.gen (headHandlePairSwap j .tau) = PWord.gen .tau
  rw [headHandlePairSwap_tau]

@[simp] theorem headHandlePairNielsen_backward_tau {h : ℕ} (j : Fin h) :
    (headHandlePairNielsen j).backward .tau = .gen .tau := by
  change PWord.gen ((headHandlePairSwap j).symm .tau) = PWord.gen .tau
  rw [headHandlePairSwap_symm, headHandlePairSwap_tau]

theorem headHandlePairCompactW_eq_nielsenBackward {alpha h : ℕ} (j : Fin h) :
    headHandlePairCompactW alpha j =
      PWord.subst (headHandlePairNielsen j).backward (mCompactW alpha h) := by
  rw [headHandlePairCompactW, headHandleCompactW,
    GQ2.Dyadic.Certificates.MProcyclic.subst_subst]
  apply congrArg (fun f => PWord.subst f (mCompactW alpha h))
  funext g
  change PWord.gen (tailHandleSwap j (headHandleSwap j g)) =
    PWord.gen ((headHandlePairSwap j).symm g)
  rw [headHandlePairSwap_symm]
  rfl

private theorem corePresentation_cast_mark
    {n : ℕ} {R S : PWord (Generator n)} {P : ProfiniteGrp}
    (hRS : R = S) (C : CorePresentation n R P) :
    (hRS ▸ C).mark = C.mark := by
  subst S
  rfl

/-- The pair-swapped word presents the same pro-2 core, with the marking transported through
the full pair exchange. -/
noncomputable def headHandlePairCorePresentation
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h) :
    CorePresentation (2 + 2 * h) (headHandlePairCompactW alpha j) (DM alpha h) :=
  (headHandlePairCompactW_eq_nielsenBackward (alpha := alpha) j).symm ▸
    (MCompactCore.mCorePresentation alpha h halpha).ofNielsen
      (headHandlePairNielsen j)
      (headHandlePairNielsen_forward_tau j)
      (headHandlePairNielsen_backward_tau j)

@[simp] theorem headHandlePairCorePresentation_mark
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h)
    (g : Generator (2 + 2 * h)) :
    (headHandlePairCorePresentation alpha h halpha j).mark g =
      (MCompactCore.mCorePresentation alpha h halpha).mark (headHandlePairSwap j g) := by
  rw [headHandlePairCorePresentation, corePresentation_cast_mark]
  rfl

@[simp] theorem headHandlePairCorePresentation_mark_sigma
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h) :
    (headHandlePairCorePresentation alpha h halpha j).mark .sigma =
      dmGen alpha h (handleIdxU j) := by
  rw [headHandlePairCorePresentation_mark, headHandlePairSwap_sigma]
  change (MCompactCore.mCorePresentation alpha h halpha).mark
    (.wild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩) = _
  rw [MCompactCore.mCorePresentation_mark_wild]
  rw [show PilotN.nWildIdx h
    ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩ = handleIdxU j by
      apply Fin.ext
      simp only [PilotN.nWildIdx, handleIdxU_val]
      split <;> omega]
  exact MCompactCore.mUntwist_apply_ne _ _ _ (by rw [handleIdxU_val]; omega)

@[simp] theorem headHandlePairCorePresentation_mark_handleU
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h) :
    (headHandlePairCorePresentation alpha h halpha j).mark (handleU j) =
      dmC alpha h := by
  rw [headHandlePairCorePresentation_mark, headHandlePairSwap_handleU_self,
    MCompactCore.mCorePresentation_mark_sigma, dmC]

@[simp] theorem headHandlePairCorePresentation_mark_coreTwo
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h) :
    (headHandlePairCorePresentation alpha h halpha j).mark (coreLetter h 2) =
      dmGen alpha h (handleIdxV j) := by
  rw [headHandlePairCorePresentation_mark, headHandlePairSwap_coreTwo]
  change (MCompactCore.mCorePresentation alpha h halpha).mark
    (.wild ⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩) = _
  rw [MCompactCore.mCorePresentation_mark_wild]
  rw [show PilotN.nWildIdx h
    ⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩ = handleIdxV j by
      apply Fin.ext
      simp only [PilotN.nWildIdx, handleIdxV_val]
      split <;> omega]
  exact MCompactCore.mUntwist_apply_ne _ _ _ (by rw [handleIdxV_val]; omega)

/-- The exact remaining normalization condition after promoting one handle pair.  It is a
single all-wild row statement and is independent of degree, level, and nilpotency class. -/
def HeadHandlePairWildNormalized
    {alpha h : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) : Prop :=
  ∀ i : Fin (2 + 2 * h + 1),
    nuP ((headHandlePairCorePresentation alpha h halpha j).mark (.wild i)) = 1

/-- Once the promoted handle is the unramified row and all displaced wild rows vanish, the
pair-swapped word has the complete table-free pro-2 core packet. -/
noncomputable def headHandlePairFlexibleCore
    {alpha h : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hU : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne)
    (hWild : HeadHandlePairWildNormalized halpha j nuP) :
    FlexibleCoreLeavesRN (2 + 2 * h) (headHandlePairCompactW alpha j)
      (DM alpha h) nuP where
  presentation := headHandlePairCorePresentation alpha h halpha j
  nu_sigma := by rw [headHandlePairCorePresentation_mark_sigma]; exact hU
  nu_wild := hWild

#print axioms headHandlePairSwap_involutive
#print axioms headHandlePairCompactW_eq_nielsenBackward
#print axioms headHandlePairCorePresentation
#print axioms headHandlePairCorePresentation_mark_sigma
#print axioms headHandlePairCorePresentation_mark_handleU
#print axioms headHandlePairCorePresentation_mark_coreTwo
#print axioms HeadHandlePairWildNormalized
#print axioms headHandlePairFlexibleCore

end

end GQ2.Dyadic.Instances.EvenMHeadHandlePairCore

