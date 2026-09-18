/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicFox

namespace GQ2.Dyadic

/-!
# The raw hyperbolic Fox row with arbitrary sigma action

The hyperbolic word is the pure pair word followed by a source head shear. This
shear fixes every wild letter; it multiplies the head base by the selected wild U
base, which acts trivially. Thus the ramified row is unchanged, without imposing
triviality of the original sigma action.
-/

noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.GammaRPWordNielsen
open Instances.GammaRPWordNielsenElementary
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandleMixed

namespace Instances.EvenMHeadHandleHyperbolicGeneralFox

/-- The source head shear `sigma ↦ sigma * U_j`, fixing all other letters. -/
def headShear {h : ℕ} (j : Fin h) :
    Generator (2 + 2 * h) → PWord (Generator (2 + 2 * h)) :=
  rightMulBackward .sigma (handleU j)

/-- Factor the hyperbolic backward map through the pair exchange and a head shear. -/
theorem hyperbolic_backward_as_headShear {h : ℕ} (j : Fin h)
    (g : Generator (2 + 2 * h)) :
    (headHandleHyperbolicNielsen j).backward g =
      PWord.subst (headShear j) ((headHandlePairNielsen j).backward g) := by
  change _ = PWord.subst (headShear j) (.gen ((headHandlePairSwap j).symm g))
  rw [headHandlePairSwap_symm, PWord.subst_gen]
  by_cases hg : g = handleU j
  · subst g
    rw [headHandleHyperbolicNielsen_backward_handleU,
      headHandlePairSwap_handleU_self]
    simp [headShear, rightMulBackward]
  · rw [headHandleHyperbolicNielsen_backward_of_ne j g hg]
    have hne : headHandlePairSwap j g ≠ .sigma := by
      intro heq
      apply hg
      apply (headHandlePairSwap j).injective
      rw [headHandlePairSwap_handleU_self]
      exact heq
    simp [headShear, rightMulBackward, hne]

/-- The same factorization at the level of the whole wild word. -/
theorem headHandleHyperbolicW_as_headShear {h : ℕ} (alpha : ℕ) (j : Fin h) :
    headHandleHyperbolicW alpha j =
      PWord.subst (headShear j) (headHandlePairCompactW alpha j) := by
  rw [headHandleHyperbolicW, headHandlePairCompactW_eq_nielsenBackward,
    subst_subst]
  congr 1
  funext g
  exact hyperbolic_backward_as_headShear j g

/-- The ramified wild row is valid for arbitrary sigma action. -/
theorem foxD_headHandleHyperbolicW_ram_general
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h)
    (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    foxD ⇑t a E E₂ (headHandleHyperbolicW alpha j) =
      -a (handleV j) +
        (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦
    (foxEval ⇑t a E E₂ (headShear j g)).g⟩
  let b : Generator (2 + 2 * h) → A := fun g ↦
    (foxEval ⇑t a E E₂ (headShear j g)).u
  have hswild (i : Fin (2 + 2 * h + 1)) : s.x i = t.x i := by
    change (foxEval ⇑t a E E₂ (headShear j (.wild i))).g = t (.wild i)
    rw [headShear, rightMulBackward, if_neg (by simp), foxEval_gen]
  have hstau : s.τ = t.τ := by
    change (foxEval ⇑t a E E₂ (headShear j .tau)).g = t .tau
    rw [headShear, rightMulBackward, if_neg (by simp), foxEval_gen]
  have hssigma : s.σ = t.σ * t (handleU j) := by
    change (foxEval ⇑t a E E₂ (headShear j .sigma)).g = t .sigma * t (handleU j)
    rw [headShear, rightMulBackward, if_pos rfl, foxEval_mul, foxEval_gen, foxEval_gen]
    rfl
  have hbV : b (handleV j) = a (handleV j) := by
    change (foxEval ⇑t a E E₂ (headShear j (handleV j))).u = a (handleV j)
    rw [headShear, rightMulBackward, if_neg (by simp [handleV]), foxEval_gen]
  have hbTwo : b (coreLetter h 2) = a (coreLetter h 2) := by
    change (foxEval ⇑t a E E₂ (headShear j (coreLetter h 2))).u = a (coreLetter h 2)
    rw [headShear, rightMulBackward, if_neg (by simp [coreLetter]), foxEval_gen]
  have hlift : (fun g ↦ foxEval ⇑t a E E₂ (headShear j g)) =
      foxLift ⇑s b := by
    funext g
    apply WordLift.ext <;> rfl
  rw [headHandleHyperbolicW_as_headShear, foxD_def, foxEval_subst, hlift]
  change foxD ⇑s b E E₂ (headHandlePairCompactW alpha j) = _
  rw [foxD_headHandlePairCompactW_ram s b E E₂ alpha j hA₂
      (by intro i v; rw [hswild]; exact hwild i v)
      (by simpa [hstau] using hτfpf) (by simpa [hstau] using hTodd),
    hbV, hbTwo, hssigma, mul_inv_rev, mul_smul,
    mem_trivAct.mp (inv_mem (Certificates.trivAct_handleU t hwild j))]

/-- Package the canonical tame row and arbitrary-sigma hyperbolic wild row. -/
theorem isHeadHandlePairRamRow_hyperbolicRaw_general
    {h q alpha : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hA₂ : ∀ a : A, a + a = 0) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hres : ResolverLifts E (WordLift A C)) :
    IsHeadHandlePairRamRow (q := q) t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j) j A := by
  intro x
  funext k
  fin_cases k
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).a = _
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres,
      Certificates.foxD_tameRelW_of_tameRel t E E₂ ht]
    simp
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (headHandleHyperbolicW alpha j))).a = _
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres,
      foxD_headHandleHyperbolicW_ram_general t x E E₂ alpha j hA₂ hwild hτfpf hTodd]
    simp

#print axioms headShear
#print axioms hyperbolic_backward_as_headShear
#print axioms headHandleHyperbolicW_as_headShear
#print axioms foxD_headHandleHyperbolicW_ram_general
#print axioms isHeadHandlePairRamRow_hyperbolicRaw_general

end Instances.EvenMHeadHandleHyperbolicGeneralFox
end
end GQ2.Dyadic

