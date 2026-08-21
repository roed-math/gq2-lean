import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicPairing
import GQ2.Dyadic.Instances.EvenMHeadHandlePairFox

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNoGo
open Instances.EvenMHeadHandlePairNormalize

namespace Instances.EvenMHeadHandleHyperbolicFox

variable {h : ℕ} {C A : Type*} [Group C] [Finite C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- The hyperbolic substitution has the selected-handle ramified row. -/
theorem foxD_headHandleHyperbolicW_ram
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h)
    (hA₂ : ∀ v : A, v + v = 0)
    (hs : ∀ v : A, t.σ • v = v)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    foxD ⇑t a E E₂ (headHandleHyperbolicW alpha j) =
      -a (handleV j) +
        (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦
    (foxEval ⇑t a E E₂ ((headHandleHyperbolicNielsen j).backward g)).g⟩
  let b : Generator (2 + 2 * h) → A := fun g ↦
    (foxEval ⇑t a E E₂ ((headHandleHyperbolicNielsen j).backward g)).u
  have hlift : (fun g ↦
      foxEval ⇑t a E E₂ ((headHandleHyperbolicNielsen j).backward g)) =
      foxLift ⇑s b := by
    funext g
    apply WordLift.ext <;> rfl
  have hswild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), s.x i • v = v := by
    intro i v
    change (foxEval ⇑t a E E₂
      ((headHandleHyperbolicNielsen j).backward (.wild i))).g • v = v
    rw [foxEval_g]
    by_cases hi : (Generator.wild i : Generator (2 + 2 * h)) = handleU j
    · rw [hi, headHandleHyperbolicNielsen_backward_handleU,
        PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, mul_smul]
      exact (hs _).trans
        (mem_trivAct.mp (Certificates.trivAct_handleU t hwild j) v)
    · rw [headHandleHyperbolicNielsen_backward_of_ne j (.wild i) hi,
        PWord.evalFin_gen]
      exact pairSwap_wild_trivial t j hs hwild i v
  have hsTau : s.τ = t.τ := by
    change (foxEval ⇑t a E E₂
      ((headHandleHyperbolicNielsen j).backward .tau)).g = t.τ
    rw [headHandleHyperbolicNielsen_backward_tau, foxEval_gen]
    rfl
  have hsSigma : s.σ = t (handleU j) := by
    change (foxEval ⇑t a E E₂
      ((headHandleHyperbolicNielsen j).backward .sigma)).g = t (handleU j)
    rw [headHandleHyperbolicNielsen_backward_sigma, foxEval_gen]
  have hbCoreTwo : b (coreLetter h 2) = a (handleV j) := by
    change (foxEval ⇑t a E E₂
      ((headHandleHyperbolicNielsen j).backward (coreLetter h 2))).u = _
    rw [headHandleHyperbolicNielsen_backward_coreTwo, foxEval_gen]
  rw [headHandleHyperbolicW, foxD_def,
    Certificates.MProcyclic.foxEval_subst, hlift]
  change foxD ⇑s b E E₂ (Words.MCompact.mCompactW alpha h) = _
  rw [Certificates.MCompact.foxD_mCompact_ram s E E₂ hA₂ hswild
      (by simpa [hsTau] using hτfpf)
      (by simpa [hsTau] using hTodd), hsSigma, hbCoreTwo]
  have hUinv : (t (handleU j))⁻¹ • a (handleV j) = a (handleV j) :=
    mem_trivAct.mp (inv_mem (Certificates.trivAct_handleU t hwild j)) _
  have hSinv : t.σ⁻¹ • a (coreLetter h 2) = a (coreLetter h 2) :=
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr hs)) _
  rw [hUinv, hSinv, sub_self, add_zero]

/-- The reflected two-relator family built from the hyperbolic source. -/
def headHandleHyperbolicRawFamily (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha h q : ℕ) (j : Fin h) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree E E₂
    (gammaFam (2 + 2 * h) q (headHandleHyperbolicW alpha j) l)

/-- The hyperbolic source has the same abstract ramified first row as the pair source. -/
theorem isHeadHandlePairRamRow_hyperbolicRaw
    {q alpha : ℕ} (t : Marking (2 + 2 * h) C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hA₂ : ∀ a : A, a + a = 0) (ht : t.TameRelAt q)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hres : ResolverLifts E (WordLift A C)) :
    IsHeadHandlePairRamRow (q := q) t
      (headHandleHyperbolicRawFamily E E₂ alpha h q j) j A := by
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
      foxD_headHandleHyperbolicW_ram t x E E₂ alpha j hA₂ hs hwild hτfpf hTodd]
    simp

#print axioms foxD_headHandleHyperbolicW_ram
#print axioms headHandleHyperbolicRawFamily
#print axioms isHeadHandlePairRamRow_hyperbolicRaw

end Instances.EvenMHeadHandleHyperbolicFox
end
end GQ2.Dyadic

