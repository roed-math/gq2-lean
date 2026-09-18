import GQ2.Dyadic.MarkedCore.FreeNOrientation
import GQ2.Dyadic.MarkedCore.Certificate

/-!
# Crossed-derivation annihilation of the actual N-word defect

Exact canonical orientation values make every crossed derivation kill the
N word, for every handle rank. Consequently the defect between two such
markings is also killed. No basis, filtration or reachability conclusion is
assumed or produced: this establishes the necessary image condition only.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 FoxH

theorem nRelWord_wordLift_eq_one_of_base {α h : ℕ} (hα : 1 ≤ α)
    (m : Fin (coreRank h) → WordLift ℤ_[2] ℤ_[2]ˣ)
    (hm : ∀ i, (m i).g = coreMark 1 (nUnit α) 1 1 i) :
    nRelWord α m = 1 := by
  have he : m = nMasterMark α (fun i => (m i).u) := by
    funext i
    apply WordLift.ext
    · rfl
    · exact hm i
  rw [he]
  exact nRelWord_nMasterMark hα _

theorem nRelWord_crossed_eq_one {G : Type*} [Group G] {α h : ℕ} (hα : 1 ≤ α)
    (m : Fin (coreRank h) → G) (Φ : G →* WordLift ℤ_[2] ℤ_[2]ˣ)
    (hm : ∀ i, (Φ (m i)).g = coreMark 1 (nUnit α) 1 1 i) :
    Φ (nRelWord α m) = 1 := by
  rw [map_nRelWord]
  exact nRelWord_wordLift_eq_one_of_base hα _ hm

theorem nRelWord_defect_crossed_eq_one {G : Type*} [Group G] {α h : ℕ}
    (hα : 1 ≤ α) (m y : Fin (coreRank h) → G)
    (Φ : G →* WordLift ℤ_[2] ℤ_[2]ˣ)
    (hm : ∀ i, (Φ (m i)).g = coreMark 1 (nUnit α) 1 1 i)
    (hy : ∀ i, (Φ (y i)).g = coreMark 1 (nUnit α) 1 1 i) :
    Φ (nRelWord α y * (nRelWord α m)⁻¹) = 1 := by
  rw [map_mul, map_inv, nRelWord_crossed_eq_one hα y Φ hy,
    nRelWord_crossed_eq_one hα m Φ hm, inv_one, mul_one]

private theorem freeNOrientation_gen_coreMark (α h : ℕ) (i : Fin (coreRank h)) :
    freeNOrientation α h (freeTwoRankGen (coreRank h) i) = coreMark 1 (nUnit α) 1 1 i := by
  rw [freeNOrientation_gen]
  have hi : (i : ℕ) = 1 ↔ i = 1 := by
    rw [← coreVal_one (h := h)]
    exact Fin.val_injective.eq_iff
  by_cases hz : (i : ℕ) = 0
  · have hn : i ≠ 1 := by intro he; rw [he, coreVal_one] at hz; omega
    simp [coreMark, hz, hn]
  · simp [coreMark, hz, hi]

/-- The desired crossed-defect condition is automatic from the current
marking's exact orientation rows, even before assuming it is a basis. -/
theorem freeNRelatorDefect_crossed {α h : ℕ} (hα : 1 ≤ α)
    (y : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hy : ∀ i, freeNOrientation α h (y i) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (Φ : (FreeTwoRank (coreRank h) : Type) →* WordLift ℤ_[2] ℤ_[2]ˣ)
    (hΦ : ∀ x, (Φ x).g = freeNOrientation α h x) :
    Φ (nRelWord α y * (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹) = 1 := by
  apply nRelWord_defect_crossed_eq_one hα _ y Φ
  · intro i
    rw [hΦ, freeNOrientation_gen_coreMark]
  · intro i
    rw [hΦ, hy, freeNOrientation_gen_coreMark]

#print axioms nRelWord_wordLift_eq_one_of_base
#print axioms nRelWord_crossed_eq_one
#print axioms nRelWord_defect_crossed_eq_one
#print axioms freeNRelatorDefect_crossed

end GQ2.Dyadic.MarkedCore
