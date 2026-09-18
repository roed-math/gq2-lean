/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Roe.Labute.Levelwise

/-!
# Exact N-word invariance under top-layer slack

Central involutions do not change the literal N-relator: every commutator
ignores central factors, and the head exponent is even when `alpha >= 1`.
In `Q_(k+1)` this applies to arbitrary pointwise changes in `Z_k`.

Consequently replacing correction representatives modulo `lambda_k` preserves
the actual relator value modulo `lambda_(k+1)`, uniformly in every rank and
depth. No assumption that the corrections lie in `lambda_(k-1)` is needed.
This supplies representative-independence, not existence of corrections.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Roe.Labute

section Central
variable {H : Type*} [Group H]

private theorem commP_mul_central_factors (a b z w : H)
    (hz : ∀ x, Commute z x) (hw : ∀ x, Commute w x) :
    commP (a*z) (b*w) = commP a b := by
  rw [← (hz a).eq, ← (hw b).eq, commP_central_left hz,
    commP_central_right hw]

/-- Pure group identity for the actual full N-relator. The head exponent is
even already for `alpha >= 1`; no filtered group structure is needed. -/
theorem nRelWord_central_involution_dress {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (m z : Fin (coreRank h) → H)
    (hz : ∀ i x, Commute (z i) x) (hzsq : ∀ i, z i ^ 2 = 1) :
    nRelWord alpha (fun i => m i * z i) = nRelWord alpha m := by
  have hp : z 0 ^ (2 + 2 ^ alpha) = 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, alpha = a + 1 := ⟨alpha - 1, by omega⟩
    have he : 2 + 2 ^ (a+1) = 2 * (1 + 2 ^ a) := by rw [pow_succ']; ring
    rw [he, pow_mul, hzsq, one_pow]
  have hhead : (m 0 * z 0) ^ (2 + 2 ^ alpha) = m 0 ^ (2 + 2 ^ alpha) := by
    rw [(hz 0 (m 0)).symm.mul_pow, hp, mul_one]
  have hhandle : handleWord (fun j : Fin h => m (handleIdxU j) * z (handleIdxU j))
      (fun j => m (handleIdxV j) * z (handleIdxV j)) =
      handleWord (fun j => m (handleIdxU j)) (fun j => m (handleIdxV j)) := by
    unfold handleWord
    congr 1
    apply List.map_congr_left
    intro j _
    exact commP_mul_central_factors _ _ _ _ (hz _) (hz _)
  unfold nRelWord nWord
  rw [hhead, commP_mul_central_factors _ _ _ _ (hz 0) (hz 1),
    commP_mul_central_factors _ _ _ _ (hz 2) (hz 3), hhandle]

end Central

section Filtered
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every top-layer dressing is invisible in the actual N-relator. -/
theorem nRelWord_zLayer_dress {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m z : Fin (coreRank h) → levelQuot G (k+1))
    (hz : ∀ i, z i ∈ zLayer G k) :
    nRelWord alpha (fun i => m i * z i) = nRelWord alpha m :=
  nRelWord_central_involution_dress halpha m z
    (fun i => zLayer_commute (hz i)) (fun i => zLayer_sq G (hz i))

/-- Correction representatives with the same class modulo the central layer
give exactly the same N-relator value in `Q_(k+1)`, for arbitrary original tuple. -/
theorem nRelWord_correction_zLayer_congr {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m t t' : Fin (coreRank h) → levelQuot G (k+1))
    (hslack : ∀ i, (t i)⁻¹ * t' i ∈ zLayer G k) :
    nRelWord alpha (fun i => m i * t' i) =
      nRelWord alpha (fun i => m i * t i) := by
  have he := nRelWord_zLayer_dress halpha k (fun i => m i * t i)
    (fun i => (t i)⁻¹ * t' i) hslack
  simpa only [mul_assoc, mul_inv_cancel_left] using he

/-- Actual group-level representative replacement preserves the relator
modulo one level deeper. No lower-depth membership assumptions are hidden. -/
theorem nRelWord_correction_level_congr {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m t t' : Fin (coreRank h) → G)
    (hslack : ∀ i, (t i)⁻¹ * t' i ∈ twoCentralSeries G k) :
    levelMk G (k+1) (nRelWord alpha (fun i => m i * t' i)) =
      levelMk G (k+1) (nRelWord alpha (fun i => m i * t i)) := by
  rw [map_nRelWord, map_nRelWord]
  simp only [map_mul]
  apply nRelWord_correction_zLayer_congr halpha k
  intro i
  exact ⟨(t i)⁻¹ * t' i, hslack i, by simp only [map_mul, map_inv]⟩

/-- The defect membership statement is preserved as well, with the same
literal target word, not a modified relation or an altered marking. -/
theorem nRelWord_correction_defect_mem_iff {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m t t' : Fin (coreRank h) → G) (target : G)
    (hslack : ∀ i, (t i)⁻¹ * t' i ∈ twoCentralSeries G k) :
    (nRelWord alpha (fun i => m i * t' i) * target⁻¹ ∈ twoCentralSeries G (k+1)) ↔
      (nRelWord alpha (fun i => m i * t i) * target⁻¹ ∈ twoCentralSeries G (k+1)) := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff]
  change levelMk G (k+1) _ = 1 ↔ levelMk G (k+1) _ = 1
  rw [map_mul, map_mul, nRelWord_correction_level_congr halpha k m t t' hslack]

end Filtered

#print axioms nRelWord_central_involution_dress
#print axioms nRelWord_zLayer_dress
#print axioms nRelWord_correction_zLayer_congr
#print axioms nRelWord_correction_level_congr
#print axioms nRelWord_correction_defect_mem_iff

end GQ2.Dyadic.MarkedCore
