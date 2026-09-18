/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Roe.Labute.StageLemma.Congruence

/-!
# The actual N relator derivative at every two-central depth

This is a group identity in Q_(k+1), for k at least three and corrections
in the image of lambda_(k-1). It identifies the derivative of the actual
arbitrary-rank N relator, including both head brackets. It does not assert
surjectivity of that derivative or construct a restricted correction.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Roe.Labute

section Filtered
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable (k : ℕ)

theorem nFiltered_square (hk : 3 ≤ k) (a : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (a * v)^2 = a^2 * (v^2 * commP v a) := by
  have hw : ∀ i : Fin 3, (![v, 1, 1] : Fin 3 → levelQuot G (k + 1)) i ∈
      lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i <;> simp [hv]
  have he := d0Word_mul_lambdaImage k hk a 1 1 hw
  simpa [d0Word, dbarWordR0, commP, mul_assoc] using he

theorem nFiltered_fourth (hk : 3 ≤ k) (a : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (a * v)^4 = a^4 := by
  have hw : ∀ i : Fin 3, (![1, v, 1] : Fin 3 → levelQuot G (k + 1)) i ∈
      lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i <;> simp [hv]
  have he := d0Word_mul_lambdaImage k hk 1 a 1 hw
  simpa [d0Word, dbarWordR0, commP] using he

theorem nFiltered_commutator (hk : 3 ≤ k) (a b : levelQuot G (k + 1))
    {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1))
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (a*u) (b*v) = commP a b * (commP u b * commP v a) := by
  have hw : ∀ i : Fin 3, (![1, u, v] : Fin 3 → levelQuot G (k + 1)) i ∈
      lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i <;> simp [hu, hv]
  have he := d0Word_mul_lambdaImage k hk 1 a b hw
  simp only [d0Word, dbarWordR0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, one_mul, mul_one, one_pow] at he
  rw [nFiltered_fourth k hk a hu] at he
  have hc : commP (1 : levelQuot G (k+1)) 1 = 1 := by simp [commP]
  rw [hc, one_mul] at he
  change a^4 * commP (a*u) (b*v) = a^4 * commP a b * (commP u b * commP v a) at he
  apply mul_left_cancel (a := a^4)
  simpa only [mul_assoc] using he

private theorem mul_central_pair {A : Type*} [Group A] (a b z w : A)
    (hz : z*b=b*z) : (a*z)*(b*w)=(a*b)*(z*w) := by
  calc
    (a*z)*(b*w) = a*(z*b)*w := by group
    _ = a*(b*z)*w := by rw [hz]
    _ = (a*b)*(z*w) := by group

theorem nFiltered_head_power (hk : 3 ≤ k) (alpha : ℕ) (halpha : 2 ≤ alpha)
    (a : levelQuot G (k+1)) {v : levelQuot G (k+1)}
    (hv : v ∈ lambdaImage G (k-1) (k+1)) :
    (a*v)^(2+2^alpha) = a^(2+2^alpha) * (v^2 * commP v a) := by
  have hi : (a*v)^(2^alpha) = a^(2^alpha) := by
    obtain ⟨d, rfl⟩ : ∃ d, alpha=2+d := ⟨alpha-2, by omega⟩
    rw [pow_add, show (2:ℕ)^2=4 by norm_num, pow_mul, pow_mul,
      nFiltered_fourth k hk a hv]
  have hz : v^2 * commP v a ∈ zLayer G k :=
    (zLayer G k).mul_mem (sq_mem_zLayer k hk hv) (commP_mem_zLayer k hk hv a)
  rw [pow_add, nFiltered_square k hk a hv, hi, mul_assoc,
    (zLayer_commute hz (a^(2^alpha))).eq, ← mul_assoc, ← pow_add]

/-- The literal compact derivative, in the fixed repository order. -/
def nFilteredCoreDerivative {A : Type*} [Group A]
    (a b c d u v w z : A) : A :=
  (u^2 * commP u a) * (commP u b * commP v a) *
    (commP w d * commP z c)

theorem nFiltered_nWord (hk : 3 ≤ k) (alpha : ℕ) (halpha : 2 ≤ alpha)
    (a b c d : levelQuot G (k+1)) {u v w z : levelQuot G (k+1)}
    (hu : u ∈ lambdaImage G (k-1) (k+1))
    (hv : v ∈ lambdaImage G (k-1) (k+1))
    (hw : w ∈ lambdaImage G (k-1) (k+1))
    (hz : z ∈ lambdaImage G (k-1) (k+1)) :
    nWord alpha (a*u) (b*v) (c*w) (d*z) =
      nWord alpha a b c d * nFilteredCoreDerivative a b c d u v w z := by
  have h0 : u^2 * commP u a ∈ zLayer G k :=
    (zLayer G k).mul_mem (sq_mem_zLayer k hk hu) (commP_mem_zLayer k hk hu a)
  have h1 : commP u b * commP v a ∈ zLayer G k :=
    (zLayer G k).mul_mem (commP_mem_zLayer k hk hu b) (commP_mem_zLayer k hk hv a)
  unfold nWord nFilteredCoreDerivative
  rw [nFiltered_head_power k hk alpha halpha a hu,
    nFiltered_commutator k hk a b hu hv, nFiltered_commutator k hk c d hw hz,
    mul_central_pair _ _ _ _ ((zLayer_commute h0 (commP a b)).eq),
    mul_central_pair _ _ _ _ ((zLayer_commute ((zLayer G k).mul_mem h0 h1) (commP c d)).eq)]

/-- The central handle correction, with the same fixed handle order. -/
def nFilteredHandleDerivative {A : Type*} [Group A] {h : ℕ}
    (u v t s : Fin h → A) : A :=
  ((List.finRange h).map fun j => commP (t j) (v j) * commP (s j) (u j)).prod

theorem nFiltered_handleWord (hk : 3 ≤ k) {h : ℕ}
    (u v t s : Fin h → levelQuot G (k+1))
    (ht : ∀ j, t j ∈ lambdaImage G (k-1) (k+1))
    (hs : ∀ j, s j ∈ lambdaImage G (k-1) (k+1)) :
    handleWord (fun j => u j*t j) (fun j => v j*s j) =
      handleWord u v * nFilteredHandleDerivative u v t s := by
  unfold handleWord nFilteredHandleDerivative
  generalize List.finRange h = l
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, nFiltered_commutator k hk (u j) (v j) (ht j) (hs j)]
    exact mul_central_pair _ _ _ _
      ((zLayer_commute ((zLayer G k).mul_mem
        (commP_mem_zLayer k hk (ht j) (v j))
        (commP_mem_zLayer k hk (hs j) (u j))) _).eq)

/-- The actual arbitrary-rank derivative word. The first head bracket is
`[t0,m0]`, in addition to the paired bracket `[t0,m1]`. -/
def nFilteredDerivative {A : Type*} [Group A] {h : ℕ}
    (m t : Fin (coreRank h) → A) : A :=
  nFilteredCoreDerivative (m 0) (m 1) (m 2) (m 3) (t 0) (t 1) (t 2) (t 3) *
    nFilteredHandleDerivative (fun j => m (handleIdxU j)) (fun j => m (handleIdxV j))
      (fun j => t (handleIdxU j)) (fun j => t (handleIdxV j))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem nFilteredCoreDerivative_mem (hk : 3 ≤ k)
    (a b c d : levelQuot G (k+1)) {u v w z : levelQuot G (k+1)}
    (hu : u ∈ lambdaImage G (k-1) (k+1))
    (hv : v ∈ lambdaImage G (k-1) (k+1))
    (hw : w ∈ lambdaImage G (k-1) (k+1))
    (hz : z ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredCoreDerivative a b c d u v w z ∈ zLayer G k := by
  exact (zLayer G k).mul_mem
    ((zLayer G k).mul_mem
      ((zLayer G k).mul_mem (sq_mem_zLayer k hk hu) (commP_mem_zLayer k hk hu a))
      ((zLayer G k).mul_mem (commP_mem_zLayer k hk hu b) (commP_mem_zLayer k hk hv a)))
    ((zLayer G k).mul_mem (commP_mem_zLayer k hk hw d) (commP_mem_zLayer k hk hz c))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem nFilteredDerivative_mem (hk : 3 ≤ k) {h : ℕ}
    (m t : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredDerivative m t ∈ zLayer G k := by
  apply (zLayer G k).mul_mem
    (nFilteredCoreDerivative_mem k hk _ _ _ _ (ht 0) (ht 1) (ht 2) (ht 3))
  apply (zLayer G k).list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact (zLayer G k).mul_mem
    (commP_mem_zLayer k hk (ht _) _) (commP_mem_zLayer k hk (ht _) _)

/-- Actual N-relator shift, uniformly in rank, alpha and filtration depth. -/
theorem nFiltered_nRelWord (hk : 3 ≤ k) (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ}
    (m t : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1)) :
    nRelWord alpha (fun i => m i*t i) = nRelWord alpha m * nFilteredDerivative m t := by
  unfold nRelWord nFilteredDerivative
  rw [nFiltered_nWord k hk alpha halpha _ _ _ _ (ht 0) (ht 1) (ht 2) (ht 3),
    nFiltered_handleWord k hk _ _ _ _ (fun j => ht (handleIdxU j))
      (fun j => ht (handleIdxV j))]
  exact mul_central_pair _ _ _ _ ((zLayer_commute
    (nFilteredCoreDerivative_mem k hk _ _ _ _ (ht 0) (ht 1) (ht 2) (ht 3)) _).eq)

#print axioms nFiltered_square
#print axioms nFiltered_fourth
#print axioms nFiltered_commutator
#print axioms nFiltered_head_power
#print axioms nFilteredCoreDerivative
#print axioms nFiltered_nWord
#print axioms nFilteredHandleDerivative
#print axioms nFiltered_handleWord
#print axioms nFilteredDerivative
#print axioms nFilteredCoreDerivative_mem
#print axioms nFilteredDerivative_mem
#print axioms nFiltered_nRelWord

end Filtered
end GQ2.Dyadic.MarkedCore
