import GQ2.Dyadic.MarkedCore.NPlaneCorrectionKernel

/-!
# All-coordinate N derivative-kernel tuples

The b-coordinate case has trivial extra head terms. Together with the existing
non-b case, it supplies kernel directions for every ordinary coordinate.
-/

namespace GQ2.Dyadic.MarkedCore
open Roe.Labute

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem kernelB_map_commP {H : Type*} [Group H] (f : G →* H) (x y : G) :
    f (commP x y) = commP (f x) (f y) := by simp only [commP, map_mul, map_inv]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem kernelB_comm_reverse (x y : G) : commP x y * commP y x = 1 := by
  simp [commP, mul_assoc]

theorem nPlaneKernelTuple_filteredDerivative_b (n : ℕ) {h : ℕ}
    (letter : Fin (coreRank h) → G) (i : Fin (coreRank h)) (hi : i ≠ 0) :
    nFilteredDerivative (fun j => levelMk G (n + 4) (letter j))
      (fun j => levelMk G (n + 4) (nPlaneKernelTuple n 0 1 i 1 letter nPartner j)) = 1 := by
  let f := levelMk G (n + 4)
  let m := fun j => f (letter j)
  let w := letter 1 ^ (2 ^ (n + 1))
  let p := commP (letter 1) (letter (nPartner i)) ^ (2 ^ n)
  let u₀ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle i (f w)
  let u₁ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle 0 (f p)
  let u₂ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle 1 (f p)
  let K := lambdaImage G (n + 2) (n + 4)
  have hc (x y : G) : commP x y ∈ twoCentralSeries G 2 :=
    commP_mem_twoCentralSeries_add (G := G) (a := 1) (b := 1) (by simp) (by simp)
  have hw : w ∈ twoCentralSeries G (n + 2) :=
    pow_two_pow_mem_twoCentralSeries_succ G (letter 1) (n + 1)
  have hp : p ∈ twoCentralSeries G (n + 2) := by
    simpa only [p, Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add
      (hc (letter 1) (letter (nPartner i))) n
  have hsingle (j : Fin (coreRank h)) (x : G) (hx : x ∈ twoCentralSeries G (n + 2)) :
      ∀ k, (Pi.mulSingle j (f x) : Fin (coreRank h) → levelQuot G (n + 4)) k ∈ K := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [K] using (show f x ∈ lambdaImage G (n + 2) (n + 4) from ⟨x, hx, rfl⟩)
    · simp [hkj, K]
  have hu₀ : ∀ j, u₀ j ∈ K := hsingle i w hw
  have hu₁ : ∀ j, u₁ j ∈ K := hsingle 0 p hp
  have hu₂ : ∀ j, u₂ j ∈ K := hsingle 1 p hp
  have hmul (t z : Fin (coreRank h) → levelQuot G (n + 4))
      (ht : ∀ j, t j ∈ K) (hz : ∀ j, z j ∈ K) :
      nFilteredDerivative m (t * z) = nFilteredDerivative m t * nFilteredDerivative m z := by
    exact nFilteredDerivative_mul (n + 3) (by omega) m t z
      (by simpa [K] using ht) (by simpa [K] using hz)
  have hu01 : ∀ j, (u₀ * u₁) j ∈ K := fun j => K.mul_mem (hu₀ j) (hu₁ j)
  have he : (fun j => f (nPlaneKernelTuple n 0 1 i 1 letter nPartner j)) =
      u₀ * u₁ * u₂ := by
    funext j
    simp only [nPlaneKernelTuple, kernelB_comm_reverse, one_pow]
    have hs : commP (letter 1) (letter 1) = 1 := by simp [commP]
    simp only [hs, one_pow, ite_self, mul_one, u₀, u₁, u₂, Pi.mul_apply,
      Pi.mulSingle_apply, map_mul, apply_ite f, map_one]
    simp only [eq_comm, w, p]
  change nFilteredDerivative m _ = 1
  rw [he, hmul _ _ hu01 hu₂, hmul _ _ hu₀ hu₁]
  have h10 : (1 : Fin (coreRank h)) ≠ 0 := by
    intro heq
    have hh := congrArg Fin.val heq
    simp only [coreVal_one, coreVal_zero] at hh
    omega
  simp only [u₀, u₁, u₂, nFilteredDerivative_mulSingle,
    if_neg hi, if_neg h10, ite_true, one_mul]
  have hbase := nMixedCorrectionWord_with_head_level (letter 0) (letter 1) (letter 1)
    (letter (nPartner i)) n
  have hs : commP (letter 1) (letter 1) = 1 := by simp [commP]
  simp only [kernelB_comm_reverse, hs, one_pow] at hbase
  have hcommone (x : levelQuot G (n + 4)) : commP 1 x = 1 := by simp [commP]
  simpa only [m, f, w, p, map_mul, map_pow, kernelB_map_commP, map_one,
    nPartner_zero, nPartner_one, hcommone, mul_one] using hbase

theorem nPlaneKernelTuple_filteredDerivative_all (n : ℕ) {h : ℕ}
    (letter : Fin (coreRank h) → G) (i v : Fin (coreRank h)) (hi : i ≠ 0) :
    nFilteredDerivative (fun j => levelMk G (n + 4) (letter j))
      (fun j => levelMk G (n + 4) (nPlaneKernelTuple n 0 1 i v letter nPartner j)) = 1 := by
  by_cases hv : v = 1
  · subst v
    exact nPlaneKernelTuple_filteredDerivative_b n letter i hi
  · exact nPlaneKernelTuple_filteredDerivative n letter i v hi hv

theorem nPlaneKernelTuple_mem_correctionKernel_all (n : ℕ) {h : ℕ}
    (m : Fin (coreRank h) → G) (i v : Fin (coreRank h)) (hi : i ≠ 0) :
    nPlaneKernelTuple n 0 1 i v m nPartner ∈ nPlaneCorrectionKernel (n + 3) (by omega) m := by
  constructor
  · intro j; simpa using nPlaneKernelTuple_mem n 0 1 i v m nPartner j
  · exact nPlaneKernelTuple_filteredDerivative_all n m i v hi

#print axioms nPlaneKernelTuple_filteredDerivative_b
#print axioms nPlaneKernelTuple_filteredDerivative_all
#print axioms nPlaneKernelTuple_mem_correctionKernel_all
end GQ2.Dyadic.MarkedCore
