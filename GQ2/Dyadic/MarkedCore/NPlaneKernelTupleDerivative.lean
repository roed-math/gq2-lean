import GQ2.Dyadic.MarkedCore.NPlaneMixedGroupKernel
import GQ2.Dyadic.MarkedCore.NPlaneKernelTuple
import GQ2.Dyadic.MarkedCore.NPlaneFilteredDerivativeLinear
import GQ2.Dyadic.MarkedCore.NPlaneFilteredSlots

/-!
# The actual relative N correction tuple is in the derivative kernel

The conclusion is about the actual arbitrary-rank filtered N derivative.
Repeated slots are accumulated as ordered products. This does not assert a
derivative image theorem or a convergent relator-normalizing automorphism.
-/

namespace GQ2.Dyadic.MarkedCore

open Roe.Labute

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem kernelTuple_map_commP {H : Type*} [Group H] (f : G →* H) (x y : G) :
    f (commP x y) = commP (f x) (f y) := by simp only [commP, map_mul, map_inv]

/-- Uniform relative kernel correction in the actual N derivative. Only the
ordinary correction slot `i=0` and the ordinary letter `v=1` are excluded. -/
theorem nPlaneKernelTuple_filteredDerivative (n : ℕ) {h : ℕ}
    (letter : Fin (coreRank h) → G) (i v : Fin (coreRank h))
    (hi : i ≠ 0) (hv : v ≠ 1) :
    nFilteredDerivative (fun j => levelMk G (n + 4) (letter j))
      (fun j => levelMk G (n + 4) (nPlaneKernelTuple n 0 1 i v letter nPartner j)) = 1 := by
  let f := levelMk G (n + 4)
  let m := fun j => f (letter j)
  let w := letter v ^ (2 ^ (n + 1))
  let p := commP (letter v) (letter (nPartner i)) ^ (2 ^ n)
  let r := (commP (letter v) (letter (nPartner i)) *
    commP (letter (nPartner i)) (letter 1)) ^ (2 ^ n)
  let s := commP (letter v) (letter 1) ^ (2 ^ n)
  let u₀ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle i (f w)
  let u₁ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle 0 (f p)
  let u₂ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle 1 (f p)
  let u₃ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle (nPartner v) (f r)
  let u₄ : Fin (coreRank h) → levelQuot G (n + 4) := Pi.mulSingle (nPartner (nPartner i)) (f s)
  let K := lambdaImage G (n + 2) (n + 4)
  have hc (x y : G) : commP x y ∈ twoCentralSeries G 2 :=
    commP_mem_twoCentralSeries_add (G := G) (a := 1) (b := 1)
      (by simp) (by simp)
  have hw : w ∈ twoCentralSeries G (n + 2) :=
    pow_two_pow_mem_twoCentralSeries_succ G (letter v) (n + 1)
  have hp : p ∈ twoCentralSeries G (n + 2) := by
    simpa only [p, Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add
      (hc (letter v) (letter (nPartner i))) n
  have hr : r ∈ twoCentralSeries G (n + 2) := by
    simpa only [r, Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add
      ((twoCentralSeries G 2).mul_mem (hc (letter v) (letter (nPartner i)))
        (hc (letter (nPartner i)) (letter 1))) n
  have hs : s ∈ twoCentralSeries G (n + 2) := by
    simpa only [s, Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add
      (hc (letter v) (letter 1)) n
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
  have hu₃ : ∀ j, u₃ j ∈ K := hsingle (nPartner v) r hr
  have hu₄ : ∀ j, u₄ j ∈ K := hsingle (nPartner (nPartner i)) s hs
  have hmul (t z : Fin (coreRank h) → levelQuot G (n + 4))
      (ht : ∀ j, t j ∈ K) (hz : ∀ j, z j ∈ K) :
      nFilteredDerivative m (t * z) = nFilteredDerivative m t * nFilteredDerivative m z := by
    exact nFilteredDerivative_mul (n + 3) (by omega) m t z
      (by simpa [K] using ht) (by simpa [K] using hz)
  have hu01 : ∀ j, (u₀ * u₁) j ∈ K := fun j => K.mul_mem (hu₀ j) (hu₁ j)
  have hu012 : ∀ j, (u₀ * u₁ * u₂) j ∈ K := fun j => K.mul_mem (hu01 j) (hu₂ j)
  have hu0123 : ∀ j, (u₀ * u₁ * u₂ * u₃) j ∈ K := fun j => K.mul_mem (hu012 j) (hu₃ j)
  have he : (fun j => f (nPlaneKernelTuple n 0 1 i v letter nPartner j)) =
      u₀ * u₁ * u₂ * u₃ * u₄ := by
    funext j
    simp only [nPlaneKernelTuple, u₀, u₁, u₂, u₃, u₄, Pi.mul_apply,
      Pi.mulSingle_apply, map_mul, apply_ite f, map_one]
    simp only [eq_comm, w, p, r, s]
  change nFilteredDerivative m _ = 1
  rw [he, hmul _ _ hu0123 hu₄, hmul _ _ hu012 hu₃, hmul _ _ hu01 hu₂,
    hmul _ _ hu₀ hu₁]
  have hvp : nPartner v ≠ 0 := by
    intro heq
    have hh := congrArg nPartner heq
    rw [nPartner_involutive v, nPartner_zero] at hh
    exact hv hh
  have hip : nPartner (nPartner i) ≠ 0 := by rwa [nPartner_involutive i]
  have h10 : (1 : Fin (coreRank h)) ≠ 0 := by
    intro heq
    have hh := congrArg Fin.val heq
    simp only [coreVal_one, coreVal_zero] at hh
    omega
  simp only [u₀, u₁, u₂, u₃, u₄, nFilteredDerivative_mulSingle,
    if_neg hi, if_neg h10, if_neg hvp, if_neg hip, ite_true, one_mul]
  simpa only [m, f, w, p, r, s, map_mul, map_pow, kernelTuple_map_commP,
    nPartner_involutive v, nPartner_involutive (nPartner i),
    nPartner_zero, nPartner_one] using
    nMixedCorrectionWord_with_head_level (letter 0) (letter 1) (letter v)
      (letter (nPartner i)) n

/-- Applying this actual kernel tuple leaves the literal N relator unchanged
at the next correction level, uniformly in alpha and in the number of handles.
The topological assumptions are those of the existing actual-relator shift
theorem; no hypothesis that the old relator vanishes is required. -/
theorem nPlaneKernelTuple_nRelWord [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (alpha : ℕ) (halpha : 2 ≤ alpha) (n : ℕ) {h : ℕ}
    (letter : Fin (coreRank h) → G) (i v : Fin (coreRank h))
    (hi : i ≠ 0) (hv : v ≠ 1) :
    levelMk G (n + 4)
        (nRelWord alpha (fun j => letter j * nPlaneKernelTuple n 0 1 i v letter nPartner j)) =
      levelMk G (n + 4) (nRelWord alpha letter) := by
  rw [map_nRelWord, map_nRelWord]
  simp only [map_mul]
  rw [nFiltered_nRelWord (n + 3) (by omega) alpha halpha _ _ (fun j => ?_)]
  · rw [nPlaneKernelTuple_filteredDerivative n letter i v hi hv, mul_one]
  · refine ⟨nPlaneKernelTuple n 0 1 i v letter nPartner j, ?_, rfl⟩
    simpa using nPlaneKernelTuple_mem n 0 1 i v letter nPartner j

#print axioms nPlaneKernelTuple_filteredDerivative
#print axioms nPlaneKernelTuple_nRelWord

end GQ2.Dyadic.MarkedCore
