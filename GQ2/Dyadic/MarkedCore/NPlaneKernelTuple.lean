import GQ2.Dyadic.MarkedCore.FreeNOrientation
import GQ2.Roe.Labute.MixedPowerCongruence

/-!
# Actual relative-correction tuples: depth and ordinary rows

The five increments are multiplied in the displayed order, so repeated slots
accumulate rather than overwrite each other. All entries have the required
filtration depth, and their only ordinary row is the requested one. This file
does not assert a derivative-kernel identity or an N-boundary lift.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Multiplicative
open GQ2.Roe.Labute

section Tuple
variable {I G : Type*} [DecidableEq I] [Group G]

def nPlaneKernelTuple (n : ℕ) (a b i v : I) (letter : I → G) (partner : I → I)
    (k : I) : G :=
  (if k = i then letter v ^ (2^(n+1)) else 1) *
  (if k = a then commP (letter v) (letter (partner i)) ^ (2^n) else 1) *
  (if k = b then commP (letter v) (letter (partner i)) ^ (2^n) else 1) *
  (if k = partner v then
    (commP (letter v) (letter (partner i)) *
      commP (letter (partner i)) (letter b)) ^ (2^n) else 1) *
  (if k = partner (partner i) then commP (letter v) (letter b) ^ (2^n) else 1)

/-- Exact multiplicative rows in every abelian target, including coincident
slots. No topological or rank assumption is needed for this algebraic identity. -/
theorem nPlaneKernelTuple_map {Q : Type*} [CommGroup Q] (f : G →* Q)
    (n : ℕ) (a b i v : I) (letter : I → G) (partner : I → I) (k : I) :
    f (nPlaneKernelTuple n a b i v letter partner k) =
      if k = i then f (letter v) ^ (2^(n+1)) else 1 := by
  have hcomm (x y : G) : f (commP x y) = 1 := by simp [commP, mul_comm]
  simp only [nPlaneKernelTuple, map_mul, apply_ite f, map_one, map_pow, hcomm,
    one_pow, ite_self, mul_one]

theorem nPlaneKernelTuple_character
    (f : G →* Multiplicative ℤ_[2]) (n : ℕ) (a b i v : I)
    (letter : I → G) (partner : I → I) (k : I) :
    toAdd (f (nPlaneKernelTuple n a b i v letter partner k)) =
      if k = i then (2^(n+1) : ℤ_[2]) * toAdd (f (letter v)) else 0 := by
  rw [nPlaneKernelTuple_map]
  split_ifs
  · simp only [toAdd_pow, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  · rfl

theorem nPlaneKernelTuple_map_eq_one {Q : Type*} [CommGroup Q] (f : G →* Q)
    (n : ℕ) (a b i v : I) (letter : I → G) (partner : I → I)
    (hv : f (letter v) = 1) (k : I) :
    f (nPlaneKernelTuple n a b i v letter partner k) = 1 := by
  rw [nPlaneKernelTuple_map, hv, one_pow]
  exact ite_self _

end Tuple

section Depth
variable {I G : Type*} [DecidableEq I] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

private theorem comm_mem_two (x y : G) : commP x y ∈ twoCentralSeries G 2 :=
  commP_mem_twoCentralSeries_add (G := G) (a := 1) (b := 1)
    (by simp) (by simp)

/-- Uniform depth for every entry of the actual multiplicative tuple. -/
theorem nPlaneKernelTuple_mem (n : ℕ) (a b i v : I)
    (letter : I → G) (partner : I → I) (k : I) :
    nPlaneKernelTuple n a b i v letter partner k ∈ twoCentralSeries G (n+2) := by
  have hp : ∀ x : G, x ∈ twoCentralSeries G 2 →
      x^(2^n) ∈ twoCentralSeries G (n+2) := by
    intro x hx
    simpa only [Nat.add_comm] using pow_two_pow_mem_twoCentralSeries_add hx n
  have hi : letter v ^ (2^(n+1)) ∈ twoCentralSeries G (n+2) :=
    pow_two_pow_mem_twoCentralSeries_succ G (letter v) (n+1)
  have hq := hp _ (comm_mem_two (letter v) (letter (partner i)))
  have hr := hp _ ((twoCentralSeries G 2).mul_mem
    (comm_mem_two (letter v) (letter (partner i)))
    (comm_mem_two (letter (partner i)) (letter b)))
  have hs := hp _ (comm_mem_two (letter v) (letter b))
  have hite (P : Prop) [Decidable P] (x : G) (hx : x ∈ twoCentralSeries G (n+2)) :
      (if P then x else 1) ∈ twoCentralSeries G (n+2) := by
    split_ifs
    · exact hx
    · exact Subgroup.one_mem _
  exact (twoCentralSeries G (n+2)).mul_mem
    ((twoCentralSeries G (n+2)).mul_mem
      ((twoCentralSeries G (n+2)).mul_mem
        ((twoCentralSeries G (n+2)).mul_mem (hite _ _ hi) (hite _ _ hq))
        (hite _ _ hq)) (hite _ _ hr)) (hite _ _ hs)

end Depth

/-- For the actual free N orientation, the excluded ordinary letter is b.
No alpha bound is needed here because the generator value is explicit. -/
theorem nPlaneKernelTuple_freeNOrientation (α h n : ℕ)
    (a b i v : Fin (coreRank h)) (partner : Fin (coreRank h) → Fin (coreRank h))
    (hv : v ≠ 1) (k : Fin (coreRank h)) :
    freeNOrientation α h
      (nPlaneKernelTuple n a b i v (freeTwoRankGen (coreRank h)) partner k) = 1 := by
  apply nPlaneKernelTuple_map_eq_one (freeNOrientation α h).toMonoidHom
  change freeNOrientation α h (freeTwoRankGen (coreRank h) v) = 1
  rw [freeNOrientation_gen, if_neg hv]

#print axioms nPlaneKernelTuple
#print axioms nPlaneKernelTuple_map
#print axioms nPlaneKernelTuple_character
#print axioms nPlaneKernelTuple_map_eq_one
#print axioms nPlaneKernelTuple_mem
#print axioms nPlaneKernelTuple_freeNOrientation

end GQ2.Dyadic.MarkedCore
