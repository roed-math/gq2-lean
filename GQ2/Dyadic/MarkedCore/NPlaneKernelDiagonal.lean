import GQ2.Dyadic.MarkedCore.NPlaneKernelTuple

/-!
# Kernel-tuple rows at the current diagonal marking

The coefficient belongs to the current marking, not implicitly to the
original free basis. An exact diagonal coordinate matrix gives the exact
kernel-tuple coefficient 2^(n+1) times that diagonal unit. The initial
unit-power marking satisfies the hypothesis. These statements supply rows
and orientation, not an unrestricted derivative-image theorem.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2 Multiplicative

/-- The tuple may be the image of the original basis under an automorphism;
only its explicit coordinate equations are needed for this conclusion. -/
theorem nPlaneKernelTuple_coordinate_diagonal (N n : ℕ)
    (a b i v : Fin N) (y : Fin N → FreeTwoRank N) (u : Fin N → ℤ_[2]ˣ)
    (hy : ∀ j w, toAdd (freeTwoCoordinate N j (y w)) =
      if j = w then (u w : ℤ_[2]) else 0)
    (partner : Fin N → Fin N) (k j : Fin N) :
    toAdd (freeTwoCoordinate N j (nPlaneKernelTuple n a b i v y partner k)) =
      if k = i ∧ j = v then (2^(n+1) : ℤ_[2]) * (u v : ℤ_[2]) else 0 := by
  have he := nPlaneKernelTuple_character (freeTwoCoordinate N j).toMonoidHom
    n a b i v y partner k
  change toAdd (freeTwoCoordinate N j (nPlaneKernelTuple n a b i v y partner k)) =
    (if k = i then (2^(n+1) : ℤ_[2]) * toAdd (freeTwoCoordinate N j (y v)) else 0) at he
  rw [he, hy]
  by_cases hk : k = i <;> by_cases hj : j = v <;> simp [hk, hj]

theorem nPlaneKernelTuple_current_orientation (α h n : ℕ)
    (a b i v : Fin (coreRank h)) (y : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hy : ∀ w, freeNOrientation α h (y w) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) w))
    (partner : Fin (coreRank h) → Fin (coreRank h))
    (hv : v ≠ 1) (k : Fin (coreRank h)) :
    freeNOrientation α h (nPlaneKernelTuple n a b i v y partner k) = 1 := by
  apply nPlaneKernelTuple_map_eq_one (freeNOrientation α h).toMonoidHom
  change freeNOrientation α h (y v) = 1
  rw [hy, freeNOrientation_gen, if_neg hv]

noncomputable def freeTwoUnitPowerWeights (N : ℕ) (c : Fin N) (κ : ℤ_[2]ˣ) (v : Fin N) : ℤ_[2]ˣ :=
  if v = c then κ else 1

theorem freeTwoUnitPowerMark_coordinate (N : ℕ) (c : Fin N) (κ : ℤ_[2]ˣ)
    (j v : Fin N) :
    toAdd (freeTwoCoordinate N j (freeTwoUnitPowerMark N c κ v)) =
      if j = v then (freeTwoUnitPowerWeights N c κ v : ℤ_[2]) else 0 := by
  have he := freeTwoUnitPowerEquiv_character_gen N c v κ (freeTwoCoordinate N j)
  rw [freeTwoUnitPowerEquiv_gen] at he
  rw [he]
  simp only [freeTwoCoordinate_gen, toAdd_ofAdd, freeTwoUnitPowerWeights]
  by_cases hv : v = c
  · subst v
    by_cases hj : j = c <;> simp [hj, Ne.symm]
  · by_cases hj : j = v <;> simp [hv, hj, Ne.symm]

theorem freeTwoUnitPowerMark_orientation (α h : ℕ) (c : Fin (coreRank h))
    (hc : c ≠ 1) (κ : ℤ_[2]ˣ) (v : Fin (coreRank h)) :
    freeNOrientation α h (freeTwoUnitPowerMark (coreRank h) c κ v) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) v) := by
  rw [← freeTwoUnitPowerEquiv_gen]
  exact freeNOrientation_unitPowerEquiv α h c hc κ _

/-- Initial current-basis kernel coefficients, with the actual kappa weight
retained whenever v is the originally scaled generator. -/
theorem nPlaneKernelTuple_unitPower_coordinate (N n : ℕ)
    (a b i v c : Fin N) (κ : ℤ_[2]ˣ) (partner : Fin N → Fin N) (k j : Fin N) :
    toAdd (freeTwoCoordinate N j
      (nPlaneKernelTuple n a b i v (freeTwoUnitPowerMark N c κ) partner k)) =
      if k = i ∧ j = v then (2^(n+1) : ℤ_[2]) *
        (freeTwoUnitPowerWeights N c κ v : ℤ_[2]) else 0 :=
  nPlaneKernelTuple_coordinate_diagonal N n a b i v _ _
    (freeTwoUnitPowerMark_coordinate N c κ) partner k j

theorem nPlaneKernelTuple_unitPower_orientation (α h n : ℕ)
    (a b i v c : Fin (coreRank h)) (hc : c ≠ 1) (κ : ℤ_[2]ˣ)
    (partner : Fin (coreRank h) → Fin (coreRank h))
    (hv : v ≠ 1) (k : Fin (coreRank h)) :
    freeNOrientation α h (nPlaneKernelTuple n a b i v
      (freeTwoUnitPowerMark (coreRank h) c κ) partner k) = 1 :=
  nPlaneKernelTuple_current_orientation α h n a b i v _
    (freeTwoUnitPowerMark_orientation α h c hc κ) partner hv k

#print axioms nPlaneKernelTuple_coordinate_diagonal
#print axioms nPlaneKernelTuple_current_orientation
#print axioms freeTwoUnitPowerWeights
#print axioms freeTwoUnitPowerMark_coordinate
#print axioms freeTwoUnitPowerMark_orientation
#print axioms nPlaneKernelTuple_unitPower_coordinate
#print axioms nPlaneKernelTuple_unitPower_orientation

end GQ2.Dyadic.MarkedCore
