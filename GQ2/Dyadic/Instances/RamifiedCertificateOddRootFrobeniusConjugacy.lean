/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateOddRootFrobeniusCompactness

/-!
# Finite odd-root Frobenius as local conjugacy

For a primitive `m`-th root `zeta`, one absolute Galois element squares every `m`-th root if and
only if `zeta` and `zeta ^ 2` are conjugate over `Q_2`. Thus the finite-level input from the
compactness theorem is exactly equality of these two minimal polynomials. It suffices to prove
this for one primitive root at each odd order.

No local conjugacy assertion is assumed or proved here.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

theorem mem_oddRootFrobeniusSet_iff_primitive {m : ℕ} [NeZero m]
    {zeta : ℚ̄₂} (hzeta : IsPrimitiveRoot zeta m)
    (g : Kummer.GaloisGroup ℚ_[2]) :
    g ∈ oddRootFrobeniusSet m ↔ g • zeta = zeta ^ 2 := by
  constructor
  · intro hg
    exact hg zeta hzeta.pow_eq_one
  · intro hg xi hxi
    obtain ⟨i, _, rfl⟩ := hzeta.eq_pow_of_pow_eq_one hxi
    change g zeta = zeta ^ 2 at hg
    change g (zeta ^ i) = (zeta ^ i) ^ 2
    rw [map_pow, hg]
    calc
      (zeta ^ 2) ^ i = zeta ^ (2 * i) := (pow_mul zeta 2 i).symm
      _ = zeta ^ (i * 2) := by rw [Nat.mul_comm]
      _ = (zeta ^ i) ^ 2 := pow_mul zeta i 2

theorem oddRootFrobeniusSet_nonempty_iff_primitive {m : ℕ} [NeZero m]
    {zeta : ℚ̄₂} (hzeta : IsPrimitiveRoot zeta m) :
    (oddRootFrobeniusSet m).Nonempty ↔
      ∃ g : Kummer.GaloisGroup ℚ_[2], g • zeta = zeta ^ 2 := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (mem_oddRootFrobeniusSet_iff_primitive hzeta g).mp hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (mem_oddRootFrobeniusSet_iff_primitive hzeta g).mpr hg⟩

theorem oddRootFrobeniusSet_nonempty_iff_isConjRoot {m : ℕ} [NeZero m]
    {zeta : ℚ̄₂} (hzeta : IsPrimitiveRoot zeta m) :
    (oddRootFrobeniusSet m).Nonempty ↔ IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  rw [oddRootFrobeniusSet_nonempty_iff_primitive hzeta]
  constructor
  · rintro ⟨g, hg⟩
    change g zeta = zeta ^ 2 at hg
    simpa only [hg] using (isConjRoot_of_algEquiv (R := ℚ_[2]) zeta g)
  · intro hconj
    obtain ⟨g, hg⟩ := hconj.symm.exists_algEquiv
    exact ⟨g, hg⟩

theorem finite_cyclotomic_lifts_iff_primitive_conjugacy :
    (∀ m : ℕ, Odd m → (oddRootFrobeniusSet m).Nonempty) ↔
      ∀ (m : ℕ) (_hm : Odd m) (zeta : ℚ̄₂),
        IsPrimitiveRoot zeta m → IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  constructor
  · intro H m hm zeta hzeta
    letI : NeZero m := ⟨hm.pos.ne'⟩
    exact (oddRootFrobeniusSet_nonempty_iff_isConjRoot hzeta).mp (H m hm)
  · intro H m hm
    letI : NeZero m := ⟨hm.pos.ne'⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄₂ m
    exact (oddRootFrobeniusSet_nonempty_iff_isConjRoot hzeta).mpr (H m hm zeta hzeta)

theorem finite_cyclotomic_lifts_iff_exists_primitive_conjugacy :
    (∀ m : ℕ, Odd m → (oddRootFrobeniusSet m).Nonempty) ↔
      ∀ m : ℕ, Odd m → ∃ zeta : ℚ̄₂,
        IsPrimitiveRoot zeta m ∧ IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  constructor
  · intro H m hm
    letI : NeZero m := ⟨hm.pos.ne'⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄₂ m
    exact ⟨zeta, hzeta, (oddRootFrobeniusSet_nonempty_iff_isConjRoot hzeta).mp (H m hm)⟩
  · rintro H m hm
    letI : NeZero m := ⟨hm.pos.ne'⟩
    obtain ⟨zeta, hzeta, hconj⟩ := H m hm
    exact (oddRootFrobeniusSet_nonempty_iff_isConjRoot hzeta).mpr hconj

theorem exists_squaresOddRoots_iff_primitive_conjugacy :
    (∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g) ↔
      ∀ (m : ℕ) (_hm : Odd m) (zeta : ℚ̄₂),
        IsPrimitiveRoot zeta m → IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  rw [exists_squaresOddRoots_iff_finite_cyclotomic_lifts,
    finite_cyclotomic_lifts_iff_primitive_conjugacy]

theorem exists_squaresOddRoots_iff_exists_primitive_conjugacy :
    (∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g) ↔
      ∀ m : ℕ, Odd m → ∃ zeta : ℚ̄₂,
        IsPrimitiveRoot zeta m ∧ IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  rw [exists_squaresOddRoots_iff_finite_cyclotomic_lifts,
    finite_cyclotomic_lifts_iff_exists_primitive_conjugacy]

/-- The remaining local cyclotomic input, stated solely as a minimal-polynomial equality. -/
theorem exists_squaresOddRoots_iff_minpoly_square :
    (∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g) ↔
      ∀ m : ℕ, Odd m → ∃ zeta : ℚ̄₂,
        IsPrimitiveRoot zeta m ∧ minpoly ℚ_[2] zeta = minpoly ℚ_[2] (zeta ^ 2) := by
  simpa only [isConjRoot_def] using exists_squaresOddRoots_iff_exists_primitive_conjugacy

#print axioms mem_oddRootFrobeniusSet_iff_primitive
#print axioms oddRootFrobeniusSet_nonempty_iff_primitive
#print axioms oddRootFrobeniusSet_nonempty_iff_isConjRoot
#print axioms finite_cyclotomic_lifts_iff_primitive_conjugacy
#print axioms finite_cyclotomic_lifts_iff_exists_primitive_conjugacy
#print axioms exists_squaresOddRoots_iff_primitive_conjugacy
#print axioms exists_squaresOddRoots_iff_exists_primitive_conjugacy
#print axioms exists_squaresOddRoots_iff_minpoly_square

end
end GQ2.Dyadic
