/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueFrobeniusLift

/-!
# Compactness for odd-root Frobenius lifts

An absolute Galois element squaring every odd-order root of unity exists if and only if such an
element exists separately at every finite odd cyclotomic level. No compatibility between the
finite choices is required: the corresponding loci are closed, directed under divisibility, and
compactness supplies one element in their intersection.

Consequently the remaining arithmetic input is finite-level existence, not a compatible inverse
system of choices. This module makes no such finite-level existence assertion.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The closed locus of absolute Galois elements acting by square Frobenius on all
`m`-th roots of unity. -/
def oddRootFrobeniusSet (m : ℕ) : Set (Kummer.GaloisGroup ℚ_[2]) :=
  {g | ∀ zeta : ℚ̄₂, zeta ^ m = 1 → g • zeta = zeta ^ 2}

private theorem root_ne_zero {m : ℕ} (hm : 0 < m) {zeta : ℚ̄₂}
    (hzeta : zeta ^ m = 1) : zeta ≠ 0 := by
  intro hz
  rw [hz, zero_pow hm.ne'] at hzeta
  exact zero_ne_one hzeta

theorem oddRootFrobeniusSet_isClosed (m : ℕ) (hm : 0 < m) :
    IsClosed (oddRootFrobeniusSet m) := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [oddRootFrobeniusSet]
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro zeta
  by_cases hzeta : zeta ^ m = 1
  · let u : ℚ̄₂ˣ := Units.mk0 zeta (root_ne_zero hm hzeta)
    let x : MuN m := Additive.ofMul ⟨u, by
      rw [mem_rootsOfUnity]
      apply Units.ext
      exact hzeta⟩
    have hset : {g : Kummer.GaloisGroup ℚ_[2] | g • zeta = zeta ^ 2} =
        {g : Kummer.GaloisGroup ℚ_[2] | g • x = Additive.ofMul (x.toMul ^ 2)} := by
      ext g
      change g • zeta = zeta ^ 2 ↔ _
      constructor <;> intro h
      · apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        exact h
      · have h' := congrArg (fun y : MuN m => (((y.toMul : ℚ̄₂ˣ) : ℚ̄₂))) h
        exact h'
    simp only [hzeta]
    rw [hset]
    have hleft : Continuous
        (fun g : Kummer.GaloisGroup ℚ_[2] => g • x) :=
      continuous_id.smul continuous_const
    have hright : Continuous
        (fun _ : Kummer.GaloisGroup ℚ_[2] => Additive.ofMul (x.toMul ^ 2)) :=
      continuous_const
    simpa only [Set.iInter_true] using isClosed_eq hleft hright
  · simp only [hzeta, Set.iInter_false, isClosed_univ]

theorem oddRootFrobeniusSet_antitone_of_dvd {m n : ℕ} (hm : m ∣ n) :
    oddRootFrobeniusSet n ⊆ oddRootFrobeniusSet m := by
  rintro g hg zeta hzeta
  obtain ⟨k, rfl⟩ := hm
  apply hg zeta
  rw [pow_mul, hzeta, one_pow]

theorem oddRootFrobeniusSet_iInter_nonempty
    (H : ∀ m : ℕ, Odd m → (oddRootFrobeniusSet m).Nonempty) :
    (⋂ m : {m : ℕ // Odd m}, oddRootFrobeniusSet m.1).Nonempty := by
  letI : Nonempty {m : ℕ // Odd m} := ⟨⟨1, by simp⟩⟩
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro m n
    let k : {k : ℕ // Odd k} := ⟨m.1 * n.1, m.2.mul n.2⟩
    exact ⟨k, oddRootFrobeniusSet_antitone_of_dvd (dvd_mul_right m.1 n.1),
      oddRootFrobeniusSet_antitone_of_dvd (dvd_mul_left n.1 m.1)⟩
  · exact fun m => H m.1 m.2
  · exact fun m => (oddRootFrobeniusSet_isClosed m.1 m.2.pos).isCompact
  · exact fun m => oddRootFrobeniusSet_isClosed m.1 m.2.pos

/-- Finite cyclotomic Frobenius lifts at every odd order assemble to one absolute lift. -/
theorem exists_squaresOddRoots_of_finite_cyclotomic_lifts
    (H : ∀ m : ℕ, Odd m → (oddRootFrobeniusSet m).Nonempty) :
    ∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g := by
  obtain ⟨g, hg⟩ := oddRootFrobeniusSet_iInter_nonempty H
  refine ⟨g, fun m zeta hm hzeta => ?_⟩
  exact Set.mem_iInter.mp hg ⟨m, hm⟩ zeta hzeta

/-- A global absolute Frobenius lift is equivalent to finite lifts at every odd order. -/
theorem exists_squaresOddRoots_iff_finite_cyclotomic_lifts :
    (∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g) ↔
      ∀ m : ℕ, Odd m → (oddRootFrobeniusSet m).Nonempty := by
  constructor
  · rintro ⟨g, hg⟩ m hm
    exact ⟨g, fun zeta hzeta => hg m zeta hm hzeta⟩
  · exact exists_squaresOddRoots_of_finite_cyclotomic_lifts

#print axioms oddRootFrobeniusSet
#print axioms oddRootFrobeniusSet_isClosed
#print axioms oddRootFrobeniusSet_antitone_of_dvd
#print axioms oddRootFrobeniusSet_iInter_nonempty
#print axioms exists_squaresOddRoots_of_finite_cyclotomic_lifts
#print axioms exists_squaresOddRoots_iff_finite_cyclotomic_lifts

end
end GQ2.Dyadic
