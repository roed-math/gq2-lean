/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.MarkedMaxProTwo

/-!
# Consequences of ramification of `K(i)/K`

This file records the two arithmetic consequences of the campaign's formal ramified-`i`
hypothesis that are available without a local-class-field-theory computation of the
abelianization of `G_K(2)`:

* `K` has no nontrivial fourth or higher 2-power roots of unity; and
* the cyclotomic character on pro-2 inertia is nontrivial modulo `4`.

These facts are inputs to, but not substitutes for, a proof that `demushkinQ (G_K(2)) = 2`.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]

omit [FiniteDimensional ℚ_[2] K] in
/-- In a field without a square root of `-1`, every element killed by a power of `2` is `1`
or `-1`.  This is the elementary root-of-unity input needed in the eventual local-reciprocity
calculation of the torsion in the pro-2 completion of `K^x`. -/
theorem twoPowerRoot_eq_one_or_neg_one_of_no_sqrt_neg_one
    (hno : ¬ ∃ y : K, y ^ 2 = -1) (x : K) :
    ∀ n : ℕ, x ^ (2 ^ n) = 1 → x = 1 ∨ x = -1 := by
  intro n
  induction n with
  | zero =>
      intro hx
      exact Or.inl (by simpa using hx)
  | succ n ih =>
      intro hx
      have hsq : (x ^ (2 ^ n)) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_succ]
        exact hx
      have hfac : (x ^ (2 ^ n) - 1) * (x ^ (2 ^ n) + 1) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · exact ih (by linear_combination h)
      · cases n with
        | zero => exact Or.inr (by simpa using (show x ^ (2 ^ 0) = -1 by linear_combination h))
        | succ n =>
            exfalso
            apply hno
            refine ⟨x ^ (2 ^ n), ?_⟩
            rw [← pow_mul, ← pow_succ]
            linear_combination h

omit [FiniteDimensional ℚ_[2] K] in
/-- The field-language ramification witness rules out all 2-power roots of unity in `K` except
`1` and `-1`.  The conclusion is deliberately stated on elements of `K`; transporting it to
the torsion of the pro-2 abelianization is the missing local-reciprocity/completion bridge. -/
theorem twoPowerRoot_eq_one_or_neg_one_of_ramifiedI
    {deltaI : ℚbar2} (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) (x : K) (n : ℕ)
    (hx : x ^ (2 ^ n) = 1) : x = 1 ∨ x = -1 :=
  twoPowerRoot_eq_one_or_neg_one_of_no_sqrt_neg_one
    (fun h => hram (hasEqualNormValueGroups_of_exists_sqrt hdeltaI h)) x n hx

/-- The elements of `K` killed by some power of `2`.  They are automatically nonzero, but the
field-valued spelling makes the elementary classification independent of any units API. -/
abbrev TwoPowerRoots (K : IntermediateField ℚ_[2] ℚbar2) :=
  {x : K // ∃ n : ℕ, x ^ (2 ^ n) = 1}

omit [FiniteDimensional ℚ_[2] K] in
/-- Under the ramified-`i` hypothesis, the 2-primary roots of unity in `K` are exactly `1` and
`-1`, hence form a two-element type.  This packages the root classification in the precise
cardinality-ready form needed after the missing reciprocity/completion torsion bridge. -/
noncomputable def twoPowerRootsEquivZModTwo_of_ramifiedI
    {deltaI : ℚbar2} (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) : TwoPowerRoots K ≃ ZMod 2 := by
  classical
  exact Equiv.ofBijective (fun x : TwoPowerRoots K => if (x : K) = 1 then 0 else 1) (by
    have hneg : (-1 : K) ≠ 1 := by norm_num
    constructor
    · intro a b hab
      apply Subtype.ext
      obtain ⟨n, hn⟩ := a.2
      obtain ⟨m, hm⟩ := b.2
      rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI hdeltaI hram a n hn with ha | ha <;>
        rcases twoPowerRoot_eq_one_or_neg_one_of_ramifiedI hdeltaI hram b m hm with hb | hb
      · exact ha.trans hb.symm
      · exfalso
        simp [ha, hb, hneg] at hab
      · exfalso
        simp [ha, hb, hneg] at hab
      · exact ha.trans hb.symm
    · intro y
      rcases ZMod.eq_zero_or_eq_one y with rfl | rfl
      · exact ⟨⟨1, 0, by simp⟩, by simp⟩
      · exact ⟨⟨-1, 1, by norm_num⟩, by simp [hneg]⟩)

omit [FiniteDimensional ℚ_[2] K] in
/-- Cardinality form of `twoPowerRootsEquivZModTwo_of_ramifiedI`. -/
theorem natCard_twoPowerRoots_of_ramifiedI
    {deltaI : ℚbar2} (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) : Nat.card (TwoPowerRoots K) = 2 := by
  rw [Nat.card_congr (twoPowerRootsEquivZModTwo_of_ramifiedI hdeltaI hram), Nat.card_zmod]

end

end GQ2.Dyadic
