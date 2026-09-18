/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection
import GQ2.Roe.Labute.AdditiveCharacters
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan

/-!
# The coupled ordinary head row of an actual M-relator correction

The full, arbitrary-rank `M_alpha` word has ordinary row
`2 f(x0) + 2^alpha f(x2)`: unlike the `N` word it is **coupled**, carrying the
`C` column as well as the `A` column. This module extracts the head digit from
that coupled row without setting the `C` row to zero and without any
orientation or vanishing-`C` premise.

Every declaration here carries the lane prefix `mHead`. That prefix is a naming
reservation for this module; it is not a claim about the peripheral head word
`GQ2.Dyadic.MarkedCore.mHead` of `Cores`, which is a different object.

Nothing in the head-cleanup sections constructs the corrections, asserts a
derivative image, or preserves a relator equation after replacement. The final
section is a coordination re-export for the sibling derivative-kernel lane and
proves no new mathematics.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

section OrdinaryRows
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {h : ℕ}

omit [IsTopologicalGroup G] in
/-- The **coupled** ordinary row of the literal full `M_alpha` relator, every
handle included: `2 f(A) + 2^alpha f(C)`. Unlike the `N` row it carries the `C`
column as well, so the head digit cannot be read off by cancelling a single
unit factor. -/
theorem mHead_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y : Fin (coreRank h) → G) :
    (f (mRelWord alpha y)).toAdd =
      2 * (f (y 0)).toAdd + (2 : ℤ_[2]) ^ alpha * (f (y 2)).toAdd := by
  rw [map_mRelWord, mRelWord_comm, toAdd_mul, toAdd_pow, toAdd_pow,
    nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

omit [IsTopologicalGroup G] in
/-- Right-multiplying the marking by corrections moves the target-relative
defect row to the corrections' own coupled row. The original relation need only
agree with the target under `f`; no relator equation is assumed. -/
theorem mHead_correction_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (mRelWord alpha y) = f target) :
    (f (mRelWord alpha (fun i => y i * t i) * target⁻¹)).toAdd =
      2 * (f (t 0)).toAdd + (2 : ℤ_[2]) ^ alpha * (f (t 2)).toAdd := by
  have hb := congrArg Multiplicative.toAdd hrow
  rw [mHead_ordinary_row] at hb
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, mHead_ordinary_row, ← hb]
  simp only [map_mul, toAdd_mul]
  ring

end OrdinaryRows

/-- The scalar heart of the cleanup. One factor of two cancels from the coupled
row; the `C` summand is then already divisible by `2^d`, because `2^(alpha-1)`
contributes at least one further factor when `alpha >= 2` and the `C` row itself
carries `2^(d-1)`. No hypothesis forces `C = 0`. -/
theorem mHead_dvd_of_coupled_row {alpha d : ℕ} (halpha : 2 ≤ alpha) (hd : 1 ≤ d)
    {A C : ℤ_[2]} (hCrow : (2 : ℤ_[2]) ^ (d - 1) ∣ C)
    (hdefect : (2 : ℤ_[2]) ^ (d + 1) ∣ 2 * A + (2 : ℤ_[2]) ^ alpha * C) :
    (2 : ℤ_[2]) ^ d ∣ A := by
  obtain ⟨a, rfl⟩ : ∃ a, alpha = a + 2 := ⟨alpha - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hCrow
  obtain ⟨c, rfl⟩ := hCrow
  obtain ⟨b, hb⟩ := hdefect
  refine ⟨b - 2 ^ a * c, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0)
  linear_combination hb

section HeadDigit
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {h : ℕ}

/-- **T1.** One extra ordinary digit at the `A` column of an actual `M_alpha`
correction, at arbitrary rank and arbitrary target. The `C` column is only
assumed to lie in `lambda_d`; it is not set to zero, and no orientation premise
is used. No compactness, pro-two or finite-generation assumption on `G`. -/
theorem mHead_correction_dvd {alpha d : ℕ} (halpha : 2 ≤ alpha) (hd : 1 ≤ d)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (mRelWord alpha y) = f target)
    (hC : t 2 ∈ twoCentralSeries G d)
    (hdefect : mRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries G (d + 2)) :
    (2 : ℤ_[2]) ^ d ∣ (f (t 0)).toAdd := by
  refine mHead_dvd_of_coupled_row halpha hd
    (twoCentralSeries_z2_character_dvd f hd hC) ?_
  rw [← mHead_correction_ordinary_row alpha f y t target hrow]
  exact twoCentralSeries_z2_character_dvd_succ f hdefect

end HeadDigit

/-- **T2.** The actual coupled defect supplies every coordinate divisibility
needed for an exact all-ordinary-character-zero `A` column in its current
two-central class, at arbitrary rank `n`, arbitrary handle count `h` and
arbitrary target. The hypotheses `hA`/`hC` are the two columns of the coupled
row; in the intended consumer both come from one `forall i` depth hypothesis,
exactly as `exists_freeTwo_nHead_characterZero_same_class` is consumed on the
`N` side. No claim about the other columns, about the orientation, or about
the new relator defect is made here. -/
theorem mHead_exists_freeTwo_characterZero_same_class {alpha h n d : ℕ}
    (halpha : 2 ≤ alpha) (hd : 1 ≤ d) (y t : Fin (coreRank h) → FreeTwoRank n)
    (target : FreeTwoRank n)
    (hrow : ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]),
      f (mRelWord alpha y) = f target)
    (hA : t 0 ∈ twoCentralSeries (FreeTwoRank n : Type) d)
    (hC : t 2 ∈ twoCentralSeries (FreeTwoRank n : Type) d)
    (hdefect : mRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank n : Type) (d + 2)) :
    ∃ t0 : FreeTwoRank n,
      t0 ∈ twoCentralSeries (FreeTwoRank n : Type) d ∧
      (t 0)⁻¹ * t0 ∈ twoCentralSeries (FreeTwoRank n : Type) (d + 1) ∧
      ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]),
        f t0 = 1 := by
  apply exists_freeTwo_characterZero_same_twoCentralClass n d (t 0) hA
  intro i
  exact mHead_correction_dvd halpha hd (freeTwoCoordinate n i)
    y t target (hrow _) hC hdefect

/-! ## The M derivative-kernel coordination statement

This section is a **coordination statement for the sibling MKERNEL lane**, not
the adapter itself. It re-exports the already proved
`GQ2.Dyadic.StageGeneric.evenRawStageShift_m` in the packaging that lane needs:
the literal `mRelWord` shift, with no `StageWord` datum to construct and no
separate `1 <= alpha` argument to supply. MKERNEL owns the actual adapter.

Note the instance burden inherited from `evenRawStageShift_m`: `G` must be a
compact Hausdorff totally disconnected topological group, not merely a
topological group as in the head-cleanup sections above.
-/

section MKernelCoordination
open GQ2.Dyadic.StageGeneric

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **T3, part 1.** The literal `M_alpha` relator shift in `levelQuot G (k+1)`
is the even crossed-derivation word, for `alpha >= 2`, `k >= 3` and depth-`(k-1)`
corrections. This is `evenRawStageShift_m` with the `mStageWord` packaging
unfolded; the mathematical content is that theorem's, not this lane's. -/
theorem mHead_mRelWord_shift_eq_evenRawDbarWord {alpha : ℕ} (halpha : 2 ≤ alpha)
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    (mRelWord alpha base)⁻¹ * mRelWord alpha (fun i => base i * correction i) =
      evenRawDbarWord base correction :=
  evenRawStageShift_m halpha (by omega) h k hk base correction hdepth

/-- **T3, part 2.** The `M` and `N` filtered derivatives literally agree, as an
equation between relator shifts in the actual quotient group `levelQuot G (k+1)`,
and not merely an associated-graded analogy. This is the identification the scaffold's
item 1 asks for before any `N` kernel witness may be reused on the `M` side. It
is **not** a claim that any `N`-relator conclusion is an `M` theorem. -/
theorem mHead_mRelWord_shift_eq_nRelWord_shift {alpha : ℕ} (halpha : 2 ≤ alpha)
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    (mRelWord alpha base)⁻¹ * mRelWord alpha (fun i => base i * correction i) =
      (nRelWord alpha base)⁻¹ * nRelWord alpha (fun i => base i * correction i) := by
  rw [mHead_mRelWord_shift_eq_evenRawDbarWord halpha h k hk base correction hdepth]
  exact (evenRawStageShift_n halpha (by omega) h k hk base correction hdepth).symm

end MKernelCoordination

#print axioms mHead_ordinary_row
#print axioms mHead_correction_ordinary_row
#print axioms mHead_dvd_of_coupled_row
#print axioms mHead_correction_dvd
#print axioms mHead_exists_freeTwo_characterZero_same_class
#print axioms mHead_mRelWord_shift_eq_evenRawDbarWord
#print axioms mHead_mRelWord_shift_eq_nRelWord_shift

end
end GQ2.Dyadic.MarkedCore
