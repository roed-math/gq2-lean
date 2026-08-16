/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcFive

/-!
# W88-SIX: the `M6` word at class six

Wave 87 (`GQ2/Dyadic/Instances/MpcFive.lean`) climbed the class-five rung of the `M6` ansatz, so
the residue of `MpcPivShift 2` starts at class six.  This module is the class-six lane.

Declaration prefix `mpcSx` (namespace `GQ2.Dyadic.Instances.MpcSx`).  No `sorry`, no new axiom,
no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcSx

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-! ## §0 The class-six layer calculus

Everything is read in `Q₆ = G/λ₆`, with four layers in play instead of class five's three:

* `Y = λ₂/λ₆` (`lambdaImage G 2 6`), where every bracket lands;
* `L = λ₃/λ₆`, where `⁅Y, G⁆`, `Y²` and `p⁴` land;
* `M = λ₄/λ₆`, where `⁅L, G⁆`, `⁅Y, Y⁆`, `L²` and `p⁸` land;
* `Z = λ₅/λ₆` (`zLayer G 5`), central of exponent two, where `⁅M, G⁆`, `⁅L, Y⁆`, `M²` and `p¹⁶`
  land.

**What changes from class five.**  At class five the correction layer `L` was abelian and
commuted with `Y`, so the four factors of `mWord` assembled with nothing incurred (`MpcFive` §4).
At class six that is false: `⁅L, Y⁆ ⊆ Z` is not trivial, so `L` is not abelian and does not
commute with `Y`.  What survives one layer deeper is `⁅M, Y⁆ = 1` (`mpcSx_vanish_four`, the
instance `k = 4` of `cfive_commutator_lambdaTwo`), and that single fact is what every cancellation
below reduces to, together with the centrality of `Z`.

So the class-six discipline is: `M`-valued factors move freely through `Y`, `Z`-valued factors
move freely through everything, and `L`-valued factors move only at the cost of a `Z`-term. -/

section Calculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The bracket swap, in any group. -/
theorem mpcSx_swap {Q : Type*} [Group Q] (x y : Q) : commP x y = (commP y x)⁻¹ := by
  simp only [commP]; group

/-- Moving a central factor one place to the right. -/
private theorem mpcSx_cmove {Q : Type*} [Group Q] {z : Q} (hz : ∀ x : Q, z * x = x * z)
    (x y : Q) : x * z * y = x * y * z := by
  rw [mul_assoc, hz, ← mul_assoc]

/-- Moving a central factor one place to the left. -/
private theorem mpcSx_cmoveL {Q : Type*} [Group Q] {z : Q} (hz : ∀ x : Q, z * x = x * z)
    (x y : Q) : x * y * z = x * z * y := (mpcSx_cmove hz x y).symm

/-- Moving one factor one place to the right past another it commutes with. -/
private theorem mpcSx_mv {Q : Type*} [Group Q] {e x : Q} (h : e * x = x * e) (u v : Q) :
    u * e * x * v = u * x * e * v := by rw [mul_assoc u e x, h, ← mul_assoc]

/-- **The class-six collection step.**  One central factor `c₁` interleaved with a marked factor
`s`, and one factor `mz` that commutes with `s`: the three central factors come out at the right
and `mz` passes `s`.  This is the shape every reordering below takes. -/
private theorem mpcSx_collect3 {Q : Type*} [Group Q] {c₁ mz s : Q}
    (h₁ : ∀ x : Q, c₁ * x = x * c₁) (hms : mz * s = s * mz) (P c₂ c₃ : Q) :
    P * mz * (c₁ * s * c₂) * c₃ = P * s * mz * (c₁ * c₂ * c₃) := by
  calc P * mz * (c₁ * s * c₂) * c₃ = P * mz * c₁ * s * c₂ * c₃ := by group
    _ = P * mz * s * c₁ * c₂ * c₃ := by rw [mpcSx_cmove h₁ (P * mz) s]
    _ = P * mz * s * (c₁ * c₂ * c₃) := by group
    _ = P * s * mz * (c₁ * c₂ * c₃) := by rw [mul_assoc P mz s, hms]; group

/-- The layers of `Q₆` are nested. -/
theorem mpcSx_lam_le {j k : ℕ} (h : k ≤ j) {y : levelQuot G 6} (hy : y ∈ lambdaImage G j 6) :
    y ∈ lambdaImage G k 6 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v, twoCentralSeries_antitone (G := G) h hv, rfl⟩

/-- **`λ₆` is trivial in `Q₆`.**  Every class-six cancellation below is an instance of this. -/
theorem mpcSx_six_eq_one {y : levelQuot G 6} (hy : y ∈ lambdaImage G 6 6) : y = 1 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact (QuotientGroup.eq_one_iff v).mpr hv

/-- A bracket with a `λ_k`-slot on the left drops one layer. -/
theorem mpcSx_commP_step {k : ℕ} {y : levelQuot G 6} (hy : y ∈ lambdaImage G k 6)
    (x : levelQuot G 6) : commP y x ∈ lambdaImage G (k + 1) 6 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := levelMk_surjective G 6 x
  exact ⟨commP v b, cfive_commP_mem_succ hv b, by simp only [commP, map_mul, map_inv]⟩

/-- A bracket with a `λ_k`-slot on the right drops one layer. -/
theorem mpcSx_commP_step' {k : ℕ} (x : levelQuot G 6) {y : levelQuot G 6}
    (hy : y ∈ lambdaImage G k 6) : commP x y ∈ lambdaImage G (k + 1) 6 := by
  rw [mpcSx_swap]
  exact Subgroup.inv_mem _ (mpcSx_commP_step hy x)

/-- ⭐ **A bracket of a `λ_k`-slot against a `Y`-slot drops TWO layers**: the instance of
`cfive_commutator_lambdaTwo` read in `Q₆`.  This is the engine of the whole section. -/
theorem mpcSx_commP_lam {k : ℕ} {v w : levelQuot G 6} (hv : v ∈ lambdaImage G k 6)
    (hw : w ∈ lambdaImage G 2 6) : commP v w ∈ lambdaImage G (k + 2) 6 := by
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := hw
  exact ⟨commP a b, cfive_commutator_lambdaTwo ha hb, by simp only [commP, map_mul, map_inv]⟩

/-- The same with the slots exchanged. -/
theorem mpcSx_commP_lam' {k : ℕ} {v w : levelQuot G 6} (hv : v ∈ lambdaImage G k 6)
    (hw : w ∈ lambdaImage G 2 6) : commP w v ∈ lambdaImage G (k + 2) 6 := by
  rw [mpcSx_swap]
  exact Subgroup.inv_mem _ (mpcSx_commP_lam hv hw)

/-- The square of a `λ_k`-image is a `λ_{k+1}`-image. -/
theorem mpcSx_sq_step {k : ℕ} {y : levelQuot G 6} (hy : y ∈ lambdaImage G k 6) :
    y ^ 2 ∈ lambdaImage G (k + 1) 6 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G hv, by rw [map_pow]⟩

/-- ⭐⭐ **`⁅M, Y⁆ = 1` in `Q₆`.**  The class-six replacement for class five's `⁅L, Y⁆ = 1`:
one layer deeper, and the only free commutation the class-six calculus has. -/
theorem mpcSx_vanish_four {m y : levelQuot G 6} (hm : m ∈ lambdaImage G 4 6)
    (hy : y ∈ lambdaImage G 2 6) : commP m y = 1 :=
  mpcSx_six_eq_one (mpcSx_commP_lam hm hy)

/-- `⁅Y, M⁆ = 1` in `Q₆`. -/
theorem mpcSx_vanish_four' {m y : levelQuot G 6} (hm : m ∈ lambdaImage G 4 6)
    (hy : y ∈ lambdaImage G 2 6) : commP y m = 1 :=
  mpcSx_six_eq_one (mpcSx_commP_lam' hm hy)

/-- An `M`-element commutes with every `Y`-element. -/
theorem mpcSx_mcomm {m y : levelQuot G 6} (hm : m ∈ lambdaImage G 4 6)
    (hy : y ∈ lambdaImage G 2 6) : m * y = y * m :=
  (cfour_commute_of_comm (mpcSx_vanish_four hm hy)).eq

/-- Moving an `M`-factor one place to the right past a `Y`-factor. -/
private theorem mpcSx_mmove {m y : levelQuot G 6} (hm : m ∈ lambdaImage G 4 6)
    (hy : y ∈ lambdaImage G 2 6) (x : levelQuot G 6) : x * m * y = x * y * m := by
  rw [mul_assoc, mpcSx_mcomm hm hy, ← mul_assoc]

/-- A `Z`-element commutes with everything in `Q₆`. -/
theorem mpcSx_zcomm {z : levelQuot G 6} (hz : z ∈ zLayer G 5) (x : levelQuot G 6) :
    z * x = x * z := (zLayer_commute hz x).eq

/-- A `Z`-element kills a bracket from the left. -/
theorem mpcSx_commP_zLayer_left {z : levelQuot G 6} (hz : z ∈ zLayer G 5) (x : levelQuot G 6) :
    commP z x = 1 := bridge_comm_of_commute (zLayer_commute hz x).eq

/-- A `Z`-element kills a bracket from the right. -/
theorem mpcSx_commP_zLayer_right (x : levelQuot G 6) {z : levelQuot G 6} (hz : z ∈ zLayer G 5) :
    commP x z = 1 := by rw [mpcSx_swap, mpcSx_commP_zLayer_left hz x, inv_one]

/-- Squares in `Q₆`: `p²` is a `Y`-element. -/
theorem mpcSx_pow_two_mem (p : levelQuot G 6) : p ^ 2 ∈ lambdaImage G 2 6 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 6 p
  exact ⟨a ^ 2, sq_mem_twoCentralSeries_succ G (Subgroup.mem_top a), by rw [map_pow]⟩

/-- Fourth powers are `L`-elements in `Q₆`. -/
theorem mpcSx_pow_four_mem (p : levelQuot G 6) : p ^ 4 ∈ lambdaImage G 3 6 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 6 p
  refine ⟨a ^ 4, ?_, by rw [map_pow]⟩
  have h := pow_two_pow_mem_twoCentralSeries_succ (G := G) a 2
  rwa [show (2 : ℕ) ^ 2 = 4 from by norm_num] at h

/-- ⭐ **Eighth powers are `M`-elements at class six**, where at class five they were central.
This is one of the two hazards the wave-87 note named. -/
theorem mpcSx_pow_eight_mem (p : levelQuot G 6) : p ^ 8 ∈ lambdaImage G 4 6 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 6 p
  refine ⟨a ^ 8, ?_, by rw [map_pow]⟩
  have h := pow_two_pow_mem_twoCentralSeries_succ (G := G) a 3
  rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at h

/-- **Sixteenth powers are what is central at class six.** -/
theorem mpcSx_pow_sixteen_mem (p : levelQuot G 6) : p ^ 16 ∈ zLayer G 5 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 6 p
  refine ⟨a ^ 16, ?_, by rw [map_pow]⟩
  have h := pow_two_pow_mem_twoCentralSeries_succ (G := G) a 4
  rwa [show (2 : ℕ) ^ 4 = 16 from by norm_num] at h

/-- **Left-slot additivity against an `L`-factor followed by a `Y`-factor**: the correction of
`cfour_commP_mul_left` is a bracket of an `M`-element against a `Y`-element. -/
theorem mpcSx_commP_add_left_three {a b : levelQuot G 6} (ha : a ∈ lambdaImage G 3 6)
    (hb : b ∈ lambdaImage G 2 6) (c : levelQuot G 6) :
    commP (a * b) c = commP a c * commP b c := by
  rw [cfour_commP_mul_left, mpcSx_vanish_four (mpcSx_commP_step ha c) hb, mul_one]

/-- **Left-slot additivity against an `M`-factor**: the correction is a bracket of a
`Z`-element. -/
theorem mpcSx_commP_add_left_four {a : levelQuot G 6} (ha : a ∈ lambdaImage G 4 6)
    (b c : levelQuot G 6) : commP (a * b) c = commP a c * commP b c := by
  rw [cfour_commP_mul_left, mpcSx_commP_zLayer_left (mpcSx_commP_step ha c) b, mul_one]

/-- **A leading `Z`-factor is invisible in the left slot.** -/
theorem mpcSx_commP_drop_left {a : levelQuot G 6} (ha : a ∈ zLayer G 5) (b c : levelQuot G 6) :
    commP (a * b) c = commP b c := by
  rw [cfour_commP_mul_left, mpcSx_commP_zLayer_left ha c, cfour_one_comm, one_mul, one_mul]

/-- **A trailing `Z`-factor is invisible in the left slot.** -/
theorem mpcSx_commP_drop_left_tail {c : levelQuot G 6} (hc : c ∈ zLayer G 5)
    (b a : levelQuot G 6) : commP (b * c) a = commP b a := by
  rw [cfour_commP_mul_left, mpcSx_commP_zLayer_left hc a,
    mpcSx_commP_zLayer_right (commP b a) hc, mul_one, mul_one]

/-- **A trailing `Z`-factor is invisible in the right slot.** -/
theorem mpcSx_commP_drop_right (a b : levelQuot G 6) {c : levelQuot G 6} (hc : c ∈ zLayer G 5) :
    commP a (b * c) = commP a b := by
  rw [cfour_commP_mul_right, mpcSx_commP_zLayer_right a hc,
    mpcSx_commP_zLayer_right (commP a b) hc, one_mul, mul_one]

/-- **Right-slot additivity against an `L`-factor and a `Y`-factor**, in the reversed order
`cfour_commP_mul_right` produces. -/
theorem mpcSx_commP_add_right_three (a : levelQuot G 6) {b c : levelQuot G 6}
    (hb : b ∈ lambdaImage G 3 6) (hc : c ∈ lambdaImage G 2 6) :
    commP a (b * c) = commP a c * commP a b := by
  rw [cfour_commP_mul_right, mpcSx_vanish_four (mpcSx_commP_step' a hb) hc, mul_one]

end Calculus

/-! ## §1 The `Ā`-letter's square

`mpcFv_sq_letA` reads `(p·z·σ)² = p²·(σ²·⁅σ,p⁆)·(z²·⁅z,p⁆)` in `Q₅`, where the two extra factors
`z²` and `⁅z,p⁆` are central and the three terms `⁅σ,z⁆`, `⁅⁅σ,p⁆,z⁆` and `⁅⁅σ,p⁆,σ⁆` are all
`⁅Y, L⁆`- or `⁅L, Y⁆`-terms and therefore trivial.  At class six those three survive, central of
exponent two, and `z²`, `⁅z,p⁆` sink from `Z` to `M`. -/

section LetterA

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **THE `Ā`-LETTER'S SQUARE AT CLASS SIX.**

    (p·z·σ)² = p² · (σ²·⁅σ,p⁆) · (z²·⁅z,p⁆) · (⁅σ,z⁆·⁅⁅σ,p⁆,z⁆·⁅⁅σ,p⁆,σ⁆) ,

with `z` an `L`-element and `σ` a `Y`-correction.  The first three groups are `mpcFv_sq_letA`;
the fourth is central of exponent two and is `1` in `Q₅`, where each of its three factors is a
bracket of an `L`-element against a `Y`-element. -/
theorem mpcSx_sq_letA {p σ z : levelQuot G 6} (hσ : σ ∈ lambdaImage G 2 6)
    (hz : z ∈ lambdaImage G 3 6) :
    (p * z * σ) ^ 2
      = p ^ 2 * (σ ^ 2 * commP σ p) * (z ^ 2 * commP z p) *
        (commP σ z * commP (commP σ p) z * commP (commP σ p) σ) := by
  have hzY : z ∈ lambdaImage G 2 6 := mpcSx_lam_le (by omega) hz
  have hz2 : z ^ 2 ∈ lambdaImage G 4 6 := mpcSx_sq_step hz
  have hzp : commP z p ∈ lambdaImage G 4 6 := mpcSx_commP_step hz p
  have hσp : commP σ p ∈ lambdaImage G 3 6 := mpcSx_commP_step hσ p
  have hσz : commP σ z ∈ zLayer G 5 := mpcSx_commP_lam' hz hσ
  have hσpz : commP (commP σ p) z ∈ zLayer G 5 := mpcSx_commP_lam hσp hzY
  have hσpσ : commP (commP σ p) σ ∈ zLayer G 5 := mpcSx_commP_lam hσp hσ
  have hσ2 : σ ^ 2 ∈ lambdaImage G 2 6 := mpcSx_lam_le (by omega) (mpcSx_sq_step hσ)
  have hσpY : commP σ p ∈ lambdaImage G 2 6 := mpcSx_lam_le (by omega) hσp
  -- the square of the `z`-shifted head: the second-order term is an `⁅M, Y⁆`-term
  have h1 : (p * z) ^ 2 = p ^ 2 * (z ^ 2 * commP z p) := by
    rw [cfour_sq_mul, mpcSx_vanish_four hzp hzY, mul_one, mul_assoc]
  -- the correction against the shifted head
  have h2 : commP σ (p * z) = commP σ z * commP σ p * commP (commP σ p) z :=
    cfour_commP_mul_right _ _ _
  -- the second-order term sees only the marked head
  have h3 : commP (commP σ (p * z)) σ = commP (commP σ p) σ := by
    rw [h2, mpcSx_commP_drop_left_tail hσpz, mpcSx_commP_drop_left hσz]
  calc (p * z * σ) ^ 2
      = (p * z) ^ 2 * σ ^ 2 * commP σ (p * z) * commP (commP σ (p * z)) σ := cfour_sq_mul _ _
    _ = p ^ 2 * (z ^ 2 * commP z p) * σ ^ 2 *
          (commP σ z * commP σ p * commP (commP σ p) z) * commP (commP σ p) σ := by
        rw [h1, h3, h2]
    _ = p ^ 2 * σ ^ 2 * (z ^ 2 * commP z p) *
          (commP σ z * commP σ p * commP (commP σ p) z) * commP (commP σ p) σ := by
        rw [mpcSx_mmove (Subgroup.mul_mem _ hz2 hzp) hσ2 (p ^ 2)]
    _ = p ^ 2 * σ ^ 2 * commP σ p * (z ^ 2 * commP z p) *
          (commP σ z * commP (commP σ p) z * commP (commP σ p) σ) :=
        mpcSx_collect3 (mpcSx_zcomm hσz)
          (mpcSx_mcomm (Subgroup.mul_mem _ hz2 hzp) hσpY) _ _ _
    _ = p ^ 2 * (σ ^ 2 * commP σ p) * (z ^ 2 * commP z p) *
          (commP σ z * commP (commP σ p) z * commP (commP σ p) σ) := by group

end LetterA

/-! ## §2 Axiom pins

One line per public declaration, in declaration order, measured against the mirror. -/

section AxiomPins

#print axioms mpcSx_swap
#print axioms mpcSx_lam_le
#print axioms mpcSx_six_eq_one
#print axioms mpcSx_commP_step
#print axioms mpcSx_commP_step'
#print axioms mpcSx_commP_lam
#print axioms mpcSx_commP_lam'
#print axioms mpcSx_sq_step
#print axioms mpcSx_vanish_four
#print axioms mpcSx_vanish_four'
#print axioms mpcSx_mcomm
#print axioms mpcSx_zcomm
#print axioms mpcSx_commP_zLayer_left
#print axioms mpcSx_commP_zLayer_right
#print axioms mpcSx_pow_two_mem
#print axioms mpcSx_pow_four_mem
#print axioms mpcSx_pow_eight_mem
#print axioms mpcSx_pow_sixteen_mem
#print axioms mpcSx_commP_add_left_three
#print axioms mpcSx_commP_add_left_four
#print axioms mpcSx_commP_drop_left
#print axioms mpcSx_commP_drop_left_tail
#print axioms mpcSx_commP_drop_right
#print axioms mpcSx_commP_add_right_three
#print axioms mpcSx_sq_letA

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcSx
