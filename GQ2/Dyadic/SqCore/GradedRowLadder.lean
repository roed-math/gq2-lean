/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedRowMove

/-!
# W86-LADDER4: the row-move ladder at class `k ≥ 4`

Wave 85 (`GradedRowMove.lean`) reduced the row-move pair, hence the clearing
`SqNuOrientedClearAtUnitPivot h` and through it the odd-degree classification, to the rungs
`(gRowSet h A B k).Nonempty` for `k ≥ 4` on the unit locus `IsUnit (A - c0 B)`.  Rungs
`k ≤ 3` are proved there: `k ≤ 2` free for every frame, `k = 3` free with the bare frame.

This module extends the ladder with the increment engine, the wave-85 M6 pattern
(`mpcBld_incr_*`) transferred to the row word:

* **The slot increments, uniform in the class** (section 2): a `λ_j`-factor on a slot of
  `sqWord` costs, in `Q_{j+2}`, exactly one central element: `commP ε x` on the sigma slot,
  `commP s ε` on the `x₀`-slot, the bundle `ε² · commP ε y` on the `x₁`-slot, and single
  brackets on the handle slots.  The `x₀`-slot's own fourth power is invisible (`ε⁻⁴ = 1`).
* **The master increment** (section 3): `gLad_relWord_incr` prices a full correction tuple on
  the relator word in closed form (`gLadCost`), and `gLad_step` turns a rung-`(j+1)` solution
  plus a cost tuple killing the defect into a rung-`(j+2)` solution of `gRowSet`.

All declarations carry `#print axioms` pins recorded at the end of the file.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The exact word calculus, and the layer calculus in `Q_{j+2}`

Exact identities first (any group), then the `Q_{j+2}`-facts for a `λ_j`-image factor `ε`:
its brackets are central, its square is central, its fourth power dies, and brackets against
`λ₂`-images die.  Everything is stated at the uniform depth `j`, so the same engine prices
every rung of the ladder. -/

section ExactCalculus

variable {Q : Type*} [Group Q]

/-- The swap law `u v = v u [u, v]`, exactly. -/
theorem gLad_swap (u v : Q) : u * v = v * u * commP u v := by
  simp only [commP]
  group

/-- Bracket inversion `[u,v]⁻¹ = [v,u]`, exactly. -/
theorem gLad_commP_inv (u v : Q) : (commP u v)⁻¹ = commP v u := by
  simp only [commP]
  group

/-- Conjugation in bracket form: `a^s = a [a, s]`, exactly. -/
theorem gLad_conjP_eq (a s : Q) : conjP a s = a * commP a s := by
  simp only [conjP, commP]
  group

/-- Conjugation is multiplicative in the conjugated slot. -/
theorem gLad_conjP_mul (a b s : Q) : conjP (a * b) s = conjP a s * conjP b s := by
  simp only [conjP]
  group

/-- Conjugation by a product is iterated conjugation. -/
theorem gLad_conjP_conjP (a s t : Q) : conjP a (s * t) = conjP (conjP a s) t := by
  simp only [conjP]
  group

/-- Slide a two-sided-central element from the head of a five-factor product to its tail. -/
theorem gLad_zmove4 {z : Q} (hz : ∀ w : Q, z * w = w * z) (a b c d : Q) :
    z * a * b * c * d = a * b * c * d * z := by
  rw [hz a, mul_assoc a z b, hz b, ← mul_assoc, mul_assoc (a * b) z c, hz c, ← mul_assoc,
    mul_assoc (a * b * c) z d, hz d, ← mul_assoc]

end ExactCalculus

section LayerCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

/-- Every bracket of `Q_{j+2}` lies in the `λ₂`-image. -/
theorem gLad_commP_mem_two (p q : levelQuot G (j + 2)) :
    commP p q ∈ lambdaImage G 2 (j + 2) := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G (j + 2) p
  obtain ⟨b, rfl⟩ := levelMk_surjective G (j + 2) q
  exact ⟨commP a b, cfour_commP_mem_two a b, by simp only [commP, map_mul, map_inv]⟩

/-- `⁅λ₂, λ_j⁆` dies in `Q_{j+2}`. -/
theorem gLad_vanish {y ε : levelQuot G (j + 2)} (hy : y ∈ lambdaImage G 2 (j + 2))
    (hε : ε ∈ lambdaImage G j (j + 2)) : commP y ε = 1 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hε
  have h : commP (levelMk G (j + 2) v) (levelMk G (j + 2) w)
      = levelMk G (j + 2) (commP v w) := by simp only [commP, map_mul, map_inv]
  rw [h]
  exact (QuotientGroup.eq_one_iff _).mpr
    (cfive_commutator_lambdaTwo_swap (SetLike.mem_coe.mp hw) (SetLike.mem_coe.mp hv))

/-- `⁅λ_j, λ₂⁆` dies in `Q_{j+2}`, the slots the other way round. -/
theorem gLad_vanish' {y ε : levelQuot G (j + 2)} (hy : y ∈ lambdaImage G 2 (j + 2))
    (hε : ε ∈ lambdaImage G j (j + 2)) : commP ε y = 1 := by
  rw [← gLad_commP_inv, gLad_vanish hy hε, inv_one]

/-- The central layer of `Q_{j+2}` sits inside the `λ_j`-image. -/
theorem gLad_zLayer_le : zLayer G (j + 1) ≤ lambdaImage G j (j + 2) :=
  Subgroup.map_mono (twoCentralSeries_antitone G (Nat.le_succ j))

/-- At depth `j ≥ 2` the `λ_j`-image sits inside the `λ₂`-image. -/
theorem gLad_le_two (hj : 2 ≤ j) : lambdaImage G j (j + 2) ≤ lambdaImage G 2 (j + 2) :=
  Subgroup.map_mono (twoCentralSeries_antitone G hj)

/-- The square of a `λ_j`-image lands in the central layer of `Q_{j+2}`. -/
theorem gLad_sq_mem_zLayer {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2)) :
    ε ^ 2 ∈ zLayer G (j + 1) := by
  obtain ⟨v, hv, rfl⟩ := hε
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G hv, by rw [map_pow]⟩

/-- The fourth power of a `λ_j`-image dies in `Q_{j+2}`. -/
theorem gLad_pow_four {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2)) :
    ε ^ 4 = 1 := by
  have h := zLayer_sq G (gLad_sq_mem_zLayer hε)
  rwa [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl] at h

/-- A central-layer element kills a bracket from the right. -/
theorem gLad_commP_zLayer_right (q : levelQuot G (j + 2)) {z : levelQuot G (j + 2)}
    (hz : z ∈ zLayer G (j + 1)) : commP q z = 1 := by
  rw [← gLad_commP_inv, cfive_commP_zLayer_left hz q, inv_one]

/-- Inverting the `λ_j`-slot inverts the bracket, in `Q_{j+2}`. -/
theorem gLad_commP_inv_left {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2))
    (g : levelQuot G (j + 2)) : commP ε⁻¹ g = (commP ε g)⁻¹ := by
  have h := cfour_commP_mul_left ε ε⁻¹ g
  rw [mul_inv_cancel, cfour_one_comm,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hε g) ε⁻¹, mul_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- Inverting the other slot against a `λ_j`-element inverts the bracket, in `Q_{j+2}`. -/
theorem gLad_commP_inv_right {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2))
    (g : levelQuot G (j + 2)) : commP ε g⁻¹ = (commP ε g)⁻¹ := by
  have h := cfour_commP_mul_right ε g⁻¹ g
  rw [inv_mul_cancel, cfour_comm_one,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hε g⁻¹) g, mul_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- The cube of a `λ_j`-element brackets like the element itself, in `Q_{j+2}`. -/
theorem gLad_commP_cube_left {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2))
    (g : levelQuot G (j + 2)) : commP (ε ^ 3) g = commP ε g := by
  have hsq : commP (ε ^ 2) g = 1 :=
    cfive_commP_zLayer_left (gLad_sq_mem_zLayer hε) g
  have h := cfour_commP_mul_left (ε ^ 2) ε g
  rwa [← pow_succ, hsq, one_mul, cfour_one_comm, one_mul] at h

/-- A `λ₂`-image tail is invisible to a `λ_j`-bracket, in `Q_{j+2}`. -/
theorem gLad_commP_absorb_right {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2))
    (g : levelQuot G (j + 2)) {y : levelQuot G (j + 2)} (hy : y ∈ lambdaImage G 2 (j + 2)) :
    commP ε (g * y) = commP ε g := by
  rw [cfive_commP_right_hom hε, gLad_vanish' hy hε, one_mul]

/-- Brackets of a `λ_j`-element read conjugates at their leading letter, in `Q_{j+2}`. -/
theorem gLad_commP_conj {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2))
    (x s : levelQuot G (j + 2)) : commP ε (conjP x s) = commP ε x := by
  rw [gLad_conjP_eq, gLad_commP_absorb_right hε x (gLad_commP_mem_two x s)]

end LayerCalculus

/-! ## §2 The slot increments of the row word, uniform in the class

`sqWord s x y = (x^s)⁻¹ · x⁻³ · y² · [y, y^s]`.  A `λ_j`-factor `ε` on one slot costs, in
`Q_{j+2}`, one central element, computed against the other letters as they stand:

* sigma slot: `commP ε x` (the conjugation sees `ε` exactly once, through the `x`-letter);
* `x₀`-slot: `commP s ε` (the fourth power `ε⁻⁴` dies, the two conjugation brackets cancel);
* `x₁`-slot: the bundle `ε² · commP ε y` (the square survives, the `[y, y^s]`-factor is
  blind);
* handle slots: the single brackets `commP ε v`, `commP u ε`.

These are the `mpcBld_incr_*` statements of the M6 core, transferred to the row word. -/

section Increments

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

/-- ⭐⭐ **The sigma slot's increment**: a `λ_j`-factor on the `s`-letter costs exactly
`commP ε x` in `Q_{j+2}`, whatever the three letters are. -/
theorem gLad_incr_s (s x y : levelQuot G (j + 2)) {ε : levelQuot G (j + 2)}
    (hε : ε ∈ lambdaImage G j (j + 2)) :
    sqWord (s * ε) x y = sqWord s x y * commP ε x := by
  have hcx : commP x ε ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_right x hε
  have hcy : commP y ε ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_right y hε
  have h1 : conjP x (s * ε) = conjP x s * commP x ε := by
    rw [gLad_conjP_conjP, gLad_conjP_eq (conjP x s) ε]
    congr 1
    rw [gLad_conjP_eq x s, cfour_commP_mul_left,
      cfive_commP_zLayer_left hcx (commP x s), mul_one,
      gLad_vanish (gLad_commP_mem_two x s) hε, mul_one]
  have h2 : conjP y (s * ε) = conjP y s * commP y ε := by
    rw [gLad_conjP_conjP, gLad_conjP_eq (conjP y s) ε]
    congr 1
    rw [gLad_conjP_eq y s, cfour_commP_mul_left,
      cfive_commP_zLayer_left hcy (commP y s), mul_one,
      gLad_vanish (gLad_commP_mem_two y s) hε, mul_one]
  have h4 : commP y (conjP y (s * ε)) = commP y (conjP y s) := by
    rw [h2, cfour_commP_mul_right, gLad_commP_zLayer_right y hcy, one_mul,
      gLad_commP_zLayer_right (commP y (conjP y s)) hcy, mul_one]
  have hslide : ∀ w : levelQuot G (j + 2), commP ε x * w = w * commP ε x := fun w =>
    (zLayer_commute (cfive_commP_mem_zLayer_left hε x) w).eq
  rw [sqWord, sqWord, h1, h4, mul_inv_rev, gLad_commP_inv x ε, gLad_zmove4 hslide]

/-- ⭐⭐ **The `x₀`-slot's increment**: a `λ_j`-factor on the `x`-letter costs exactly
`commP s ε` in `Q_{j+2}`: the fourth power of `ε` dies outright, and the conjugation
brackets cancel in pairs. -/
theorem gLad_incr_x (s x y : levelQuot G (j + 2)) {ε : levelQuot G (j + 2)}
    (hε : ε ∈ lambdaImage G j (j + 2)) :
    sqWord s (x * ε) y = sqWord s x y * commP s ε := by
  have hc : commP ε x ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_left hε x
  have hcube : (x * ε) ^ 3 = x ^ 3 * ε ^ 3 * commP ε x := by
    have hsq : (x * ε) ^ 2 = x ^ 2 * ε ^ 2 * commP ε x := by
      rw [cfour_sq_mul, cfive_commP_zLayer_left hc ε, mul_one]
    calc (x * ε) ^ 3 = (x * ε) ^ 2 * (x * ε) := pow_succ (x * ε) 2
      _ = x ^ 2 * ε ^ 2 * commP ε x * (x * ε) := by rw [hsq]
      _ = x ^ 2 * ε ^ 2 * (commP ε x * (x * ε)) := by group
      _ = x ^ 2 * ε ^ 2 * ((x * ε) * commP ε x) := by rw [(zLayer_commute hc (x * ε)).eq]
      _ = x ^ 2 * (ε ^ 2 * x) * ε * commP ε x := by group
      _ = x ^ 2 * (x * ε ^ 2) * ε * commP ε x := by
          rw [(zLayer_commute (gLad_sq_mem_zLayer hε) x).eq]
      _ = x ^ 3 * ε ^ 3 * commP ε x := by group
  have hconj : conjP (x * ε) s = conjP x s * (ε * commP ε s) := by
    rw [gLad_conjP_mul, gLad_conjP_eq ε s]
  have hcubeK : commP (ε ^ 3) (conjP x s) = commP ε x := by
    rw [gLad_commP_cube_left hε, gLad_commP_conj hε]
  have hU : (x * ε) ^ 3 * conjP (x * ε) s = x ^ 3 * conjP x s * commP ε s := by
    rw [hcube, hconj]
    calc x ^ 3 * ε ^ 3 * commP ε x * (conjP x s * (ε * commP ε s))
        = x ^ 3 * ε ^ 3 * (commP ε x * conjP x s) * ε * commP ε s := by group
      _ = x ^ 3 * ε ^ 3 * (conjP x s * commP ε x) * ε * commP ε s := by
          rw [(zLayer_commute hc (conjP x s)).eq]
      _ = x ^ 3 * (ε ^ 3 * conjP x s) * (commP ε x * ε) * commP ε s := by group
      _ = x ^ 3 * (ε ^ 3 * conjP x s) * (ε * commP ε x) * commP ε s := by
          rw [(zLayer_commute hc ε).eq]
      _ = x ^ 3 * (conjP x s * ε ^ 3 * commP (ε ^ 3) (conjP x s)) * (ε * commP ε x)
            * commP ε s := by rw [← gLad_swap (ε ^ 3) (conjP x s)]
      _ = x ^ 3 * (conjP x s * ε ^ 3 * commP ε x) * (ε * commP ε x) * commP ε s := by
          rw [hcubeK]
      _ = x ^ 3 * conjP x s * ε ^ 3 * (commP ε x * ε) * commP ε x * commP ε s := by group
      _ = x ^ 3 * conjP x s * ε ^ 3 * (ε * commP ε x) * commP ε x * commP ε s := by
          rw [(zLayer_commute hc ε).eq]
      _ = x ^ 3 * conjP x s * (ε ^ 3 * ε) * (commP ε x * commP ε x) * commP ε s := by group
      _ = x ^ 3 * conjP x s * ε ^ 4 * (commP ε x ^ 2) * commP ε s := by
          rw [← pow_succ, ← pow_two]
      _ = x ^ 3 * conjP x s * commP ε s := by
          rw [gLad_pow_four hε, zLayer_sq G hc, mul_one, mul_one]
  have hslide : ∀ w : levelQuot G (j + 2), commP s ε * w = w * commP s ε := fun w =>
    (zLayer_commute (cfive_commP_mem_zLayer_right s hε) w).eq
  calc sqWord s (x * ε) y
      = (conjP (x * ε) s)⁻¹ * ((x * ε) ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s) := rfl
    _ = ((x * ε) ^ 3 * conjP (x * ε) s)⁻¹ * y ^ 2 * commP y (conjP y s) := by
        rw [mul_inv_rev ((x * ε) ^ 3) (conjP (x * ε) s)]
    _ = (x ^ 3 * conjP x s * commP ε s)⁻¹ * y ^ 2 * commP y (conjP y s) := by rw [hU]
    _ = (commP ε s)⁻¹ * ((conjP x s)⁻¹ * (x ^ 3)⁻¹) * y ^ 2 * commP y (conjP y s) := by
        group
    _ = commP s ε * (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s) := by
        rw [gLad_commP_inv ε s]
        group
    _ = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s) * commP s ε :=
        gLad_zmove4 hslide _ _ _ _
    _ = sqWord s x y * commP s ε := rfl

/-- ⭐⭐ **The `x₁`-slot's increment**: a `λ_j`-factor on the `y`-letter costs exactly the
bundle `ε² · commP ε y` in `Q_{j+2}`.  The square survives, and the commutator factor of the
word is blind to the increment.  This is the knob-bundle shape of the uniform tower. -/
theorem gLad_incr_y (s x y : levelQuot G (j + 2)) {ε : levelQuot G (j + 2)}
    (hε : ε ∈ lambdaImage G j (j + 2)) :
    sqWord s x (y * ε) = sqWord s x y * (ε ^ 2 * commP ε y) := by
  have hcy : commP ε y ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_left hε y
  have hzs : commP ε s ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_left hε s
  have h2 : (y * ε) ^ 2 = y ^ 2 * (ε ^ 2 * commP ε y) := by
    rw [cfour_sq_mul, cfive_commP_zLayer_left hcy ε, mul_one, mul_assoc]
  have hconj : conjP (y * ε) s = conjP y s * (ε * commP ε s) := by
    rw [gLad_conjP_mul, gLad_conjP_eq ε s]
  have hRmem : ε * commP ε s ∈ lambdaImage G j (j + 2) :=
    Subgroup.mul_mem _ hε (gLad_zLayer_le hzs)
  have hεR : commP ε (ε * commP ε s) = 1 := by
    rw [cfour_commP_mul_right, gLad_commP_zLayer_right ε hzs, one_mul, bridge_comm_self,
      cfour_one_comm, mul_one]
  have hyR : commP y (ε * commP ε s) = commP y ε := by
    rw [cfour_commP_mul_right, gLad_commP_zLayer_right y hzs, one_mul,
      gLad_commP_zLayer_right (commP y ε) hzs, mul_one]
  have h4 : commP (y * ε) (conjP (y * ε) s) = commP y (conjP y s) := by
    rw [hconj, cfour_commP_mul_left,
      gLad_vanish (gLad_commP_mem_two y (conjP y s * (ε * commP ε s))) hε, mul_one,
      cfive_commP_right_hom hε (conjP y s) (ε * commP ε s), hεR, one_mul,
      gLad_commP_conj hε y s, cfour_commP_mul_right, hyR,
      gLad_vanish (gLad_commP_mem_two y (conjP y s)) hRmem, mul_one]
    calc commP y ε * commP y (conjP y s) * commP ε y
        = commP y ε * (commP y (conjP y s) * commP ε y) := by group
      _ = commP y ε * (commP ε y * commP y (conjP y s)) := by
          rw [(zLayer_commute hcy (commP y (conjP y s))).eq]
      _ = commP y ε * commP ε y * commP y (conjP y s) := by group
      _ = commP y (conjP y s) := by
          rw [← gLad_commP_inv ε y, inv_mul_cancel, one_mul]
  have hz : ε ^ 2 * commP ε y ∈ zLayer G (j + 1) :=
    Subgroup.mul_mem _ (gLad_sq_mem_zLayer hε) hcy
  calc sqWord s x (y * ε)
      = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * ((y * ε) ^ 2) * commP (y * ε) (conjP (y * ε) s) := rfl
    _ = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * (y ^ 2 * (ε ^ 2 * commP ε y)) * commP y (conjP y s) := by
        rw [h2, h4]
    _ = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * ((ε ^ 2 * commP ε y) * commP y (conjP y s)) := by
        group
    _ = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * (commP y (conjP y s) * (ε ^ 2 * commP ε y)) := by
        rw [(zLayer_commute hz (commP y (conjP y s))).eq]
    _ = sqWord s x y * (ε ^ 2 * commP ε y) := by
        rw [sqWord]
        group

/-- ⭐ **The handle pair's increment**: `λ_j`-factors on both letters of one handle cost
exactly the two single brackets, in `Q_{j+2}`. -/
theorem gLad_incr_pair (hj : 2 ≤ j) (u v : levelQuot G (j + 2)) {εu εv : levelQuot G (j + 2)}
    (hεu : εu ∈ lambdaImage G j (j + 2)) (hεv : εv ∈ lambdaImage G j (j + 2)) :
    commP (u * εu) (v * εv) = commP u v * (commP εu v * commP u εv) := by
  have h1 : commP εu (v * εv) = commP εu v := by
    rw [cfive_commP_right_hom hεu, gLad_vanish (gLad_le_two hj hεu) hεv, one_mul]
  have h2 : commP u (v * εv) = commP u εv * commP u v := by
    rw [cfour_commP_mul_right, gLad_vanish (gLad_commP_mem_two u v) hεv, mul_one]
  rw [cfour_commP_mul_left, gLad_vanish (gLad_commP_mem_two u (v * εv)) hεu, mul_one, h1, h2]
  calc commP u εv * commP u v * commP εu v
      = commP u εv * (commP u v * commP εu v) := by group
    _ = commP u v * commP εu v * commP u εv := by
        rw [(zLayer_commute (cfive_commP_mem_zLayer_right u hεv) (commP u v * commP εu v)).eq]
    _ = commP u v * (commP εu v * commP u εv) := by group

end Increments

/-! ## §3 The master increment, and the rung step

The per-slot costs assemble into one closed cost `gLadCost` for a full correction tuple on
the relator word, and the cost turns rung-`(j+1)` solutions of `gRowSet` into rung-`(j+2)`
solutions: the ladder climbs by exact linear algebra in `λ_{j+1}/λ_{j+2}` and nothing else. -/

section Master

/-- **The increment cost of a full correction tuple on the relator word**: the three slot
costs of the core word followed by the handle brackets, in engine order. -/
def gLadCost {Q : Type*} [Group Q] {n : ℕ} (m ε : Fin (sqRank n) → Q) : Q :=
  commP (ε 0) (m 1) * commP (m 0) (ε 1) * (ε 2 ^ 2 * commP (ε 2) (m 2))
    * ((List.finRange n).map fun i =>
        commP (ε (sqHandleIdxU i)) (m (sqHandleIdxV i))
          * commP (m (sqHandleIdxU i)) (ε (sqHandleIdxV i))).prod

private theorem gLad_listProd_succ {Q : Type*} [Monoid Q] {n : ℕ} (f : Fin (n + 1) → Q) :
    ((List.finRange (n + 1)).map f).prod
      = f 0 * ((List.finRange n).map fun i => f i.succ).prod := by
  rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
  rfl

/-- Peeling the first handle off the handle word (local copy of the class-five kit's
`handleWord_succ`, which is outside this module's import cone). -/
private theorem gLad_handleWord_succ {Q : Type*} [Group Q] {n : ℕ} (u v : Fin (n + 1) → Q) :
    handleWord u v
      = commP (u 0) (v 0) * handleWord (fun i => u i.succ) (fun i => v i.succ) := by
  rw [handleWord, handleWord, List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

/-- ⭐⭐ **The handle word's increment**: `λ_j`-factors on all handle letters cost the product
of the single brackets, in `Q_{j+2}`. -/
theorem gLad_incr_handle (hj : 2 ≤ j) {n : ℕ} (u v εu εv : Fin n → levelQuot G (j + 2))
    (hεu : ∀ i, εu i ∈ lambdaImage G j (j + 2))
    (hεv : ∀ i, εv i ∈ lambdaImage G j (j + 2)) :
    handleWord (fun i => u i * εu i) (fun i => v i * εv i)
      = handleWord u v
        * ((List.finRange n).map fun i => commP (εu i) (v i) * commP (u i) (εv i)).prod := by
  induction n with
  | zero =>
    rw [handleWord_zero, handleWord_zero, List.finRange_zero, List.map_nil, List.prod_nil,
      mul_one]
  | succ n ih =>
    have hhead : commP (u 0 * εu 0) (v 0 * εv 0)
        = commP (u 0) (v 0) * (commP (εu 0) (v 0) * commP (u 0) (εv 0)) :=
      gLad_incr_pair hj (u 0) (v 0) (hεu 0) (hεv 0)
    have htail := ih (fun i => u i.succ) (fun i => v i.succ) (fun i => εu i.succ)
      (fun i => εv i.succ) (fun i => hεu i.succ) (fun i => hεv i.succ)
    have hz : commP (εu 0) (v 0) * commP (u 0) (εv 0) ∈ zLayer G (j + 1) :=
      Subgroup.mul_mem _ (cfive_commP_mem_zLayer_left (hεu 0) (v 0))
        (cfive_commP_mem_zLayer_right (u 0) (hεv 0))
    calc handleWord (fun i => u i * εu i) (fun i => v i * εv i)
        = commP (u 0 * εu 0) (v 0 * εv 0)
          * handleWord (fun i => u i.succ * εu i.succ) (fun i => v i.succ * εv i.succ) :=
          gLad_handleWord_succ _ _
      _ = commP (u 0) (v 0) * (commP (εu 0) (v 0) * commP (u 0) (εv 0))
          * (handleWord (fun i => u i.succ) (fun i => v i.succ)
            * ((List.finRange n).map fun i =>
                commP (εu i.succ) (v i.succ) * commP (u i.succ) (εv i.succ)).prod) := by
          rw [hhead, htail]
      _ = commP (u 0) (v 0)
          * ((commP (εu 0) (v 0) * commP (u 0) (εv 0))
            * handleWord (fun i => u i.succ) (fun i => v i.succ))
          * ((List.finRange n).map fun i =>
              commP (εu i.succ) (v i.succ) * commP (u i.succ) (εv i.succ)).prod := by
          group
      _ = commP (u 0) (v 0)
          * (handleWord (fun i => u i.succ) (fun i => v i.succ)
            * (commP (εu 0) (v 0) * commP (u 0) (εv 0)))
          * ((List.finRange n).map fun i =>
              commP (εu i.succ) (v i.succ) * commP (u i.succ) (εv i.succ)).prod := by
          rw [(zLayer_commute hz (handleWord (fun i => u i.succ) (fun i => v i.succ))).eq]
      _ = (commP (u 0) (v 0) * handleWord (fun i => u i.succ) (fun i => v i.succ))
          * ((commP (εu 0) (v 0) * commP (u 0) (εv 0))
            * ((List.finRange n).map fun i =>
                commP (εu i.succ) (v i.succ) * commP (u i.succ) (εv i.succ)).prod) := by
          group
      _ = handleWord u v
          * ((List.finRange (n + 1)).map fun i =>
              commP (εu i) (v i) * commP (u i) (εv i)).prod := by
          rw [← gLad_handleWord_succ, ← gLad_listProd_succ fun i => commP (εu i) (v i)
            * commP (u i) (εv i)]

/-- ⭐⭐ **The core word's increment**: `λ_j`-factors on all three core slots cost the three
slot costs, in `Q_{j+2}`. -/
theorem gLad_sqWord_incr (hj : 2 ≤ j) (s x y : levelQuot G (j + 2))
    {εs εx εy : levelQuot G (j + 2)} (hεs : εs ∈ lambdaImage G j (j + 2))
    (hεx : εx ∈ lambdaImage G j (j + 2)) (hεy : εy ∈ lambdaImage G j (j + 2)) :
    sqWord (s * εs) (x * εx) (y * εy)
      = sqWord s x y * (commP εs x * commP s εx * (εy ^ 2 * commP εy y)) := by
  rw [gLad_incr_y (s * εs) (x * εx) y hεy, gLad_incr_x (s * εs) x y hεx,
    cfive_commP_left_hom s εs hεx, gLad_vanish (gLad_le_two hj hεs) hεx, mul_one,
    gLad_incr_s s x y hεs]
  group

/-- The full cost lies in the central layer of `Q_{j+2}`. -/
theorem gLad_cost_mem {n : ℕ} (m ε : Fin (sqRank n) → levelQuot G (j + 2))
    (hε : ∀ i, ε i ∈ lambdaImage G j (j + 2)) :
    gLadCost m ε ∈ zLayer G (j + 1) := by
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact cfive_commP_mem_zLayer_left (hε 0) (m 1)
  · exact cfive_commP_mem_zLayer_right (m 0) (hε 1)
  · exact Subgroup.mul_mem _ (gLad_sq_mem_zLayer (hε 2))
      (cfive_commP_mem_zLayer_left (hε 2) (m 2))
  · refine list_prod_mem fun w hw => ?_
    rw [List.mem_map] at hw
    obtain ⟨i, -, rfl⟩ := hw
    exact Subgroup.mul_mem _ (cfive_commP_mem_zLayer_left (hε _) (m _))
      (cfive_commP_mem_zLayer_right (m _) (hε _))

/-- ⭐⭐⭐ **THE MASTER INCREMENT**: a full `λ_j`-correction tuple on the letters of the
relator word costs exactly `gLadCost` in `Q_{j+2}`, uniformly in the class.  This is the
per-slot increment table of the row-move ansatz, the deliverable pattern of the M6 ladder
(`mpcBld_incr_*`) at the square-commutator core. -/
theorem gLad_relWord_incr (hj : 2 ≤ j) {n : ℕ} (m ε : Fin (sqRank n) → levelQuot G (j + 2))
    (hε : ∀ i, ε i ∈ lambdaImage G j (j + 2)) :
    sqRelWord (fun i => m i * ε i) = sqRelWord m * gLadCost m ε := by
  have hcore := gLad_sqWord_incr hj (m 0) (m 1) (m 2) (hε 0) (hε 1) (hε 2)
  have hhandle := gLad_incr_handle hj (fun i => m (sqHandleIdxU i))
    (fun i => m (sqHandleIdxV i)) (fun i => ε (sqHandleIdxU i))
    (fun i => ε (sqHandleIdxV i)) (fun i => hε _) (fun i => hε _)
  have hC : commP (ε 0) (m 1) * commP (m 0) (ε 1) * (ε 2 ^ 2 * commP (ε 2) (m 2))
      ∈ zLayer G (j + 1) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact cfive_commP_mem_zLayer_left (hε 0) (m 1)
    · exact cfive_commP_mem_zLayer_right (m 0) (hε 1)
    · exact Subgroup.mul_mem _ (gLad_sq_mem_zLayer (hε 2))
        (cfive_commP_mem_zLayer_left (hε 2) (m 2))
  calc sqRelWord (fun i => m i * ε i)
      = sqWord (m 0 * ε 0) (m 1 * ε 1) (m 2 * ε 2)
        * handleWord (fun i => m (sqHandleIdxU i) * ε (sqHandleIdxU i))
          (fun i => m (sqHandleIdxV i) * ε (sqHandleIdxV i)) := rfl
    _ = (sqWord (m 0) (m 1) (m 2)
          * (commP (ε 0) (m 1) * commP (m 0) (ε 1) * (ε 2 ^ 2 * commP (ε 2) (m 2))))
        * (handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i))
          * ((List.finRange n).map fun i =>
              commP (ε (sqHandleIdxU i)) (m (sqHandleIdxV i))
                * commP (m (sqHandleIdxU i)) (ε (sqHandleIdxV i))).prod) := by
        rw [hcore, hhandle]
    _ = sqWord (m 0) (m 1) (m 2)
        * ((commP (ε 0) (m 1) * commP (m 0) (ε 1) * (ε 2 ^ 2 * commP (ε 2) (m 2)))
          * handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)))
        * ((List.finRange n).map fun i =>
            commP (ε (sqHandleIdxU i)) (m (sqHandleIdxV i))
              * commP (m (sqHandleIdxU i)) (ε (sqHandleIdxV i))).prod := by
        group
    _ = sqWord (m 0) (m 1) (m 2)
        * (handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i))
          * (commP (ε 0) (m 1) * commP (m 0) (ε 1) * (ε 2 ^ 2 * commP (ε 2) (m 2))))
        * ((List.finRange n).map fun i =>
            commP (ε (sqHandleIdxU i)) (m (sqHandleIdxV i))
              * commP (m (sqHandleIdxU i)) (ε (sqHandleIdxV i))).prod := by
        rw [(zLayer_commute hC (handleWord (fun i => m (sqHandleIdxU i))
          (fun i => m (sqHandleIdxV i)))).eq]
    _ = sqRelWord m * gLadCost m ε := by
        rw [sqRelWord, gLadCost]
        group

end Master

/-! ## §4 The rung step on the row ladder -/

section Step

variable {h : ℕ}

/-- The ansatz is multiplicative in the correction tuple. -/
theorem gLad_mark_mul (A B : ℤ_[2]) (c ε : Fin (sqRank h) → (DSq h : Type)) :
    gRowMark h A B (fun i => c i * ε i) = fun i => gRowMark h A B c i * ε i := by
  funext i
  simp only [gRowMark_apply]
  group

/-- The defect of a rung-`(j+1)` solution is a central-layer class of `Q_{j+2}`. -/
theorem gLad_defect_mem {A B : ℤ_[2]} {j : ℕ} {c : Fin (sqRank h) → (DSq h : Type)}
    (hc : c ∈ gRowSet h A B (j + 1)) :
    levelMk (DSq h : Type) (j + 2) (sqRelWord (gRowMark h A B c))
      ∈ zLayer (DSq h : Type) (j + 1) :=
  ⟨_, hc.2, rfl⟩

/-- ⭐⭐⭐ **THE RUNG STEP.**  A rung-`(j+1)` solution `c` of the row ladder and a depth-`j`
correction tuple `ε` in the carrier whose cost kills the defect in `Q_{j+2}` produce the
rung-`(j+2)` solution `c · ε`.  Together with the engine this reduces every rung to exact
linear algebra in the layer `λ_{j+1}/λ_{j+2}`: the defect is a central class, the reachable
costs are the bracket images and the `x₁`-bundles of the carrier, and nothing else moves. -/
theorem gLad_step {A B : ℤ_[2]} {j : ℕ} (hj : 2 ≤ j)
    {c ε : Fin (sqRank h) → (DSq h : Type)} (hc : c ∈ gRowSet h A B (j + 1))
    (hεmem : ∀ i, ε i ∈ twoCentralSeries (DSq h : Type) j)
    (hεlam : ∀ i, nuLam h (ε i) = 1) (hεnu : ∀ i, nuSq h (ε i) = 1)
    (hkill : levelMk (DSq h : Type) (j + 2) (sqRelWord (gRowMark h A B c))
        * gLadCost (fun i => levelMk (DSq h : Type) (j + 2) (gRowMark h A B c i))
          (fun i => levelMk (DSq h : Type) (j + 2) (ε i)) = 1) :
    (fun i => c i * ε i) ∈ gRowSet h A B (j + 2) := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨⟨hc2, hclam⟩, hcnu⟩ := gRow_mem_corr.mp (hc.1 i)
    refine gRow_mem_corr.mpr ⟨⟨Subgroup.mul_mem _ hc2 ?_, ?_⟩, ?_⟩
    · exact twoCentralSeries_antitone (DSq h : Type) hj (hεmem i)
    · rw [map_mul, hclam, hεlam i, mul_one]
    · rw [map_mul, hcnu, hεnu i, mul_one]
  · have hone : levelMk (DSq h : Type) (j + 2)
        (sqRelWord (gRowMark h A B fun i => c i * ε i)) = 1 := by
      have hmk : levelMk (DSq h : Type) (j + 2)
          (sqRelWord (gRowMark h A B fun i => c i * ε i))
          = sqRelWord fun i => levelMk (DSq h : Type) (j + 2) (gRowMark h A B c i)
              * levelMk (DSq h : Type) (j + 2) (ε i) := by
        rw [gLad_mark_mul, map_sqRelWord]
        simp only [map_mul]
      rw [hmk, gLad_relWord_incr hj _ _ fun i => ⟨ε i, hεmem i, rfl⟩, ← map_sqRelWord]
      exact hkill
    exact (QuotientGroup.eq_one_iff _).mp hone

end Step

/-! ## §5 The pivot twist in `Q₄`, exactly

The bare rung-4 defect.  On the unit locus the marked letters are `s·q·z`, `x·q`, `y·q²`
with `q` the `B`-th pivot power and `z` a square; the `z`-part and the corrections are `λ₂`
and priced by the engine, so the whole class-4 content of the bare frame is the `q`-twist of
the core word by an arbitrary letter `q`.  This section computes it in closed form: the
`λ₂`-part `[s,q]·[q,x]` and five central classes.  Everything is exact in `Q₄`; no parity is
consumed here. -/

section QTwist

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Squares of `Q₄` lie in the `λ₂`-image. -/
theorem gLad_sq_mem_two (p : levelQuot G 4) : p ^ 2 ∈ lambdaImage G 2 4 := by
  obtain ⟨v, rfl⟩ := levelMk_surjective G 4 p
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G (Subgroup.mem_top v), by rw [map_pow]⟩

/-- `⁅λ₂, λ₂⁆` dies in `Q₄` (the depth-two instance of the vanishing). -/
theorem gLad_vanish4 {e f : levelQuot G 4} (he : e ∈ lambdaImage G 2 4)
    (hf : f ∈ lambdaImage G 2 4) : commP e f = 1 :=
  gLad_vanish (j := 2) he hf

/-- `λ₂`-images commute in `Q₄`. -/
theorem gLad_two_comm {e f : levelQuot G 4} (he : e ∈ lambdaImage G 2 4)
    (hf : f ∈ lambdaImage G 2 4) : e * f = f * e := by
  have h := gLad_swap e f
  rwa [gLad_vanish4 he hf, mul_one] at h

/-- Brackets out of a `λ₂`-product split, in `Q₄`. -/
theorem gLad_commP_mul_left_two {e f : levelQuot G 4} (he : e ∈ lambdaImage G 2 4)
    (g : levelQuot G 4) : commP (e * f) g = commP e g * commP f g := by
  rw [cfour_commP_mul_left, cfive_commP_zLayer_left (cfour_commP_mem_zLayer_left he g) f,
    mul_one]

/-- A letter absorbs itself in its own bracket, exactly. -/
theorem gLad_commP_self_absorb {Q : Type*} [Group Q] (a k : Q) :
    commP a (a * k) = commP a k := by
  rw [cfour_commP_mul_right, bridge_comm_self, cfour_one_comm, mul_one, mul_one]

/-- The commutator factor of the core word reads the bracket, exactly. -/
theorem gLad_commP_conj_self {Q : Type*} [Group Q] (a u : Q) :
    commP a (conjP a u) = commP a (commP a u) := by
  rw [gLad_conjP_eq, gLad_commP_self_absorb]

/-- **The fourth power of a twisted letter**: `(xq)⁴ = x⁴ q⁴ [q,x]²` in `Q₄`. -/
theorem gLad_qtwist_four (x q : levelQuot G 4) :
    (x * q) ^ 4 = x ^ 4 * q ^ 4 * commP q x ^ 2 := by
  have hz : commP (commP q x) q ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo q x) q
  have hsq : (x * q) ^ 2 = x ^ 2 * q ^ 2 * commP q x * commP (commP q x) q := cfour_sq_mul x q
  have hA : (x ^ 2 * q ^ 2 * commP q x * commP (commP q x) q) ^ 2
      = (x ^ 2 * q ^ 2 * commP q x) ^ 2 := by
    rw [cfour_sq_mul (x ^ 2 * q ^ 2 * commP q x) (commP (commP q x) q),
      cfive_commP_zLayer_left hz, cfour_one_comm, mul_one, mul_one, zLayer_sq G hz, mul_one]
  have hcm : commP (commP q x) (x ^ 2 * q ^ 2) = 1 := by
    rw [cfive_commP_right_hom (gLad_le_two le_rfl (cfour_commP_mem_lambdaTwo q x)) (x ^ 2)
      (q ^ 2), gLad_vanish4 (cfour_commP_mem_lambdaTwo q x) (gLad_sq_mem_two q),
      gLad_vanish4 (cfour_commP_mem_lambdaTwo q x) (gLad_sq_mem_two x), mul_one]
  have hB : (x ^ 2 * q ^ 2 * commP q x) ^ 2 = (x ^ 2 * q ^ 2) ^ 2 * commP q x ^ 2 := by
    rw [cfour_sq_mul (x ^ 2 * q ^ 2) (commP q x), hcm, cfour_one_comm, mul_one, mul_one]
  have hC : (x ^ 2 * q ^ 2) ^ 2 = x ^ 4 * q ^ 4 := by
    rw [cfour_sq_mul (x ^ 2) (q ^ 2), gLad_vanish4 (gLad_sq_mem_two q) (gLad_sq_mem_two x),
      cfour_one_comm, mul_one, mul_one, ← pow_mul, ← pow_mul]
  calc (x * q) ^ 4 = ((x * q) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = x ^ 4 * q ^ 4 * commP q x ^ 2 := by rw [hsq, hA, hB, hC]

/-- **The twisted bracket**: `[xq, sq] = [x,q][x,s][q,s]` up to two central classes, in
`Q₄`. -/
theorem gLad_qtwist_comm (s x q : levelQuot G 4) :
    commP (x * q) (s * q)
      = commP x q * commP x s * commP q s
        * (commP (commP x q) q * commP (commP q s) q) := by
  have hξ : commP (commP x s) q ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo x s) q
  have hζ₁ : commP (commP x q) q ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo x q) q
  have hζ₂ : commP (commP q s) q ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo q s) q
  have h1 : commP x (s * q) = commP x q * commP x s * commP (commP x s) q :=
    cfour_commP_mul_right x s q
  have h2 : commP q (s * q) = commP q s * commP (commP q s) q := by
    rw [cfour_commP_mul_right, bridge_comm_self, one_mul]
  have h3 : commP (commP x (s * q)) q
      = commP (commP x q) q * commP (commP x s) q := by
    rw [h1, gLad_commP_mul_left_two (Subgroup.mul_mem _ (cfour_commP_mem_lambdaTwo x q)
        (cfour_commP_mem_lambdaTwo x s)) q,
      gLad_commP_mul_left_two (cfour_commP_mem_lambdaTwo x q) q,
      cfive_commP_zLayer_left hξ q, mul_one]
  rw [cfour_commP_mul_left x q (s * q), h3, h1, h2]
  calc commP x q * commP x s * commP (commP x s) q
        * (commP (commP x q) q * commP (commP x s) q) * (commP q s * commP (commP q s) q)
      = commP x q * commP x s
        * (commP (commP x s) q * (commP (commP x q) q * commP (commP x s) q) * commP q s)
        * commP (commP q s) q := by group
    _ = commP x q * commP x s
        * (commP q s * (commP (commP x s) q * (commP (commP x q) q * commP (commP x s) q)))
        * commP (commP q s) q := by
        rw [(zLayer_commute (Subgroup.mul_mem _ hξ (Subgroup.mul_mem _ hζ₁ hξ))
          (commP q s)).eq]
    _ = commP x q * commP x s * commP q s
        * (commP (commP x s) q * commP (commP x q) q * commP (commP x s) q)
        * commP (commP q s) q := by group
    _ = commP x q * commP x s * commP q s
        * (commP (commP x q) q * commP (commP x s) q * commP (commP x s) q)
        * commP (commP q s) q := by
        rw [(zLayer_commute hξ (commP (commP x q) q)).eq]
    _ = commP x q * commP x s * commP q s
        * (commP (commP x q) q * commP (commP x s) q ^ 2) * commP (commP q s) q := by
        rw [mul_assoc (commP (commP x q) q), ← pow_two]
    _ = commP x q * commP x s * commP q s
        * (commP (commP x q) q * commP (commP q s) q) := by
        rw [zLayer_sq G hξ, mul_one]
        group

/-- **The twisted square slot**: `(y q²)² = y² · q⁴ [q², y]` in `Q₄`. -/
theorem gLad_qtwist_sqslot (y q : levelQuot G 4) :
    (y * q ^ 2) ^ 2 = y ^ 2 * (q ^ 4 * commP (q ^ 2) y) := by
  have hz : commP (q ^ 2) y ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (gLad_sq_mem_two q) y
  rw [cfour_sq_mul y (q ^ 2), cfive_commP_zLayer_left hz, mul_one, ← pow_mul]
  group

/-- **The twisted commutator slot is blind up to one class**:
`[yq², (yq²)^{sq}] = [y, y^s] · [y,[y,q]]` in `Q₄`. -/
theorem gLad_qtwist_commslot (s y q : levelQuot G 4) :
    commP (y * q ^ 2) (conjP (y * q ^ 2) (s * q))
      = commP y (conjP y s) * commP y (commP y q) := by
  have hq2 : (q ^ 2 : levelQuot G 4) ∈ lambdaImage G 2 4 := gLad_sq_mem_two q
  have hξ : commP (commP y s) q ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo y s) q
  have hζ : commP (q ^ 2) (s * q) ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left hq2 (s * q)
  -- the bracket of the twisted letter against the twisted `s`-letter
  have hk : commP (y * q ^ 2) (s * q)
      = commP y q * commP y s * (commP (commP y s) q * commP (q ^ 2) (s * q)) := by
    rw [cfour_commP_mul_left y (q ^ 2) (s * q),
      gLad_vanish4 (cfour_commP_mem_lambdaTwo y (s * q)) hq2, mul_one,
      cfour_commP_mul_right y s q]
    group
  have hkmem : commP (y * q ^ 2) (s * q) ∈ lambdaImage G 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  -- the outer bracket collapses onto the `y`-letter
  have houter : commP (y * q ^ 2) (commP (y * q ^ 2) (s * q))
      = commP y (commP (y * q ^ 2) (s * q)) := by
    rw [cfour_commP_mul_left y (q ^ 2) (commP (y * q ^ 2) (s * q)),
      cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right y hkmem) (q ^ 2), mul_one,
      gLad_vanish4 hq2 hkmem, mul_one]
  -- the inner value reads the two `y`-brackets
  have hinner : commP y (commP y q * commP y s * (commP (commP y s) q * commP (q ^ 2) (s * q)))
      = commP y (commP y s) * commP y (commP y q) := by
    have hzz : commP (commP y s) q * commP (q ^ 2) (s * q) ∈ zLayer G 3 :=
      Subgroup.mul_mem _ hξ hζ
    rw [cfour_commP_mul_right y (commP y q * commP y s)
        (commP (commP y s) q * commP (q ^ 2) (s * q)),
      gLad_commP_zLayer_right y hzz, one_mul,
      cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right y
        (Subgroup.mul_mem _ (cfour_commP_mem_lambdaTwo y q)
          (cfour_commP_mem_lambdaTwo y s))) _, mul_one,
      cfour_commP_mul_right y (commP y q) (commP y s),
      cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right y
        (cfour_commP_mem_lambdaTwo y q)) (commP y s), mul_one]
  rw [gLad_commP_conj_self (y * q ^ 2) (s * q), houter, hk, hinner,
    gLad_commP_conj_self y s]

end QTwist

end SqCore

end Dyadic

end GQ2
