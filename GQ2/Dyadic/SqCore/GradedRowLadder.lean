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

end SqCore

end Dyadic

end GQ2
