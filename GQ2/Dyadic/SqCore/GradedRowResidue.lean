/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedRowLadder
import GQ2.Dyadic.SqCore.GradedClassFourDefect

/-!
# W87-BLOCK: rung 4 of the row ladder, decided at every residue

Wave 86 (`GradedRowLadder.lean`) proved rung 4 of the row-move ladder free on the quarter
locus `4 | A - 1`, `4 | B` and reduced it at every other residue of `(A - 1, B)` to the exact
equation `defect * gLadCost = 1` in the layer `lambda_3/lambda_4`.  The wave-86 note mapped
the reachability analysis and isolated the bracket-square block, with the y-legged triple
`[[sigma, x_0], x_1]` guarding it, as the first genuine question.  This module decides that
question, POSITIVELY, at all three open mod-4 residues, and with them on the whole unit
locus: rung 4 of the row ladder is a theorem wherever the consumer asks for it.

## The decision

1. **The pivot exponent obeys `c_0 = 3 mod 4`** (section 1): `X^{c_0} = S` with
   `X = 5 mod 16`, `S = 13 mod 16` forces it, through the closed subgroup `1 + 16 Z_2` of
   `Z_2^x`.  Consequently the pivot splits as `w = sigma * (x_0 * z)` with `z` a CENTRAL
   class of `Q_4` (section 2): every pivot-power bracket collapses onto the two core letters.

2. **The defect in closed form at every residue** (sections 3 to 5).  With
   `zeta = [S, X]` the whole class-4 defect of the bare frame is built from five atoms:
   `zeta^2`, `[zeta, X]`, `[zeta, S]`, the y-squares `[S,Y]^2 [X,Y]^2`, and eight triples.
   On the even locus `2 | B` the defect is `1` for `t` even, so the free locus of rung 4
   grows from the quarter locus to the half locus `4 | A - 1 - B`, and equals the single
   element `gRsdKillE = zeta^2 [zeta,X] [zeta,S]` for `t` odd.  At odd `B` the y-block
   appears and the two-y triples `[[S,Y],Y]`, `[[X,Y],Y]` enter.

3. **The block is reachable** (section 6).  The engine costs of explicit carrier tuples
   built from the three commutators `[sigma, x_0]`, `[sigma, x_1]`, `[x_0, x_1]` evaluate to
   EXACTLY the defect: the bracket square rides the `x_1`-bundle, and the guarding y-triple
   `[zeta, Y]` Jacobi-rotates onto an s-legged and an x-legged triple, which are slot costs.
   The kill equation is then `defect * cost = cost^2 = 1`, an involution of the layer.

4. **Rung 4 everywhere** (section 7): `(gRowSet h A B 4).Nonempty` at every `(A, B)` on the
   unit locus (`gRsd_nonempty_four`), so the residual of the row ladder starts at class
   FIVE, the same threshold as the M6 ladder after `mpcBld_nonempty_four`.  The sharpened
   conditional chain to the odd-degree classification is recorded in section 8.

## Honesty

The wave-86 note's framing of the block ("reachable only inside bundles", membership in
`sq(ker bY)`) was too pessimistic: y-legged triples with both inner letters distinct from
`x_1` rotate out of the y-slot by Jacobi, which the note's species count missed.  The note's
first genuine question is nevertheless exactly what section 6 answers, and the answer is
YES at every residue.  Rungs `k >= 5` are NOT decided here: each higher rung is a fresh
linear-algebra question one layer up, reachable by the same engine.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3**
(`propext`, `Classical.choice`, `Quot.sound`) or a subset.  Pins in section 10.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The pivot exponent is `3 mod 4`

`X^{c_0} = S` with `X = 5`, `S = 13 mod 16`.  If `c_0` were `1 mod 4` then `S X^{-1}`
would be a `Z_2`-power of `X^4`, hence `1 mod 16`; but `S - X = 8 * unit` exactly.  The
congruence is the arithmetic seed of the whole module: it is what makes the pivot's
`x_0`-tail central at class 4. -/

section PivotExp

/-- The set of units congruent to `1 mod 16`, as a subgroup of `Z_2^x`. -/
noncomputable def gRsdSixteen : Subgroup ℤ_[2]ˣ where
  carrier := {u | (2 : ℤ_[2]) ^ 4 ∣ (u : ℤ_[2]) - 1}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨16 * s * t + s + t, ?_⟩
    rw [Units.val_mul]
    linear_combination (b : ℤ_[2]) * hs + (1 + 16 * s) * ht
  inv_mem' := by
    rintro a ⟨s, hs⟩
    refine ⟨-(((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * s), ?_⟩
    have hav : ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (a : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (-((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hs + hav

theorem gRsd_mem_sixteen_iff {u : ℤ_[2]ˣ} :
    u ∈ gRsdSixteen ↔ (2 : ℤ_[2]) ^ 4 ∣ (u : ℤ_[2]) - 1 := Iff.rfl

/-- The congruence subgroup is closed: divisibility is a closed condition on the ball. -/
theorem gRsd_isClosed_sixteen : IsClosed ((gRsdSixteen : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) := by
  have hdvd : IsClosed {z : ℤ_[2] | (2 : ℤ_[2]) ^ 4 ∣ z} := by
    have hset : {z : ℤ_[2] | (2 : ℤ_[2]) ^ 4 ∣ z}
        = Metric.closedBall 0 (((2 : ℕ) : ℝ) ^ (-((4 : ℕ) : ℤ))) := by
      ext z
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
      rw [h2]
    rw [hset]
    exact Metric.isClosed_closedBall
  have hset : ((gRsdSixteen : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ)
      = (fun u : ℤ_[2]ˣ => (u : ℤ_[2]) - 1) ⁻¹' {z : ℤ_[2] | (2 : ℤ_[2]) ^ 4 ∣ z} := rfl
  rw [hset]
  exact IsClosed.preimage ((Units.continuous_val).sub continuous_const) hdvd

/-- The fourth power of `X` is `1 mod 16`: pure ring algebra from `X - 1 = 4 * unit`. -/
theorem gRsd_rootX_four_mem : rootXUnit ^ 4 ∈ gRsdSixteen := by
  obtain ⟨a, ha⟩ := rootX_sub_one_eq
  have hX : rootX = 1 + 4 * (a : ℤ_[2]) := by linear_combination ha
  refine ⟨(a : ℤ_[2]) * (1 + 2 * a) * (1 + 4 * a + 8 * (a : ℤ_[2]) ^ 2), ?_⟩
  have hval : ((rootXUnit ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) = rootX ^ 4 := by
    rw [Units.val_pow_eq_pow_val]; rfl
  rw [hval, hX]
  ring

/-- `S - X = 8 * unit`: the exact level of the separator, from the mod-16 pins. -/
theorem gRsd_Sval_sub_rootX : ∃ w : ℤ_[2], ¬ (2 : ℤ_[2]) ∣ w ∧ Sval - rootX = 8 * w := by
  have hmem : Sval - rootX - 8 ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 4) := by
    rw [RingHom.mem_ker, map_sub, map_sub, Sval_toZModPow_four, rootX_toZModPow_four,
      map_ofNat]
    decide
  rw [PadicInt.ker_toZModPow] at hmem
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨1 + 2 * k, fun hdvd => ?_, by linear_combination hk⟩
  obtain ⟨e, he⟩ := hdvd
  have h21 : (2 : ℤ_[2]) ∣ 1 := ⟨e - k, by linear_combination he⟩
  exact (isUnit_iff_not_two_dvd.mp (isUnit_of_dvd_one h21)) ⟨1, (mul_one 2).symm⟩

/-- ⭐⭐ **The pivot exponent congruence**: `4 | c_0 + 1`, i.e. `c_0 = 3 mod 4`.  If not,
oddness puts `c_0 = 1 mod 4`, so `S X^{-1}` is a `Z_2`-power of `X^4`, hence lies in the
closed subgroup `1 + 16 Z_2`; but `S - X = 8 * unit` exactly.  This single bit of arithmetic
is what makes the pivot's `x_0`-tail a CENTRAL class of `Q_4` (section 2), and through it
every closed defect form below. -/
theorem gRsd_pivotExp_congr : (4 : ℤ_[2]) ∣ sqPivotExp + 1 := by
  by_contra hcon
  -- oddness forces `4 | c_0 - 1`
  obtain ⟨d, hd⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
  have hdeven : (2 : ℤ_[2]) ∣ d := by
    by_contra hdodd
    obtain ⟨e, he⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hdodd) isUnit_one
    exact hcon ⟨1 + e, by linear_combination hd + 2 * he⟩
  obtain ⟨e, he⟩ := hdeven
  have hc : sqPivotExp = 1 + 4 * e := by linear_combination hd + 2 * he
  -- `S X^{-1}` is a `Z_2`-power of `X^4`
  have hS : SvalUnit = rootXUnit * zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 4) e := by
    have h4 : zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 4) e
        = zpowZtwo isProP_two_unitsPadicInt rootXUnit (4 * e) := by
      rw [show (rootXUnit ^ 4 : ℤ_[2]ˣ)
          = zpowZtwo isProP_two_unitsPadicInt rootXUnit ((4 : ℕ) : ℤ_[2]) from
          (zpowZtwo_natCast isProP_two_unitsPadicInt rootXUnit 4).symm,
        zpowZtwo_zpowZtwo]
      norm_num
    rw [h4, ← zpowZtwo_one_exp isProP_two_unitsPadicInt rootXUnit, zpowZtwo_zpowZtwo,
      one_mul, ← zpowZtwo_add, ← hc, zpowZtwo_rootXUnit_sqPivotExp]
  -- hence `S X^{-1} = 1 mod 16`
  have hmemM : zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 4) e ∈ gRsdSixteen := by
    have hle : (Subgroup.closure ({rootXUnit ^ 4} : Set ℤ_[2]ˣ)).topologicalClosure
        ≤ gRsdSixteen := by
      refine Subgroup.topologicalClosure_minimal _ ?_ gRsd_isClosed_sixteen
      refine (Subgroup.closure_le _).2 ?_
      rintro u rfl
      exact gRsd_rootX_four_mem
    exact hle (zpowZtwo_mem_topologicalClosure isProP_two_unitsPadicInt (rootXUnit ^ 4) e)
  obtain ⟨s, hs⟩ := gRsd_mem_sixteen_iff.mp hmemM
  -- against the exact level of `S - X`
  obtain ⟨w, hwodd, hw⟩ := gRsd_Sval_sub_rootX
  have hSX : Sval - rootX = rootX * (2 ^ 4 * s) := by
    have hSval : (SvalUnit : ℤ_[2])
        = rootX * ((zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 4) e : ℤ_[2]ˣ) : ℤ_[2]) := by
      rw [hS, Units.val_mul]; rfl
    calc Sval - rootX
        = rootX * (((zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 4) e : ℤ_[2]ˣ) : ℤ_[2]) - 1)
          := by rw [show Sval = (SvalUnit : ℤ_[2]) from rfl, hSval]; ring
      _ = rootX * (2 ^ 4 * s) := by rw [hs]
  have h8 : (8 : ℤ_[2]) * w = 8 * (2 * (rootX * s)) := by linear_combination hSX - hw
  exact hwodd ⟨rootX * s, mul_left_cancel₀ (by norm_num : (8 : ℤ_[2]) ≠ 0) h8⟩

end PivotExp

/-! ## §2 The pivot splits over the core letters, centrally

`w = sigma * x_0^{-c_0}` with `4 | c_0 + 1` makes `x_0^{-(c_0 + 1)}` a fourth `x_0`-power,
hence a CENTRAL class of `Q_4`.  So `W = S * (X * Z)` with `Z` central: every pivot bracket
of class 4 collapses onto the two core letters, and the odd pivot powers inherit the same
shape.  Everything below is in `Q_4 = levelQuot (D_sq h) 4`. -/

section PivotSplit

variable {h : ℕ}

/-- Same-base `Z_2`-powers commute. -/
theorem gRsd_zpow_commute {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P) (g : P)
    (a b : ℤ_[2]) : Commute (zpowZtwo hP g a) (zpowZtwo hP g b) := by
  show _ * _ = _ * _
  rw [← zpowZtwo_add, ← zpowZtwo_add, add_comm]

/-- The `Q_4`-class of a `4 Z_2`-power of any element is central. -/
theorem gRsd_zpow_mem_zLayer_of_four (g : (DSq h : Type)) {a : ℤ_[2]} (ha : (4 : ℤ_[2]) ∣ a) :
    levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g a) ∈ zLayer (DSq h : Type) 3 := by
  obtain ⟨b, rfl⟩ := ha
  have hsplit : (4 : ℤ_[2]) * b = 2 * (2 * b) := by ring
  rw [hsplit, zpowZtwo_two_mul, map_pow]
  refine cfour_sq_mem_zLayer ?_
  rw [zpowZtwo_two_mul, map_pow]
  exact cfour_sq_mem_lambdaTwo _

/-- The central tail of the pivot: the `Q_4`-class of `x_0^{-(c_0 + 1)}`. -/
noncomputable def gRsdZ (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  levelMk (DSq h : Type) 4 ((zpowZtwo (isProP_DSq h) (dsqX0 h) (sqPivotExp + 1))⁻¹)

/-- The tail is central. -/
theorem gRsdZ_mem : gRsdZ h ∈ zLayer (DSq h : Type) 3 := by
  rw [gRsdZ, map_inv]
  exact (zLayer (DSq h : Type) 3).inv_mem
    (gRsd_zpow_mem_zLayer_of_four (dsqX0 h) gRsd_pivotExp_congr)

/-- ⭐⭐ **The pivot splits over the core letters**: `W = S * (X * Z)` in `Q_4`, with `Z`
central.  The bracket calculus of every pivot power reduces to the two core letters. -/
theorem gRsd_W_split : gLadQ h 1 = gLadS h * (gLadX h * gRsdZ h) := by
  have helem : zpowZtwo (isProP_DSq h) (sqPivot h) 1
      = dsqSigma h * (dsqX0 h * (zpowZtwo (isProP_DSq h) (dsqX0 h) (sqPivotExp + 1))⁻¹) := by
    rw [zpowZtwo_one_exp]
    show sqMixPivotElem h sqPivotExp = _
    rw [sqMixPivotElem]
    congr 1
    have hsplit : zpowZtwo (isProP_DSq h) (dsqX0 h) (sqPivotExp + 1)
        = zpowZtwo (isProP_DSq h) (dsqX0 h) 1 * zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp
        := by rw [← zpowZtwo_add, add_comm]
    have hcomm : Commute (dsqX0 h) ((zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp)⁻¹) := by
      have h1 := gRsd_zpow_commute (isProP_DSq h) (dsqX0 h) 1 sqPivotExp
      rw [zpowZtwo_one_exp] at h1
      exact h1.inv_right
    rw [eq_comm, hsplit, zpowZtwo_one_exp, mul_inv_rev, ← mul_assoc, hcomm.eq, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [gLadQ, helem, map_mul, map_mul, map_inv]
  rfl

/-- Pivot powers are additive in the exponent. -/
theorem gRsdQ_add (a b : ℤ_[2]) : gLadQ h (a + b) = gLadQ h a * gLadQ h b := by
  rw [gLadQ, gLadQ, gLadQ, zpowZtwo_add, map_mul]

/-- Pivot powers commute with one another in `Q_4`. -/
theorem gRsdQ_commP (a b : ℤ_[2]) : commP (gLadQ h a) (gLadQ h b) = 1 := by
  have hc : Commute (gLadQ h a) (gLadQ h b) := by
    show _ * _ = _ * _
    rw [← gRsdQ_add, ← gRsdQ_add, add_comm]
  show (gLadQ h a)⁻¹ * (gLadQ h b)⁻¹ * gLadQ h a * gLadQ h b = 1
  rw [mul_assoc, hc.eq]
  group

/-- Even pivot powers are `lambda_2`-classes. -/
theorem gRsd_Q_even_mem {c : ℤ_[2]} (hc : (2 : ℤ_[2]) ∣ c) :
    gLadQ h c ∈ lambdaImage (DSq h : Type) 2 4 := by
  obtain ⟨b, rfl⟩ := hc
  rw [gLadQ_two_mul]
  exact gLadQ_sq_mem b

end PivotSplit

end SqCore

end Dyadic

end GQ2
