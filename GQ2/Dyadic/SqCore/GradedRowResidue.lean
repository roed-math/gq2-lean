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

/-! ## §3 The five atoms, and the bracket calculus of pivot powers

The whole class-4 content of the residues is built from `zeta = [S, X]`, its two triples
`[zeta, X]`, `[zeta, S]`, the two y-brackets `xiS = [S, Y]`, `xiX = [X, Y]`, their squares,
their s/x-triples, and their two-y triples.  This section evaluates every pivot-power
bracket the defect contains against those atoms, exactly, in `Q_4`. -/

section Atoms

variable {h : ℕ}

/-- The block atom: `zeta = [S, X]` in `Q_4`. -/
noncomputable def gRsdZeta (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gLadS h) (gLadX h)

/-- The y-atoms: `xiS = [S, Y]` and `xiX = [X, Y]` in `Q_4`. -/
noncomputable def gRsdXiS (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gLadS h) (gLadY h)

noncomputable def gRsdXiX (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gLadX h) (gLadY h)

theorem gRsdZeta_mem : gRsdZeta h ∈ lambdaImage (DSq h : Type) 2 4 :=
  cfour_commP_mem_lambdaTwo _ _

theorem gRsdXiS_mem : gRsdXiS h ∈ lambdaImage (DSq h : Type) 2 4 :=
  cfour_commP_mem_lambdaTwo _ _

theorem gRsdXiX_mem : gRsdXiX h ∈ lambdaImage (DSq h : Type) 2 4 :=
  cfour_commP_mem_lambdaTwo _ _

theorem gRsdZetaX_mem : commP (gRsdZeta h) (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
  cfour_commP_mem_zLayer_left gRsdZeta_mem _

theorem gRsdZetaS_mem : commP (gRsdZeta h) (gLadS h) ∈ zLayer (DSq h : Type) 3 :=
  cfour_commP_mem_zLayer_left gRsdZeta_mem _

/-- The even-locus kill element: `zeta^2 [zeta,X] [zeta,S]`. -/
noncomputable def gRsdKillE (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h))

theorem gRsdKillE_mem : gRsdKillE h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ (cfour_sq_mem_zLayer gRsdZeta_mem)
    (Subgroup.mul_mem _ gRsdZetaX_mem gRsdZetaS_mem)

/-- A `lambda_2`-class brackets an odd-shaped power through the two core letters. -/
theorem gRsd_lam_shape {E V : levelQuot (DSq h : Type) 4}
    (hE : E ∈ lambdaImage (DSq h : Type) 2 4) (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP E (gLadS h * (gLadX h * V)) = commP E (gLadX h) * commP E (gLadS h) := by
  rw [cfive_commP_right_hom hE (gLadS h) (gLadX h * V),
    cfive_commP_right_hom hE (gLadX h) V, gLad_commP_zLayer_right E hV, one_mul]

/-- The sigma bracket of an odd-shaped power is exactly `zeta`. -/
theorem gRsd_S_shape {V : levelQuot (DSq h : Type) 4} (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP (gLadS h) (gLadS h * (gLadX h * V)) = gRsdZeta h := by
  rw [cfour_commP_mul_right (gLadS h) (gLadS h) (gLadX h * V), cfour_comm_self,
    cfour_one_comm, mul_one, mul_one, cfour_commP_mul_right (gLadS h) (gLadX h) V,
    gLad_commP_zLayer_right (gLadS h) hV, one_mul,
    gLad_commP_zLayer_right (commP (gLadS h) (gLadX h)) hV, mul_one]
  rfl

/-- The x-bracket of an odd-shaped power is exactly `zeta * [zeta, X]`. -/
theorem gRsd_shape_X {V : levelQuot (DSq h : Type) 4} (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP (gLadS h * (gLadX h * V)) (gLadX h)
      = gRsdZeta h * commP (gRsdZeta h) (gLadX h) := by
  rw [cfour_commP_mul_left (gLadS h) (gLadX h * V) (gLadX h),
    show commP (gLadS h) (gLadX h) = gRsdZeta h from rfl,
    cfive_commP_right_hom gRsdZeta_mem (gLadX h) V,
    gLad_commP_zLayer_right (gRsdZeta h) hV, one_mul,
    cfour_commP_mul_left (gLadX h) V (gLadX h), cfour_comm_self, cfour_one_comm, one_mul,
    one_mul, cfive_commP_zLayer_left hV (gLadX h), mul_one]

/-- The inverse-sigma bracket of an odd-shaped power: `[Q, S] = [X, S]`. -/
theorem gRsd_shape_S {V : levelQuot (DSq h : Type) 4} (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP (gLadS h * (gLadX h * V)) (gLadS h) = commP (gLadX h) (gLadS h) := by
  rw [cfour_commP_mul_left (gLadS h) (gLadX h * V) (gLadS h), cfour_comm_self,
    cfour_one_comm, one_mul, one_mul,
    cfour_commP_mul_left (gLadX h) V (gLadS h),
    gLad_commP_zLayer_right (commP (gLadX h) (gLadS h)) hV, mul_one,
    cfive_commP_zLayer_left hV (gLadS h), mul_one]

/-- The x-side self bracket of an odd-shaped power: `[X, Q] = [X, S] * [[X, S], X]`. -/
theorem gRsd_X_shape {V : levelQuot (DSq h : Type) 4} (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP (gLadX h) (gLadS h * (gLadX h * V))
      = commP (gLadX h) (gLadS h) * commP (commP (gLadX h) (gLadS h)) (gLadX h) := by
  rw [cfour_commP_mul_right (gLadX h) (gLadS h) (gLadX h * V),
    cfour_commP_mul_right (gLadX h) (gLadX h) V, cfour_comm_self, cfour_one_comm, mul_one,
    mul_one, gLad_commP_zLayer_right (gLadX h) hV, one_mul,
    cfive_commP_right_hom (cfour_commP_mem_lambdaTwo (gLadX h) (gLadS h)) (gLadX h) V,
    gLad_commP_zLayer_right (commP (gLadX h) (gLadS h)) hV, one_mul]

/-- The y-bracket of an odd-shaped power: `[Y, Q] = [Y, X] * [Y, S] * [[Y, S], X]`. -/
theorem gRsd_Y_shape {V : levelQuot (DSq h : Type) 4} (hV : V ∈ zLayer (DSq h : Type) 3) :
    commP (gLadY h) (gLadS h * (gLadX h * V))
      = commP (gLadY h) (gLadX h) * commP (gLadY h) (gLadS h)
        * commP (commP (gLadY h) (gLadS h)) (gLadX h) := by
  rw [cfour_commP_mul_right (gLadY h) (gLadS h) (gLadX h * V),
    cfour_commP_mul_right (gLadY h) (gLadX h) V,
    gLad_commP_zLayer_right (gLadY h) hV, one_mul,
    gLad_commP_zLayer_right (commP (gLadY h) (gLadX h)) hV, mul_one,
    cfive_commP_right_hom (cfour_commP_mem_lambdaTwo (gLadY h) (gLadS h)) (gLadX h) V,
    gLad_commP_zLayer_right (commP (gLadY h) (gLadS h)) hV, one_mul]

end Atoms

/-! ## §4 The pivot-power brackets, at every parity

`W = S(XZ)` gives the base values; additivity in the exponent and the central `4 Z_2`-powers
extend them to every even power `2b` with `b` odd, which is all the defect consumes. -/

section PowerBrackets

variable {h : ℕ}

theorem gRsd_S_W : commP (gLadS h) (gLadQ h 1) = gRsdZeta h := by
  rw [gRsd_W_split]
  exact gRsd_S_shape gRsdZ_mem

theorem gRsd_W_X :
    commP (gLadQ h 1) (gLadX h) = gRsdZeta h * commP (gRsdZeta h) (gLadX h) := by
  rw [gRsd_W_split]
  exact gRsd_shape_X gRsdZ_mem

theorem gRsd_zeta_W :
    commP (gRsdZeta h) (gLadQ h 1)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
  rw [gRsd_W_split]
  exact gRsd_lam_shape gRsdZeta_mem gRsdZ_mem

/-- The sigma bracket of the pivot square is the even kill element. -/
theorem gRsd_S_Wsq : commP (gLadS h) (gLadQ h 2) = gRsdKillE h := by
  have h2 : gLadQ h 2 = gLadQ h 1 * gLadQ h 1 := by
    rw [← gRsdQ_add]
    norm_num
  rw [h2, cfour_commP_mul_right (gLadS h) (gLadQ h 1) (gLadQ h 1), gRsd_S_W, gRsd_zeta_W,
    ← pow_two]
  rfl

/-- The x-bracket of the pivot square is the SAME even kill element. -/
theorem gRsd_Wsq_X : commP (gLadQ h 2) (gLadX h) = gRsdKillE h := by
  have h2 : gLadQ h 2 = gLadQ h 1 ^ 2 := by
    rw [← gLadQ_two_mul]
    norm_num
  rw [h2, gThreeFour_commP_sq_left (gLadQ h 1) (gLadX h), gRsd_W_X,
    cfour_sq_mul (gRsdZeta h) (commP (gRsdZeta h) (gLadX h)),
    zLayer_sq (DSq h : Type) gRsdZetaX_mem, mul_one,
    cfive_commP_zLayer_left gRsdZetaX_mem (gRsdZeta h), cfour_one_comm, mul_one, mul_one,
    cfour_commP_mul_left (gRsdZeta h) (commP (gRsdZeta h) (gLadX h)) (gLadQ h 1),
    gRsd_zeta_W,
    cfive_commP_zLayer_left (Subgroup.mul_mem _ gRsdZetaX_mem gRsdZetaS_mem)
      (commP (gRsdZeta h) (gLadX h)), mul_one,
    cfive_commP_zLayer_left gRsdZetaX_mem (gLadQ h 1), mul_one]
  rfl

/-- The central complement of an even power `2b` at odd `b`. -/
theorem gRsd_Qeven_tail_zLayer {b : ℤ_[2]} (hb : ¬ (2 : ℤ_[2]) ∣ b) :
    gLadQ h (2 * b - 2) ∈ zLayer (DSq h : Type) 3 := by
  refine gLadQ_mem_zLayer_of_four ?_
  obtain ⟨d, hd⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hb) isUnit_one
  exact ⟨d, by linear_combination 2 * hd⟩

theorem gRsd_Qeven_split {b : ℤ_[2]} :
    gLadQ h (2 * b) = gLadQ h 2 * gLadQ h (2 * b - 2) := by
  rw [← gRsdQ_add, show (2 : ℤ_[2]) + (2 * b - 2) = 2 * b from by ring]

/-- ⭐ The x-bracket of EVERY even pivot power at odd half: the even kill element. -/
theorem gRsd_Qeven_X {b : ℤ_[2]} (hb : ¬ (2 : ℤ_[2]) ∣ b) :
    commP (gLadQ h (2 * b)) (gLadX h) = gRsdKillE h := by
  rw [gRsd_Qeven_split, cfour_commP_mul_left (gLadQ h 2) (gLadQ h (2 * b - 2)) (gLadX h),
    gRsd_Wsq_X, gLad_commP_zLayer_right (gRsdKillE h) (gRsd_Qeven_tail_zLayer hb), mul_one,
    cfive_commP_zLayer_left (gRsd_Qeven_tail_zLayer hb) (gLadX h), mul_one]

/-- ⭐ The sigma bracket of EVERY even pivot power at odd half: the SAME element. -/
theorem gRsd_S_Qeven {b : ℤ_[2]} (hb : ¬ (2 : ℤ_[2]) ∣ b) :
    commP (gLadS h) (gLadQ h (2 * b)) = gRsdKillE h := by
  rw [gRsd_Qeven_split, cfour_commP_mul_right (gLadS h) (gLadQ h 2) (gLadQ h (2 * b - 2)),
    gLad_commP_zLayer_right (gLadS h) (gRsd_Qeven_tail_zLayer hb), one_mul, gRsd_S_Wsq,
    gLad_commP_zLayer_right (gRsdKillE h) (gRsd_Qeven_tail_zLayer hb), mul_one]

/-- ⭐⭐ **The lambda_2-part of the defect dies on the whole even locus**: at every even `B`
the product `[S, Q] [Q, X]` is `1` in `Q_4`, either because `Q` is central (`4 | B`) or
because the two factors are the SAME involution (`B = 2 mod 4`). -/
theorem gRsd_SQ_QX_even {B : ℤ_[2]} (hB : (2 : ℤ_[2]) ∣ B) :
    commP (gLadS h) (gLadQ h B) * commP (gLadQ h B) (gLadX h) = 1 := by
  obtain ⟨b, rfl⟩ := hB
  by_cases hb : (2 : ℤ_[2]) ∣ b
  · obtain ⟨e, rfl⟩ := hb
    have hz : gLadQ h (2 * (2 * e)) ∈ zLayer (DSq h : Type) 3 :=
      gLadQ_mem_zLayer_of_four ⟨e, by ring⟩
    rw [gLad_commP_zLayer_right (gLadS h) hz, cfive_commP_zLayer_left hz (gLadX h), one_mul]
  · rw [gRsd_S_Qeven hb, gRsd_Qeven_X hb, ← pow_two,
      zLayer_sq (DSq h : Type) gRsdKillE_mem]

end PowerBrackets

/-! ## §5 The odd pivot powers

Every odd power is `S(XV)` with `V` central, possibly with one factor `W^2` peeled off; the
peeled factor is invisible in every slot the defect uses (it brackets to the involution
`gRsdKillE`, which squares away, or dies outright).  The atoms of the odd-`B` defect follow:
the pair `[S,Q][Q,X]`, the two rotated triples, the bracket square, the y-block of `Q^2`,
and the two-y triples of `[Y,[Y,Q]]`. -/

section OddPowers

variable {h : ℕ}

/-- The y-block squares: `[S,Y]^2 [X,Y]^2`. -/
noncomputable def gRsdYSq (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  gRsdXiS h ^ 2 * gRsdXiX h ^ 2

/-- The y-block triples: `[[S,Y],X] [[S,Y],S] [[X,Y],X] [[X,Y],S]`. -/
noncomputable def gRsdYTrip (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gRsdXiS h) (gLadX h) * commP (gRsdXiS h) (gLadS h)
    * (commP (gRsdXiX h) (gLadX h) * commP (gRsdXiX h) (gLadS h))

/-- The y-block of the even pivot powers: `[W^2, Y]`. -/
noncomputable def gRsdKillY (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  gRsdYSq h * gRsdYTrip h

/-- The two-y triples: `[[S,Y],Y] [[X,Y],Y]`. -/
noncomputable def gRsdYY (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gRsdXiS h) (gLadY h) * commP (gRsdXiX h) (gLadY h)

theorem gRsdYSq_mem : gRsdYSq h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ (cfour_sq_mem_zLayer gRsdXiS_mem) (cfour_sq_mem_zLayer gRsdXiX_mem)

theorem gRsdYTrip_mem : gRsdYTrip h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (cfour_commP_mem_zLayer_left gRsdXiS_mem _)
      (cfour_commP_mem_zLayer_left gRsdXiS_mem _))
    (Subgroup.mul_mem _ (cfour_commP_mem_zLayer_left gRsdXiX_mem _)
      (cfour_commP_mem_zLayer_left gRsdXiX_mem _))

theorem gRsdKillY_mem : gRsdKillY h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ gRsdYSq_mem gRsdYTrip_mem

theorem gRsdYY_mem : gRsdYY h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ (cfour_commP_mem_zLayer_left gRsdXiS_mem _)
    (cfour_commP_mem_zLayer_left gRsdXiX_mem _)

/-- `W^2` is a `lambda_2`-class. -/
theorem gRsd_Wsq_mem : gLadQ h 2 ∈ lambdaImage (DSq h : Type) 2 4 :=
  gRsd_Q_even_mem ⟨1, by norm_num⟩

/-- ⭐ **The odd-power dichotomy**: every odd pivot power is `S(XV)` with `V` central, or
`W^2` times such a shape. -/
theorem gRsd_Q_odd_cases {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    (∃ V ∈ zLayer (DSq h : Type) 3, gLadQ h c = gLadS h * (gLadX h * V)) ∨
    (∃ V ∈ zLayer (DSq h : Type) 3,
      gLadQ h c = gLadQ h 2 * (gLadS h * (gLadX h * V))) := by
  obtain ⟨d, hd⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hc) isUnit_one
  by_cases hdpar : (2 : ℤ_[2]) ∣ d
  · obtain ⟨e, he⟩ := hdpar
    have hc1 : (4 : ℤ_[2]) ∣ c - 1 := ⟨e, by linear_combination hd + 2 * he⟩
    refine Or.inl ⟨gRsdZ h * gLadQ h (c - 1),
      Subgroup.mul_mem _ gRsdZ_mem (gLadQ_mem_zLayer_of_four hc1), ?_⟩
    have hsplit : gLadQ h c = gLadQ h 1 * gLadQ h (c - 1) := by
      rw [← gRsdQ_add, show (1 : ℤ_[2]) + (c - 1) = c from by ring]
    rw [hsplit, gRsd_W_split, mul_assoc, mul_assoc]
  · obtain ⟨f, hf⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hdpar) isUnit_one
    have hc3 : (4 : ℤ_[2]) ∣ c - 3 := ⟨f, by linear_combination hd + 2 * hf⟩
    refine Or.inr ⟨gRsdZ h * gLadQ h (c - 3),
      Subgroup.mul_mem _ gRsdZ_mem (gLadQ_mem_zLayer_of_four hc3), ?_⟩
    have hsplit : gLadQ h c = gLadQ h 2 * (gLadQ h 1 * gLadQ h (c - 3)) := by
      rw [← gRsdQ_add, ← gRsdQ_add, show (1 : ℤ_[2]) + (c - 3) = c - 2 from by ring,
        show (2 : ℤ_[2]) + (c - 2) = c from by ring]
    rw [hsplit, gRsd_W_split, mul_assoc, mul_assoc]

/-- A `lambda_2`-class brackets EVERY odd pivot power through the two core letters. -/
theorem gRsd_lam_Q_odd {E : levelQuot (DSq h : Type) 4}
    (hE : E ∈ lambdaImage (DSq h : Type) 2 4) {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP E (gLadQ h c) = commP E (gLadX h) * commP E (gLadS h) := by
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [hQ]
    exact gRsd_lam_shape hE hV
  · rw [hQ, cfive_commP_right_hom hE (gLadQ h 2) (gLadS h * (gLadX h * V)),
      gLad_vanish4 hE gRsd_Wsq_mem, mul_one]
    exact gRsd_lam_shape hE hV

/-- The zeta bracket of every odd pivot power: the canonical triple pair. -/
theorem gRsd_zeta_Q_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (gRsdZeta h) (gLadQ h c)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) :=
  gRsd_lam_Q_odd gRsdZeta_mem hc

/-- ⭐ **The pair atom**: `[S,Q] [Q,X] = zeta^2 [zeta,X]` at every odd `B`. -/
theorem gRsd_SQ_QX_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (gLadS h) (gLadQ h c) * commP (gLadQ h c) (gLadX h)
      = gRsdZeta h ^ 2 * commP (gRsdZeta h) (gLadX h) := by
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [hQ, gRsd_S_shape hV, gRsd_shape_X hV, ← mul_assoc, ← pow_two]
  · rw [hQ, cfour_commP_mul_right (gLadS h) (gLadQ h 2) (gLadS h * (gLadX h * V)),
      gRsd_S_shape hV, gRsd_S_Wsq,
      cfive_commP_zLayer_left gRsdKillE_mem (gLadS h * (gLadX h * V)), mul_one,
      cfour_commP_mul_left (gLadQ h 2) (gLadS h * (gLadX h * V)) (gLadX h),
      gRsd_Wsq_X, cfive_commP_zLayer_left gRsdKillE_mem (gLadS h * (gLadX h * V)), mul_one,
      gRsd_shape_X hV]
    calc gRsdZeta h * gRsdKillE h
          * (gRsdKillE h * (gRsdZeta h * commP (gRsdZeta h) (gLadX h)))
        = gRsdZeta h * (gRsdKillE h * gRsdKillE h)
          * (gRsdZeta h * commP (gRsdZeta h) (gLadX h)) := by group
      _ = gRsdZeta h * (gRsdZeta h * commP (gRsdZeta h) (gLadX h)) := by
          rw [← pow_two, zLayer_sq (DSq h : Type) gRsdKillE_mem, mul_one]
      _ = gRsdZeta h ^ 2 * commP (gRsdZeta h) (gLadX h) := by
          rw [← mul_assoc, ← pow_two]

/-- The inner normalization: `[[X,S], X] [[X,S], S] = [zeta,X] [zeta,S]`, through the
inverse-invisibility of the near slot. -/
private theorem gRsd_XS_normalize :
    commP (commP (gLadX h) (gLadS h)) (gLadX h) * commP (commP (gLadX h) (gLadS h)) (gLadS h)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
  have hXS : commP (gLadX h) (gLadS h) = (gRsdZeta h)⁻¹ :=
    (gLad_commP_inv (gLadS h) (gLadX h)).symm
  rw [hXS, gThreeFour_ad_inv_left gRsdZeta_mem (gLadX h),
    gThreeFour_ad_inv_left gRsdZeta_mem (gLadS h)]

/-- ⭐ **The first rotated triple**: `[[X,Q],Q] = [zeta,X] [zeta,S]` at every odd `B`. -/
theorem gRsd_XQQ_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (commP (gLadX h) (gLadQ h c)) (gLadQ h c)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
  have hXS : commP (gLadX h) (gLadS h) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  have hXSX : commP (commP (gLadX h) (gLadS h)) (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hXS _
  have hcore :
      commP (commP (gLadX h) (gLadS h) * commP (commP (gLadX h) (gLadS h)) (gLadX h))
        (gLadQ h c) = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
    rw [cfour_commP_mul_left (commP (gLadX h) (gLadS h))
        (commP (commP (gLadX h) (gLadS h)) (gLadX h)) (gLadQ h c),
      cfive_commP_zLayer_left hXSX (gLadQ h c), mul_one,
      gRsd_lam_Q_odd hXS hc,
      cfive_commP_zLayer_left (Subgroup.mul_mem _ (cfour_commP_mem_zLayer_left hXS _)
        (cfour_commP_mem_zLayer_left hXS _)) (commP (commP (gLadX h) (gLadS h)) (gLadX h)),
      mul_one, gRsd_XS_normalize]
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [show commP (gLadX h) (gLadQ h c)
        = commP (gLadX h) (gLadS h) * commP (commP (gLadX h) (gLadS h)) (gLadX h) from by
      rw [hQ]; exact gRsd_X_shape hV]
    exact hcore
  · have hXQ2 : commP (gLadX h) (gLadQ h 2) ∈ zLayer (DSq h : Type) 3 :=
      cfour_commP_mem_zLayer_right (gLadX h) gRsd_Wsq_mem
    rw [show commP (gLadX h) (gLadQ h c)
        = commP (gLadX h) (gLadS h) * commP (commP (gLadX h) (gLadS h)) (gLadX h)
          * commP (gLadX h) (gLadQ h 2) from by
      rw [hQ, cfour_commP_mul_right (gLadX h) (gLadQ h 2) (gLadS h * (gLadX h * V)),
        gRsd_X_shape hV, cfive_commP_zLayer_left hXQ2 (gLadS h * (gLadX h * V)), mul_one],
      cfour_commP_mul_left (commP (gLadX h) (gLadS h)
        * commP (commP (gLadX h) (gLadS h)) (gLadX h)) (commP (gLadX h) (gLadQ h 2))
        (gLadQ h c),
      cfive_commP_zLayer_left hXQ2 (gLadQ h c), mul_one, hcore,
      gLad_commP_zLayer_right _ hXQ2, mul_one]

/-- The pivot square against the sigma letter: the same involution. -/
theorem gRsd_Wsq_S : commP (gLadQ h 2) (gLadS h) = gRsdKillE h := by
  rw [← gLad_commP_inv (gLadS h) (gLadQ h 2), gRsd_S_Wsq]
  exact zLayer_inv_self gRsdKillE_mem

/-- ⭐ **The second rotated triple**: `[[Q,S],Q] = [zeta,X] [zeta,S]` at every odd `B`. -/
theorem gRsd_QSQ_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (commP (gLadQ h c) (gLadS h)) (gLadQ h c)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
  have hXS : commP (gLadX h) (gLadS h) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  have hcore : commP (commP (gLadX h) (gLadS h)) (gLadQ h c)
      = commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h) := by
    rw [gRsd_lam_Q_odd hXS hc, gRsd_XS_normalize]
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [show commP (gLadQ h c) (gLadS h) = commP (gLadX h) (gLadS h) from by
      rw [hQ]; exact gRsd_shape_S hV]
    exact hcore
  · rw [show commP (gLadQ h c) (gLadS h)
        = gRsdKillE h * commP (gLadX h) (gLadS h) from by
      rw [hQ, cfour_commP_mul_left (gLadQ h 2) (gLadS h * (gLadX h * V)) (gLadS h),
        gRsd_Wsq_S, cfive_commP_zLayer_left gRsdKillE_mem (gLadS h * (gLadX h * V)),
        mul_one, gRsd_shape_S hV],
      cfour_commP_mul_left (gRsdKillE h) (commP (gLadX h) (gLadS h)) (gLadQ h c),
      cfive_commP_zLayer_left gRsdKillE_mem (gLadQ h c), cfour_one_comm, one_mul, one_mul,
      hcore]

/-- The block square, extracted: `(zeta [zeta,X])^2 = zeta^2`. -/
private theorem gRsd_zeta_ZX_sq :
    (gRsdZeta h * commP (gRsdZeta h) (gLadX h)) ^ 2 = gRsdZeta h ^ 2 := by
  rw [cfour_sq_mul (gRsdZeta h) (commP (gRsdZeta h) (gLadX h)),
    zLayer_sq (DSq h : Type) gRsdZetaX_mem, mul_one,
    cfive_commP_zLayer_left gRsdZetaX_mem (gRsdZeta h), cfour_one_comm, mul_one, mul_one]

/-- ⭐ **The bracket square**: `[Q,X]^2 = zeta^2` at every odd `B`. -/
theorem gRsd_QX_sq_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (gLadQ h c) (gLadX h) ^ 2 = gRsdZeta h ^ 2 := by
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [hQ, gRsd_shape_X hV, gRsd_zeta_ZX_sq]
  · have hQX : commP (gLadQ h c) (gLadX h)
        = gRsdKillE h * (gRsdZeta h * commP (gRsdZeta h) (gLadX h)) := by
      rw [hQ, cfour_commP_mul_left (gLadQ h 2) (gLadS h * (gLadX h * V)) (gLadX h),
        gRsd_Wsq_X, cfive_commP_zLayer_left gRsdKillE_mem (gLadS h * (gLadX h * V)),
        mul_one, gRsd_shape_X hV]
    rw [hQX, cfour_sq_mul (gRsdKillE h) (gRsdZeta h * commP (gRsdZeta h) (gLadX h)),
      zLayer_sq (DSq h : Type) gRsdKillE_mem, one_mul, gRsd_zeta_ZX_sq,
      gLad_commP_zLayer_right (gRsdZeta h * commP (gRsdZeta h) (gLadX h)) gRsdKillE_mem,
      cfour_one_comm, mul_one, mul_one]

/-- The y-bracket of the base pivot: `[W, Y] = xiS [[S,Y],X] xiX`, exactly. -/
private theorem gRsd_W_Y : commP (gLadQ h 1) (gLadY h)
    = gRsdXiS h * commP (gRsdXiS h) (gLadX h) * gRsdXiX h := by
  rw [gRsd_W_split, cfour_commP_mul_left (gLadS h) (gLadX h * gRsdZ h) (gLadY h),
    show commP (gLadS h) (gLadY h) = gRsdXiS h from rfl,
    cfive_commP_right_hom gRsdXiS_mem (gLadX h) (gRsdZ h),
    gLad_commP_zLayer_right (gRsdXiS h) gRsdZ_mem, one_mul,
    cfour_commP_mul_left (gLadX h) (gRsdZ h) (gLadY h),
    cfive_commP_zLayer_left gRsdZ_mem (gLadY h), mul_one,
    gLad_commP_zLayer_right (commP (gLadX h) (gLadY h)) gRsdZ_mem, mul_one]
  rfl

/-- ⭐ **The y-block of the pivot square**: `[W^2, Y] = gRsdKillY`. -/
theorem gRsd_Wsq_Y : commP (gLadQ h 2) (gLadY h) = gRsdKillY h := by
  have h2 : gLadQ h 2 = gLadQ h 1 ^ 2 := by
    rw [← gLadQ_two_mul]
    norm_num
  have humem : commP (gRsdXiS h) (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left gRsdXiS_mem _
  have hxiSW : commP (gRsdXiS h) (gLadQ h 1)
      = commP (gRsdXiS h) (gLadX h) * commP (gRsdXiS h) (gLadS h) := by
    rw [gRsd_W_split]
    exact gRsd_lam_shape gRsdXiS_mem gRsdZ_mem
  have hxiXW : commP (gRsdXiX h) (gLadQ h 1)
      = commP (gRsdXiX h) (gLadX h) * commP (gRsdXiX h) (gLadS h) := by
    rw [gRsd_W_split]
    exact gRsd_lam_shape gRsdXiX_mem gRsdZ_mem
  have hXcross : commP (gRsdXiX h) (gRsdXiS h * commP (gRsdXiS h) (gLadX h)) = 1 := by
    rw [cfour_commP_mul_right (gRsdXiX h) (gRsdXiS h) (commP (gRsdXiS h) (gLadX h)),
      gLad_commP_zLayer_right (gRsdXiX h) humem, one_mul,
      gLad_vanish4 gRsdXiX_mem gRsdXiS_mem, cfour_one_comm, mul_one]
  have hSu : (gRsdXiS h * commP (gRsdXiS h) (gLadX h)) ^ 2 = gRsdXiS h ^ 2 := by
    rw [cfour_sq_mul (gRsdXiS h) (commP (gRsdXiS h) (gLadX h)),
      zLayer_sq (DSq h : Type) humem, mul_one,
      cfive_commP_zLayer_left humem (gRsdXiS h), cfour_one_comm, mul_one, mul_one]
  have hSuW : commP (gRsdXiS h * commP (gRsdXiS h) (gLadX h)) (gLadQ h 1)
      = commP (gRsdXiS h) (gLadX h) * commP (gRsdXiS h) (gLadS h) := by
    rw [cfour_commP_mul_left (gRsdXiS h) (commP (gRsdXiS h) (gLadX h)) (gLadQ h 1), hxiSW,
      gLad_commP_zLayer_right _ humem, mul_one,
      cfive_commP_zLayer_left humem (gLadQ h 1), mul_one]
  rw [h2, gThreeFour_commP_sq_left (gLadQ h 1) (gLadY h), gRsd_W_Y,
    cfour_sq_mul (gRsdXiS h * commP (gRsdXiS h) (gLadX h)) (gRsdXiX h), hSu, hXcross,
    cfour_one_comm, mul_one, mul_one,
    cfour_commP_mul_left (gRsdXiS h * commP (gRsdXiS h) (gLadX h)) (gRsdXiX h) (gLadQ h 1),
    hSuW, hxiXW,
    cfive_commP_zLayer_left
      (Subgroup.mul_mem _ humem (cfour_commP_mem_zLayer_left gRsdXiS_mem _))
      (gRsdXiX h), mul_one]
  rfl

/-- The y-block of every even pivot power at odd half. -/
theorem gRsd_Qeven_Y {b : ℤ_[2]} (hb : ¬ (2 : ℤ_[2]) ∣ b) :
    commP (gLadQ h (2 * b)) (gLadY h) = gRsdKillY h := by
  rw [gRsd_Qeven_split, cfour_commP_mul_left (gLadQ h 2) (gLadQ h (2 * b - 2)) (gLadY h),
    gRsd_Wsq_Y, gLad_commP_zLayer_right (gRsdKillY h) (gRsd_Qeven_tail_zLayer hb), mul_one,
    cfive_commP_zLayer_left (gRsd_Qeven_tail_zLayer hb) (gLadY h), mul_one]

/-- The two-y core: the outer y-bracket of the odd-shape value is the canonical pair. -/
private theorem gRsd_YY_core :
    commP (gLadY h) (commP (gLadY h) (gLadX h) * commP (gLadY h) (gLadS h)
      * commP (commP (gLadY h) (gLadS h)) (gLadX h)) = gRsdYY h := by
  have haL : commP (gLadY h) (gLadX h) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  have hbL : commP (gLadY h) (gLadS h) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  have hu₂ : commP (commP (gLadY h) (gLadS h)) (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hbL _
  have hYa : commP (gLadY h) (commP (gLadY h) (gLadX h)) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right _ haL
  rw [cfour_commP_mul_right (gLadY h)
      (commP (gLadY h) (gLadX h) * commP (gLadY h) (gLadS h))
      (commP (commP (gLadY h) (gLadS h)) (gLadX h)),
    gLad_commP_zLayer_right (gLadY h) hu₂, one_mul,
    cfour_commP_mul_right (gLadY h) (commP (gLadY h) (gLadX h))
      (commP (gLadY h) (gLadS h)),
    cfive_commP_zLayer_left hYa (commP (gLadY h) (gLadS h)), mul_one,
    gLad_commP_zLayer_right _ hu₂, mul_one,
    ← gLad_commP_inv (commP (gLadY h) (gLadS h)) (gLadY h),
    zLayer_inv_self (cfour_commP_mem_zLayer_left hbL (gLadY h)),
    ← gLad_commP_inv (commP (gLadY h) (gLadX h)) (gLadY h),
    zLayer_inv_self (cfour_commP_mem_zLayer_left haL (gLadY h)),
    ← gLad_commP_inv (gLadS h) (gLadY h),
    gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo (gLadS h) (gLadY h)) (gLadY h),
    ← gLad_commP_inv (gLadX h) (gLadY h),
    gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo (gLadX h) (gLadY h)) (gLadY h)]
  rfl

/-- ⭐ **The two-y triples**: `[Y,[Y,Q]] = [[S,Y],Y] [[X,Y],Y]` at every odd `B`. -/
theorem gRsd_YYQ_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    commP (gLadY h) (commP (gLadY h) (gLadQ h c)) = gRsdYY h := by
  rcases gRsd_Q_odd_cases (h := h) hc with ⟨V, hV, hQ⟩ | ⟨V, hV, hQ⟩
  · rw [hQ, gRsd_Y_shape hV, gRsd_YY_core]
  · have hz₂ : commP (gLadY h) (gLadQ h 2) ∈ zLayer (DSq h : Type) 3 :=
      cfour_commP_mem_zLayer_right _ gRsd_Wsq_mem
    have hinner : commP (gLadY h) (gLadQ h c)
        = commP (gLadY h) (gLadX h) * commP (gLadY h) (gLadS h)
          * commP (commP (gLadY h) (gLadS h)) (gLadX h)
          * commP (gLadY h) (gLadQ h 2) := by
      rw [hQ, cfour_commP_mul_right (gLadY h) (gLadQ h 2) (gLadS h * (gLadX h * V)),
        gRsd_Y_shape hV, cfive_commP_zLayer_left hz₂ (gLadS h * (gLadX h * V)), mul_one]
    rw [hinner, cfour_commP_mul_right (gLadY h)
        (commP (gLadY h) (gLadX h) * commP (gLadY h) (gLadS h)
          * commP (commP (gLadY h) (gLadS h)) (gLadX h))
        (commP (gLadY h) (gLadQ h 2)),
      gLad_commP_zLayer_right (gLadY h) hz₂, one_mul, gRsd_YY_core,
      gLad_commP_zLayer_right (gRsdYY h) hz₂, mul_one]

/-- The excess cost dies at even `t`. -/
theorem gRsd_Zcost_even_t {B t : ℤ_[2]} (ht : (2 : ℤ_[2]) ∣ t) :
    commP (gLadQ h t ^ 2) (gLadX h * gLadQ h B) = 1 := by
  obtain ⟨u, rfl⟩ := ht
  have hz : gLadQ h (2 * u) ^ 2 ∈ zLayer (DSq h : Type) 3 := by
    rw [← gLadQ_two_mul]
    exact gLadQ_mem_zLayer_of_four ⟨u, by ring⟩
  exact cfive_commP_zLayer_left hz _

/-- ⭐ The excess cost at odd `t` is the even kill element, at EVERY `B`. -/
theorem gRsd_Zcost_odd_t {B t : ℤ_[2]} (ht : ¬ (2 : ℤ_[2]) ∣ t) :
    commP (gLadQ h t ^ 2) (gLadX h * gLadQ h B) = gRsdKillE h := by
  rw [cfive_commP_right_hom (gLadQ_sq_mem t) (gLadX h) (gLadQ h B), ← gLadQ_two_mul,
    gRsdQ_commP, one_mul, gRsd_Qeven_X ht]

end OddPowers

/-! ## §6 The defect at every residue, in closed atomic form

`gLad_defect_bare` times the atom table.  On the even locus the whole defect IS the excess
cost: `1` at even `t` (the free locus of rung 4 grows from the quarter to the half locus),
and the involution `gRsdKillE` at odd `t`.  At odd `B` the y-block enters, and the defect
collapses to `gRsdKillO` (even `t`) or `gRsdKillO'` (odd `t`). -/

section DefectForms

variable {h : ℕ}

/-- ⭐⭐ **The even-locus defect is the excess cost alone**: at `2 | B` every twist class of
the bare defect dies and the lambda_2-part cancels, leaving `[(w^t)^2, X Q]`. -/
theorem gRsd_defect_even {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : (2 : ℤ_[2]) ∣ B) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1))
      = commP (gLadQ h t ^ 2) (gLadX h * gLadQ h B) := by
  have hQmem : gLadQ h B ∈ lambdaImage (DSq h : Type) 2 4 := gRsd_Q_even_mem hB
  rw [gLad_defect_bare hsplit, gRsd_SQ_QX_even hB,
    cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right (gLadX h) hQmem) (gLadQ h B),
    cfive_commP_zLayer_left (cfour_commP_mem_zLayer_left hQmem (gLadS h)) (gLadQ h B),
    zLayer_sq (DSq h : Type) (cfour_commP_mem_zLayer_left hQmem (gLadX h)),
    cfive_commP_zLayer_left (cfour_sq_mem_zLayer hQmem) (gLadY h),
    gLad_commP_zLayer_right (gLadY h) (cfour_commP_mem_zLayer_right (gLadY h) hQmem)]
  simp only [one_mul]

/-- ⭐⭐ **RUNG 4 IS FREE ON THE HALF LOCUS**: at `2 | B` and `4 | A - 1 - B` the bare
relator word already lies in `lambda_4`.  This extends `gLad_defect_bare_quarter` from the
quarter locus to the whole even locus with even excess. -/
theorem gRsd_defect_even_even_t {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : (2 : ℤ_[2]) ∣ B) (ht : (2 : ℤ_[2]) ∣ t) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1)) = 1 := by
  rw [gRsd_defect_even hsplit hB, gRsd_Zcost_even_t ht]

/-- ⭐⭐ **The even-locus defect at odd excess is the single involution `gRsdKillE`**. -/
theorem gRsd_defect_even_odd_t {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : (2 : ℤ_[2]) ∣ B) (ht : ¬ (2 : ℤ_[2]) ∣ t) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1)) = gRsdKillE h := by
  rw [gRsd_defect_even hsplit hB, gRsd_Zcost_odd_t ht]

/-- The odd-locus kill element at even excess: `[zeta,X]` times the y-block. -/
noncomputable def gRsdKillO (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  commP (gRsdZeta h) (gLadX h) * (gRsdKillY h * gRsdYY h)

/-- The odd-locus kill element at odd excess: `zeta^2 [zeta,S]` times the y-block. -/
noncomputable def gRsdKillO' (h : ℕ) : levelQuot (DSq h : Type) 4 :=
  gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadS h) * (gRsdKillY h * gRsdYY h))

theorem gRsdKillO_mem : gRsdKillO h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ gRsdZetaX_mem (Subgroup.mul_mem _ gRsdKillY_mem gRsdYY_mem)

theorem gRsdKillO'_mem : gRsdKillO' h ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _ (cfour_sq_mem_zLayer gRsdZeta_mem)
    (Subgroup.mul_mem _ gRsdZetaS_mem (Subgroup.mul_mem _ gRsdKillY_mem gRsdYY_mem))

/-- The raw odd-locus defect: the atom table substituted into `gLad_defect_bare`. -/
theorem gRsd_defect_odd_raw {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : ¬ (2 : ℤ_[2]) ∣ B) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1))
      = gRsdZeta h ^ 2 * commP (gRsdZeta h) (gLadX h)
        * (commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h)
          * (commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h))
          * gRsdZeta h ^ 2 * gRsdKillY h * gRsdYY h
          * commP (gLadQ h t ^ 2) (gLadX h * gLadQ h B)) := by
  rw [gLad_defect_bare hsplit, gRsd_SQ_QX_odd hB, gRsd_XQQ_odd hB, gRsd_QSQ_odd hB,
    gRsd_QX_sq_odd hB, show gLadQ h B ^ 2 = gLadQ h (2 * B) from (gLadQ_two_mul B).symm,
    gRsd_Qeven_Y hB, gRsd_YYQ_odd hB]

/-- Bubble a central involution to the front: `a (z b) = z (a b)`. -/
private theorem gRsd_swap {z : levelQuot (DSq h : Type) 4}
    (hz : z ∈ zLayer (DSq h : Type) 3) (a b : levelQuot (DSq h : Type) 4) :
    a * (z * b) = z * (a * b) := by
  rw [← mul_assoc, ((zLayer_commute hz a).eq).symm, mul_assoc]

/-- Collapse an adjacent central pair: `z (z b) = b`. -/
private theorem gRsd_pair_collapse {z : levelQuot (DSq h : Type) 4}
    (hz : z ∈ zLayer (DSq h : Type) 3) (b : levelQuot (DSq h : Type) 4) :
    z * (z * b) = b := by
  rw [← mul_assoc, ← pow_two, zLayer_sq (DSq h : Type) hz, one_mul]

/-- ⭐⭐ **The odd-locus defect at even excess**. -/
theorem gRsd_defect_odd_even_t {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : ¬ (2 : ℤ_[2]) ∣ B) (ht : (2 : ℤ_[2]) ∣ t) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1)) = gRsdKillO h := by
  have hζ₂ : gRsdZeta h ^ 2 ∈ zLayer (DSq h : Type) 3 := cfour_sq_mem_zLayer gRsdZeta_mem
  rw [gRsd_defect_odd_raw hsplit hB, gRsd_Zcost_even_t ht, ← pow_two,
    zLayer_sq (DSq h : Type) (Subgroup.mul_mem _ gRsdZetaX_mem gRsdZetaS_mem), one_mul,
    mul_one]
  calc gRsdZeta h ^ 2 * commP (gRsdZeta h) (gLadX h)
      * (gRsdZeta h ^ 2 * gRsdKillY h * gRsdYY h)
      = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h)
        * (gRsdZeta h ^ 2 * (gRsdKillY h * gRsdYY h))) := by group
    _ = gRsdZeta h ^ 2 * (gRsdZeta h ^ 2
        * (commP (gRsdZeta h) (gLadX h) * (gRsdKillY h * gRsdYY h))) := by
        rw [gRsd_swap hζ₂ (commP (gRsdZeta h) (gLadX h)) (gRsdKillY h * gRsdYY h)]
    _ = gRsdKillO h := gRsd_pair_collapse hζ₂ _

/-- ⭐⭐ **The odd-locus defect at odd excess**. -/
theorem gRsd_defect_odd_odd_t {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : ¬ (2 : ℤ_[2]) ∣ B) (ht : ¬ (2 : ℤ_[2]) ∣ t) :
    levelMk (DSq h : Type) 4 (sqRelWord (gRowMark h A B fun _ => 1)) = gRsdKillO' h := by
  have hζ₂ : gRsdZeta h ^ 2 ∈ zLayer (DSq h : Type) 3 := cfour_sq_mem_zLayer gRsdZeta_mem
  rw [gRsd_defect_odd_raw hsplit hB, gRsd_Zcost_odd_t ht, ← pow_two,
    zLayer_sq (DSq h : Type) (Subgroup.mul_mem _ gRsdZetaX_mem gRsdZetaS_mem), one_mul,
    gRsdKillE]
  calc gRsdZeta h ^ 2 * commP (gRsdZeta h) (gLadX h)
      * (gRsdZeta h ^ 2 * gRsdKillY h * gRsdYY h
        * (gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h))))
      = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (gRsdZeta h ^ 2 * (gRsdKillY h
        * (gRsdYY h * (gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h)
          * commP (gRsdZeta h) (gLadS h))))))) := by group
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (gRsdZeta h ^ 2 * (gRsdZeta h ^ 2
        * (gRsdKillY h * (gRsdYY h * (commP (gRsdZeta h) (gLadX h)
          * commP (gRsdZeta h) (gLadS h))))))) := by
        rw [gRsd_swap hζ₂ (gRsdYY h) (commP (gRsdZeta h) (gLadX h)
            * commP (gRsdZeta h) (gLadS h)),
          gRsd_swap hζ₂ (gRsdKillY h) (gRsdYY h * (commP (gRsdZeta h) (gLadX h)
            * commP (gRsdZeta h) (gLadS h)))]
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (gRsdKillY h
        * (gRsdYY h * (commP (gRsdZeta h) (gLadX h) * commP (gRsdZeta h) (gLadS h))))) := by
        rw [gRsd_pair_collapse hζ₂ (gRsdKillY h * (gRsdYY h * (commP (gRsdZeta h) (gLadX h)
          * commP (gRsdZeta h) (gLadS h))))]
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (commP (gRsdZeta h) (gLadX h)
        * (gRsdKillY h * (gRsdYY h * commP (gRsdZeta h) (gLadS h))))) := by
        rw [gRsd_swap gRsdZetaX_mem (gRsdYY h) (commP (gRsdZeta h) (gLadS h)),
          gRsd_swap gRsdZetaX_mem (gRsdKillY h) (gRsdYY h * commP (gRsdZeta h) (gLadS h))]
    _ = gRsdZeta h ^ 2 * (gRsdKillY h * (gRsdYY h * commP (gRsdZeta h) (gLadS h))) := by
        rw [gRsd_pair_collapse gRsdZetaX_mem (gRsdKillY h
          * (gRsdYY h * commP (gRsdZeta h) (gLadS h)))]
    _ = gRsdKillO' h := by
        rw [((zLayer_commute gRsdZetaS_mem (gRsdYY h)).eq).symm,
          gRsd_swap gRsdZetaS_mem (gRsdKillY h) (gRsdYY h)]
        rfl

end DefectForms

/-! ## §7 The carrier tuples and their engine costs

Commutator words lie in the correction carrier outright (both rows are homomorphisms into
an abelian group).  The witness tuples put one carrier word on each core slot and `1` on
every handle slot, so the handle block of `gLadCost` dies and the three slot costs evaluate
against the residue's marked letters. -/

section CarrierCost

variable {h : ℕ}

private theorem gRsd_map_commP_one
    (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (a b : (DSq h : Type)) :
    f (commP a b) = 1 := by
  show f (a⁻¹ * b⁻¹ * a * b) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv,
    mul_assoc ((f a)⁻¹ * (f b)⁻¹) (f a) (f b), mul_mul_mul_comm, inv_mul_cancel,
    inv_mul_cancel, one_mul]

/-- ⭐ **Commutators lie in the correction carrier**: both rows are homomorphisms into an
abelian group, and every bracket is a `lambda_2`-element. -/
theorem gRsd_commP_mem_corr (a b : (DSq h : Type)) : commP a b ∈ gRowCorr h :=
  gRow_mem_corr.mpr ⟨⟨gRow_commP_mem_two a b, gRsd_map_commP_one (nuLam h) a b⟩,
    gRsd_map_commP_one (nuSq h) a b⟩

/-- The witness tuple: three carrier words on the core slots, `1` on the handles. -/
noncomputable def gRsdTuple (h : ℕ) (e₀ e₁ e₂ : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = 0 then e₀ else if (i : ℕ) = 1 then e₁ else
    if (i : ℕ) = 2 then e₂ else 1

@[simp] theorem gRsdTuple_zero (e₀ e₁ e₂ : (DSq h : Type)) :
    gRsdTuple h e₀ e₁ e₂ 0 = e₀ := by
  simp only [gRsdTuple, sqVal_zero]
  norm_num

@[simp] theorem gRsdTuple_one (e₀ e₁ e₂ : (DSq h : Type)) :
    gRsdTuple h e₀ e₁ e₂ 1 = e₁ := by
  simp only [gRsdTuple, sqVal_one]
  norm_num

@[simp] theorem gRsdTuple_two (e₀ e₁ e₂ : (DSq h : Type)) :
    gRsdTuple h e₀ e₁ e₂ 2 = e₂ := by
  simp only [gRsdTuple, sqVal_two]
  norm_num

@[simp] theorem gRsdTuple_handleU (e₀ e₁ e₂ : (DSq h : Type)) (j : Fin h) :
    gRsdTuple h e₀ e₁ e₂ (sqHandleIdxU j) = 1 := by
  simp only [gRsdTuple, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem gRsdTuple_handleV (e₀ e₁ e₂ : (DSq h : Type)) (j : Fin h) :
    gRsdTuple h e₀ e₁ e₂ (sqHandleIdxV j) = 1 := by
  simp only [gRsdTuple, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Carrier membership of the tuple, slotwise. -/
theorem gRsdTuple_mem_corr {e₀ e₁ e₂ : (DSq h : Type)} (h₀ : e₀ ∈ gRowCorr h)
    (h₁ : e₁ ∈ gRowCorr h) (h₂ : e₂ ∈ gRowCorr h) (i : Fin (sqRank h)) :
    gRsdTuple h e₀ e₁ e₂ i ∈ gRowCorr h := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rwa [gRsdTuple_zero]
  · rwa [gRsdTuple_one]
  · rwa [gRsdTuple_two]
  · rw [gRsdTuple_handleU]; exact one_mem _
  · rw [gRsdTuple_handleV]; exact one_mem _

/-- ⭐ **The engine cost of a witness tuple**: the handle block dies, leaving the three slot
costs. -/
theorem gRsd_cost_tuple (m : Fin (sqRank h) → levelQuot (DSq h : Type) 4)
    (e₀ e₁ e₂ : (DSq h : Type)) :
    gLadCost m (fun i => levelMk (DSq h : Type) 4 (gRsdTuple h e₀ e₁ e₂ i))
      = commP (levelMk (DSq h : Type) 4 e₀) (m 1)
        * commP (m 0) (levelMk (DSq h : Type) 4 e₁)
        * (levelMk (DSq h : Type) 4 e₂ ^ 2 * commP (levelMk (DSq h : Type) 4 e₂) (m 2)) := by
  rw [gLadCost]
  simp only [gRsdTuple_zero, gRsdTuple_one, gRsdTuple_two, gRsdTuple_handleU,
    gRsdTuple_handleV, map_one, cfour_one_comm, cfour_comm_one, one_mul]
  rw [List.prod_eq_one (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    rfl), mul_one]

/-- The bare marked letters in `Q_4`. -/
theorem gRsd_bare_zero (A B : ℤ_[2]) :
    levelMk (DSq h : Type) 4 (gRowMark h A B (fun _ => 1) 0)
      = gLadS h * gLadQ h (A - 1) := by
  rw [gRowMark_zero, mul_one, map_mul]
  rfl

theorem gRsd_bare_one (A B : ℤ_[2]) :
    levelMk (DSq h : Type) 4 (gRowMark h A B (fun _ => 1) 1) = gLadX h * gLadQ h B := by
  rw [gRowMark_one, mul_one, map_mul]
  rfl

theorem gRsd_bare_two (A B : ℤ_[2]) :
    levelMk (DSq h : Type) 4 (gRowMark h A B (fun _ => 1) 2)
      = gLadY h * gLadQ h (2 * B) := by
  rw [gRowMark_two, mul_one, map_mul]
  rfl

/-- Slot 0 on the even locus: `[E, X Q] = [E, X]`. -/
theorem gRsd_cost0_even {B : ℤ_[2]} (hB : (2 : ℤ_[2]) ∣ B)
    {E : levelQuot (DSq h : Type) 4} (hE : E ∈ lambdaImage (DSq h : Type) 2 4) :
    commP E (gLadX h * gLadQ h B) = commP E (gLadX h) := by
  rw [cfive_commP_right_hom hE (gLadX h) (gLadQ h B),
    gLad_vanish4 hE (gRsd_Q_even_mem hB), one_mul]

/-- Slot 0 on the odd locus: the legs swap, `[E, X Q] = [E, S]`. -/
theorem gRsd_cost0_odd {B : ℤ_[2]} (hB : ¬ (2 : ℤ_[2]) ∣ B)
    {E : levelQuot (DSq h : Type) 4} (hE : E ∈ lambdaImage (DSq h : Type) 2 4) :
    commP E (gLadX h * gLadQ h B) = commP E (gLadS h) := by
  have hEX : commP E (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hE _
  have hES : commP E (gLadS h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hE _
  rw [cfive_commP_right_hom hE (gLadX h) (gLadQ h B), gRsd_lam_Q_odd hE hB, mul_assoc,
    gRsd_swap hES (commP E (gLadX h)) (commP E (gLadX h)), ← pow_two,
    zLayer_sq (DSq h : Type) hEX, mul_one]

/-- Slot 1 at even twist: `[S Q, E] = [S, E]`. -/
theorem gRsd_cost1_even {c : ℤ_[2]} (hc : (2 : ℤ_[2]) ∣ c)
    {E : levelQuot (DSq h : Type) 4} (hE : E ∈ lambdaImage (DSq h : Type) 2 4) :
    commP (gLadS h * gLadQ h c) E = commP (gLadS h) E := by
  rw [cfour_commP_mul_left (gLadS h) (gLadQ h c) E,
    cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right (gLadS h) hE) (gLadQ h c),
    mul_one, gLad_vanish4 (gRsd_Q_even_mem hc) hE, mul_one]

/-- Slot 1 at odd twist: the legs swap, `[S Q, E] = [E, X]`. -/
theorem gRsd_cost1_odd {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c)
    {E : levelQuot (DSq h : Type) 4} (hE : E ∈ lambdaImage (DSq h : Type) 2 4) :
    commP (gLadS h * gLadQ h c) E = commP E (gLadX h) := by
  have hES : commP E (gLadS h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hE _
  rw [cfour_commP_mul_left (gLadS h) (gLadQ h c) E,
    cfive_commP_zLayer_left (cfour_commP_mem_zLayer_right (gLadS h) hE) (gLadQ h c),
    mul_one, ← gLad_commP_inv E (gLadQ h c), gRsd_lam_Q_odd hE hc, mul_inv_rev,
    zLayer_inv_self hES,
    zLayer_inv_self (cfour_commP_mem_zLayer_left hE (gLadX h) :
      commP E (gLadX h) ∈ zLayer (DSq h : Type) 3),
    ← gLad_commP_inv E (gLadS h), zLayer_inv_self hES,
    gRsd_pair_collapse hES (commP E (gLadX h))]

/-- Slot 2 at every residue: `[E, Y Q^2] = [E, Y]`. -/
theorem gRsd_cost2 (B : ℤ_[2]) {E : levelQuot (DSq h : Type) 4}
    (hE : E ∈ lambdaImage (DSq h : Type) 2 4) :
    commP E (gLadY h * gLadQ h (2 * B)) = commP E (gLadY h) := by
  rw [cfive_commP_right_hom hE (gLadY h) (gLadQ h (2 * B)),
    gLad_vanish4 hE (gRsd_Q_even_mem ⟨B, rfl⟩), one_mul]

/-- Projection of a bracket word. -/
private theorem gRsd_mk_commP (a b : (DSq h : Type)) :
    levelMk (DSq h : Type) 4 (commP a b)
      = commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b) := by
  simp only [commP, map_mul, map_inv]

private theorem gRsd_mk_zeta :
    levelMk (DSq h : Type) 4 (commP (dsqSigma h) (dsqX0 h)) = gRsdZeta h :=
  gRsd_mk_commP _ _

private theorem gRsd_mk_xiS :
    levelMk (DSq h : Type) 4 (commP (dsqSigma h) (dsqX1 h)) = gRsdXiS h :=
  gRsd_mk_commP _ _

private theorem gRsd_mk_xiX :
    levelMk (DSq h : Type) 4 (commP (dsqX0 h) (dsqX1 h)) = gRsdXiX h :=
  gRsd_mk_commP _ _

/-- ⭐⭐⭐ **THE JACOBI ROTATION OF THE GUARDING TRIPLE**: `[zeta, Y] = [[X,Y],S] [[S,Y],X]`
in `Q_4`.  The y-legged triple that guards the bracket-square block rotates onto an s-legged
and an x-legged triple, which are slot costs of the engine.  This is the single move the
wave-86 reachability analysis missed, and it is what decides the block POSITIVELY. -/
theorem gRsd_zeta_Y :
    commP (gRsdZeta h) (gLadY h)
      = commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h) := by
  show commP (commP (gLadS h) (gLadX h)) (gLadY h) = _
  rw [cfourDef_jacobi_solve (gLadS h) (gLadX h) (gLadY h),
    ← gLad_commP_inv (gLadS h) (gLadY h),
    gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo (gLadS h) (gLadY h)) (gLadX h)]
  rfl

/-- Squares split over `lambda_2`-factors. -/
private theorem gRsd_sq_split {a b : levelQuot (DSq h : Type) 4}
    (ha : a ∈ lambdaImage (DSq h : Type) 2 4) (hb : b ∈ lambdaImage (DSq h : Type) 2 4) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  rw [cfour_sq_mul a b, gLad_vanish4 hb ha, cfour_one_comm, mul_one, mul_one]

end CarrierCost

/-! ## §8 The kills: rung 4 at every residue

Each residue's witness tuple is built from the three commutators `[sigma, x_0]`,
`[sigma, x_1]`, `[x_0, x_1]`; its engine cost evaluates to EXACTLY the residue's defect,
so the kill equation is `defect * cost = cost^2 = 1`, an involution of the central layer. -/

section Kills

variable {h : ℕ}

/-- ⭐⭐ **RUNG 4 IS FREE ON THE HALF LOCUS** `2 | B`, `4 | A - 1 - B`, with the bare frame:
the quarter-locus result of wave 86, doubled. -/
theorem gRsd_nonempty_four_half {A B : ℤ_[2]} (hB : (2 : ℤ_[2]) ∣ B)
    (hAB : (4 : ℤ_[2]) ∣ A - 1 - B) : (gRowSet h A B 4).Nonempty := by
  obtain ⟨t', ht'⟩ := hAB
  have hsplit : A - 1 = B + 2 * (2 * t') := by linear_combination ht'
  exact ⟨fun _ => 1, fun _ => one_mem _,
    (QuotientGroup.eq_one_iff _).mp (gRsd_defect_even_even_t hsplit hB ⟨t', rfl⟩)⟩

/-- The cost of the even-locus witness `(zeta xiS, zeta xiX, zeta)` is exactly the
even-locus defect `gRsdKillE`. -/
private theorem gRsd_cost_even {A B : ℤ_[2]} (hB : (2 : ℤ_[2]) ∣ B)
    (hA1 : (2 : ℤ_[2]) ∣ A - 1) :
    gLadCost (fun i => levelMk (DSq h : Type) 4 (gRowMark h A B (fun _ => 1) i))
      (fun i => levelMk (DSq h : Type) 4 (gRsdTuple h
        (commP (dsqSigma h) (dsqX0 h) * commP (dsqSigma h) (dsqX1 h))
        (commP (dsqSigma h) (dsqX0 h) * commP (dsqX0 h) (dsqX1 h))
        (commP (dsqSigma h) (dsqX0 h)) i)) = gRsdKillE h := by
  have hζ₂ : gRsdZeta h ^ 2 ∈ zLayer (DSq h : Type) 3 := cfour_sq_mem_zLayer gRsdZeta_mem
  have hu₁ : commP (gRsdXiS h) (gLadX h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left gRsdXiS_mem _
  have hu₂ : commP (gRsdXiX h) (gLadS h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left gRsdXiX_mem _
  have hSζ : commP (gLadS h) (gRsdZeta h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right _ gRsdZeta_mem
  rw [gRsd_cost_tuple]
  simp only [gRsd_bare_zero, gRsd_bare_one, gRsd_bare_two, map_mul, gRsd_mk_zeta,
    gRsd_mk_xiS, gRsd_mk_xiX]
  rw [gRsd_cost0_even hB (Subgroup.mul_mem _ gRsdZeta_mem gRsdXiS_mem),
    gRsd_cost1_even hA1 (Subgroup.mul_mem _ gRsdZeta_mem gRsdXiX_mem),
    gRsd_cost2 B gRsdZeta_mem,
    gLad_commP_mul_left_two gRsdZeta_mem (gLadX h),
    cfour_commP_mul_right (gLadS h) (gRsdZeta h) (gRsdXiX h),
    cfive_commP_zLayer_left hSζ (gRsdXiX h), mul_one,
    ← gLad_commP_inv (gRsdZeta h) (gLadS h), zLayer_inv_self gRsdZetaS_mem,
    ← gLad_commP_inv (gRsdXiX h) (gLadS h), zLayer_inv_self hu₂,
    gRsd_zeta_Y]
  calc commP (gRsdZeta h) (gLadX h) * commP (gRsdXiS h) (gLadX h)
      * (commP (gRsdXiX h) (gLadS h) * commP (gRsdZeta h) (gLadS h))
      * (gRsdZeta h ^ 2
        * (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))
      = commP (gRsdZeta h) (gLadX h) * (commP (gRsdXiS h) (gLadX h)
        * (commP (gRsdXiX h) (gLadS h) * (commP (gRsdZeta h) (gLadS h) * (gRsdZeta h ^ 2
          * (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))))) := by group
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (commP (gRsdXiS h) (gLadX h)
        * (commP (gRsdXiX h) (gLadS h) * (commP (gRsdZeta h) (gLadS h)
          * (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))))) := by
        rw [gRsd_swap hζ₂ (commP (gRsdZeta h) (gLadS h))
            (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h)),
          gRsd_swap hζ₂ (commP (gRsdXiX h) (gLadS h))
            (commP (gRsdZeta h) (gLadS h)
              * (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h))),
          gRsd_swap hζ₂ (commP (gRsdXiS h) (gLadX h))
            (commP (gRsdXiX h) (gLadS h) * (commP (gRsdZeta h) (gLadS h)
              * (commP (gRsdXiX h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))),
          gRsd_swap hζ₂ (commP (gRsdZeta h) (gLadX h))
            (commP (gRsdXiS h) (gLadX h) * (commP (gRsdXiX h) (gLadS h)
              * (commP (gRsdZeta h) (gLadS h) * (commP (gRsdXiX h) (gLadS h)
                * commP (gRsdXiS h) (gLadX h)))))]
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (commP (gRsdXiS h) (gLadX h)
        * (commP (gRsdXiX h) (gLadS h) * (commP (gRsdXiX h) (gLadS h)
          * (commP (gRsdZeta h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))))) := by
        rw [gRsd_swap hu₂ (commP (gRsdZeta h) (gLadS h)) (commP (gRsdXiS h) (gLadX h))]
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (commP (gRsdXiS h) (gLadX h)
        * (commP (gRsdZeta h) (gLadS h) * commP (gRsdXiS h) (gLadX h)))) := by
        rw [gRsd_pair_collapse hu₂
          (commP (gRsdZeta h) (gLadS h) * commP (gRsdXiS h) (gLadX h))]
    _ = gRsdZeta h ^ 2 * (commP (gRsdZeta h) (gLadX h) * (commP (gRsdZeta h) (gLadS h)
        * (commP (gRsdXiS h) (gLadX h) * commP (gRsdXiS h) (gLadX h)))) := by
        rw [gRsd_swap gRsdZetaS_mem (commP (gRsdXiS h) (gLadX h))
          (commP (gRsdXiS h) (gLadX h))]
    _ = gRsdKillE h := by
        rw [← pow_two, zLayer_sq (DSq h : Type) hu₁, mul_one]
        rfl

/-- ⭐⭐ **RUNG 4 ON THE EVEN LOCUS AT ODD EXCESS**: the witness
`(zeta xiS, zeta xiX, zeta)` kills the defect. -/
theorem gRsd_nonempty_four_even_odd {A B t : ℤ_[2]} (hsplit : A - 1 = B + 2 * t)
    (hB : (2 : ℤ_[2]) ∣ B) (ht : ¬ (2 : ℤ_[2]) ∣ t) : (gRowSet h A B 4).Nonempty := by
  have hA1 : (2 : ℤ_[2]) ∣ A - 1 := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b + t, by linear_combination hsplit + hb⟩
  have hc : ∀ i, gRsdTuple h
      (commP (dsqSigma h) (dsqX0 h) * commP (dsqSigma h) (dsqX1 h))
      (commP (dsqSigma h) (dsqX0 h) * commP (dsqX0 h) (dsqX1 h))
      (commP (dsqSigma h) (dsqX0 h)) i ∈ gRowCorr h :=
    gRsdTuple_mem_corr
      (Subgroup.mul_mem _ (gRsd_commP_mem_corr _ _) (gRsd_commP_mem_corr _ _))
      (Subgroup.mul_mem _ (gRsd_commP_mem_corr _ _) (gRsd_commP_mem_corr _ _))
      (gRsd_commP_mem_corr _ _)
  refine gLad_nonempty_four_of_kill (by exact ⟨t, by linear_combination hsplit⟩)
    (fun i => ((gRow_mem_corr.mp (hc i)).1).1) (fun i => ((gRow_mem_corr.mp (hc i)).1).2)
    (fun i => (gRow_mem_corr.mp (hc i)).2) ?_
  rw [gRsd_defect_even_odd_t hsplit hB ht, gRsd_cost_even hB hA1, ← pow_two]
  exact zLayer_sq (DSq h : Type) gRsdKillE_mem

end Kills

end SqCore

end Dyadic

end GQ2
