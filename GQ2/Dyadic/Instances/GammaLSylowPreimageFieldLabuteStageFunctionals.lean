/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteVariableStageOne
import GQ2.Roe.Labute.StageLemma.CrossedDerivation

/-!
# Stage functionals: the χ-shadowed crossed-derivation calculus at every level

The cubic obstruction file identifies membership in the literal raw shift span of the improved
square presentation, at the free model and level three, with simultaneous vanishing of the
`2h + 2` mod-`16` coordinate crossed derivations.  This file generalizes the whole functional
calculus from `(k = 3, WL 4, D_sq(h))` to every stage `k ≥ 3` and every group `G` carrying a
continuous character `χ` and a continuous homomorphism `Φ : G → WL (k+1)` whose base component
is the mod-`2^(k+1)` shadow of `χ` (`IsChiShadowDeriv`).  The exports:

* every improved-presentation row over ambient marked lifts is killed at digit `k`
  (`stageDeriv_commP_row_mem_derivKer`, `stageDeriv_diagonal_row_mem_derivKer`), hence the
  whole raw shift span (`stageDeriv_rawShiftSpan_le_derivKer`);
* the ambient improved relator value of any tuple with exact per-slot χ-targets is killed
  **for every offset vector**: the improved word is universally closed in the word-lift group
  at the canonical orientation (`sqStageChiTarget_relWord_wordLift`,
  `stageDeriv_relWord_mem_derivKer`).  This is the mechanism forcing every χ-shadowed
  functional to annihilate the honest stage defect;
* a non-twisted tail `x^(2^(k-1))` is killed exactly when the offset of `x` is even
  (`stageDeriv_tail_mem_derivKer_of_even`, `stageDeriv_tail_not_mem_derivKer_of_odd`).  In
  particular one χ-shadowed derivation with an odd offset at a non-twisted slot reproves the
  tail obstruction `sqCore_sigma_rawTail_not_mem_rawShiftSpan` at every level `k ≥ 3` over any
  group carrying it (`stageDeriv_rawTail_not_mem_rawShiftSpan`);
* central coordinatewise shifts of the base do not move the literal core-plus-handle shift
  word (`sqCoreHandleDbarWord_central_base_shift`), so all of the above applies verbatim to
  the canonical-lift base of a field stage tuple.

No arithmetic existence statement is proved here: the file is the exact functional calculus
that a `SqStageCoordinateDerivationFamily` (next file) feeds.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

scoped instance instTopologicalSpaceWLStageFn (N : ℕ) : TopologicalSpace (WL N) := ⊥
scoped instance instDiscreteTopologyWLStageFn (N : ℕ) : DiscreteTopology (WL N) := ⟨rfl⟩
scoped instance instTopologicalSpaceZModUnitsStageFn (N : ℕ) :
    TopologicalSpace ((ZMod (2 ^ N))ˣ) := ⊥
scoped instance instDiscreteTopologyZModUnitsStageFn (N : ℕ) :
    DiscreteTopology ((ZMod (2 ^ N))ˣ) := ⟨rfl⟩

/-! ## Word-lift arithmetic helpers -/

/-- Powers in `R ⋊ Rˣ`: the offset picks up the geometric sum of the base. -/
private theorem stageFunctional_wl_pow {R : Type*} [CommRing R] (u : R) (g : Rˣ) (m : ℕ) :
    ((⟨u, g⟩ : WordLift R Rˣ) ^ m) =
      ⟨(∑ j ∈ Finset.range m, (g : R) ^ j) * u, g ^ m⟩ := by
  induction m with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext
    · show (∑ j ∈ Finset.range m, (g : R) ^ j) * u + ((g ^ m : Rˣ) : R) * u
        = (∑ j ∈ Finset.range (m + 1), (g : R) ^ j) * u
      rw [Finset.sum_range_succ, add_mul, Units.val_pow_eq_pow_val]
    · simp [pow_succ]

/-- The offset of the repository commutator in a word lift. -/
private theorem stageFunctional_commP_u {R : Type*} [CommRing R] (p q : WordLift R Rˣ) :
    (commP p q).u = ((p.g⁻¹ : Rˣ) : R) * (((q.g⁻¹ : Rˣ) : R) - 1) * p.u +
      ((q.g⁻¹ : Rˣ) : R) * (1 - ((p.g⁻¹ : Rˣ) : R)) * q.u := by
  have hp : ((p.g⁻¹ : Rˣ) : R) * (p.g : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
    Units.smul_def, smul_eq_mul, Units.val_mul]
  linear_combination (((q.g⁻¹ : Rˣ) : R) * q.u) * hp

/-- Closed offset formula for the twisted diagonal row `p²[p,q]`. -/
private theorem stageFunctional_sq_mul_commP_u {R : Type*} [CommRing R]
    (p q : WordLift R Rˣ) :
    (p ^ 2 * commP p q).u =
      (1 + (p.g : R) * ((q.g⁻¹ : Rˣ) : R)) * p.u +
        (p.g : R) ^ 2 * ((q.g⁻¹ : Rˣ) : R) *
          (1 - ((p.g⁻¹ : Rˣ) : R)) * q.u := by
  have hp : (p.g : R) * ((p.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [pow_two, WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul,
    Units.val_mul, stageFunctional_commP_u]
  linear_combination
    -(p.u * (p.g : R)) * hp +
      (p.u * (p.g : R) * ((q.g⁻¹ : Rˣ) : R)) * hp

/-- Inversion preserves a `2`-power congruence to `1`. -/
private theorem stageFunctional_inv_sub_one {R : Type*} [CommRing R]
    (g : Rˣ) (j : ℕ) (hg : (2 : R) ^ j ∣ (g : R) - 1) :
    (2 : R) ^ j ∣ ((g⁻¹ : Rˣ) : R) - 1 := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨-((g⁻¹ : Rˣ) : R) * c, ?_⟩
  have hunit : (g : R) * ((g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination -((g⁻¹ : Rˣ) : R) * hc + hunit

/-- Inversion preserves a `2`-power congruence to `-1`. -/
private theorem stageFunctional_inv_add_one {R : Type*} [CommRing R]
    (g : Rˣ) (j : ℕ) (hg : (2 : R) ^ j ∣ (g : R) + 1) :
    (2 : R) ^ j ∣ ((g⁻¹ : Rˣ) : R) + 1 := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨((g⁻¹ : Rˣ) : R) * c, ?_⟩
  have hunit : (g : R) * ((g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((g⁻¹ : Rˣ) : R) * hc - hunit

private theorem stageFunctional_two_pow_zmod_self {j : ℕ} : (2 : ZMod (2 ^ j)) ^ j = 0 := by
  have h : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h

/-- Divisibility by `2^j` in `ℤ/2^N` (`j ≤ N`) is vanishing of the mod-`2^j` reduction. -/
private theorem stageFunctional_two_pow_dvd_zmod_iff {N j : ℕ} (hj : j ≤ N)
    {x : ZMod (2 ^ N)} :
    (2 : ZMod (2 ^ N)) ^ j ∣ x ↔
      ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) x = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_pow, map_ofNat, stageFunctional_two_pow_zmod_self, zero_mul]
  · intro h
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) x
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-- Halving: if `2^k` divides `2^(k-1)·z` in `ℤ/2^N` (`k ≤ N`), then `z` is even. -/
private theorem stageFunctional_two_dvd_of_two_pow_dvd_mul {N k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ N) {z : ZMod (2 ^ N)}
    (h : (2 : ZMod (2 ^ N)) ^ k ∣ (2 : ZMod (2 ^ N)) ^ (k - 1) * z) :
    (2 : ZMod (2 ^ N)) ∣ z := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) z
  rw [stageFunctional_two_pow_dvd_zmod_iff hkN] at h
  rw [show (2 : ZMod (2 ^ N)) = ((2 : ℤ) : ZMod (2 ^ N)) by push_cast; ring, ← Int.cast_pow,
    ← Int.cast_mul, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h2 : (2 : ℤ) ∣ m := by
    have hpow : ((2 ^ k : ℕ) : ℤ) = 2 ^ (k - 1) * 2 := by
      push_cast
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at h
    have hne : (2 : ℤ) ^ (k - 1) ≠ 0 := by positivity
    exact (mul_dvd_mul_iff_left hne).mp
      (by rw [mul_comm ((2 : ℤ) ^ (k - 1)) 2] at h ⊢; exact h)
  obtain ⟨c, hc⟩ := h2
  exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-- Parity of a product with an odd factor. -/
private theorem stageFunctional_two_dvd_mul_iff_of_odd {N : ℕ} (hN : 1 ≤ N)
    {c z : ZMod (2 ^ N)} (hc : ¬ (2 : ZMod (2 ^ N)) ∣ c) :
    (2 : ZMod (2 ^ N)) ∣ c * z ↔ (2 : ZMod (2 ^ N)) ∣ z := by
  have h2 : ∀ x : ZMod (2 ^ N), (2 : ZMod (2 ^ N)) ∣ x ↔
      ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1)) x = 0 := by
    intro x
    have h := stageFunctional_two_pow_dvd_zmod_iff (N := N) (j := 1) hN (x := x)
    rwa [pow_one] at h
  rw [h2, h2, map_mul]
  have hc1 : ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1)) c = 1 := by
    have hc0 : ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1)) c ≠ 0 :=
      fun h0 ↦ hc ((h2 c).mpr h0)
    revert hc0
    generalize ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1)) c = a
    revert a
    decide
  rw [hc1, one_mul]

/-- The geometric sum of a base `≡ 1 (mod 4)` over `2^m` terms is `2^m · odd`. -/
private theorem stageFunctional_geom_sum {u : ℤ_[2]} (hu : (2 : ℤ_[2]) ^ 2 ∣ u - 1) (m : ℕ) :
    ∃ c : ℤ_[2], (∑ j ∈ Finset.range (2 ^ m), u ^ j) = 2 ^ m * c ∧ ¬ (2 : ℤ_[2]) ∣ c := by
  induction m with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    simpa using two_not_dvd_one_add_two_mul 0
  | succ m ih =>
    obtain ⟨c, hc, hc2⟩ := ih
    obtain ⟨d, hd⟩ := dvd_pow_sub_one hu (2 ^ m)
    refine ⟨c * (1 + 2 * d), ?_, two_not_dvd_mul hc2 (two_not_dvd_one_add_two_mul d)⟩
    have hsplit : (∑ j ∈ Finset.range (2 ^ (m + 1)), u ^ j)
        = (∑ j ∈ Finset.range (2 ^ m), u ^ j) * (1 + u ^ 2 ^ m) := by
      rw [show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by ring, Finset.sum_range_add]
      have hshift : ∀ j : ℕ, u ^ (2 ^ m + j) = u ^ 2 ^ m * u ^ j := fun j ↦ by rw [pow_add]
      simp only [hshift, ← Finset.mul_sum]
      ring
    have hval : 1 + u ^ 2 ^ m = 2 * (1 + 2 * d) := by
      have hpow : u ^ 2 ^ m = 1 + 2 ^ 2 * d := by linear_combination hd
      rw [hpow]
      ring
    rw [hsplit, hc, hval]
    ring

/-- `2`-power powers sink into the ambient lower two-central tower. -/
private theorem stageFunctional_pow_two_pow_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (g : G) (n : ℕ) : g ^ 2 ^ n ∈ twoCentralSeries G (1 + n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_one, Nat.add_zero, twoCentralSeries_one]
    exact Subgroup.mem_top g
  | succ n ih =>
    have h : g ^ 2 ^ (n + 1) = (g ^ 2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [h, show 1 + (n + 1) = 1 + n + 1 from rfl]
    exact sq_mem_twoCentralSeries_succ G ih

/-! ## Exact mod-4 facts for the canonical per-slot targets -/

private theorem stageFunctional_sval_sub_one_dvd_four :
    (2 : ℤ_[2]) ^ 2 ∣ ((GQ2.Roe.SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rw [GQ2.Roe.val_SvalUnit, ← two_pow_dvd_toZModPow_iff (N := 4) (j := 2) (by omega),
    map_sub, map_one, GQ2.Roe.Sval_toZModPow_four]
  exact ⟨3, by decide⟩

private theorem stageFunctional_rootX_sub_one_dvd_four :
    (2 : ℤ_[2]) ^ 2 ∣ ((GQ2.Roe.rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rw [GQ2.Roe.val_rootXUnit, ← two_pow_dvd_toZModPow_iff (N := 4) (j := 2) (by omega),
    map_sub, map_one, GQ2.Roe.rootX_toZModPow_four]
  exact ⟨1, by decide⟩

private theorem stageFunctional_yval_add_one_dvd_four :
    (2 : ℤ_[2]) ^ 2 ∣ ((GQ2.Roe.YvalUnit : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  rw [GQ2.Roe.val_YvalUnit, ← two_pow_dvd_toZModPow_iff (N := 4) (j := 2) (by omega),
    map_add, map_one, GQ2.Roe.Yval_toZModPow_four]
  exact ⟨2, by decide⟩

/-- Every non-twisted per-slot target is `≡ 1 (mod 4)`. -/
theorem sqStageChiTargetUnit_sub_one_dvd_four (h : ℕ) (i : Fin (SqCore.sqRank h))
    (hi : i ≠ 2) :
    (2 : ℤ_[2]) ^ 2 ∣ ((sqStageChiTargetUnit h i : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [sqStageChiTargetUnit_zero]
    exact stageFunctional_sval_sub_one_dvd_four
  · rw [sqStageChiTargetUnit_one]
    exact stageFunctional_rootX_sub_one_dvd_four
  · exact absurd rfl hi
  · rw [sqStageChiTargetUnit_handleU]
    simp
  · rw [sqStageChiTargetUnit_handleV]
    simp

/-! ## The universal word-lift kill of the improved relator

The improved square word dies in `ℤ₂ ⋊ ℤ₂ˣ` at the canonical orientation for **every** offset
vector: the rank-three core is Labute's orientation identity, and each hyperbolic handle is a
commutator of two base-one lifts, which commute. -/

/-- The improved relator word is universally closed at the canonical per-slot targets. -/
theorem sqStageChiTarget_relWord_wordLift (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    SqCore.sqRelWord
      (fun i ↦ (⟨v i, sqStageChiTargetUnit h i⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) = 1 := by
  have hcore : SqCore.sqWord (⟨v 0, sqStageChiTargetUnit h 0⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)
      ⟨v 1, sqStageChiTargetUnit h 1⟩ ⟨v 2, sqStageChiTargetUnit h 2⟩ = 1 := by
    rw [sqStageChiTargetUnit_zero, sqStageChiTargetUnit_one, sqStageChiTargetUnit_two,
      SqCore.sqWord_eq_drWord]
    convert GQ2.Roe.isLabuteOrientation_chiR (v 0) (v 1) (v 2) using 1
    all_goals simp
  rw [SqCore.sqRelWord, hcore, one_mul, GQ2.Dyadic.MarkedCore.handleWord]
  apply List.prod_eq_one
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨j, _, rfl⟩ := hz
  apply commP_eq_one_of_mul_comm
  ext
  · simp only [WordLift.mul_u, sqStageChiTargetUnit_handleU, sqStageChiTargetUnit_handleV,
      Units.smul_def, smul_eq_mul, Units.val_one, one_mul]
    exact add_comm _ _
  · simp only [WordLift.mul_g, sqStageChiTargetUnit_handleU, sqStageChiTargetUnit_handleV,
      mul_one]

/-! ## χ-shadowed derivations -/

section ChiShadow

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous homomorphism into the finite lift group whose base component is the
mod-`2^N` shadow of the given `2`-adic character. -/
def IsChiShadowDeriv (chi : ContinuousMonoidHom G ℤ_[2]ˣ) {N : ℕ}
    (Φ : ContinuousMonoidHom G (WL N)) : Prop :=
  ∀ g : G, (Φ g).g =
    Units.map (PadicInt.toZModPow N).toMonoidHom (chi g)

omit [IsTopologicalGroup G] in
/-- The base value of a χ-shadowed derivation, as a ring element. -/
theorem IsChiShadowDeriv.base_val {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}
    {Φ : ContinuousMonoidHom G (WL N)} (hbase : IsChiShadowDeriv chi Φ) (a : G) :
    ((Φ a).g : ZMod (2 ^ N)) = PadicInt.toZModPow N ((chi a : ℤ_[2]ˣ) : ℤ_[2]) := by
  rw [hbase a]
  rfl

/-- The offset congruence along the lower two-central tower. -/
theorem stageDeriv_u_dvd {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {j : ℕ} (hj : 1 ≤ j) {a : G} (ha : a ∈ twoCentralSeries G j) :
    (2 : ZMod (2 ^ N)) ^ (j - 1) ∣ (Φ a).u :=
  (deriv_mem_wlCong hN Φ hj ha).1

/-- The sharp χ-side base congruence along the tower: one digit deeper than the generic
word-lift filtration bound. -/
theorem stageDeriv_g_sub_one_dvd {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}
    {Φ : ContinuousMonoidHom G (WL N)} (hbase : IsChiShadowDeriv chi Φ)
    {j : ℕ} (hj : 2 ≤ j) (hjN : j + 1 ≤ N) {a : G} (ha : a ∈ twoCentralSeries G j) :
    (2 : ZMod (2 ^ N)) ^ (j + 1) ∣ ((Φ a).g : ZMod (2 ^ N)) - 1 := by
  have hchi := dvd_chi_of_mem_twoCentralSeries chi hj ha
  have hz := (two_pow_dvd_toZModPow_iff (N := N) (j := j + 1) hjN).mpr hchi
  rw [map_sub, map_one] at hz
  rw [hbase.base_val a]
  exact hz

omit [IsTopologicalGroup G] in
/-- A χ-level base congruence transported to the word-lift base component. -/
theorem stageDeriv_g_target_dvd {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}
    {Φ : ContinuousMonoidHom G (WL N)} (hbase : IsChiShadowDeriv chi Φ)
    {j : ℕ} (hjN : j ≤ N) {b : G}
    (hb : (2 : ℤ_[2]) ^ j ∣ ((chi b : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    (2 : ZMod (2 ^ N)) ^ j ∣ ((Φ b).g : ZMod (2 ^ N)) - 1 := by
  have hz := (two_pow_dvd_toZModPow_iff (N := N) (j := j) hjN).mpr hb
  rw [map_sub, map_one] at hz
  rw [hbase.base_val b]
  exact hz

omit [IsTopologicalGroup G] in
/-- The `-1`-side variant of the base transport. -/
theorem stageDeriv_g_target_dvd_add {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {N : ℕ}
    {Φ : ContinuousMonoidHom G (WL N)} (hbase : IsChiShadowDeriv chi Φ)
    {j : ℕ} (hjN : j ≤ N) {b : G}
    (hb : (2 : ℤ_[2]) ^ j ∣ ((chi b : ℤ_[2]ˣ) : ℤ_[2]) + 1) :
    (2 : ZMod (2 ^ N)) ^ j ∣ ((Φ b).g : ZMod (2 ^ N)) + 1 := by
  have hz := (two_pow_dvd_toZModPow_iff (N := N) (j := j) hjN).mpr hb
  rw [map_add, map_one] at hz
  rw [hbase.base_val b]
  exact hz

/-- Representative independence of the digit functional: membership of a class in the
vanishing subgroup forces the divisibility at every representative. -/
theorem stageDeriv_derivKer_dvd {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {k : ℕ} {b : G} (hb : levelMk G (k + 1) b ∈ derivKer Φ k) :
    (2 : ZMod (2 ^ N)) ^ k ∣ (Φ b).u := by
  obtain ⟨a, ha, hab, hda⟩ := hb
  have hmem : a⁻¹ * b ∈ twoCentralSeries G (k + 1) := QuotientGroup.eq.mp hab
  have hcong := (deriv_mem_wlCong hN Φ (by omega) hmem).1
  rw [show b = a * (a⁻¹ * b) by group, map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul]
  refine dvd_add hda (Dvd.dvd.mul_left ?_ _)
  simpa using hcong

variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {k : ℕ}
  {Φ : ContinuousMonoidHom G (WL (k + 1))}

/-- **The bracket-row kill.**  A commutator of a depth-`k-1` ambient element against a marked
letter with χ `≡ 1 (mod 4)` lies in the digit-`k` vanishing subgroup of every χ-shadowed
derivation. -/
theorem stageDeriv_commP_row_mem_derivKer (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    {p : G} (hp : p ∈ twoCentralSeries G (k - 1)) (b : G)
    (hb : (2 : ℤ_[2]) ^ 2 ∣ ((chi b : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    levelMk G (k + 1) (commP p b) ∈ derivKer Φ k := by
  refine ⟨commP p b, ?_, rfl, ?_⟩
  · have hmem : commP p b ∈ twoCentralSucc (twoCentralSeries G (k - 1)) :=
      commP_mem_twoCentralSucc hp b
    have heq : twoCentralSeries G ((k - 1) + 1) =
        twoCentralSucc (twoCentralSeries G (k - 1)) :=
      twoCentralSeries_succ G (by omega)
    rw [show k = (k - 1) + 1 by omega, heq]
    exact hmem
  · have hgb := stageDeriv_g_target_dvd hbase (by omega : 2 ≤ k + 1) hb
    have hgbInv := stageFunctional_inv_sub_one (Φ b).g 2 hgb
    have hga : (2 : ZMod (2 ^ (k + 1))) ^ k ∣ ((Φ p).g : ZMod (2 ^ (k + 1))) - 1 := by
      have h := stageDeriv_g_sub_one_dvd hbase (by omega : 2 ≤ k - 1) (by omega) hp
      rwa [show k - 1 + 1 = k by omega] at h
    have hgaInv := stageFunctional_inv_sub_one (Φ p).g k hga
    have hu : (2 : ZMod (2 ^ (k + 1))) ^ (k - 2) ∣ (Φ p).u := by
      have h := stageDeriv_u_dvd (by omega : 1 ≤ k + 1) Φ (by omega : 1 ≤ k - 1) hp
      rwa [show k - 1 - 1 = k - 2 by omega] at h
    rw [show Φ (commP p b) = commP (Φ p) (Φ b) from Marking.map_commP Φ.toMonoidHom p b,
      stageFunctional_commP_u]
    refine dvd_add ?_ ?_
    · have hm := mul_dvd_mul hgbInv hu
      rw [← pow_add] at hm
      have hm' : (2 : ZMod (2 ^ (k + 1))) ^ k ∣
          ((((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) - 1) * (Φ p).u := by
        rwa [show 2 + (k - 2) = k by omega] at hm
      simpa [mul_assoc] using hm'.mul_left
        ((((Φ p).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))))
    · have hneg : (2 : ZMod (2 ^ (k + 1))) ^ k ∣
          1 - (((Φ p).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) := by
        simpa [sub_eq_add_neg, add_comm] using hgaInv.neg_right
      exact (hneg.mul_left _).mul_right _

/-- **The diagonal-row kill.**  The twisted row `p²[p,b]` at a marked letter with
χ `≡ -1 (mod 4)` lies in the digit-`k` vanishing subgroup: the square term cancels the
otherwise surviving bracket digit. -/
theorem stageDeriv_diagonal_row_mem_derivKer (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    {p : G} (hp : p ∈ twoCentralSeries G (k - 1)) (b : G)
    (hb : (2 : ℤ_[2]) ^ 2 ∣ ((chi b : ℤ_[2]ˣ) : ℤ_[2]) + 1) :
    levelMk G (k + 1) (p ^ 2 * commP p b) ∈ derivKer Φ k := by
  refine ⟨p ^ 2 * commP p b, ?_, rfl, ?_⟩
  · refine Subgroup.mul_mem _ ?_ ?_
    · have hsq := sq_mem_twoCentralSeries_succ G hp
      rwa [show k - 1 + 1 = k by omega] at hsq
    · have hmem : commP p b ∈ twoCentralSucc (twoCentralSeries G (k - 1)) :=
        commP_mem_twoCentralSucc hp b
      have heq : twoCentralSeries G ((k - 1) + 1) =
          twoCentralSucc (twoCentralSeries G (k - 1)) :=
        twoCentralSeries_succ G (by omega)
      rw [show k = (k - 1) + 1 by omega, heq]
      exact hmem
  · have hgbPlus := stageDeriv_g_target_dvd_add hbase (by omega : 2 ≤ k + 1) hb
    have hgbInvPlus := stageFunctional_inv_add_one (Φ b).g 2 hgbPlus
    have hga : (2 : ZMod (2 ^ (k + 1))) ^ k ∣ ((Φ p).g : ZMod (2 ^ (k + 1))) - 1 := by
      have h := stageDeriv_g_sub_one_dvd hbase (by omega : 2 ≤ k - 1) (by omega) hp
      rwa [show k - 1 + 1 = k by omega] at h
    have hgaInv := stageFunctional_inv_sub_one (Φ p).g k hga
    have hgaFour : (2 : ZMod (2 ^ (k + 1))) ^ 2 ∣ ((Φ p).g : ZMod (2 ^ (k + 1))) - 1 :=
      dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) hga
    have hu : (2 : ZMod (2 ^ (k + 1))) ^ (k - 2) ∣ (Φ p).u := by
      have h := stageDeriv_u_dvd (by omega : 1 ≤ k + 1) Φ (by omega : 1 ≤ k - 1) hp
      rwa [show k - 1 - 1 = k - 2 by omega] at h
    have hcoef : (2 : ZMod (2 ^ (k + 1))) ^ 2 ∣
        1 + ((Φ p).g : ZMod (2 ^ (k + 1))) *
          (((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) := by
      have hs := dvd_add hgbInvPlus (hgaFour.mul_right
        ((((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1)))))
      have heq : 1 + ((Φ p).g : ZMod (2 ^ (k + 1))) *
          (((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) =
          (((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) + 1 +
            (((Φ p).g : ZMod (2 ^ (k + 1))) - 1) *
              (((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) := by
        ring
      rw [heq]
      exact hs
    rw [map_mul, map_pow,
      show Φ (commP p b) = commP (Φ p) (Φ b) from Marking.map_commP Φ.toMonoidHom p b,
      stageFunctional_sq_mul_commP_u]
    refine dvd_add ?_ ?_
    · have hm := mul_dvd_mul hcoef hu
      rw [← pow_add] at hm
      rwa [show 2 + (k - 2) = k by omega] at hm
    · have hneg : (2 : ZMod (2 ^ (k + 1))) ^ k ∣
          1 - (((Φ p).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) := by
        simpa [sub_eq_add_neg, add_comm] using hgaInv.neg_right
      have hm := hneg.mul_left (((Φ p).g : ZMod (2 ^ (k + 1))) ^ 2 *
        (((Φ b).g⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))))
      exact hm.mul_right (Φ b).u

/-- **The non-twisted tail with even offset is killed.** -/
theorem stageDeriv_tail_mem_derivKer_of_even (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    {x : G} (hx4 : (2 : ℤ_[2]) ^ 2 ∣ ((chi x : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hu : (2 : ZMod (2 ^ (k + 1))) ∣ (Φ x).u) :
    levelMk G (k + 1) (x ^ 2 ^ (k - 1)) ∈ derivKer Φ k := by
  obtain ⟨c, hc, hcodd⟩ := stageFunctional_geom_sum hx4 (k - 1)
  refine ⟨x ^ 2 ^ (k - 1), ?_, rfl, ?_⟩
  · have h := stageFunctional_pow_two_pow_mem x (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h
  · have hpow : (Φ x) ^ 2 ^ (k - 1) =
        (⟨(∑ j ∈ Finset.range (2 ^ (k - 1)),
              ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) * (Φ x).u,
          (Φ x).g ^ 2 ^ (k - 1)⟩ : WL (k + 1)) := by
      conv_lhs => rw [show Φ x = ⟨(Φ x).u, (Φ x).g⟩ from rfl]
      exact stageFunctional_wl_pow _ _ _
    have hsum : (∑ j ∈ Finset.range (2 ^ (k - 1)),
          ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) =
        (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) * PadicInt.toZModPow (k + 1) c := by
      calc (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j)
          = PadicInt.toZModPow (k + 1)
              (∑ j ∈ Finset.range (2 ^ (k - 1)), ((chi x : ℤ_[2]ˣ) : ℤ_[2]) ^ j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [map_pow, hbase.base_val x]
        _ = PadicInt.toZModPow (k + 1) ((2 : ℤ_[2]) ^ (k - 1) * c) := by rw [hc]
        _ = (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) * PadicInt.toZModPow (k + 1) c := by
            rw [map_mul, map_pow, map_ofNat]
    obtain ⟨w, hw⟩ := hu
    rw [map_pow, hpow]
    show (2 : ZMod (2 ^ (k + 1))) ^ k ∣
      (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) * (Φ x).u
    refine ⟨PadicInt.toZModPow (k + 1) c * w, ?_⟩
    rw [hsum, hw, show (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) * PadicInt.toZModPow (k + 1) c *
        (2 * w) = 2 ^ (k - 1) * 2 * (PadicInt.toZModPow (k + 1) c * w) by ring,
      ← pow_succ, show k - 1 + 1 = k by omega]

/-- **The non-twisted tail with odd offset survives.** -/
theorem stageDeriv_tail_not_mem_derivKer_of_odd (hk : 3 ≤ k) (hbase : IsChiShadowDeriv chi Φ)
    {x : G} (hx4 : (2 : ℤ_[2]) ^ 2 ∣ ((chi x : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hu : ¬ (2 : ZMod (2 ^ (k + 1))) ∣ (Φ x).u) :
    levelMk G (k + 1) (x ^ 2 ^ (k - 1)) ∉ derivKer Φ k := by
  intro hmem
  obtain ⟨c, hc, hcodd⟩ := stageFunctional_geom_sum hx4 (k - 1)
  have hdvd := stageDeriv_derivKer_dvd (by omega : 1 ≤ k + 1) Φ hmem
  have hpow : (Φ x) ^ 2 ^ (k - 1) =
      (⟨(∑ j ∈ Finset.range (2 ^ (k - 1)),
            ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) * (Φ x).u,
        (Φ x).g ^ 2 ^ (k - 1)⟩ : WL (k + 1)) := by
    conv_lhs => rw [show Φ x = ⟨(Φ x).u, (Φ x).g⟩ from rfl]
    exact stageFunctional_wl_pow _ _ _
  have hsum : (∑ j ∈ Finset.range (2 ^ (k - 1)),
        ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) =
      (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) * PadicInt.toZModPow (k + 1) c := by
    calc (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j)
        = PadicInt.toZModPow (k + 1)
            (∑ j ∈ Finset.range (2 ^ (k - 1)), ((chi x : ℤ_[2]ˣ) : ℤ_[2]) ^ j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [map_pow, hbase.base_val x]
      _ = PadicInt.toZModPow (k + 1) ((2 : ℤ_[2]) ^ (k - 1) * c) := by rw [hc]
      _ = (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) * PadicInt.toZModPow (k + 1) c := by
          rw [map_mul, map_pow, map_ofNat]
  rw [map_pow, hpow] at hdvd
  have hdvd' : (2 : ZMod (2 ^ (k + 1))) ^ k ∣
      (2 : ZMod (2 ^ (k + 1))) ^ (k - 1) *
        (PadicInt.toZModPow (k + 1) c * (Φ x).u) := by
    have h : (2 : ZMod (2 ^ (k + 1))) ^ k ∣
        (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ (k + 1))) ^ j) *
          (Φ x).u := hdvd
    rwa [hsum, mul_assoc] at h
  have h2 := stageFunctional_two_dvd_of_two_pow_dvd_mul (by omega : 1 ≤ k)
    (by omega : k ≤ k + 1) hdvd'
  have hcbar : ¬ (2 : ZMod (2 ^ (k + 1))) ∣ PadicInt.toZModPow (k + 1) c := by
    intro hdc
    apply hcodd
    have h' : (2 : ZMod (2 ^ (k + 1))) ^ 1 ∣ PadicInt.toZModPow (k + 1) c := by
      rwa [pow_one]
    have h'' := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := 1) (by omega)).mp h'
    rwa [pow_one] at h''
  exact hu ((stageFunctional_two_dvd_mul_iff_of_odd (by omega) hcbar).mp h2)

/-- **The ambient relator kill.**  If a tuple of ambient lifts has the exact per-slot
χ-targets and its level-`k` classes satisfy the improved relation, then the level-`k+1` class
of its literal ambient relator value is killed by every χ-shadowed derivation, regardless of
the derivation's offsets. -/
theorem stageDeriv_relWord_mem_derivKer {h : ℕ}
    (hbase : IsChiShadowDeriv chi Φ) (x : Fin (SqCore.sqRank h) → G)
    (hchi : ∀ i, chi (x i) = sqStageChiTargetUnit h i)
    (hrel : SqCore.sqRelWord (fun i ↦ levelMk G k (x i)) = 1) :
    levelMk G (k + 1) (SqCore.sqRelWord x) ∈ derivKer Φ k := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  refine ⟨SqCore.sqRelWord x, ?_, rfl, ?_⟩
  · apply (QuotientGroup.eq_one_iff _).mp
    show levelMk G k (SqCore.sqRelWord x) = 1
    rw [SqCore.map_sqRelWord (levelMk G k) x]
    exact hrel
  · have hΦx : ∀ i, Φ (x i) = redWL (k + 1)
        ⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), sqStageChiTargetUnit h i⟩ := by
      intro i
      refine WordLift.ext ?_ ?_
      · show (Φ (x i)).u = PadicInt.toZModPow (k + 1) (((Φ (x i)).u.val : ℕ) : ℤ_[2])
        rw [map_natCast]
        exact (ZMod.natCast_rightInverse (Φ (x i)).u).symm
      · show (Φ (x i)).g = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
            (sqStageChiTargetUnit h i)
        rw [hbase (x i), hchi i]
    have hword : Φ (SqCore.sqRelWord x) = 1 := by
      calc Φ (SqCore.sqRelWord x)
          = SqCore.sqRelWord (fun i ↦ Φ (x i)) := SqCore.map_sqRelWord Φ.toMonoidHom x
        _ = SqCore.sqRelWord (fun i ↦ redWL (k + 1)
            ⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), sqStageChiTargetUnit h i⟩) := by
              exact congrArg SqCore.sqRelWord (funext hΦx)
        _ = redWL (k + 1) (SqCore.sqRelWord (fun i ↦
            (⟨(((Φ (x i)).u.val : ℕ) : ℤ_[2]), sqStageChiTargetUnit h i⟩ :
              WordLift ℤ_[2] ℤ_[2]ˣ))) :=
              (SqCore.map_sqRelWord (redWL (k + 1)) _).symm
        _ = 1 := by
              rw [sqStageChiTarget_relWord_wordLift h
                (fun i ↦ (((Φ (x i)).u.val : ℕ) : ℤ_[2]))]
              exact map_one _
    rw [hword]
    show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ (0 : ZMod (2 ^ (k + 1)))
    exact dvd_zero _

end ChiShadow

/-! ## The whole raw shift span is killed -/

section SpanKill

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem stageFunctional_list_single
    {H I : Type*} [Monoid H] (l : List I) (j : I) (f : I → H)
    (hj : j ∈ l) (hnodup : l.Nodup)
    (hf : ∀ i ∈ l, i ≠ j → f i = 1) :
    (l.map f).prod = f j := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hj with hij | hj
      · subst i
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hf b (List.mem_cons_of_mem _ hb) (fun hbj ↦ hnd.1 (hbj ▸ hb))
        simp [htail]
      · have hij : i ≠ j := by
          intro h
          exact hnd.1 (h ▸ hj)
        rw [List.map_cons, List.prod_cons, hf i (by simp) hij, one_mul,
          ih hj hnd.2 (fun b hb hbj ↦ hf b (List.mem_cons_of_mem _ hb) hbj)]

/-- A raw depth correction is the ordered product of its one-coordinate corrections. -/
private theorem stageFunctional_rawDepthCorrection_eq_prod {h k : ℕ}
    (V : RawDepthCorrection G h k) :
    V = ((List.finRange (SqCore.sqRank h)).map fun i ↦
      rawDepthCoordinateCorrection i
        (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))).prod := by
  classical
  ext j
  let ev : RawDepthCorrection G h k →* levelQuot G (k + 1) :=
    { toFun := fun W ↦ W.correction j
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  change ev V = ev (((List.finRange (SqCore.sqRank h)).map fun i ↦
    rawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))).prod)
  rw [map_list_prod]
  have hsingle := stageFunctional_list_single
    (List.finRange (SqCore.sqRank h)) j
    (fun i ↦ ev (rawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage G (k - 1) (k + 1))))
    (by simp) (List.nodup_finRange _) (by
      intro i _ hij
      simp [ev, rawDepthCoordinateCorrection_apply, Ne.symm hij])
  simpa [List.map_map, Function.comp_def, ev, rawDepthCoordinateCorrection_apply] using
    hsingle.symm

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {k : ℕ}
  {Φ : ContinuousMonoidHom G (WL (k + 1))}

/-- Every one-coordinate raw shift over exactly χ-marked ambient lifts is killed. -/
theorem stageDeriv_coordinateShift_mem_derivKer {h : ℕ} (hk : 3 ≤ k)
    (hbase : IsChiShadowDeriv chi Φ) (xb : Fin (SqCore.sqRank h) → G)
    (hchi : ∀ i, chi (xb i) = sqStageChiTargetUnit h i)
    (i : Fin (SqCore.sqRank h)) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom (fun i ↦ levelMk G (k + 1) (xb i)) hk)
      (rawDepthCoordinateCorrection i p)).1 ∈ derivKer Φ k := by
  obtain ⟨a, ha, hpa⟩ := p.2
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [rawDepthShiftHom_zero_apply, ← hpa,
      show commP (levelMk G (k + 1) a) (levelMk G (k + 1) (xb 1)) =
        levelMk G (k + 1) (commP a (xb 1)) from (Marking.map_commP _ _ _).symm]
    refine stageDeriv_commP_row_mem_derivKer hk hbase ha (xb 1) ?_
    rw [hchi 1, sqStageChiTargetUnit_one]
    exact stageFunctional_rootX_sub_one_dvd_four
  · rw [rawDepthShiftHom_one_apply, ← hpa,
      show commP (levelMk G (k + 1) a) (levelMk G (k + 1) (xb 0)) =
        levelMk G (k + 1) (commP a (xb 0)) from (Marking.map_commP _ _ _).symm]
    refine stageDeriv_commP_row_mem_derivKer hk hbase ha (xb 0) ?_
    rw [hchi 0, sqStageChiTargetUnit_zero]
    exact stageFunctional_sval_sub_one_dvd_four
  · rw [rawDepthShiftHom_two_apply, ← hpa, ← Marking.map_commP, ← map_pow, ← map_mul]
    refine stageDeriv_diagonal_row_mem_derivKer hk hbase ha (xb 2) ?_
    rw [hchi 2, sqStageChiTargetUnit_two]
    exact stageFunctional_yval_add_one_dvd_four
  · rw [rawDepthShiftHom_handleU_apply, ← hpa,
      show commP (levelMk G (k + 1) a) (levelMk G (k + 1) (xb (SqCore.sqHandleIdxV j))) =
        levelMk G (k + 1) (commP a (xb (SqCore.sqHandleIdxV j))) from
          (Marking.map_commP _ _ _).symm]
    refine stageDeriv_commP_row_mem_derivKer hk hbase ha (xb (SqCore.sqHandleIdxV j)) ?_
    rw [hchi (SqCore.sqHandleIdxV j), sqStageChiTargetUnit_handleV]
    simp
  · rw [rawDepthShiftHom_handleV_apply, ← hpa,
      show commP (levelMk G (k + 1) a) (levelMk G (k + 1) (xb (SqCore.sqHandleIdxU j))) =
        levelMk G (k + 1) (commP a (xb (SqCore.sqHandleIdxU j))) from
          (Marking.map_commP _ _ _).symm]
    refine stageDeriv_commP_row_mem_derivKer hk hbase ha (xb (SqCore.sqHandleIdxU j)) ?_
    rw [hchi (SqCore.sqHandleIdxU j), sqStageChiTargetUnit_handleU]
    simp

/-- **The raw shift span is killed by every χ-shadowed derivation.** -/
theorem stageDeriv_rawShiftSpan_le_derivKer {h : ℕ} (hk : 3 ≤ k)
    (hbase : IsChiShadowDeriv chi Φ) (xb : Fin (SqCore.sqRank h) → G)
    (hchi : ∀ i, chi (xb i) = sqStageChiTargetUnit h i) :
    rawShiftSpan (h := h) (fun i ↦ levelMk G (k + 1) (xb i)) hk ≤ derivKer Φ k := by
  rintro z ⟨q, hq, rfl⟩
  obtain ⟨V, rfl⟩ := hq
  rw [stageFunctional_rawDepthCorrection_eq_prod V, map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  exact stageDeriv_coordinateShift_mem_derivKer hk hbase xb hchi i
    ⟨V.correction i, V.depth i⟩

/-- **The tail obstruction at every stage.**  One χ-shadowed derivation with an odd offset at
a non-twisted marked letter certifies that the letter's `2^(k-1)`-th power tail is outside the
literal raw shift span.  This generalizes the model's cubic refutation to every level and any
carrier of such a functional. -/
theorem stageDeriv_rawTail_not_mem_rawShiftSpan {h : ℕ} (hk : 3 ≤ k)
    (hbase : IsChiShadowDeriv chi Φ) (xb : Fin (SqCore.sqRank h) → G)
    (hchi : ∀ i, chi (xb i) = sqStageChiTargetUnit h i)
    (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2)
    (hodd : ¬ (2 : ZMod (2 ^ (k + 1))) ∣ (Φ (xb i₀)).u) :
    levelMk G (k + 1) (xb i₀) ^ 2 ^ (k - 1) ∉
      rawShiftSpan (h := h) (fun i ↦ levelMk G (k + 1) (xb i)) hk := by
  intro hmem
  have hker := stageDeriv_rawShiftSpan_le_derivKer hk hbase xb hchi hmem
  rw [← map_pow] at hker
  refine stageDeriv_tail_not_mem_derivKer_of_odd hk hbase ?_ hodd hker
  rw [hchi i₀]
  exact sqStageChiTargetUnit_sub_one_dvd_four h i₀ hi₀

end SpanKill

/-! ## Central base shifts do not move the literal shift word -/

section CentralBaseShift

/-- A central left factor in the second argument does not change the commutator. -/
private theorem stageFunctional_commP_central_right {H : Type*} [Group H] {z : H}
    (hz : ∀ t : H, z * t = t * z) (w b : H) : commP w (z * b) = commP w b := by
  have hzi : ∀ t : H, z⁻¹ * t = t * z⁻¹ := by
    intro t
    calc z⁻¹ * t = z⁻¹ * (t * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * t) * z⁻¹ := by rw [← hz t]
      _ = t * z⁻¹ := by group
  simp only [commP, mul_inv_rev]
  calc w⁻¹ * (b⁻¹ * z⁻¹) * w * (z * b)
      = w⁻¹ * b⁻¹ * (z⁻¹ * w) * z * b := by group
    _ = w⁻¹ * b⁻¹ * (w * z⁻¹) * z * b := by rw [hzi w]
    _ = w⁻¹ * b⁻¹ * w * b := by group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-- Coordinatewise central shifts of the base do not move the handle shift word. -/
theorem sqHandleDbarWord_central_base_shift
    {z base : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hz : ∀ i, z i ∈ zLayer G k)
    (correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    sqHandleDbarWord (fun i ↦ z i * base i) correction =
      sqHandleDbarWord base correction := by
  rw [sqHandleDbarWord, sqHandleDbarWord]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  rw [stageFunctional_commP_central_right
      (fun t ↦ (zLayer_commute (hz (SqCore.sqHandleIdxU j)) t).eq),
    stageFunctional_commP_central_right
      (fun t ↦ (zLayer_commute (hz (SqCore.sqHandleIdxV j)) t).eq)]

/-- Central shifts of the three core base letters do not move the `r₂`-shift word. -/
theorem dbarWordR2_central_base_shift {z0 z1 z2 s x y : levelQuot G (k + 1)}
    (h0 : z0 ∈ zLayer G k) (h1 : z1 ∈ zLayer G k) (h2 : z2 ∈ zLayer G k)
    (w : Fin 3 → levelQuot G (k + 1)) :
    dbarWordR2 (z0 * s) (z1 * x) (z2 * y) w = dbarWordR2 s x y w := by
  rw [dbarWordR2, dbarWordR2,
    stageFunctional_commP_central_right (fun t ↦ (zLayer_commute h2 t).eq) (w 2) y,
    stageFunctional_commP_central_right (fun t ↦ (zLayer_commute h1 t).eq) (w 0) x,
    stageFunctional_commP_central_right (fun t ↦ (zLayer_commute h0 t).eq) (w 1) s]

/-- **Coordinatewise central shifts of the base do not move the literal core-plus-handle
shift word.**  Consequently the raw span calculus is insensitive to which coherent lifts of a
level-`k` marking are used as the base. -/
theorem sqCoreHandleDbarWord_central_base_shift
    {z base : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hz : ∀ i, z i ∈ zLayer G k)
    (correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    sqCoreHandleDbarWord (fun i ↦ z i * base i) correction =
      sqCoreHandleDbarWord base correction := by
  rw [sqCoreHandleDbarWord, sqCoreHandleDbarWord,
    sqHandleDbarWord_central_base_shift hz correction]
  congr 1
  exact dbarWordR2_central_base_shift (hz 0) (hz 1) (hz 2) _

end CentralBaseShift

#print axioms sqStageChiTargetUnit_sub_one_dvd_four
#print axioms sqStageChiTarget_relWord_wordLift
#print axioms stageDeriv_commP_row_mem_derivKer
#print axioms stageDeriv_diagonal_row_mem_derivKer
#print axioms stageDeriv_tail_mem_derivKer_of_even
#print axioms stageDeriv_tail_not_mem_derivKer_of_odd
#print axioms stageDeriv_relWord_mem_derivKer
#print axioms stageDeriv_rawShiftSpan_le_derivKer
#print axioms stageDeriv_rawTail_not_mem_rawShiftSpan
#print axioms sqCoreHandleDbarWord_central_base_shift

end

end GQ2.Dyadic.LSquare
