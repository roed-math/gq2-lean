/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.DigitToolkit

/-!
# The χ-twisted crossed derivations, `d̄`-additivity, and tail separation

Piece 4/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  SL1's separating functionals: the finite lift group
`WL N = ℤ/2^N ⋊ (ℤ/2^N)ˣ`, the two coordinate derivations out of the towers, the
`d̄`-image subgroup structure, and the endgame showing the derivations separate the
two tails.
-/

namespace GQ2.Roe.Labute

/-! ### The χ-twisted crossed derivations (SL1's separating functionals)

SL1 needs functionals on `Zₖ` that kill `Im d̄` and the defect but pair non-degenerately with
the two tails.  The numerics report (`docs/orchestration/sl1-numerics.md` §6) identifies them
as digit-`(k−1)` shadows of **θ-crossed derivations**; the repo already carries the exact
(un-truncated) version of that calculus — Labute's descent condition
`IsLabuteOrientationDatum` (`GQ2/Roe/CrossedDerivation.lean`), which says that for the
canonical orientation `χ` **every** crossed derivation `D(gh) = Dg + χ(g)·Dh` kills the
presenting relator.  So the functionals descend to the towers *on the nose*, with no relation
module theory: a derivation is just the `.u`-component of a hom into `A ⋊ ℤ₂ˣ`.

Since `ℤ₂ ⋊ ℤ₂ˣ` is not known here to be pro-2 (the universal properties `drLiftHom` /
`d0LiftHom` demand that), we run the whole calculus at the finite shadow
`WL N = ℤ/2^N ⋊ (ℤ/2^N)ˣ`, which is a finite 2-group by cardinality.  All the sharp 2-adic
input (the orientation values, `η⁻¹ = −3`, `v₂(X−1) = v₂(S−1) = 2`, `v₂(Y+1) = 3`) stays in
`ℤ₂` and is pushed down by the reduction ring hom. -/

open FoxH in
/-- The **finite lift group** `ℤ/2^N ⋊ (ℤ/2^N)ˣ` (`WordLift`, product law
`(u,g)(v,h) = (u + g·v, gh)`): the mod-`2^N` shadow of Labute's `ℤ₂(χ) ⋊ ℤ₂ˣ`. -/
abbrev WL (N : ℕ) : Type := FoxH.WordLift (ZMod (2 ^ N)) ((ZMod (2 ^ N))ˣ)

local instance instTopologicalSpaceWL (N : ℕ) : TopologicalSpace (WL N) := ⊥
local instance instDiscreteTopologyWL (N : ℕ) : DiscreteTopology (WL N) := ⟨rfl⟩
local instance instTopUnitsZMod (N : ℕ) : TopologicalSpace ((ZMod (2 ^ N))ˣ) := ⊥
local instance instDiscUnitsZMod (N : ℕ) : DiscreteTopology ((ZMod (2 ^ N))ˣ) := ⟨rfl⟩

section CrossedFunctional

open FoxH

/-- `WL N` is a finite 2-group: `|ℤ/2^N| · |(ℤ/2^N)ˣ| = 2^N · 2^{N-1}`. -/
private theorem isPGroup_WL {N : ℕ} (hN : 1 ≤ N) : IsPGroup 2 (WL N) := by
  have hcard : Nat.card (WL N) = 2 ^ (N + (N - 1)) := by
    have h1 : Nat.card (WL N) = Nat.card (ZMod (2 ^ N)) * Nat.card ((ZMod (2 ^ N))ˣ) := by
      rw [Nat.card_congr (WordLift.equivProd (A := ZMod (2 ^ N)) (C := (ZMod (2 ^ N))ˣ)),
        Nat.card_prod]
    have h2 : Nat.card (ZMod (2 ^ N)) = 2 ^ N := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      simp [Nat.card_eq_fintype_card]
    have h3 : Nat.card ((ZMod (2 ^ N))ˣ) = 2 ^ (N - 1) := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [h1, h2, h3, ← pow_add]
  exact IsPGroup.of_card hcard

/-- `WL N` is pro-2, hence a legal target for `drLiftHom` / `d0LiftHom`. -/
private theorem isProP_WL {N : ℕ} (hN : 1 ≤ N) : IsProP 2 (WL N) :=
  isProP_of_isPGroup (isPGroup_WL hN)

/-- The reduction `ℤ₂ ⋊ ℤ₂ˣ → ℤ/2^N ⋊ (ℤ/2^N)ˣ` (a group hom: reduction is a ring hom, so it
intertwines the two product laws). -/
noncomputable def redWL (N : ℕ) : WordLift ℤ_[2] ℤ_[2]ˣ →* WL N where
  toFun p := ⟨PadicInt.toZModPow N p.u, Units.map (PadicInt.toZModPow N).toMonoidHom p.g⟩
  map_one' := by ext <;> simp
  map_mul' p q := by
    ext
    · show PadicInt.toZModPow N (p.u + (p.g : ℤ_[2]) * q.u)
        = PadicInt.toZModPow N p.u
          + ((Units.map (PadicInt.toZModPow N).toMonoidHom p.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))
            * PadicInt.toZModPow N q.u
      simp
    · exact map_mul _ _ _

@[simp] private theorem redWL_u (N : ℕ) (p : WordLift ℤ_[2] ℤ_[2]ˣ) :
    (redWL N p).u = PadicInt.toZModPow N p.u := rfl

@[simp] theorem redWL_g (N : ℕ) (p : WordLift ℤ_[2] ℤ_[2]ˣ) :
    (redWL N p).g = Units.map (PadicInt.toZModPow N).toMonoidHom p.g := rfl

/-- The `.g`-projection `A ⋊ C → C`, as a monoid hom. -/
private def wlBase (N : ℕ) : WL N →* (ZMod (2 ^ N))ˣ where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Powers in `R ⋊ Rˣ`: the offset picks up the geometric sum of the base. -/
private theorem wl_pow {R : Type*} [CommRing R] (u : R) (g : Rˣ) (m : ℕ) :
    ((⟨u, g⟩ : WordLift R Rˣ) ^ m) = ⟨(∑ j ∈ Finset.range m, (g : R) ^ j) * u, g ^ m⟩ := by
  induction m with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext
    · show (∑ j ∈ Finset.range m, (g : R) ^ j) * u + ((g ^ m : Rˣ) : R) * u
        = (∑ j ∈ Finset.range (m + 1), (g : R) ^ j) * u
      rw [Finset.sum_range_succ, add_mul, Units.val_pow_eq_pow_val]
    · simp [pow_succ]

/-! #### `2`-power divisibility in `ℤ/2^N`, read through the reductions -/

private theorem two_pow_zmod_self {j : ℕ} : (2 : ZMod (2 ^ j)) ^ j = 0 := by
  have h : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h

/-- Divisibility by `2^j` in `ℤ/2^N` (`j ≤ N`) is the vanishing of the mod-`2^j` reduction. -/
private theorem two_pow_dvd_zmod_iff {N j : ℕ} (hj : j ≤ N) {x : ZMod (2 ^ N)} :
    (2 : ZMod (2 ^ N)) ^ j ∣ x ↔ ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) x = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_pow, map_ofNat, two_pow_zmod_self, zero_mul]
  · intro h
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) x
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-- Divisibility by `2^j` in `ℤ/2^N` is read off any `2`-adic lift (`j ≤ N`). -/
theorem two_pow_dvd_toZModPow_iff {N j : ℕ} (hj : j ≤ N) {x : ℤ_[2]} :
    (2 : ZMod (2 ^ N)) ^ j ∣ PadicInt.toZModPow N x ↔ (2 : ℤ_[2]) ^ j ∣ x := by
  rw [two_pow_dvd_zmod_iff hj, two_pow_dvd_iff, ZMod.castHom_apply, PadicInt.cast_toZModPow j N hj]

/-- Units of `ℤ/2^N` are odd. -/
private theorem two_dvd_units_sub_one {N : ℕ} (hN : 1 ≤ N) (g : (ZMod (2 ^ N))ˣ) :
    (2 : ZMod (2 ^ N)) ∣ (g : ZMod (2 ^ N)) - 1 := by
  have h1 : (1 : ℕ) ≤ N := hN
  have hcast := two_pow_dvd_zmod_iff (N := N) (j := 1) h1 (x := (g : ZMod (2 ^ N)) - 1)
  rw [pow_one] at hcast
  refine hcast.mpr ?_
  set ρ := ZMod.castHom (pow_dvd_pow 2 h1) (ZMod (2 ^ 1)) with hρ
  have hu : IsUnit (ρ (g : ZMod (2 ^ N))) := (g.isUnit).map ρ
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hone : ρ (g : ZMod (2 ^ N)) = 1 :=
    (by decide : ∀ a b : ZMod (2 ^ 1), a * b = 1 → a = 1) _ _ hv
  rw [map_sub, hone, map_one, sub_self]

/-- Halving: if `2^k` divides `2^{k-1}·z` in `ℤ/2^N` (`k ≤ N`), then `z` is even. -/
private theorem two_dvd_of_two_pow_dvd_mul {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {z : ZMod (2 ^ N)} (h : (2 : ZMod (2 ^ N)) ^ k ∣ (2 : ZMod (2 ^ N)) ^ (k - 1) * z) :
    (2 : ZMod (2 ^ N)) ∣ z := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) z
  rw [two_pow_dvd_zmod_iff hkN] at h
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
    exact (mul_dvd_mul_iff_left hne).mp (by rw [mul_comm ((2 : ℤ) ^ (k - 1)) 2] at h ⊢; exact h)
  obtain ⟨c, hc⟩ := h2
  exact ⟨(c : ZMod (2 ^ N)), by rw [hc]; push_cast; ring⟩

/-! #### The congruence filtration of `WL N` and the `λ`-bound -/

open scoped commutatorElement in
/-- The repo-convention commutator in `R ⋊ Rˣ` (the base components cancel). -/
private theorem wl_commutator {R : Type*} [CommRing R] (p q : WordLift R Rˣ) :
    ⁅p, q⁆ = ⟨p.u * (1 - (q.g : R)) + q.u * ((p.g : R) - 1), 1⟩ := by
  have hpg : ((p.g : R)) * ((p.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqg : ((q.g : R)) * ((q.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hpq : ((p.g : R)) * ((q.g : R)) * ((p.g⁻¹ : Rˣ) : R) * ((q.g⁻¹ : Rˣ) : R) = 1 := by
    calc ((p.g : R)) * ((q.g : R)) * ((p.g⁻¹ : Rˣ) : R) * ((q.g⁻¹ : Rˣ) : R)
        = (((p.g : R)) * ((p.g⁻¹ : Rˣ) : R)) * (((q.g : R)) * ((q.g⁻¹ : Rˣ) : R)) := by ring
      _ = 1 := by rw [hpg, hqg]; ring
  rw [commutatorElement_def]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, Units.smul_def,
      smul_eq_mul, Units.val_mul]
    linear_combination (-(p.u) * (q.g : R)) * hpg + (-(q.u)) * hpq
  · have hg : (p * q * p⁻¹ * q⁻¹).g = (1 : Rˣ) := by
      show p.g * q.g * p.g⁻¹ * q.g⁻¹ = 1
      rw [mul_comm p.g q.g]
      group
    rw [hg]

/-- The **congruence subgroup** `K_j = {(u,g) : 2^{j-1} ∣ u, 2^j ∣ g − 1}` of `WL N`: the
receptacle of the lower 2-central series (Labute's filtration bound in its finite shadow). -/
private def wlCong (N j : ℕ) : Subgroup (WL N) where
  carrier := {p | (2 : ZMod (2 ^ N)) ^ (j - 1) ∣ p.u ∧
    (2 : ZMod (2 ^ N)) ^ j ∣ (p.g : ZMod (2 ^ N)) - 1}
  one_mem' := by
    refine ⟨by simp, ?_⟩
    show (2 : ZMod (2 ^ N)) ^ j ∣ ((1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
    simp
  mul_mem' := by
    rintro p q ⟨hpu, hpg⟩ ⟨hqu, hqg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.mul_u, Units.smul_def, smul_eq_mul]
      exact dvd_add hpu (Dvd.dvd.mul_left hqu _)
    · rw [WordLift.mul_g]
      have hexp : ((p.g * q.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = ((p.g : ZMod (2 ^ N)) - 1) * (q.g : ZMod (2 ^ N)) + ((q.g : ZMod (2 ^ N)) - 1) := by
        push_cast
        ring
      rw [hexp]
      exact dvd_add (Dvd.dvd.mul_right hpg _) hqg
  inv_mem' := by
    rintro p ⟨hpu, hpg⟩
    refine ⟨?_, ?_⟩
    · rw [WordLift.inv_u, Units.smul_def, smul_eq_mul]
      exact (Dvd.dvd.mul_left hpu _).neg_right
    · rw [WordLift.inv_g]
      have hpginv : ((p.g : ZMod (2 ^ N))) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hexp : ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
          = -(((p.g : ZMod (2 ^ N)) - 1) * ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) := by
        linear_combination hpginv
      rw [hexp]
      exact (Dvd.dvd.mul_right hpg _).neg_right

private theorem mem_wlCong {N j : ℕ} {p : WL N} :
    p ∈ wlCong N j ↔ (2 : ZMod (2 ^ N)) ^ (j - 1) ∣ p.u ∧
      (2 : ZMod (2 ^ N)) ^ j ∣ (p.g : ZMod (2 ^ N)) - 1 := Iff.rfl

/-- **The filtration bound** (the finite shadow of `D(λ_j) ⊆ 2^{j-1}ℤ₂` and
`χ(λ_j) ⊆ 1 + 2^jℤ₂`): the lower 2-central series of `WL N` sinks into the congruence
filtration.  Both halves are needed: the base congruence drives the offset congruence one
step deeper at each squaring and each commutator. -/
private theorem twoCentralSeries_WL_le {N : ℕ} (hN : 1 ≤ N) {j : ℕ} (hj : 1 ≤ j) :
    twoCentralSeries (WL N) j ≤ wlCong N j := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro p _
    exact ⟨by simp, by rw [pow_one]; exact two_dvd_units_sub_one hN p.g⟩
  | succ j hj ih =>
    rw [twoCentralSeries_succ (WL N) hj]
    refine le_trans (twoCentralSucc_mono ih) ?_
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨hpu, hpg⟩ := hp
      show p ^ 2 ∈ wlCong N (j + 1)
      have h2g : (2 : ZMod (2 ^ N)) ∣ (p.g : ZMod (2 ^ N)) - 1 :=
        dvd_trans (dvd_pow_self 2 (by omega : j ≠ 0)) hpg
      obtain ⟨c, hc⟩ := h2g
      have h1 : (2 : ZMod (2 ^ N)) ∣ 1 + (p.g : ZMod (2 ^ N)) := ⟨c + 1, by linear_combination hc⟩
      have h1' : (2 : ZMod (2 ^ N)) ∣ (p.g : ZMod (2 ^ N)) + 1 := ⟨c + 1, by linear_combination hc⟩
      refine ⟨?_, ?_⟩
      · have hval : (p ^ 2).u = (1 + (p.g : ZMod (2 ^ N))) * p.u := by
          rw [pow_two, WordLift.mul_u, Units.smul_def, smul_eq_mul]
          ring
        have hmul := mul_dvd_mul h1 hpu
        rw [show (2 : ZMod (2 ^ N)) * 2 ^ (j - 1) = 2 ^ j by
          rw [← pow_succ']; congr 1; omega] at hmul
        rw [hval, show j + 1 - 1 = j from rfl]
        exact hmul
      · have hval : ((p ^ 2).g : ZMod (2 ^ N)) - 1
            = ((p.g : ZMod (2 ^ N)) - 1) * ((p.g : ZMod (2 ^ N)) + 1) := by
          rw [pow_two, WordLift.mul_g, Units.val_mul]
          ring
        rw [hval, pow_succ]
        exact mul_dvd_mul hpg h1'
    · refine Subgroup.commutator_le.2 ?_
      rintro p ⟨hpu, hpg⟩ q -
      rw [wl_commutator]
      refine ⟨?_, by simp⟩
      show (2 : ZMod (2 ^ N)) ^ (j + 1 - 1) ∣
        p.u * (1 - (q.g : ZMod (2 ^ N))) + q.u * ((p.g : ZMod (2 ^ N)) - 1)
      rw [show j + 1 - 1 = j from rfl]
      refine dvd_add ?_ (Dvd.dvd.mul_left hpg _)
      obtain ⟨c, hc⟩ := two_dvd_units_sub_one hN q.g
      have h1 : (2 : ZMod (2 ^ N)) ∣ 1 - (q.g : ZMod (2 ^ N)) := ⟨-c, by linear_combination -hc⟩
      have hmul := mul_dvd_mul hpu h1
      rw [show (2 : ZMod (2 ^ N)) ^ (j - 1) * 2 = 2 ^ j by
        rw [← pow_succ]; congr 1; omega] at hmul
      exact hmul

/-! #### The derivations out of the two towers -/

/-- Direction 1: the derivation `D_R → WL N` with generator data `(v i, χ_R)`.  It exists
because `χ_R` is Labute's orientation — **every** crossed derivation kills `r₂`
(`isLabuteOrientation_chiR`), which is exactly the relator hypothesis `drLiftHom` wants. -/
noncomputable def derivR (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    ContinuousMonoidHom (DR : Type) (WL N) :=
  drLiftHom (isProP_WL hN)
    ![redWL N ⟨v 0, chiR drS⟩, redWL N ⟨v 1, chiR drX⟩, redWL N ⟨v 2, chiR drY⟩]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [← map_drWord, show drWord (⟨v 0, chiR drS⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨v 1, chiR drX⟩
          ⟨v 2, chiR drY⟩ = 1 from isLabuteOrientation_chiR (v 0) (v 1) (v 2), map_one])

@[simp] theorem derivR_drS (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drS = redWL N ⟨v 0, chiR drS⟩ := drLiftHom_S _ _ _

@[simp] theorem derivR_drX (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drX = redWL N ⟨v 1, chiR drX⟩ := drLiftHom_X _ _ _

@[simp] theorem derivR_drY (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    derivR N hN v drY = redWL N ⟨v 2, chiR drY⟩ := drLiftHom_Y _ _ _

/-- **The base component is `χ_R`** (mod `2^N`): both sides are continuous homs `D_R → (ℤ/2^N)ˣ`
agreeing on `s, x, y`, so `dr_hom_ext` applies.  The right-hand side is continuous because it
factors through the discrete level quotient `Q_N`. -/
theorem derivR_base (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) (a : (DR : Type)) :
    (derivR N hN v a).g = Units.map (PadicInt.toZModPow N).toMonoidHom (chiR a) := by
  haveI := discreteTopology_levelQuot (DR : Type) drTopGenFinset isProP_DR N
  set f : ContinuousMonoidHom (DR : Type) ((ZMod (2 ^ N))ˣ) :=
    (⟨wlBase N, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ)).comp (derivR N hN v) with hf
  set g : ContinuousMonoidHom (DR : Type) ((ZMod (2 ^ N))ˣ) :=
    ⟨(chiLevel chiR N).comp (levelMk (DR : Type) N),
      show Continuous ((chiLevel chiR N) ∘ (levelMk (DR : Type) N)) from
        (continuous_of_discreteTopology (f := ⇑(chiLevel chiR N))).comp
          (continuous_levelMk (DR : Type) N)⟩ with hg
  have hval : ∀ b : (DR : Type), f b = (derivR N hN v b).g := fun _ => rfl
  have hval' : ∀ b : (DR : Type),
      g b = Units.map (PadicInt.toZModPow N).toMonoidHom (chiR b) := fun b => by
    show chiLevel chiR N (levelMk (DR : Type) N b) = _
    rw [chiLevel_levelMk]
  have hext : f = g := by
    refine dr_hom_ext f g ?_ ?_ ?_
    · rw [hval, hval', derivR_drS]; rfl
    · rw [hval, hval', derivR_drX]; rfl
    · rw [hval, hval', derivR_drY]; rfl
  rw [← hval a, hext, hval' a]

/-- **Hom-extensionality for `D₀`** (private clone of `dr_hom_ext`, on `SectionThree.topGen_d0`). -/
private theorem d0_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (φ ψ : ContinuousMonoidHom (D0 : Type) A)
    (hA : φ d0A = ψ d0A) (hS : φ d0S = ψ d0S) (hY : φ d0Y = ψ d0Y) : φ = ψ := by
  have hgens : Set.EqOn φ ψ ({d0A, d0S, d0Y} : Set (D0 : Type)) := by
    rintro w (rfl | rfl | rfl)
    exacts [hA, hS, hY]
  have hsub : Set.EqOn φ ψ (Subgroup.closure ({d0A, d0S, d0Y} : Set (D0 : Type))) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hgens hx
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  have hdense :
      Dense ((Subgroup.closure ({d0A, d0S, d0Y} : Set (D0 : Type))) : Set (D0 : Type)) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, SectionThree.topGen_d0,
      Subgroup.coe_top]
  refine ContinuousMonoidHom.ext (fun z => ?_)
  exact (hsub.closure φ.continuous_toFun ψ.continuous_toFun) (hdense z)

/-- **The `r₀`-side Labute datum**: with the orientation values `(−1, 1, η)` every crossed
derivation kills `r₀ = A²S⁴[S,Y]`.  The computation is the one 2-adic miracle behind SL1:
the `S⁴`-block contributes `4·Ds` and the commutator `(η⁻¹ − 1)·Ds`, and `η⁻¹ = −3` exactly,
so the total `(3 + η⁻¹)·Ds` vanishes on the nose. -/
theorem d0Word_wordLift_target (Da Ds Dy : ℤ_[2]) :
    d0Word (⟨Da, -1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Ds, 1⟩ ⟨Dy, etaUnit⟩ = 1 := by
  have hetainv : ((etaUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = -3 := by
    rw [etaUnit, inv_inv, negThreeUnit_val]
  have hsq : (⟨Da, -1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 2 = ⟨0, 1⟩ := by
    rw [wl_pow]
    ext
    · show (∑ j ∈ Finset.range 2, ((-1 : ℤ_[2]ˣ) : ℤ_[2]) ^ j) * Da = (0 : ℤ_[2])
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      push_cast
      ring
    · show (((-1 : ℤ_[2]ˣ) ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2])
      push_cast
      ring
  have hfour : (⟨Ds, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 4 = ⟨4 * Ds, 1⟩ := by
    rw [wl_pow]
    ext
    · show (∑ j ∈ Finset.range 4, ((1 : ℤ_[2]ˣ) : ℤ_[2]) ^ j) * Ds = 4 * Ds
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      push_cast
      ring
    · show (((1 : ℤ_[2]ˣ) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2])
      push_cast
      ring
  rw [d0Word, hsq, hfour, commP_wordLift]
  ext
  · simp only [WordLift.mul_u, WordLift.mul_g, WordLift.one_u, Units.smul_def, smul_eq_mul,
      Units.val_one, Units.val_mul, inv_one]
    rw [hetainv]
    ring
  · simp [commP_eq_one]

/-- Direction 2: the derivation `D₀ → WL N` with generator data `(v i, (−1, 1, η))`. -/
noncomputable def deriv0 (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    ContinuousMonoidHom (D0 : Type) (WL N) :=
  SectionThree.d0LiftHom (isProP_WL hN)
    ![redWL N ⟨v 0, -1⟩, redWL N ⟨v 1, 1⟩, redWL N ⟨v 2, etaUnit⟩]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      show d0Word (redWL N ⟨v 0, -1⟩) (redWL N ⟨v 1, 1⟩) (redWL N ⟨v 2, etaUnit⟩) = 1
      rw [← map_d0Word, d0Word_wordLift_target, map_one])

@[simp] theorem deriv0_d0A (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0A = redWL N ⟨v 0, -1⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] theorem deriv0_d0S (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0S = redWL N ⟨v 1, 1⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] theorem deriv0_d0Y (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) :
    deriv0 N hN v d0Y = redWL N ⟨v 2, etaUnit⟩ := by
  show ((maxProPHomEquiv (isProP_WL hN)).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = _
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- The base component of the `D₀`-derivation is the mod-`2^N` shadow of `χ₀`. -/
theorem deriv0_base (N : ℕ) (hN : 1 ≤ N) (v : Fin 3 → ℤ_[2]) (a : (D0 : Type)) :
    (deriv0 N hN v a).g = Units.map (PadicInt.toZModPow N).toMonoidHom (chiD0pres a) := by
  haveI := discreteTopology_levelQuot (D0 : Type) d0TopGenFinset SectionThree.d0_isProP N
  set f : ContinuousMonoidHom (D0 : Type) ((ZMod (2 ^ N))ˣ) :=
    (⟨wlBase N, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ)).comp (deriv0 N hN v) with hf
  set g : ContinuousMonoidHom (D0 : Type) ((ZMod (2 ^ N))ˣ) :=
    ⟨(chiLevel chiD0pres N).comp (levelMk (D0 : Type) N),
      show Continuous ((chiLevel chiD0pres N) ∘ (levelMk (D0 : Type) N)) from
        (continuous_of_discreteTopology (f := ⇑(chiLevel chiD0pres N))).comp
          (continuous_levelMk (D0 : Type) N)⟩ with hg
  have hval : ∀ b : (D0 : Type), f b = (deriv0 N hN v b).g := fun _ => rfl
  have hval' : ∀ b : (D0 : Type),
      g b = Units.map (PadicInt.toZModPow N).toMonoidHom (chiD0pres b) := fun b => by
    show chiLevel chiD0pres N (levelMk (D0 : Type) N b) = _
    rw [chiLevel_levelMk]
  have hext : f = g := by
    refine d0_hom_ext f g ?_ ?_ ?_
    · rw [hval, hval', deriv0_d0A, chiD0pres_d0A]; rfl
    · rw [hval, hval', deriv0_d0S, chiD0pres_d0S]; rfl
    · rw [hval, hval', deriv0_d0Y, chiD0pres_d0Y]; rfl
  rw [← hval a, hext, hval' a]

/-! #### The derivation kernel in `Zₖ`, and the tail pairing -/

/-- Powers of a general point of `R ⋊ Rˣ` (structure eta on `wl_pow`). -/
private theorem wl_pow' {R : Type*} [CommRing R] (p : WordLift R Rˣ) (m : ℕ) :
    p ^ m = ⟨(∑ j ∈ Finset.range m, (p.g : R) ^ j) * p.u, p.g ^ m⟩ := wl_pow p.u p.g m

/-- **The geometric sum at a base `≡ 1 (mod 4)`** is `2^m · odd`: doubling multiplies it by
`1 + u^{2^m} ∈ 2·(1 + 2ℤ₂)`.  This is what makes the two tails pair non-degenerately. -/
private theorem geom_sum_two_pow {u : ℤ_[2]} (hu : (2 : ℤ_[2]) ^ 2 ∣ u - 1) (m : ℕ) :
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
      have hshift : ∀ j : ℕ, u ^ (2 ^ m + j) = u ^ 2 ^ m * u ^ j := fun j => by rw [pow_add]
      simp only [hshift, ← Finset.mul_sum]
      ring
    have hval : 1 + u ^ 2 ^ m = 2 * (1 + 2 * d) := by
      have hpow : u ^ 2 ^ m = 1 + 2 ^ 2 * d := by linear_combination hd
      rw [hpow]
      ring
    rw [hsplit, hc, hval]
    ring

section DerivKer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transport of the filtration bound `λ_j(WL N) ⊆ K_j` to the tower along a derivation. -/
theorem deriv_mem_wlCong {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {j : ℕ} (hj : 1 ≤ j) {a : G} (ha : a ∈ twoCentralSeries G j) : Φ a ∈ wlCong N j :=
  twoCentralSeries_WL_le hN hj
    (map_twoCentralSeries_le Φ.toMonoidHom Φ.continuous_toFun j ⟨a, ha, rfl⟩)

/-- **The vanishing subgroup** `𝒜_Φ ⊆ Q_{k+1}`: classes admitting a `λₖ`-representative whose
derivation offset is divisible by `2^k`.  This is the Lean form of "the coker functional
`digit_{k-1} ∘ D` vanishes"; `derivKer_dvd` shows the condition does not depend on the
representative. -/
def derivKer {N : ℕ} (Φ : ContinuousMonoidHom G (WL N)) (k : ℕ) :
    Subgroup (levelQuot G (k + 1)) where
  carrier := {q | ∃ a, a ∈ twoCentralSeries G k ∧ levelMk G (k + 1) a = q ∧
    (2 : ZMod (2 ^ N)) ^ k ∣ (Φ a).u}
  one_mem' := ⟨1, one_mem _, map_one _, by simp⟩
  mul_mem' := by
    rintro q q' ⟨a, ha, rfl, hda⟩ ⟨b, hb, rfl, hdb⟩
    refine ⟨a * b, mul_mem ha hb, map_mul _ _ _, ?_⟩
    rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul]
    exact dvd_add hda (Dvd.dvd.mul_left hdb _)
  inv_mem' := by
    rintro q ⟨a, ha, rfl, hda⟩
    refine ⟨a⁻¹, inv_mem ha, map_inv _ _, ?_⟩
    rw [map_inv, WordLift.inv_u, Units.smul_def, smul_eq_mul]
    exact (Dvd.dvd.mul_left hda _).neg_right

/-- Representative-independence: membership of `levelMk b` forces the divisibility at `b`
itself (the ambiguity `λ_{k+1}` is already killed by the filtration bound). -/
private theorem derivKer_dvd {N : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N)) {k : ℕ}
    {b : G} (hb : levelMk G (k + 1) b ∈ derivKer Φ k) :
    (2 : ZMod (2 ^ N)) ^ k ∣ (Φ b).u := by
  obtain ⟨a, ha, hab, hda⟩ := hb
  have hmem : a⁻¹ * b ∈ twoCentralSeries G (k + 1) := QuotientGroup.eq.mp hab
  have hcong := (deriv_mem_wlCong hN Φ (by omega) hmem).1
  rw [show b = a * (a⁻¹ * b) by group, map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul]
  exact dvd_add hda (Dvd.dvd.mul_left hcong _)

end DerivKer

end CrossedFunctional

/-! ### Additivity of the shift word in the modification (`Im d̄` is a subgroup)

SL1 must produce a *single* modification, so the `d̄`-image has to be closed under products.
It is: every factor of `d̄` is `𝔽₂`-linear in `w` up to central corrections, and for `k ≥ 3`
all corrections lie in `Zₖ`, which is central. -/

section DbarAdditive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Moving a central factor one step to the right. -/
private theorem central_move {H : Type*} [Group H] {z : H} (hz : ∀ t : H, z * t = t * z)
    (x y : H) : z * (x * y) = x * (z * y) := by
  rw [← mul_assoc, hz, mul_assoc]

/-- Interleaving four central pairs (only the primed entries need to be central). -/
private theorem central_shuffle {H : Type*} [Group H] {A B C D A' B' C' D' : H}
    (hA' : ∀ t : H, A' * t = t * A') (hB' : ∀ t : H, B' * t = t * B')
    (hC' : ∀ t : H, C' * t = t * C') :
    A * A' * (B * B') * (C * C') * (D * D') = A * B * C * D * (A' * B' * C' * D') := by
  simp only [mul_assoc]
  rw [central_move hA' B, central_move hB' C, central_move hA' C, central_move hC' D,
    central_move hB' D, central_move hA' D]

/-- Interleaving three central pairs. -/
theorem central_shuffle3 {H : Type*} [Group H] {A B C A' B' C' : H}
    (hA' : ∀ t : H, A' * t = t * A') (hB' : ∀ t : H, B' * t = t * B') :
    A * A' * (B * B') * (C * C') = A * B * C * (A' * B' * C') := by
  simp only [mul_assoc]
  rw [central_move hA' B, central_move hB' C, central_move hA' C]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `commP · g` is additive on `λ_{k-1}`-modifications (the correction is central). -/
private theorem commP_mul_lambdaImage_left (k : ℕ) (hk : 3 ≤ k)
    {u u' : levelQuot G (k + 1)} (hu : u ∈ lambdaImage G (k - 1) (k + 1))
    (g : levelQuot G (k + 1)) : commP (u * u') g = commP u g * commP u' g := by
  rw [commP_mul_left, conj_eq_self_of_commP_eq_one
    (commP_eq_one_of_mul_comm (zLayer_commute (commP_mem_zLayer k hk hu g) u').eq)]

set_option linter.unusedSectionVars false in
/-- **Additivity of `d̄` in the modification, `r₀`-side.** -/
theorem dbarWordR0_mul (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hw' : ∀ i, w' i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y (fun i => w i * w' i) = dbarWordR0 a s y w * dbarWordR0 a s y w' := by
  have hcen : ∀ {z : levelQuot G (k + 1)}, z ∈ zLayer G k → ∀ t, z * t = t * z :=
    fun hz t => (zLayer_commute hz t).eq
  have hcomm : Commute (w 0) (w' 0) := mul_comm_lambdaImage k hk (hw 0) (hw' 0)
  have hsq : (w 0 * w' 0) ^ 2 = w 0 ^ 2 * w' 0 ^ 2 := hcomm.mul_pow 2
  simp only [dbarWordR0, hsq, commP_mul_lambdaImage_left k hk (hw 0),
    commP_mul_lambdaImage_left k hk (hw 1), commP_mul_lambdaImage_left k hk (hw 2)]
  exact central_shuffle (hcen (sq_mem_zLayer k hk (hw' 0)))
    (hcen (commP_mem_zLayer k hk (hw' 0) a)) (hcen (commP_mem_zLayer k hk (hw' 1) y))

set_option linter.unusedSectionVars false in
/-- **Additivity of `d̄` in the modification, `r₂`-side.** -/
theorem dbarWordR2_mul (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hw' : ∀ i, w' i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y (fun i => w i * w' i) = dbarWordR2 s x y w * dbarWordR2 s x y w' := by
  have hcen : ∀ {z : levelQuot G (k + 1)}, z ∈ zLayer G k → ∀ t, z * t = t * z :=
    fun hz t => (zLayer_commute hz t).eq
  have hcomm : Commute (w 2) (w' 2) := mul_comm_lambdaImage k hk (hw 2) (hw' 2)
  have hsq : (w 2 * w' 2) ^ 2 = w 2 ^ 2 * w' 2 ^ 2 := hcomm.mul_pow 2
  simp only [dbarWordR2, hsq, commP_mul_lambdaImage_left k hk (hw 2),
    commP_mul_lambdaImage_left k hk (hw 0), commP_mul_lambdaImage_left k hk (hw 1)]
  exact central_shuffle (hcen (sq_mem_zLayer k hk (hw' 2)))
    (hcen (commP_mem_zLayer k hk (hw' 2) y)) (hcen (commP_mem_zLayer k hk (hw' 0) x))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The shift word lands in the central layer `Zₖ`. -/
theorem dbarWordR0_mem_zLayer (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y w ∈ zLayer G k :=
  mul_mem (mul_mem (mul_mem (sq_mem_zLayer k hk (hw 0)) (commP_mem_zLayer k hk (hw 0) a))
    (commP_mem_zLayer k hk (hw 1) y)) (commP_mem_zLayer k hk (hw 2) s)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem dbarWordR2_mem_zLayer (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y w ∈ zLayer G k :=
  mul_mem (mul_mem (mul_mem (sq_mem_zLayer k hk (hw 2)) (commP_mem_zLayer k hk (hw 2) y))
    (commP_mem_zLayer k hk (hw 0) x)) (commP_mem_zLayer k hk (hw 1) s)

end DbarAdditive

/-! ### The endgame: the coordinate derivations separate the two tails -/

section TailSeparation

open FoxH

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The mod-2 reduction of `ℤ/2^N`. -/
private def redTwo {N : ℕ} (hN : 1 ≤ N) : ZMod (2 ^ N) →+* ZMod (2 ^ 1) :=
  ZMod.castHom (pow_dvd_pow 2 hN) (ZMod (2 ^ 1))

/-- Units reduce to `1` mod `2`. -/
private theorem redTwo_units {N : ℕ} (hN : 1 ≤ N) (g : (ZMod (2 ^ N))ˣ) :
    redTwo hN (g : ZMod (2 ^ N)) = 1 := by
  obtain ⟨v, hv⟩ := (g.isUnit.map (redTwo hN)).exists_right_inv
  exact (by decide : ∀ a b : ZMod (2 ^ 1), a * b = 1 → a = 1) _ _ hv

/-- Odd `2`-adics reduce to `1` mod `2`. -/
private theorem redTwo_odd {N : ℕ} (hN : 1 ≤ N) {c : ℤ_[2]} (hc : ¬ (2 : ℤ_[2]) ∣ c) :
    redTwo hN (PadicInt.toZModPow N c) = 1 := by
  have h : redTwo hN (PadicInt.toZModPow N c) ≠ 0 := by
    intro h0
    refine hc ?_
    rw [← pow_one (2 : ℤ_[2]), ← two_pow_dvd_toZModPow_iff hN, two_pow_dvd_zmod_iff hN]
    exact h0
  revert h
  generalize redTwo hN (PadicInt.toZModPow N c) = z
  revert z
  decide

/-- The mod-2 coordinate vector of the derivations at the three coordinate directions. -/
private noncomputable def thetaVec {N : ℕ} (hN : 1 ≤ N) (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N))
    (x : G) : Fin 3 → ZMod (2 ^ 1) :=
  fun j => redTwo hN ((Φ (Pi.single j 1) x).u)

private theorem thetaVec_mul {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (x y : G) :
    thetaVec hN Φ (x * y) = thetaVec hN Φ x + thetaVec hN Φ y := by
  funext j
  show redTwo hN ((Φ (Pi.single j 1) (x * y)).u) = _
  rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul, map_add, map_mul, redTwo_units hN,
    one_mul]
  rfl

private theorem thetaVec_one {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) : thetaVec hN Φ (1 : G) = 0 := by
  funext j
  show redTwo hN ((Φ (Pi.single j 1) 1).u) = 0
  rw [map_one]
  simp

private theorem thetaVec_inv {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (x : G) :
    thetaVec hN Φ x⁻¹ = -thetaVec hN Φ x := by
  have h := thetaVec_mul hN Φ x x⁻¹
  rw [mul_inv_cancel, thetaVec_one] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

/-- `θ` kills `λ₂` (the offset of a `λ₂`-element is already even). -/
private theorem thetaVec_lambdaTwo {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) {x : G}
    (hx : x ∈ twoCentralSeries G 2) : thetaVec hN Φ x = 0 := by
  funext j
  have h := (deriv_mem_wlCong hN (Φ (Pi.single j 1)) (by omega) hx).1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  show redTwo hN ((Φ (Pi.single j 1) x).u) = 0
  have hz : (2 : ZMod (2 ^ N)) ^ 1 ∣ (Φ (Pi.single j 1) x).u := by rwa [pow_one]
  exact (two_pow_dvd_zmod_iff (N := N) (j := 1) hN).mp hz

/-- The mod-2 reduction of a geometric sum of units counts its terms. -/
private theorem redTwo_geom {N : ℕ} (hN : 1 ≤ N) (h : (ZMod (2 ^ N))ˣ) (m : ℕ) :
    redTwo hN (∑ j ∈ Finset.range m, ((h : ZMod (2 ^ N))) ^ j) = (m : ZMod (2 ^ 1)) := by
  rw [map_sum]
  simp only [map_pow, redTwo_units hN, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]

/-- **The tail offset**: `(Φ ((x^{2^{k-1}})^α)).u = 2^{k-1}·C·(Φ x).u` with `C ≡ α (mod 2)` —
the sharpness of the geometric sum at a base `≡ 1 (mod 4)`. -/
private theorem deriv_tail_u {N k : ℕ} (hN : 1 ≤ N) (Φ : ContinuousMonoidHom G (WL N))
    {x : G} {u : ℤ_[2]} (hu : (2 : ℤ_[2]) ^ 2 ∣ u - 1)
    (hg : ((Φ x).g : ZMod (2 ^ N)) = PadicInt.toZModPow N u) (α : ℕ) :
    ∃ C : ZMod (2 ^ N), redTwo hN C = (α : ZMod (2 ^ 1)) ∧
      (Φ ((x ^ 2 ^ (k - 1)) ^ α)).u = 2 ^ (k - 1) * (C * (Φ x).u) := by
  obtain ⟨c, hc, hc2⟩ := geom_sum_two_pow hu (k - 1)
  have hSxval : (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j)
      = 2 ^ (k - 1) * PadicInt.toZModPow N c := by
    have hmap : (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j)
        = PadicInt.toZModPow N (∑ j ∈ Finset.range (2 ^ (k - 1)), u ^ j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_pow, hg]
    rw [hmap, hc, map_mul, map_pow, map_ofNat]
  refine ⟨(∑ j ∈ Finset.range α, ((Φ (x ^ 2 ^ (k - 1))).g : ZMod (2 ^ N)) ^ j) *
    PadicInt.toZModPow N c, ?_, ?_⟩
  · rw [map_mul, redTwo_geom hN, redTwo_odd hN hc2, mul_one]
  · have h1 : (Φ (x ^ 2 ^ (k - 1))).u
        = (∑ j ∈ Finset.range (2 ^ (k - 1)), ((Φ x).g : ZMod (2 ^ N)) ^ j) * (Φ x).u := by
      rw [map_pow, wl_pow']
    have h2 : (Φ ((x ^ 2 ^ (k - 1)) ^ α)).u
        = (∑ j ∈ Finset.range α, ((Φ (x ^ 2 ^ (k - 1))).g : ZMod (2 ^ N)) ^ j) *
          (Φ (x ^ 2 ^ (k - 1))).u := by
      conv_lhs => rw [map_pow, wl_pow']
    rw [h2, h1, hSxval]
    ring

/-- **The tail parity relation**: if a tail combination lies in every coordinate derivation's
kernel, the two coordinate vectors satisfy the corresponding `𝔽₂`-linear relation. -/
theorem tail_parity {N k : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N) (hkN : k ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N))
    {x y : G} {ux uy : ℤ_[2]}
    (hux : (2 : ℤ_[2]) ^ 2 ∣ ux - 1) (huy : (2 : ℤ_[2]) ^ 2 ∣ uy - 1)
    (hgx : ∀ v, ((Φ v x).g : ZMod (2 ^ N)) = PadicInt.toZModPow N ux)
    (hgy : ∀ v, ((Φ v y).g : ZMod (2 ^ N)) = PadicInt.toZModPow N uy)
    (α β : ℕ)
    (hmem : ∀ v, levelMk G (k + 1) ((x ^ 2 ^ (k - 1)) ^ α * (y ^ 2 ^ (k - 1)) ^ β) ∈
      derivKer (Φ v) k) :
    (α : ZMod (2 ^ 1)) • thetaVec hN Φ x + (β : ZMod (2 ^ 1)) • thetaVec hN Φ y = 0 := by
  funext j
  obtain ⟨Cx, hCx, hxval⟩ := deriv_tail_u (k := k) hN (Φ (Pi.single j 1)) hux (hgx _) α
  obtain ⟨Cy, hCy, hyval⟩ := deriv_tail_u (k := k) hN (Φ (Pi.single j 1)) huy (hgy _) β
  have hdvd := derivKer_dvd hN (Φ (Pi.single j 1)) (hmem (Pi.single j 1))
  rw [map_mul, WordLift.mul_u, Units.smul_def, smul_eq_mul, hxval, hyval] at hdvd
  set gα : ZMod (2 ^ N) :=
    ((Φ (Pi.single j 1) ((x ^ 2 ^ (k - 1)) ^ α)).g : ZMod (2 ^ N)) with hgα
  have hfac : (2 : ZMod (2 ^ N)) ^ (k - 1) * (Cx * (Φ (Pi.single j 1) x).u)
        + gα * (2 ^ (k - 1) * (Cy * (Φ (Pi.single j 1) y).u))
      = 2 ^ (k - 1) * (Cx * (Φ (Pi.single j 1) x).u
        + gα * (Cy * (Φ (Pi.single j 1) y).u)) := by ring
  rw [hfac] at hdvd
  have h2 := two_dvd_of_two_pow_dvd_mul (by omega : 1 ≤ k) hkN hdvd
  have hred : redTwo hN (Cx * (Φ (Pi.single j 1) x).u
      + gα * (Cy * (Φ (Pi.single j 1) y).u)) = 0 := by
    have hz : (2 : ZMod (2 ^ N)) ^ 1 ∣ Cx * (Φ (Pi.single j 1) x).u
        + gα * (Cy * (Φ (Pi.single j 1) y).u) := by rwa [pow_one]
    exact (two_pow_dvd_zmod_iff (N := N) (j := 1) hN).mp hz
  rw [map_add, map_mul, map_mul, map_mul, hCx, hCy, hgα, redTwo_units hN, one_mul] at hred
  show (α : ZMod (2 ^ 1)) * thetaVec hN Φ x j + (β : ZMod (2 ^ 1)) * thetaVec hN Φ y j = 0
  exact hred

/-- The coordinate vectors of the tower generators are the standard basis. -/
private theorem thetaVec_gen {N : ℕ} (hN : 1 ≤ N)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (gen : Fin 3 → G)
    (hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3), (Φ v (gen j)).u = PadicInt.toZModPow N (v j))
    (j : Fin 3) : thetaVec hN Φ (gen j) = Pi.single j (1 : ZMod (2 ^ 1)) := by
  funext i
  show redTwo hN ((Φ (Pi.single i 1) (gen j)).u) = _
  rw [hgenval, Pi.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    simp

/-- **Independence of a generating triple's coordinate vectors.**  The coordinate map
`𝔽₂³ → 𝔽₂³`, `c ↦ ∑ cᵢ·θ(aᵢ)`, hits the standard basis (the classes of the `aᵢ` generate
`Q_{k+1}`, and `θ` factors through it), hence is onto, hence — same finite type — injective. -/
theorem thetaVec_indep {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom G (WL N)) (gen a : Fin 3 → G)
    (hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3), (Φ v (gen j)).u = PadicInt.toZModPow N (v j))
    (hgent : Subgroup.closure (Set.range fun i => levelMk G (k + 1) (a i)) = ⊤)
    {c : Fin 3 → ZMod (2 ^ 1)}
    (hc : c 0 • thetaVec hN Φ (a 0) + c 1 • thetaVec hN Φ (a 1) + c 2 • thetaVec hN Φ (a 2) = 0) :
    c = 0 := by
  classical
  set L : (Fin 3 → ZMod (2 ^ 1)) → (Fin 3 → ZMod (2 ^ 1)) := fun d =>
    d 0 • thetaVec hN Φ (a 0) + d 1 • thetaVec hN Φ (a 1) + d 2 • thetaVec hN Φ (a 2) with hLdef
  have hLadd : ∀ d d' : Fin 3 → ZMod (2 ^ 1), L (d + d') = L d + L d' := by
    intro d d'
    funext i
    simp only [hLdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hLsmul : ∀ (z : ZMod (2 ^ 1)) (d : Fin 3 → ZMod (2 ^ 1)), L (z • d) = z • L d := by
    intro z d
    funext i
    simp only [hLdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hLzero : L 0 = 0 := by simp [hLdef]
  have hLbasis : ∀ i : Fin 3, L (Pi.single i 1) = thetaVec hN Φ (a i) := by
    intro i
    fin_cases i <;> simp [hLdef]
  set S : Subgroup (levelQuot G (k + 1)) :=
    { carrier := {q | ∃ x : G, levelMk G (k + 1) x = q ∧ thetaVec hN Φ x ∈ Set.range L}
      one_mem' := ⟨1, map_one _, ⟨0, by rw [hLzero, thetaVec_one]⟩⟩
      mul_mem' := by
        rintro p q ⟨x, rfl, d, hd⟩ ⟨y, rfl, d', hd'⟩
        exact ⟨x * y, map_mul _ _ _, ⟨d + d', by rw [hLadd, hd, hd', thetaVec_mul]⟩⟩
      inv_mem' := by
        rintro p ⟨x, rfl, d, hd⟩
        refine ⟨x⁻¹, map_inv _ _, ⟨-d, ?_⟩⟩
        have hneg : L (-d) = -L d := by
          have h := hLadd d (-d)
          rw [add_neg_cancel, hLzero] at h
          exact eq_neg_of_add_eq_zero_right h.symm
        rw [hneg, hd, thetaVec_inv] } with hSdef
  have hStop : S = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgent, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, rfl, ⟨Pi.single i 1, hLbasis i⟩⟩
  have hbasis : ∀ j : Fin 3, (Pi.single j (1 : ZMod (2 ^ 1))) ∈ Set.range L := by
    intro j
    have hmem : levelMk G (k + 1) (gen j) ∈ S := by rw [hStop]; trivial
    obtain ⟨x, hx, d, hd⟩ := hmem
    have hdiff : x⁻¹ * gen j ∈ twoCentralSeries G 2 :=
      twoCentralSeries_antitone G (by omega : 2 ≤ k + 1) (QuotientGroup.eq.mp hx)
    have hθ : thetaVec hN Φ (gen j) = thetaVec hN Φ x := by
      have hsplit : thetaVec hN Φ (x * (x⁻¹ * gen j))
          = thetaVec hN Φ x + thetaVec hN Φ (x⁻¹ * gen j) := thetaVec_mul hN Φ _ _
      rw [show x * (x⁻¹ * gen j) = gen j by group, thetaVec_lambdaTwo hN Φ hdiff,
        add_zero] at hsplit
      exact hsplit
    rw [← thetaVec_gen hN Φ gen hgenval j, hθ]
    exact ⟨d, hd⟩
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨d0, hd0⟩ := hbasis 0
    obtain ⟨d1, hd1⟩ := hbasis 1
    obtain ⟨d2, hd2⟩ := hbasis 2
    refine ⟨z 0 • d0 + (z 1 • d1 + z 2 • d2), ?_⟩
    rw [hLadd, hLadd, hLsmul, hLsmul, hLsmul, hd0, hd1, hd2]
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  have hinj : Function.Injective L := Finite.injective_iff_surjective.mpr hsurj
  have hLc : L c = L 0 := by rw [hLzero]; exact hc
  exact hinj hLc

end TailSeparation

end GQ2.Roe.Labute
