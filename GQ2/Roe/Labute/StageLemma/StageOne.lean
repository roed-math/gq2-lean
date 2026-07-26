/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.CrossedDerivation

/-!
# Reference words and SL1

Piece 5/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  The congruence bookkeeping at the pinned targets, then the
two reachability statements `stageSL1R0` / `stageSL1R2`.
-/

namespace GQ2.Roe.Labute

-- The `WL`-side topologies are declared as `local instance`s in
-- `GQ2.Roe.Labute.StageLemma.CrossedDerivation`; re-attach them here (same declarations,
-- no new ones) so the derivations remain `ContinuousMonoidHom`s in this module.
attribute [local instance] instTopologicalSpaceWL instDiscreteTopologyWL instTopUnitsZMod
  instDiscUnitsZMod

/-! ### The congruence bookkeeping: reference words at the pinned targets

Both "functional vanishes" statements (`φ(δ) = 0` and `φ(Im d̄) = 0`) are proved by *comparison*:
the actual triple is congruent, modulo the two-sided congruence subgroup `wlKer N k`, to a
reference triple whose χ-values are the pinned targets exactly.  At the reference the word
value is computed in closed form — and vanishes, by Labute's descent datum (for `δ`) or by the
target valuations (for `d̄`). -/

section Reference

open FoxH

/-- Every residue lifts to `ℤ₂`. -/
private theorem toZModPow_surj {N : ℕ} (z : ZMod (2 ^ N)) :
    ∃ x : ℤ_[2], PadicInt.toZModPow N x = z := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ N) z
  exact ⟨(m : ℤ_[2]), by rw [map_intCast]⟩

/-- The two-sided mod-`2^k` congruence subgroup of `WL N`. -/
private def wlKer (N k : ℕ) : Subgroup (WL N) where
  carrier := {p | (2 : ZMod (2 ^ N)) ^ k ∣ p.u ∧
    (2 : ZMod (2 ^ N)) ^ k ∣ (p.g : ZMod (2 ^ N)) - 1}
  one_mem' := by
    refine ⟨by simp, ?_⟩
    show (2 : ZMod (2 ^ N)) ^ k ∣ ((1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
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

private instance wlKer_normal (N k : ℕ) : (wlKer N k).Normal := by
  constructor
  rintro p ⟨hpu, hpg⟩ q
  refine ⟨?_, ?_⟩
  · have hval : (q * p * q⁻¹).u
        = (q.g : ZMod (2 ^ N)) * p.u + q.u * (1 - (p.g : ZMod (2 ^ N))) := by
      have hq : ((q.g : ZMod (2 ^ N))) * ((q.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, Units.smul_def,
        smul_eq_mul, Units.val_mul]
      linear_combination (-(q.u) * (p.g : ZMod (2 ^ N))) * hq
    rw [hval]
    refine dvd_add (Dvd.dvd.mul_left hpu _) (Dvd.dvd.mul_left ?_ _)
    obtain ⟨c, hc⟩ := hpg
    exact ⟨-c, by linear_combination -hc⟩
  · have hval : ((q * p * q⁻¹).g : ZMod (2 ^ N)) = (p.g : ZMod (2 ^ N)) := by
      have hg : (q * p * q⁻¹).g = p.g := by
        show q.g * p.g * q.g⁻¹ = p.g
        rw [mul_comm q.g p.g]
        group
      rw [hg]
    rw [hval]
    exact hpg

/-- The membership criterion used throughout: equal offsets and congruent base values. -/
private theorem inv_mul_mem_wlKer {N k : ℕ} {p q : WL N} (hu : p.u = q.u)
    (hg : (2 : ZMod (2 ^ N)) ^ k ∣ ((p.g⁻¹ * q.g : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1) :
    p⁻¹ * q ∈ wlKer N k := by
  refine ⟨?_, ?_⟩
  · have hval : (p⁻¹ * q).u
        = ((p.g⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) * (q.u - p.u) := by
      simp only [WordLift.mul_u, WordLift.inv_u, WordLift.inv_g, Units.smul_def, smul_eq_mul]
      ring
    rw [hval, hu, sub_self, mul_zero]
    exact dvd_zero _
  · exact hg

/-- Flipping the side of a unit congruence. -/
private theorem dvd_inv_mul_of_dvd_mul_inv {A B : ℤ_[2]ˣ} {n : ℕ}
    (h : (2 : ℤ_[2]) ^ n ∣ ((A * B⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    (2 : ℤ_[2]) ^ n ∣ ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨c, hc⟩ := h
  have hunit : ((A * B⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, show A * B⁻¹ * (A⁻¹ * B) = 1 by rw [mul_comm A B⁻¹]; group,
      Units.val_one]
  exact ⟨-c * ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]),
    by linear_combination hunit - ((A⁻¹ * B : ℤ_[2]ˣ) : ℤ_[2]) * hc⟩

/-- `commP` at a base-`1` modification slot. -/
private theorem commP_wl_one {R : Type*} [CommRing R] (d D : R) (t : Rˣ) :
    commP (⟨d, 1⟩ : WordLift R Rˣ) ⟨D, t⟩ = ⟨(((t⁻¹ : Rˣ) : R) - 1) * d, 1⟩ := by
  have ht : ((t⁻¹ : Rˣ) : R) * (t : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext
  · simp only [commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
      Units.smul_def, smul_eq_mul, Units.val_mul, inv_one, Units.val_one]
    ring
  · simp [commP]

/-- Squaring a base-`1` slot. -/
private theorem sq_wl_one {R : Type*} [CommRing R] (d : R) :
    (⟨d, 1⟩ : WordLift R Rˣ) ^ 2 = ⟨2 * d, 1⟩ := by
  rw [pow_two]
  ext
  · show d + ((1 : Rˣ) : R) * d = 2 * d
    push_cast
    ring
  · simp

/-- Product of base-`1` points adds the offsets. -/
private theorem mul_wl_one {R : Type*} [CommRing R] (d d' : R) :
    (⟨d, 1⟩ : WordLift R Rˣ) * ⟨d', 1⟩ = ⟨d + d', 1⟩ := by
  ext
  · show d + ((1 : Rˣ) : R) * d' = d + d'
    push_cast
    ring
  · simp

/-- **The reference shift word, `r₀`-side**, in closed form. -/
private theorem dbarWordR0_ref {R : Type*} [CommRing R] (D0 D1 D2 d0 d1 d2 : R) (t0 t1 t2 : Rˣ) :
    dbarWordR0 (⟨D0, t0⟩ : WordLift R Rˣ) ⟨D1, t1⟩ ⟨D2, t2⟩ ![⟨d0, 1⟩, ⟨d1, 1⟩, ⟨d2, 1⟩]
      = ⟨(1 + ((t0⁻¹ : Rˣ) : R)) * d0 + (((t2⁻¹ : Rˣ) : R) - 1) * d1
          + (((t1⁻¹ : Rˣ) : R) - 1) * d2, 1⟩ := by
  simp only [dbarWordR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, sq_wl_one, commP_wl_one, mul_wl_one]
  ext
  · show 2 * d0 + (((t0⁻¹ : Rˣ) : R) - 1) * d0 + ((((t2⁻¹ : Rˣ) : R) - 1) * d1)
        + (((t1⁻¹ : Rˣ) : R) - 1) * d2 = _
    ring
  · rfl

/-- **The reference shift word, `r₂`-side**, in closed form. -/
private theorem dbarWordR2_ref {R : Type*} [CommRing R] (D0 D1 D2 d0 d1 d2 : R) (t0 t1 t2 : Rˣ) :
    dbarWordR2 (⟨D0, t0⟩ : WordLift R Rˣ) ⟨D1, t1⟩ ⟨D2, t2⟩ ![⟨d0, 1⟩, ⟨d1, 1⟩, ⟨d2, 1⟩]
      = ⟨(1 + ((t2⁻¹ : Rˣ) : R)) * d2 + (((t1⁻¹ : Rˣ) : R) - 1) * d0
          + (((t0⁻¹ : Rˣ) : R) - 1) * d1, 1⟩ := by
  simp only [dbarWordR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, sq_wl_one, commP_wl_one, mul_wl_one]
  ext
  · show 2 * d2 + (((t2⁻¹ : Rˣ) : R) - 1) * d2 + ((((t1⁻¹ : Rˣ) : R) - 1) * d0)
        + (((t0⁻¹ : Rˣ) : R) - 1) * d1 = _
    ring
  · rfl

/-- Reduction of a `1 + t⁻¹` coefficient. -/
private theorem red_coeff_one_add {N : ℕ} (t : ℤ_[2]ˣ) :
    (1 : ZMod (2 ^ N))
        + (((Units.map (PadicInt.toZModPow N).toMonoidHom t)⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))
      = PadicInt.toZModPow N (1 + ((t⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
  rw [map_add, map_one, ← map_inv]
  rfl

/-- Reduction of a `t⁻¹ − 1` coefficient. -/
private theorem red_coeff_sub_one {N : ℕ} (t : ℤ_[2]ˣ) :
    (((Units.map (PadicInt.toZModPow N).toMonoidHom t)⁻¹ : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N)) - 1
      = PadicInt.toZModPow N (((t⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  rw [map_sub, map_one, ← map_inv]
  rfl

/-- A `4`-divisible coefficient times a `2^{k-2}`-divisible offset is `2^k`-divisible. -/
private theorem dvd_coeff_mul {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) {c : ℤ_[2]}
    (hc : (2 : ℤ_[2]) ^ 2 ∣ c) {d : ZMod (2 ^ N)} (hd : (2 : ZMod (2 ^ N)) ^ (k - 2) ∣ d) :
    (2 : ZMod (2 ^ N)) ^ k ∣ PadicInt.toZModPow N c * d := by
  have h1 : (2 : ZMod (2 ^ N)) ^ 2 ∣ PadicInt.toZModPow N c :=
    (two_pow_dvd_toZModPow_iff (by omega)).mpr hc
  have h := mul_dvd_mul h1 hd
  rwa [← pow_add, show 2 + (k - 2) = k by omega] at h

end Reference

/-! ## The stage lemma: SL1, SL2, and the step (spike §2.4) -/

/-- **SL1 (reachability), direction 1**: for `T ∈ S^P_ₖ` (`k ≥ 3`), the defect is
reachable — some `λ_{k-1}`-modification's shift equals `δ(T)⁻¹` (inverse form; in `Zₖ`
inverses are trivial, so this is the memo's `δₖ(T) ∈ Im d̄ₖ(T)`).  This is where the
invariant `P` earns its keep: the spike's census shows the statement is *false* without
the χ-clause (192/192 `P`-violating classes unreachable at `k = 4`).  Fill: L4b (span
theorem + the two separating functionals of spike §2.5(b)). -/
theorem stageSL1R0 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) :
    ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w = (defectR0 k T)⁻¹ := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hN : 1 ≤ k + 1 := by omega
  have hkN : k ≤ k + 1 := by omega
  choose a ha using fun i : Fin 3 =>
    levelMk_surjective (DR : Type) (k + 1) (canonLift (DR : Type) k (T i))
  have hproj : ∀ i, levelMk (DR : Type) k (a i) = T i := fun i => by
    rw [← levelProj_levelMk, ha i, levelProj_canonLift]
  have himg : (levelProj (DR : Type) k) ''
      (Set.range fun i => canonLift (DR : Type) k (T i)) = Set.range T := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => levelProj_canonLift (DR : Type) k (T i))
  have hgent : Subgroup.closure (Set.range fun i => canonLift (DR : Type) k (T i)) = ⊤ := by
    refine eq_top_of_map_levelProj_eq_top (DR : Type) drTopGenFinset isProP_DR (by omega) ?_
    rw [MonoidHom.map_closure, himg, hgen]
  have hgent' : Subgroup.closure (Set.range fun i => levelMk (DR : Type) (k + 1) (a i)) = ⊤ := by
    rw [show (fun i => levelMk (DR : Type) (k + 1) (a i))
      = fun i => canonLift (DR : Type) k (T i) from funext ha]
    exact hgent
  set Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom (DR : Type) (WL (k + 1)) :=
    fun v => derivR (k + 1) hN v with hΦ
  have hbase : ∀ (v : Fin 3 → ℤ_[2]) (x : (DR : Type)),
      (Φ v x).g = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiR x) :=
    fun v x => derivR_base (k + 1) hN v x
  have hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3),
      (Φ v (![drS, drX, drY] j)).u = PadicInt.toZModPow (k + 1) (v j) := by
    intro v j
    fin_cases j
    · show (derivR (k + 1) hN v drS).u = _
      rw [derivR_drS]; rfl
    · show (derivR (k + 1) hN v drX).u = _
      rw [derivR_drX]; rfl
    · show (derivR (k + 1) hN v drY).u = _
      rw [derivR_drY]; rfl
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiR (a i) * (chiTargetUnitsR0 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiR (chiTargetUnitsR0 i) (hproj i) ?_
    simpa [chiTargetR0] using hchi i
  -- congruence of a slot with its pinned target
  have hslot : ∀ (v : Fin 3 → ℤ_[2]) (i : Fin 3) (x : ℤ_[2]),
      PadicInt.toZModPow (k + 1) x = (Φ v (a i)).u →
      (Φ v (a i))⁻¹ * redWL (k + 1) ⟨x, chiTargetUnitsR0 i⟩ ∈ wlKer (k + 1) k := by
    intro v i x hx
    refine inv_mul_mem_wlKer hx.symm ?_
    have h2 : (2 : ℤ_[2]) ^ k ∣
        (((chiR (a i))⁻¹ * chiTargetUnitsR0 i : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (hdev i)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v (a i)).g⁻¹ * (redWL (k + 1) ⟨x, chiTargetUnitsR0 i⟩).g
          : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
          ((chiR (a i))⁻¹ * chiTargetUnitsR0 i) := by
      rw [map_mul, map_inv, hbase v (a i), redWL_g]
    rw [hg]
    exact hred
  -- congruence of a `λ_{k-1}`-modification slot with base `1`
  have hwslot : ∀ (v : Fin 3 → ℤ_[2]) (x : (DR : Type)),
      x ∈ twoCentralSeries (DR : Type) (k - 1) →
      (Φ v x)⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)) ∈ wlKer (k + 1) k := by
    intro v x hx
    refine inv_mul_mem_wlKer rfl ?_
    have h1 : (2 : ℤ_[2]) ^ k ∣ ((chiR x : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      have h := dvd_chi_of_mem_twoCentralSeries chiR (k := k - 1) (by omega) hx
      rwa [show k - 1 + 1 = k by omega] at h
    have h2 : (2 : ℤ_[2]) ^ k ∣ (((chiR x)⁻¹ * 1 : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (by simpa using h1)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v x).g⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)).g : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom ((chiR x)⁻¹ * 1) := by
      rw [map_mul, map_inv, map_one, mul_one, mul_one, hbase v x]
    rw [hg]
    exact hred
  -- the defect lies in every derivation kernel (the `r₀`-datum at the pinned targets)
  have hδker : ∀ v, defectR0 k T ∈ derivKer (Φ v) k := by
    intro v
    refine ⟨d0Word (a 0) (a 1) (a 2), ?_, ?_, ?_⟩
    · have hmk : levelMk (DR : Type) k (d0Word (a 0) (a 1) (a 2)) = 1 := by
        rw [map_d0Word, hproj, hproj, hproj]
        exact hrel
      exact (QuotientGroup.eq_one_iff _).mp hmk
    · rw [map_d0Word, ha 0, ha 1, ha 2]
      rfl
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have href : d0Word (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩)
          (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩) = 1 := by
        rw [show chiTargetUnitsR0 0 = -1 from by simp [chiTargetUnitsR0],
          show chiTargetUnitsR0 1 = 1 from by simp [chiTargetUnitsR0],
          show chiTargetUnitsR0 2 = etaUnit from by simp [chiTargetUnitsR0],
          ← map_d0Word, d0Word_wordLift_target, map_one]
      have hmkeq : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (d0Word (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (d0Word (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩)
              (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)) := by
        rw [map_d0Word, map_d0Word, hmkeq (hslot v 0 x0 hx0), hmkeq (hslot v 1 x1 hx1),
          hmkeq (hslot v 2 x2 hx2)]
      rw [href, map_one] at hcong
      have hmem : d0Word (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) ∈ wlKer (k + 1) k :=
        (QuotientGroup.eq_one_iff _).mp hcong
      have := hmem.1
      rwa [← map_d0Word] at this
  -- every `d̄`-value lies in every derivation kernel
  have hdbarker : ∀ (v : Fin 3 → ℤ_[2]) (w : Fin 3 → levelQuot (DR : Type) (k + 1)),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) →
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w ∈ derivKer (Φ v) k := by
    intro v w hw
    choose ŵ hŵmem hŵeq using fun i => hw i
    refine ⟨dbarWordR0 (a 0) (a 1) (a 2) ŵ, ?_, ?_, ?_⟩
    · have hsq : ŵ 0 ^ 2 ∈ twoCentralSeries (DR : Type) k := by
        have h := sq_mem_twoCentralSeries_succ (DR : Type) (hŵmem 0)
        rwa [show k - 1 + 1 = k by omega] at h
      have hcm : ∀ (i : Fin 3) (g : (DR : Type)),
          commP (ŵ i) g ∈ twoCentralSeries (DR : Type) k := by
        intro i g
        have h := commP_mem_twoCentralSucc (hŵmem i) g
        rwa [← twoCentralSeries_succ (DR : Type) (by omega : 1 ≤ k - 1),
          show k - 1 + 1 = k by omega] at h
      exact mul_mem (mul_mem (mul_mem hsq (hcm 0 (a 0))) (hcm 1 (a 2))) (hcm 2 (a 1))
    · rw [map_dbarWordR0, ha 0, ha 1, ha 2]
      exact congrArg _ (funext hŵeq)
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have hmkeq2 : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hval : dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          = ⟨(1 + ((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 0))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)) * (Φ v (ŵ 0)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 2))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 1)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR0 1))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 2)).u, 1⟩ :=
        dbarWordR0_ref (R := ZMod (2 ^ (k + 1)))
          (PadicInt.toZModPow (k + 1) x0) (PadicInt.toZModPow (k + 1) x1)
          (PadicInt.toZModPow (k + 1) x2) (Φ v (ŵ 0)).u (Φ v (ŵ 1)).u (Φ v (ŵ 2)).u
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 0))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 1))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR0 2))
      have href : dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          ∈ wlKer (k + 1) k := by
        rw [hval]
        have hd : ∀ i : Fin 3, (2 : ZMod (2 ^ (k + 1))) ^ (k - 2) ∣ (Φ v (ŵ i)).u := by
          intro i
          have h := (deriv_mem_wlCong hN (Φ v) (by omega : 1 ≤ k - 1) (hŵmem i)).1
          rwa [show k - 1 - 1 = k - 2 by omega] at h
        have hcoef0 : (2 : ℤ_[2]) ^ 2 ∣ 1 + (((chiTargetUnitsR0 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
          rw [show chiTargetUnitsR0 0 = -1 from by simp [chiTargetUnitsR0]]
          exact ⟨0, by simp⟩
        have hcoef1 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          rw [show chiTargetUnitsR0 1 = 1 from by simp [chiTargetUnitsR0]]
          exact ⟨0, by simp⟩
        have hcoef2 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          rw [show chiTargetUnitsR0 2 = etaUnit from by simp [chiTargetUnitsR0], etaUnit,
            inv_inv, negThreeUnit_val]
          exact ⟨-1, by ring⟩
        refine ⟨?_, ?_⟩
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ _
          rw [red_coeff_one_add, red_coeff_sub_one, red_coeff_sub_one]
          exact dvd_add (dvd_add (dvd_coeff_mul (by omega) hkN hcoef0 (hd 0))
            (dvd_coeff_mul (by omega) hkN hcoef2 (hd 1)))
            (dvd_coeff_mul (by omega) hkN hcoef1 (hd 2))
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ ((1 : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) - 1
          simp
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR0 (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) (fun i => Φ v (ŵ i)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR0 (redWL (k + 1) ⟨x0, chiTargetUnitsR0 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR0 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR0 2⟩)
              ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]) := by
        rw [map_dbarWordR0, map_dbarWordR0]
        have hfun : (fun i => (QuotientGroup.mk' (wlKer (k + 1) k)) (Φ v (ŵ i)))
            = fun i => (QuotientGroup.mk' (wlKer (k + 1) k))
              ((![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩,
                ⟨(Φ v (ŵ 2)).u, 1⟩]) i) := by
          funext i
          fin_cases i
          · exact hmkeq2 (hwslot v (ŵ 0) (hŵmem 0))
          · exact hmkeq2 (hwslot v (ŵ 1) (hŵmem 1))
          · exact hmkeq2 (hwslot v (ŵ 2) (hŵmem 2))
        rw [hfun, hmkeq2 (hslot v 0 x0 hx0), hmkeq2 (hslot v 1 x1 hx1),
          hmkeq2 (hslot v 2 x2 hx2)]
      have hB := (QuotientGroup.eq_one_iff _).mpr href
      have hmem := (QuotientGroup.eq_one_iff _).mp (hcong.trans hB)
      have hu := hmem.1
      rwa [← map_dbarWordR0] at hu
  -- the two tails, and the decomposition subgroup supplied by the span theorem
  have htz : ∀ i : Fin 3, canonLift (DR : Type) k (T i) ^ 2 ^ (k - 1) ∈ zLayer (DR : Type) k := by
    intro i
    have h := pow_two_pow_mem_lambdaImage (canonLift (DR : Type) k (T i)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h
  set P : Subgroup (levelQuot (DR : Type) (k + 1)) :=
    { carrier := {z | ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
        (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧ ∃ α β : ℕ,
          z = dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
                (canonLift (DR : Type) k (T 2)) w
              * (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
              * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β}
      one_mem' := ⟨fun _ => 1, fun _ => one_mem _, 0, 0, by
        rw [dbarWordR0_one, pow_zero, pow_zero, mul_one, mul_one]⟩
      mul_mem' := by
        rintro z z' ⟨w, hw, α, β, rfl⟩ ⟨w', hw', α', β', rfl⟩
        refine ⟨fun i => w i * w' i, fun i => mul_mem (hw i) (hw' i), α + α', β + β', ?_⟩
        have hcen : ∀ {z : levelQuot (DR : Type) (k + 1)}, z ∈ zLayer (DR : Type) k →
            ∀ t, z * t = t * z := fun hz t => (zLayer_commute hz t).eq
        rw [dbarWordR0_mul k hk _ _ _ hw hw', pow_add, pow_add]
        exact (central_shuffle3 (hcen (dbarWordR0_mem_zLayer (G := (DR : Type)) k hk _ _ _ hw'))
          (hcen (pow_mem (htz 1) α'))).symm
      inv_mem' := by
        rintro z ⟨w, hw, α, β, rfl⟩
        refine ⟨w, hw, α, β, ?_⟩
        refine zLayer_inv_self (G := (DR : Type)) ?_
        exact mul_mem (mul_mem (dbarWordR0_mem_zLayer (G := (DR : Type)) k hk _ _ _ hw)
          (pow_mem (htz 1) α)) (pow_mem (htz 2) β) } with hP
  have hδP : defectR0 k T ∈ P := by
    have hδz : defectR0 k T ∈ zLayer (DR : Type) k := defectR0_mem_zLayer k hrel
    have hsp := span_descent_r0 k hk (fun i => canonLift (DR : Type) k (T i)) hgent hδz
    refine (Subgroup.closure_le P).mpr ?_ hsp
    rintro z (⟨w, hw, rfl⟩ | hz)
    · exact ⟨w, hw, 0, 0, by rw [pow_zero, pow_zero, mul_one, mul_one]⟩
    · rcases hz with rfl | rfl
      · exact ⟨fun _ => 1, fun _ => one_mem _, 1, 0, by
          rw [dbarWordR0_one, pow_zero, pow_one, mul_one, one_mul]⟩
      · exact ⟨fun _ => 1, fun _ => one_mem _, 0, 1, by
          rw [dbarWordR0_one, pow_zero, pow_one, mul_one, one_mul]⟩
  obtain ⟨w, hw, α, β, hdec⟩ := hδP
  -- the tail combination lies in every derivation kernel
  have htail : ∀ v, levelMk (DR : Type) (k + 1)
      ((a 1 ^ 2 ^ (k - 1)) ^ α * (a 2 ^ 2 ^ (k - 1)) ^ β) ∈ derivKer (Φ v) k := by
    intro v
    have hz : levelMk (DR : Type) (k + 1) ((a 1 ^ 2 ^ (k - 1)) ^ α * (a 2 ^ 2 ^ (k - 1)) ^ β)
        = (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β := by
      rw [map_mul, map_pow, map_pow, map_pow, map_pow, ha 1, ha 2]
    have hsplit : (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β
        = (dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
            (canonLift (DR : Type) k (T 2)) w)⁻¹ * defectR0 k T := by
      rw [hdec]
      group
    rw [hz, hsplit]
    exact mul_mem (inv_mem (hdbarker v w hw)) (hδker v)
  -- the base values of the two tail slots are `≡ 1 (mod 4)`
  have hchi1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiR (a 1) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 1)
    rwa [show chiTargetUnitsR0 1 = 1 by simp [chiTargetUnitsR0], inv_one, mul_one] at h
  have heta4 : (2 : ℤ_[2]) ^ 2 ∣ ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h3 : ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * (-3) = 1 := by
      have h : ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) * ((negThreeUnit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
        rw [etaUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      rwa [negThreeUnit_val] at h
    exact ⟨((etaUnit : ℤ_[2]ˣ) : ℤ_[2]), by linear_combination h3⟩
  have hchi2 : (2 : ℤ_[2]) ^ 2 ∣ ((chiR (a 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hA := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 2)
    have hB : (2 : ℤ_[2]) ^ 2 ∣ ((chiTargetUnitsR0 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      rwa [show chiTargetUnitsR0 2 = etaUnit by simp [chiTargetUnitsR0]]
    have h := dvd_mul_sub_one hA hB
    rwa [← Units.val_mul, show chiR (a 2) * (chiTargetUnitsR0 2)⁻¹ * chiTargetUnitsR0 2
      = chiR (a 2) by group] at h
  have hpar := tail_parity (G := (DR : Type)) hk hN hkN Φ hchi1 hchi2
    (fun v => by rw [hbase v (a 1)]; rfl) (fun v => by rw [hbase v (a 2)]; rfl) α β htail
  have hc0 : (![0, (α : ZMod (2 ^ 1)), (β : ZMod (2 ^ 1))] : Fin 3 → ZMod (2 ^ 1)) = 0 := by
    refine thetaVec_indep hN (by omega) Φ ![drS, drX, drY] a hgenval hgent' ?_
    simpa using hpar
  have hα : (2 : ℕ) ∣ α := by
    have h1 := congrFun hc0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
    have := (ZMod.natCast_eq_zero_iff α (2 ^ 1)).mp h1
    rwa [pow_one] at this
  have hβ : (2 : ℕ) ∣ β := by
    have h2 := congrFun hc0 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at h2
    have := (ZMod.natCast_eq_zero_iff β (2 ^ 1)).mp h2
    rwa [pow_one] at this
  have htriv1 : (canonLift (DR : Type) k (T 1) ^ 2 ^ (k - 1)) ^ α = 1 := by
    obtain ⟨m, rfl⟩ := hα
    rw [pow_mul, zLayer_sq (DR : Type) (htz 1), one_pow]
  have htriv2 : (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 1)) ^ β = 1 := by
    obtain ⟨m, rfl⟩ := hβ
    rw [pow_mul, zLayer_sq (DR : Type) (htz 2), one_pow]
  rw [htriv1, htriv2, mul_one, mul_one] at hdec
  exact ⟨w, hw, by rw [← hdec, zLayer_inv_self (defectR0_mem_zLayer k hrel)]⟩

/-- SL1 (reachability), direction 2.  Fill: L4b. -/
theorem stageSL1R2 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) :
    ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w = (defectR2 k T)⁻¹ := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hN : 1 ≤ k + 1 := by omega
  have hkN : k ≤ k + 1 := by omega
  choose a ha using fun i : Fin 3 =>
    levelMk_surjective (D0 : Type) (k + 1) (canonLift (D0 : Type) k (T i))
  have hproj : ∀ i, levelMk (D0 : Type) k (a i) = T i := fun i => by
    rw [← levelProj_levelMk, ha i, levelProj_canonLift]
  have himg : (levelProj (D0 : Type) k) ''
      (Set.range fun i => canonLift (D0 : Type) k (T i)) = Set.range T := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => levelProj_canonLift (D0 : Type) k (T i))
  have hgent : Subgroup.closure (Set.range fun i => canonLift (D0 : Type) k (T i)) = ⊤ := by
    refine eq_top_of_map_levelProj_eq_top (D0 : Type) d0TopGenFinset SectionThree.d0_isProP (by omega) ?_
    rw [MonoidHom.map_closure, himg, hgen]
  have hgent' : Subgroup.closure (Set.range fun i => levelMk (D0 : Type) (k + 1) (a i)) = ⊤ := by
    rw [show (fun i => levelMk (D0 : Type) (k + 1) (a i))
      = fun i => canonLift (D0 : Type) k (T i) from funext ha]
    exact hgent
  set Φ : (Fin 3 → ℤ_[2]) → ContinuousMonoidHom (D0 : Type) (WL (k + 1)) :=
    fun v => deriv0 (k + 1) hN v with hΦ
  have hbase : ∀ (v : Fin 3 → ℤ_[2]) (x : (D0 : Type)),
      (Φ v x).g = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiD0pres x) :=
    fun v x => deriv0_base (k + 1) hN v x
  have hgenval : ∀ (v : Fin 3 → ℤ_[2]) (j : Fin 3),
      (Φ v (![d0A, d0S, d0Y] j)).u = PadicInt.toZModPow (k + 1) (v j) := by
    intro v j
    fin_cases j
    · show (deriv0 (k + 1) hN v d0A).u = _
      rw [deriv0_d0A]; rfl
    · show (deriv0 (k + 1) hN v d0S).u = _
      rw [deriv0_d0S]; rfl
    · show (deriv0 (k + 1) hN v d0Y).u = _
      rw [deriv0_d0Y]; rfl
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiD0pres (a i) * (chiTargetUnitsR2 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiD0pres (chiTargetUnitsR2 i) (hproj i) ?_
    simpa [chiTargetR2] using hchi i
  -- the mod-8 pins of the direction-2 targets `(S, X, Y) ≡ (5, 5, 7)`
  have hS1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiTargetUnitsR2 0 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h8 : PadicInt.toZModPow 3 ((chiTargetUnitsR2 0 : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
      simpa [chiTargetR2] using chiTargetR2_three 0
    rw [two_pow_dvd_iff, map_sub, map_one]
    have hcast := PadicInt.cast_toZModPow 2 3 (by omega)
      ((chiTargetUnitsR2 0 : ℤ_[2]ˣ) : ℤ_[2])
    rw [h8] at hcast
    rw [← hcast]
    decide
  have hX1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiTargetUnitsR2 1 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have h8 : PadicInt.toZModPow 3 ((chiTargetUnitsR2 1 : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
      simpa [chiTargetR2] using chiTargetR2_three 1
    rw [two_pow_dvd_iff, map_sub, map_one]
    have hcast := PadicInt.cast_toZModPow 2 3 (by omega)
      ((chiTargetUnitsR2 1 : ℤ_[2]ˣ) : ℤ_[2])
    rw [h8] at hcast
    rw [← hcast]
    decide
  have hY1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiTargetUnitsR2 2 : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
    have h8 : PadicInt.toZModPow 3 ((chiTargetUnitsR2 2 : ℤ_[2]ˣ) : ℤ_[2]) = 7 := by
      simpa [chiTargetR2] using chiTargetR2_three 2
    rw [two_pow_dvd_iff, map_add, map_one]
    have hcast := PadicInt.cast_toZModPow 2 3 (by omega)
      ((chiTargetUnitsR2 2 : ℤ_[2]ˣ) : ℤ_[2])
    rw [h8] at hcast
    rw [← hcast]
    decide
  -- congruence of a slot with its pinned target
  have hslot : ∀ (v : Fin 3 → ℤ_[2]) (i : Fin 3) (x : ℤ_[2]),
      PadicInt.toZModPow (k + 1) x = (Φ v (a i)).u →
      (Φ v (a i))⁻¹ * redWL (k + 1) ⟨x, chiTargetUnitsR2 i⟩ ∈ wlKer (k + 1) k := by
    intro v i x hx
    refine inv_mul_mem_wlKer hx.symm ?_
    have h2 : (2 : ℤ_[2]) ^ k ∣
        (((chiD0pres (a i))⁻¹ * chiTargetUnitsR2 i : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (hdev i)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v (a i)).g⁻¹ * (redWL (k + 1) ⟨x, chiTargetUnitsR2 i⟩).g
          : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
          ((chiD0pres (a i))⁻¹ * chiTargetUnitsR2 i) := by
      rw [map_mul, map_inv, hbase v (a i), redWL_g]
    rw [hg]
    exact hred
  -- congruence of a `λ_{k-1}`-modification slot with base `1`
  have hwslot : ∀ (v : Fin 3 → ℤ_[2]) (x : (D0 : Type)),
      x ∈ twoCentralSeries (D0 : Type) (k - 1) →
      (Φ v x)⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)) ∈ wlKer (k + 1) k := by
    intro v x hx
    refine inv_mul_mem_wlKer rfl ?_
    have h1 : (2 : ℤ_[2]) ^ k ∣ ((chiD0pres x : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      have h := dvd_chi_of_mem_twoCentralSeries chiD0pres (k := k - 1) (by omega) hx
      rwa [show k - 1 + 1 = k by omega] at h
    have h2 : (2 : ℤ_[2]) ^ k ∣ (((chiD0pres x)⁻¹ * 1 : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      dvd_inv_mul_of_dvd_mul_inv (by simpa using h1)
    have hred := (two_pow_dvd_toZModPow_iff (N := k + 1) (j := k) hkN).mpr h2
    rw [map_sub, map_one] at hred
    have hg : ((Φ v x).g⁻¹ * (⟨(Φ v x).u, 1⟩ : WL (k + 1)).g : (ZMod (2 ^ (k + 1)))ˣ)
        = Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom ((chiD0pres x)⁻¹ * 1) := by
      rw [map_mul, map_inv, map_one, mul_one, mul_one, hbase v x]
    rw [hg]
    exact hred
  -- the defect lies in every derivation kernel (the `r₀`-datum at the pinned targets)
  have hδker : ∀ v, defectR2 k T ∈ derivKer (Φ v) k := by
    intro v
    refine ⟨drWord (a 0) (a 1) (a 2), ?_, ?_, ?_⟩
    · have hmk : levelMk (D0 : Type) k (drWord (a 0) (a 1) (a 2)) = 1 := by
        rw [map_drWord, hproj, hproj, hproj]
        exact hrel
      exact (QuotientGroup.eq_one_iff _).mp hmk
    · rw [map_drWord, ha 0, ha 1, ha 2]
      rfl
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have href : drWord (redWL (k + 1) ⟨x0, chiTargetUnitsR2 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR2 1⟩)
          (redWL (k + 1) ⟨x2, chiTargetUnitsR2 2⟩) = 1 := by
        rw [show chiTargetUnitsR2 0 = chiR drS from by simp [chiTargetUnitsR2],
          show chiTargetUnitsR2 1 = chiR drX from by simp [chiTargetUnitsR2],
          show chiTargetUnitsR2 2 = chiR drY from by simp [chiTargetUnitsR2],
          ← map_drWord, show drWord (⟨x0, chiR drS⟩ : FoxH.WordLift ℤ_[2] ℤ_[2]ˣ)
            ⟨x1, chiR drX⟩ ⟨x2, chiR drY⟩ = 1 from isLabuteOrientation_chiR x0 x1 x2, map_one]
      have hmkeq : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (drWord (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (drWord (redWL (k + 1) ⟨x0, chiTargetUnitsR2 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR2 1⟩)
              (redWL (k + 1) ⟨x2, chiTargetUnitsR2 2⟩)) := by
        rw [map_drWord, map_drWord, hmkeq (hslot v 0 x0 hx0), hmkeq (hslot v 1 x1 hx1),
          hmkeq (hslot v 2 x2 hx2)]
      rw [href, map_one] at hcong
      have hmem : drWord (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) ∈ wlKer (k + 1) k :=
        (QuotientGroup.eq_one_iff _).mp hcong
      have := hmem.1
      rwa [← map_drWord] at this
  -- every `d̄`-value lies in every derivation kernel
  have hdbarker : ∀ (v : Fin 3 → ℤ_[2]) (w : Fin 3 → levelQuot (D0 : Type) (k + 1)),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) →
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w ∈ derivKer (Φ v) k := by
    intro v w hw
    choose ŵ hŵmem hŵeq using fun i => hw i
    refine ⟨dbarWordR2 (a 0) (a 1) (a 2) ŵ, ?_, ?_, ?_⟩
    · have hsq : ŵ 2 ^ 2 ∈ twoCentralSeries (D0 : Type) k := by
        have h := sq_mem_twoCentralSeries_succ (D0 : Type) (hŵmem 2)
        rwa [show k - 1 + 1 = k by omega] at h
      have hcm : ∀ (i : Fin 3) (g : (D0 : Type)),
          commP (ŵ i) g ∈ twoCentralSeries (D0 : Type) k := by
        intro i g
        have h := commP_mem_twoCentralSucc (hŵmem i) g
        rwa [← twoCentralSeries_succ (D0 : Type) (by omega : 1 ≤ k - 1),
          show k - 1 + 1 = k by omega] at h
      exact mul_mem (mul_mem (mul_mem hsq (hcm 2 (a 2))) (hcm 0 (a 1))) (hcm 1 (a 0))
    · rw [map_dbarWordR2, ha 0, ha 1, ha 2]
      exact congrArg _ (funext hŵeq)
    · obtain ⟨x0, hx0⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 0)).u)
      obtain ⟨x1, hx1⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 1)).u)
      obtain ⟨x2, hx2⟩ := toZModPow_surj (N := k + 1) ((Φ v (a 2)).u)
      have hmkeq2 : ∀ {p q : WL (k + 1)}, p⁻¹ * q ∈ wlKer (k + 1) k →
          (QuotientGroup.mk' (wlKer (k + 1) k)) p = (QuotientGroup.mk' (wlKer (k + 1) k)) q := by
        intro p q h
        simp only [QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr h
      have hval : dbarWordR2 (redWL (k + 1) ⟨x0, chiTargetUnitsR2 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR2 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR2 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          = ⟨(1 + ((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR2 2))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)) * (Φ v (ŵ 2)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR2 1))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 0)).u
              + (((Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
                (chiTargetUnitsR2 0))⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) - 1) * (Φ v (ŵ 1)).u, 1⟩ :=
        dbarWordR2_ref (R := ZMod (2 ^ (k + 1)))
          (PadicInt.toZModPow (k + 1) x0) (PadicInt.toZModPow (k + 1) x1)
          (PadicInt.toZModPow (k + 1) x2) (Φ v (ŵ 0)).u (Φ v (ŵ 1)).u (Φ v (ŵ 2)).u
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR2 0))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR2 1))
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiTargetUnitsR2 2))
      have href : dbarWordR2 (redWL (k + 1) ⟨x0, chiTargetUnitsR2 0⟩)
          (redWL (k + 1) ⟨x1, chiTargetUnitsR2 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR2 2⟩)
          ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]
          ∈ wlKer (k + 1) k := by
        rw [hval]
        have hd : ∀ i : Fin 3, (2 : ZMod (2 ^ (k + 1))) ^ (k - 2) ∣ (Φ v (ŵ i)).u := by
          intro i
          have h := (deriv_mem_wlCong hN (Φ v) (by omega : 1 ≤ k - 1) (hŵmem i)).1
          rwa [show k - 1 - 1 = k - 2 by omega] at h
        have hcoef2 : (2 : ℤ_[2]) ^ 2 ∣ 1 + (((chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
          obtain ⟨c, hc⟩ := hY1
          refine ⟨c * (((chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), ?_⟩
          have hu : ((chiTargetUnitsR2 2 : ℤ_[2]ˣ) : ℤ_[2])
              * (((chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          linear_combination (((chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hc - hu
        have hcoef1 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          have h := dvd_inv_mul_of_dvd_mul_inv (A := chiTargetUnitsR2 1) (B := 1) (n := 2)
            (by simpa using hX1)
          simpa using h
        have hcoef0 : (2 : ℤ_[2]) ^ 2 ∣ (((chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
          have h := dvd_inv_mul_of_dvd_mul_inv (A := chiTargetUnitsR2 0) (B := 1) (n := 2)
            (by simpa using hS1)
          simpa using h
        refine ⟨?_, ?_⟩
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ _
          rw [red_coeff_one_add, red_coeff_sub_one, red_coeff_sub_one]
          exact dvd_add (dvd_add (dvd_coeff_mul (by omega) hkN hcoef2 (hd 2))
            (dvd_coeff_mul (by omega) hkN hcoef1 (hd 0)))
            (dvd_coeff_mul (by omega) hkN hcoef0 (hd 1))
        · show (2 : ZMod (2 ^ (k + 1))) ^ k ∣ ((1 : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) - 1
          simp
      have hcong : (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR2 (Φ v (a 0)) (Φ v (a 1)) (Φ v (a 2)) (fun i => Φ v (ŵ i)))
          = (QuotientGroup.mk' (wlKer (k + 1) k))
            (dbarWordR2 (redWL (k + 1) ⟨x0, chiTargetUnitsR2 0⟩)
              (redWL (k + 1) ⟨x1, chiTargetUnitsR2 1⟩) (redWL (k + 1) ⟨x2, chiTargetUnitsR2 2⟩)
              ![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩, ⟨(Φ v (ŵ 2)).u, 1⟩]) := by
        rw [map_dbarWordR2, map_dbarWordR2]
        have hfun : (fun i => (QuotientGroup.mk' (wlKer (k + 1) k)) (Φ v (ŵ i)))
            = fun i => (QuotientGroup.mk' (wlKer (k + 1) k))
              ((![(⟨(Φ v (ŵ 0)).u, 1⟩ : WL (k + 1)), ⟨(Φ v (ŵ 1)).u, 1⟩,
                ⟨(Φ v (ŵ 2)).u, 1⟩]) i) := by
          funext i
          fin_cases i
          · exact hmkeq2 (hwslot v (ŵ 0) (hŵmem 0))
          · exact hmkeq2 (hwslot v (ŵ 1) (hŵmem 1))
          · exact hmkeq2 (hwslot v (ŵ 2) (hŵmem 2))
        rw [hfun, hmkeq2 (hslot v 0 x0 hx0), hmkeq2 (hslot v 1 x1 hx1),
          hmkeq2 (hslot v 2 x2 hx2)]
      have hB := (QuotientGroup.eq_one_iff _).mpr href
      have hmem := (QuotientGroup.eq_one_iff _).mp (hcong.trans hB)
      have hu := hmem.1
      rwa [← map_dbarWordR2] at hu
  -- the two tails, and the decomposition subgroup supplied by the span theorem
  have htz : ∀ i : Fin 3, canonLift (D0 : Type) k (T i) ^ 2 ^ (k - 1) ∈ zLayer (D0 : Type) k := by
    intro i
    have h := pow_two_pow_mem_lambdaImage (canonLift (D0 : Type) k (T i)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h
  set P : Subgroup (levelQuot (D0 : Type) (k + 1)) :=
    { carrier := {z | ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
        (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧ ∃ α β : ℕ,
          z = dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
                (canonLift (D0 : Type) k (T 2)) w
              * (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 1)) ^ α
              * (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 1)) ^ β}
      one_mem' := ⟨fun _ => 1, fun _ => one_mem _, 0, 0, by
        rw [dbarWordR2_one, pow_zero, pow_zero, mul_one, mul_one]⟩
      mul_mem' := by
        rintro z z' ⟨w, hw, α, β, rfl⟩ ⟨w', hw', α', β', rfl⟩
        refine ⟨fun i => w i * w' i, fun i => mul_mem (hw i) (hw' i), α + α', β + β', ?_⟩
        have hcen : ∀ {z : levelQuot (D0 : Type) (k + 1)}, z ∈ zLayer (D0 : Type) k →
            ∀ t, z * t = t * z := fun hz t => (zLayer_commute hz t).eq
        rw [dbarWordR2_mul k hk _ _ _ hw hw', pow_add, pow_add]
        exact (central_shuffle3 (hcen (dbarWordR2_mem_zLayer (G := (D0 : Type)) k hk _ _ _ hw'))
          (hcen (pow_mem (htz 0) α'))).symm
      inv_mem' := by
        rintro z ⟨w, hw, α, β, rfl⟩
        refine ⟨w, hw, α, β, ?_⟩
        refine zLayer_inv_self (G := (D0 : Type)) ?_
        exact mul_mem (mul_mem (dbarWordR2_mem_zLayer (G := (D0 : Type)) k hk _ _ _ hw)
          (pow_mem (htz 0) α)) (pow_mem (htz 1) β) } with hP
  have hδP : defectR2 k T ∈ P := by
    have hδz : defectR2 k T ∈ zLayer (D0 : Type) k := defectR2_mem_zLayer k hrel
    have hsp := span_descent_r2 k hk (fun i => canonLift (D0 : Type) k (T i)) hgent hδz
    refine (Subgroup.closure_le P).mpr ?_ hsp
    rintro z (⟨w, hw, rfl⟩ | hz)
    · exact ⟨w, hw, 0, 0, by rw [pow_zero, pow_zero, mul_one, mul_one]⟩
    · rcases hz with rfl | rfl
      · exact ⟨fun _ => 1, fun _ => one_mem _, 1, 0, by
          rw [dbarWordR2_one, pow_zero, pow_one, mul_one, one_mul]⟩
      · exact ⟨fun _ => 1, fun _ => one_mem _, 0, 1, by
          rw [dbarWordR2_one, pow_zero, pow_one, mul_one, one_mul]⟩
  obtain ⟨w, hw, α, β, hdec⟩ := hδP
  -- the tail combination lies in every derivation kernel
  have htail : ∀ v, levelMk (D0 : Type) (k + 1)
      ((a 0 ^ 2 ^ (k - 1)) ^ α * (a 1 ^ 2 ^ (k - 1)) ^ β) ∈ derivKer (Φ v) k := by
    intro v
    have hz : levelMk (D0 : Type) (k + 1) ((a 0 ^ 2 ^ (k - 1)) ^ α * (a 1 ^ 2 ^ (k - 1)) ^ β)
        = (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 1)) ^ β := by
      rw [map_mul, map_pow, map_pow, map_pow, map_pow, ha 0, ha 1]
    have hsplit : (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 1)) ^ α
          * (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 1)) ^ β
        = (dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
            (canonLift (D0 : Type) k (T 2)) w)⁻¹ * defectR2 k T := by
      rw [hdec]
      group
    rw [hz, hsplit]
    exact mul_mem (inv_mem (hdbarker v w hw)) (hδker v)
  -- the base values of the two tail slots are `≡ 1 (mod 4)`
  have hchi0 : (2 : ℤ_[2]) ^ 2 ∣ ((chiD0pres (a 0) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hA := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 0)
    have h := dvd_mul_sub_one hA hS1
    rwa [← Units.val_mul, show chiD0pres (a 0) * (chiTargetUnitsR2 0)⁻¹ * chiTargetUnitsR2 0
      = chiD0pres (a 0) by group] at h
  have hchi1 : (2 : ℤ_[2]) ^ 2 ∣ ((chiD0pres (a 1) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hA := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ k)) (hdev 1)
    have h := dvd_mul_sub_one hA hX1
    rwa [← Units.val_mul, show chiD0pres (a 1) * (chiTargetUnitsR2 1)⁻¹ * chiTargetUnitsR2 1
      = chiD0pres (a 1) by group] at h
  have hpar := tail_parity (G := (D0 : Type)) hk hN hkN Φ hchi0 hchi1
    (fun v => by rw [hbase v (a 0)]; rfl) (fun v => by rw [hbase v (a 1)]; rfl) α β htail
  have hc0 : (![(α : ZMod (2 ^ 1)), (β : ZMod (2 ^ 1)), 0] : Fin 3 → ZMod (2 ^ 1)) = 0 := by
    refine thetaVec_indep hN (by omega) Φ ![d0A, d0S, d0Y] a hgenval hgent' ?_
    simpa using hpar
  have hα : (2 : ℕ) ∣ α := by
    have h1 := congrFun hc0 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h1
    have := (ZMod.natCast_eq_zero_iff α (2 ^ 1)).mp h1
    rwa [pow_one] at this
  have hβ : (2 : ℕ) ∣ β := by
    have h2 := congrFun hc0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h2
    have := (ZMod.natCast_eq_zero_iff β (2 ^ 1)).mp h2
    rwa [pow_one] at this
  have htriv1 : (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 1)) ^ α = 1 := by
    obtain ⟨m, rfl⟩ := hα
    rw [pow_mul, zLayer_sq (D0 : Type) (htz 0), one_pow]
  have htriv2 : (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 1)) ^ β = 1 := by
    obtain ⟨m, rfl⟩ := hβ
    rw [pow_mul, zLayer_sq (D0 : Type) (htz 1), one_pow]
  rw [htriv1, htriv2, mul_one, mul_one] at hdec
  exact ⟨w, hw, by rw [← hdec, zLayer_inv_self (defectR2_mem_zLayer k hrel)]⟩

end GQ2.Roe.Labute
