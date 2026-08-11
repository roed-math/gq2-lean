/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.StageOne

/-!
# SL2 and the stage step

Piece 6/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  The two digit-adjustment statements `stageSL2R0` /
`stageSL2R2`, and the composability certificates `stageStepR0` / `stageStepR2` that
`Assembly.lean` consumes.
-/

namespace GQ2.Roe.Labute

/-- **SL2 (digit adjustment), direction 1**: for `T ∈ S^P_ₖ` (`k ≥ 3`) with vanishing
defect, some `ker d̄`-modification of the canonical lift lands in `S^P_{k+1}` — the memo's
"`ker d̄ₖ → (ℤ/2)²` onto" in its consumed form (the digit bookkeeping, including the
automatic vanishing of the π'd slot's fresh digit, is L4a's internal mechanism; the
dimension-count fallback of spike §2.5(c) is equally admissible).  Fill: L4a. -/
theorem stageSL2R0 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) (hδ : defectR0 k T = 1) :
    ∃ w : Fin 3 → levelQuot (DR : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) ∧
      dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
        (canonLift (DR : Type) k (T 2)) w = 1 ∧
      (fun i => canonLift (DR : Type) k (T i) * w i) ∈ sPR0 (k + 1) := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  choose g hg using fun i : Fin 3 =>
    levelMk_surjective (DR : Type) (k + 1) (canonLift (DR : Type) k (T i))
  -- the pinned targets and the mod-`8` anchor `η ≡ 5` (the `f = 2` discriminator)
  have ht0 : chiTargetUnitsR0 0 = -1 := by simp [chiTargetUnitsR0]
  have ht1 : chiTargetUnitsR0 1 = 1 := by simp [chiTargetUnitsR0]
  have ht2 : chiTargetUnitsR0 2 = etaUnit := by simp [chiTargetUnitsR0]
  have hη : PadicInt.toZModPow 3 ((etaUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR0, chiTargetUnitsR0] using chiTargetR0_three 2
  -- the level-`k` deviations of the three slots (this is the invariant `P` at level `k`)
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiR (g i) * (chiTargetUnitsR0 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiR (chiTargetUnitsR0 i)
      (by rw [← levelProj_levelMk, hg i, levelProj_canonLift]) ?_
    simpa [chiTargetR0] using hchi i
  -- the two moves at the group level, and their sharp level-`k` digits
  obtain ⟨Ug, hUg⟩ : ∃ Ug : (DR : Type), Ug = g 2 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ Vg : (DR : Type), Vg = (g 1 * g 2) ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨du, hdu, hdu2⟩ : ∃ d : ℤ_[2], ((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hUg, map_pow]
    exact sharp_move hk hη (by rw [← ht2]; exact hdev 2)
  obtain ⟨dv, hdv, hdv2⟩ : ∃ d : ℤ_[2], ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hVg, map_pow, map_mul]
    refine sharp_move hk hη ?_
    have h := dvd_mul_sub_one (hdev 1) (hdev 2)
    rw [← Units.val_mul] at h
    rwa [show (chiR (g 1) * (chiTargetUnitsR0 1)⁻¹) * (chiR (g 2) * (chiTargetUnitsR0 2)⁻¹)
      = chiR (g 1) * chiR (g 2) * etaUnit⁻¹ by rw [ht1, ht2]; group] at h
  -- the digit choices: the `y`-slot first, then the `s`-slot against the residue
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 2) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 2) hdv hdv2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        (((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a * ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b) - 1 := by
    have h1 : (2 : ℤ_[2]) ^ k ∣
        ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 :=
      dvd_mul_sub_one (hdev 1) (dvd_pow_sub_one ⟨dv, hdv⟩ b)
    rcases dvd_or_dvd_mul (by omega) h1 hdu hdu2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa [pow_one, mul_comm, mul_assoc, mul_left_comm] using h⟩
  -- the modification in `Q_{k+1}`: `p` a power of the `y`-slot, `q` a power of `s·y`
  obtain ⟨p, hpdef⟩ : ∃ p : levelQuot (DR : Type) (k + 1),
      p = (canonLift (DR : Type) k (T 2) ^ 2 ^ (k - 2)) ^ a := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : levelQuot (DR : Type) (k + 1),
      q = ((canonLift (DR : Type) k (T 1) * canonLift (DR : Type) k (T 2)) ^ 2 ^ (k - 2)) ^ b :=
    ⟨_, rfl⟩
  have hpm : p ∈ lambdaImage (DR : Type) (k - 1) (k + 1) := by
    rw [hpdef]
    refine Subgroup.pow_mem _ ?_ a
    have h := pow_two_pow_mem_lambdaImage (canonLift (DR : Type) k (T 2)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hqm : q ∈ lambdaImage (DR : Type) (k - 1) (k + 1) := by
    rw [hqdef]
    refine Subgroup.pow_mem _ ?_ b
    have h := pow_two_pow_mem_lambdaImage
      (canonLift (DR : Type) k (T 1) * canonLift (DR : Type) k (T 2)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hw : ∀ i, (![1, p * q, q] : Fin 3 → levelQuot (DR : Type) (k + 1)) i ∈
      lambdaImage (DR : Type) (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact one_mem _
    · exact mul_mem hpm hqm
    · exact hqm
  have hdbar : dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
      (canonLift (DR : Type) k (T 2)) ![1, p * q, q] = 1 := by
    refine dbarWordR0_kernel_witness k hk _ _ _ p q hqm ?_ ?_
    · rw [hpdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left a).eq
    · rw [hqdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left b).eq
  -- the corrected triple, presented at the group level
  have hlift0 : levelMk (DR : Type) (k + 1) (g 0)
      = canonLift (DR : Type) k (T 0) * ![1, p * q, q] 0 := by
    rw [hg 0]; simp
  have hlift1 : levelMk (DR : Type) (k + 1) (g 1 * (Ug ^ a * Vg ^ b))
      = canonLift (DR : Type) k (T 1) * ![1, p * q, q] 1 := by
    rw [hUg, hVg, hpdef, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hlift2 : levelMk (DR : Type) (k + 1) (g 2 * Vg ^ b)
      = canonLift (DR : Type) k (T 2) * ![1, p * q, q] 2 := by
    rw [hVg, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  -- the relator clause at level `k+1` (the defect is gone and the move is in `ker d̄`)
  have hrelQ : d0Word (canonLift (DR : Type) k (T 0) * ![1, p * q, q] 0)
      (canonLift (DR : Type) k (T 1) * ![1, p * q, q] 1)
      (canonLift (DR : Type) k (T 2) * ![1, p * q, q] 2) = 1 := by
    rw [d0Word_mul_lambdaImage k hk _ _ _ hw, hdbar, mul_one]
    exact hδ
  -- the `s`-slot clause, and then the π'd slot's automatic digit (memo §1.1)
  have hchi1 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 1 * (Ug ^ a * Vg ^ b)) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiR (g 1 * (Ug ^ a * Vg ^ b)) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiR (g 1) * (chiTargetUnitsR0 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          (((chiR Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a * ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b) := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact ha
  have hchi2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 2 * Vg ^ b) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiR (g 2 * Vg ^ b) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiR (g 2) * (chiTargetUnitsR0 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiR Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact hb
  have hchi0 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiR (g 0) * (chiTargetUnitsR0 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    refine dvd_succ_of_sq (by omega) (hdev 0) ?_
    -- the corrected word dies in `Q_{k+1}`, so its χ-value is `1 mod 2^{k+2}`
    have hrelG : d0Word (g 0) (g 1 * (Ug ^ a * Vg ^ b)) (g 2 * Vg ^ b) ∈
        twoCentralSeries (DR : Type) (k + 1) := by
      have hmk : levelMk (DR : Type) (k + 1)
          (d0Word (g 0) (g 1 * (Ug ^ a * Vg ^ b)) (g 2 * Vg ^ b)) = 1 := by
        rw [map_d0Word, hlift0, hlift1, hlift2]
        exact hrelQ
      exact (QuotientGroup.eq_one_iff _).mp hmk
    have hW := dvd_chi_of_mem_twoCentralSeries chiR (k := k + 1) (by omega) hrelG
    rw [map_d0Word, d0Word_comm, Units.val_mul] at hW
    -- the `⁴`-slot is invisible at `2^{k+2}`, and `(−1)² = 1` kills the target of the `π`'d slot
    have h4 : (2 : ℤ_[2]) ^ (k + 1 + 1) ∣
        ((chiR (g 1 * (Ug ^ a * Vg ^ b)) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      rw [ht1, inv_one, mul_one] at hchi1
      refine dvd_trans (pow_dvd_pow 2 (by omega : k + 1 + 1 ≤ k + 1 + 2)) ?_
      have h := dvd_pow_two_pow_sub_one (k := k + 1) (by omega) hchi1 2
      rw [Units.val_pow_eq_pow_val]
      simpa using h
    have hsq0 : chiR (g 0) ^ 2 = (chiR (g 0) * (chiTargetUnitsR0 0)⁻¹) ^ 2 := by
      rw [ht0, mul_pow, show ((-1 : ℤ_[2]ˣ)⁻¹) ^ 2 = 1 by
        rw [inv_pow, neg_one_sq, inv_one], mul_one]
    rw [hsq0, Units.val_pow_eq_pow_val] at hW
    exact dvd_sub_one_of_mul hW h4
  refine ⟨![1, p * q, q], hw, hdbar, ⟨hrelQ, ?_⟩, ?_⟩
  · -- generation: the canonical lift generates (Frattini), and `λ₂`-moves preserve that
    have himg : (levelProj (DR : Type) k) ''
        (Set.range fun i => canonLift (DR : Type) k (T i)) = Set.range T := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => levelProj_canonLift (DR : Type) k (T i))
    have hgent : Subgroup.closure (Set.range fun i => canonLift (DR : Type) k (T i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top (DR : Type) drTopGenFinset isProP_DR (by omega) ?_
      rw [MonoidHom.map_closure, himg, hgen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two (DR : Type) drTopGenFinset isProP_DR
      _ _ hgent fun i => lambdaImage_le_of_le (by omega) (hw i)
  · -- the χ-clause at level `k+1`
    intro i
    fin_cases i
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 0) hlift0 hchi0
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 1) hlift1 hchi1
    · exact chiLevel_eq_of_dvd chiR (chiTargetUnitsR0 2) hlift2 hchi2

/-- SL2 (digit adjustment), direction 2.  Fill: L4a. -/
theorem stageSL2R2 (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) (hδ : defectR2 k T = 1) :
    ∃ w : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
        (canonLift (D0 : Type) k (T 2)) w = 1 ∧
      (fun i => canonLift (D0 : Type) k (T i) * w i) ∈ sPR2 (k + 1) := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  choose g hg using fun i : Fin 3 =>
    levelMk_surjective (D0 : Type) (k + 1) (canonLift (D0 : Type) k (T i))
  -- the pinned targets and the mod-`8` anchors `S ≡ X ≡ 5`
  have ht0 : chiTargetUnitsR2 0 = SvalUnit := by simp [chiTargetUnitsR2]
  have ht1 : chiTargetUnitsR2 1 = rootXUnit := by simp [chiTargetUnitsR2]
  have ht2 : chiTargetUnitsR2 2 = YvalUnit := by simp [chiTargetUnitsR2]
  have hS : PadicInt.toZModPow 3 ((SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 0
  have hX : PadicInt.toZModPow 3 ((rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 1
  -- the level-`k` deviations of the three slots
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiD0pres (g i) * (chiTargetUnitsR2 i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    refine dvd_of_chiLevel_eq (q := T i) chiD0pres (chiTargetUnitsR2 i)
      (by rw [← levelProj_levelMk, hg i, levelProj_canonLift]) ?_
    simpa [chiTargetR2] using hchi i
  -- the two moves: a power of the `x`-slot moves slot `0`, a power of the `s`-slot moves
  -- slot `1`; each kills its own bracket, and the digits are independent
  obtain ⟨Ug, hUg⟩ : ∃ Ug : (D0 : Type), Ug = g 1 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ Vg : (D0 : Type), Vg = g 0 ^ 2 ^ (k - 2) := ⟨_, rfl⟩
  obtain ⟨du, hdu, hdu2⟩ : ∃ d : ℤ_[2], ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hUg, map_pow]
    exact sharp_move hk hX (by rw [← ht1]; exact hdev 1)
  obtain ⟨dv, hdv, hdv2⟩ : ∃ d : ℤ_[2], ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
    rw [hVg, map_pow]
    exact sharp_move hk hS (by rw [← ht0]; exact hdev 0)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 0) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 0) hdu hdu2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 1) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b - 1 := by
    rcases dvd_or_dvd_mul (by omega) (hdev 1) hdv hdv2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  -- the modification in `Q_{k+1}`
  obtain ⟨p, hpdef⟩ : ∃ p : levelQuot (D0 : Type) (k + 1),
      p = (canonLift (D0 : Type) k (T 1) ^ 2 ^ (k - 2)) ^ a := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : levelQuot (D0 : Type) (k + 1),
      q = (canonLift (D0 : Type) k (T 0) ^ 2 ^ (k - 2)) ^ b := ⟨_, rfl⟩
  have hpm : p ∈ lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    rw [hpdef]
    refine Subgroup.pow_mem _ ?_ a
    have h := pow_two_pow_mem_lambdaImage (canonLift (D0 : Type) k (T 1)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hqm : q ∈ lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    rw [hqdef]
    refine Subgroup.pow_mem _ ?_ b
    have h := pow_two_pow_mem_lambdaImage (canonLift (D0 : Type) k (T 0)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at h
  have hw : ∀ i, (![p, q, 1] : Fin 3 → levelQuot (D0 : Type) (k + 1)) i ∈
      lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact hpm
    · exact hqm
    · exact one_mem _
  have hdbar : dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
      (canonLift (D0 : Type) k (T 2)) ![p, q, 1] = 1 := by
    refine dbarWordR2_kernel_witness _ _ _ p q ?_ ?_
    · rw [hpdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left a).eq
    · rw [hqdef]
      exact commP_eq_one_of_mul_comm (((Commute.refl _).pow_left _).pow_left b).eq
  -- the corrected triple, presented at the group level
  have hlift0 : levelMk (D0 : Type) (k + 1) (g 0 * Ug ^ a)
      = canonLift (D0 : Type) k (T 0) * ![p, q, 1] 0 := by
    rw [hUg, hpdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_zero]
  have hlift1 : levelMk (D0 : Type) (k + 1) (g 1 * Vg ^ b)
      = canonLift (D0 : Type) k (T 1) * ![p, q, 1] 1 := by
    rw [hVg, hqdef]
    simp only [map_mul, map_pow, hg, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hlift2 : levelMk (D0 : Type) (k + 1) (g 2)
      = canonLift (D0 : Type) k (T 2) * ![p, q, 1] 2 := by
    rw [hg 2]; simp
  -- the relator clause at level `k+1`
  have hrelQ : drWord (canonLift (D0 : Type) k (T 0) * ![p, q, 1] 0)
      (canonLift (D0 : Type) k (T 1) * ![p, q, 1] 1)
      (canonLift (D0 : Type) k (T 2) * ![p, q, 1] 2) = 1 := by
    rw [drWord_mul_lambdaImage k hk _ _ _ hw, hdbar, mul_one]
    exact hδ
  -- the two moved slots, then the squared slot's automatic digit (memo §1.1, `r₂` mirror)
  have hchi0 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 0 * Ug ^ a) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiD0pres (g 0 * Ug ^ a) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiD0pres (g 0) * (chiTargetUnitsR2 0)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiD0pres Ug : ℤ_[2]ˣ) : ℤ_[2]) ^ a := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact ha
  have hchi1 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hEq : ((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((chiD0pres (g 1) * (chiTargetUnitsR2 1)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiD0pres Vg : ℤ_[2]ˣ) : ℤ_[2]) ^ b := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact hb
  have hchi2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiD0pres (g 2) * (chiTargetUnitsR2 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    refine dvd_succ_of_sq (by omega) (hdev 2) ?_
    have hrelG : drWord (g 0 * Ug ^ a) (g 1 * Vg ^ b) (g 2) ∈
        twoCentralSeries (D0 : Type) (k + 1) := by
      have hmk : levelMk (D0 : Type) (k + 1) (drWord (g 0 * Ug ^ a) (g 1 * Vg ^ b) (g 2)) = 1 := by
        rw [map_drWord, hlift0, hlift1, hlift2]
        exact hrelQ
      exact (QuotientGroup.eq_one_iff _).mp hmk
    have hW := dvd_chi_of_mem_twoCentralSeries chiD0pres (k := k + 1) (by omega) hrelG
    rw [map_drWord, drWord_comm] at hW
    -- the `x`-slot enters only at `2^{k+2}`, and `X⁻⁴·Y² = 1` holds on the nose
    have h4 : (2 : ℤ_[2]) ^ (k + 1 + 1) ∣
        (((chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      refine dvd_trans (pow_dvd_pow 2 (by omega : k + 1 + 1 ≤ k + 1 + 2)) ?_
      have h := dvd_pow_two_pow_sub_one (k := k + 1) (by omega) hchi1 2
      rw [Units.val_pow_eq_pow_val]
      simpa using h
    have hid : (chiD0pres (g 2) * (chiTargetUnitsR2 2)⁻¹) ^ 2
        = ((chiD0pres (g 1 * Vg ^ b) ^ 4)⁻¹ * chiD0pres (g 2) ^ 2) *
          (chiD0pres (g 1 * Vg ^ b) * (chiTargetUnitsR2 1)⁻¹) ^ 4 := by
      have hAB : ∀ A B C : ℤ_[2]ˣ, A⁻¹ * B * (A * C) = B * C := by
        intro A B C
        rw [show A⁻¹ * B * (A * C) = A⁻¹ * (B * A) * C by group, mul_comm B A,
          show A⁻¹ * (A * B) * C = A⁻¹ * A * (B * C) by group, inv_mul_cancel, one_mul]
      rw [mul_pow, mul_pow, hAB, ht1, ht2, inv_pow, inv_pow, YvalUnit_sq_eq]
    have hcomb := dvd_mul_sub_one hW h4
    rw [← Units.val_mul, ← hid, Units.val_pow_eq_pow_val] at hcomb
    exact hcomb
  refine ⟨![p, q, 1], hw, hdbar, ⟨hrelQ, ?_⟩, ?_⟩
  · -- generation
    have himg : (levelProj (D0 : Type) k) ''
        (Set.range fun i => canonLift (D0 : Type) k (T i)) = Set.range T := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => levelProj_canonLift (D0 : Type) k (T i))
    have hgent : Subgroup.closure (Set.range fun i => canonLift (D0 : Type) k (T i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top (D0 : Type) d0TopGenFinset SectionThree.d0_isProP
        (by omega) ?_
      rw [MonoidHom.map_closure, himg, hgen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two (D0 : Type) d0TopGenFinset
      SectionThree.d0_isProP _ _ hgent fun i => lambdaImage_le_of_le (by omega) (hw i)
  · -- the χ-clause at level `k+1`
    intro i
    fin_cases i
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 0) hlift0 hchi0
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 1) hlift1 hchi1
    · exact chiLevel_eq_of_dvd chiD0pres (chiTargetUnitsR2 2) hlift2 hchi2

/-- **The stage step, direction 1** (spike §2.4's conclusion; the exact interface the
assembly consumes): `S^P_ₖ ≠ ∅ → S^P_{k+1} ≠ ∅` for `k ≥ 3`.

Proved here from the frozen statements (SL1 → shift formula → modification stability →
SL2) as the L1 composability certificate — no fill needed; it inherits the upstream
sorries. -/
theorem stageStepR0 (k : ℕ) (hk : 3 ≤ k) (h : (sPR0 k).Nonempty) :
    (sPR0 (k + 1)).Nonempty := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨w, hw, hd⟩ := stageSL1R0 k hk hT
  have hT₁ : (fun i => T i * levelProj (DR : Type) k (w i)) ∈ sPR0 k :=
    sPR0_mul_mem k hk hT fun i => levelProj_mem_lambdaImage (DR : Type) (hw i)
  have hδ₁ : defectR0 k (fun i => T i * levelProj (DR : Type) k (w i)) = 1 := by
    rw [defectR0_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', hker, hmem⟩ := stageSL2R0 k hk hT₁ hδ₁
  exact ⟨_, hmem⟩

/-- The stage step, direction 2 (proved from the frozen statements; composability
certificate). -/
theorem stageStepR2 (k : ℕ) (hk : 3 ≤ k) (h : (sPR2 k).Nonempty) :
    (sPR2 (k + 1)).Nonempty := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨w, hw, hd⟩ := stageSL1R2 k hk hT
  have hT₁ : (fun i => T i * levelProj (D0 : Type) k (w i)) ∈ sPR2 k :=
    sPR2_mul_mem k hk hT fun i => levelProj_mem_lambdaImage (D0 : Type) (hw i)
  have hδ₁ : defectR2 k (fun i => T i * levelProj (D0 : Type) k (w i)) = 1 := by
    rw [defectR2_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', hker, hmem⟩ := stageSL2R2 k hk hT₁ hδ₁
  exact ⟨_, hmem⟩

end GQ2.Roe.Labute
