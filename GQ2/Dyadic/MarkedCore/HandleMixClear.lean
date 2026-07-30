/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixFrame

@[expose] public section

/-!
# Handle mixing, step 4: the ν-clearing, and the restated obligation

**Ticket HM4** — placeholder docstring, expanded at the end of the ticket.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 `A(P,h)` at the frame level  (memo §5.3's generating set) -/

section ClearGens

variable {h : ℕ}

/-- **The ν-frame endomorphism monoid**, entered explicitly.  `Function.End X` is *definitionally*
`X → X`, so a bare frame map placed in a multiplicative position gets `Pi.mulOneClass` rather than
`Function.End`'s composition monoid; `frameEnd` is the one-line barrier that keeps the composition
structure.  All of §1–§2 multiplies inside `frameEnd`, and `frameEnd_mul_apply` is the only
unfolding rule ever needed. -/
def frameEnd {h : ℕ} (F : (Fin (coreRank h) → ℤ_[2]) → Fin (coreRank h) → ℤ_[2]) :
    Function.End (Fin (coreRank h) → ℤ_[2]) := F

@[simp] theorem frameEnd_apply (F : (Fin (coreRank h) → ℤ_[2]) → Fin (coreRank h) → ℤ_[2])
    (m : Fin (coreRank h) → ℤ_[2]) : frameEnd F m = F m := rfl

/-- Composites read innermost-first (HM3's convention). -/
theorem frameEnd_mul_apply (F G : (Fin (coreRank h) → ℤ_[2]) → Fin (coreRank h) → ℤ_[2])
    (m : Fin (coreRank h) → ℤ_[2]) : (frameEnd F * frameEnd G) m = F (G m) := rfl

theorem frameEnd_pow_apply (F : (Fin (coreRank h) → ℤ_[2]) → Fin (coreRank h) → ℤ_[2]) (n : ℕ)
    (m : Fin (coreRank h) → ℤ_[2]) : (frameEnd F ^ n) m = F^[n] m := rfl

@[simp] theorem frameEnd_one_apply (m : Fin (coreRank h) → ℤ_[2]) :
    (1 : Function.End (Fin (coreRank h) → ℤ_[2])) m = m := rfl

/-- **Memo §5.3's realized frame moves**, as a generating set inside `Function.End`: the two
intra-handle transvection families at every handle and every 2-adic exponent (`frameTauU`,
`frameTauV`), the one core-side transvection both relators admit (`frameTauD`), and HM2's mixing
substitution at every handle (`frameMixAdd`).  Every element of this set is the frame action of
an *explicit continuous automorphism* of each marked core — that is §4's content, and it is why
`Submonoid.closure (frameClearGens h)` deserves the memo's name `A(P,h)`. -/
noncomputable def frameClearGens (h : ℕ) : Set (Function.End (Fin (coreRank h) → ℤ_[2])) :=
  (⋃ j : Fin h, Set.range fun k : ℤ_[2] => frameEnd (frameTauU j k))
    ∪ (⋃ j : Fin h, Set.range fun k : ℤ_[2] => frameEnd (frameTauV j k))
    ∪ Set.range (fun k : ℤ_[2] => frameEnd (frameTauD k))
    ∪ Set.range (fun j : Fin h => frameEnd (frameMixAdd j))

theorem frameTauU_mem_clearGens (j : Fin h) (k : ℤ_[2]) :
    frameEnd (frameTauU j k) ∈ frameClearGens h :=
  Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_iUnion.mpr ⟨j, ⟨k, rfl⟩⟩)))

theorem frameTauV_mem_clearGens (j : Fin h) (k : ℤ_[2]) :
    frameEnd (frameTauV j k) ∈ frameClearGens h :=
  Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _
    (Set.mem_iUnion.mpr ⟨j, ⟨k, rfl⟩⟩)))

theorem frameTauD_mem_clearGens (k : ℤ_[2]) :
    frameEnd (frameTauD (h := h) k) ∈ frameClearGens h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨k, rfl⟩)

theorem frameMixAdd_mem_clearGens (j : Fin h) :
    frameEnd (frameMixAdd j) ∈ frameClearGens h :=
  Set.mem_union_right _ ⟨j, rfl⟩

/-- **Every `SL₂(ℤ₂)` element of the `j`-th handle plane lies in `A(P,h)`** — HM3's
`frameMatEnd_mem_closure` (the 2×2 local-ring `SL₂ = E₂` argument) transported into the
generating set of this file. -/
theorem frameMatEnd_mem_clearGens (j : Fin h) {T : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hT : T.det = 1) :
    frameMatEnd (M := ℤ_[2]) j T ∈ Submonoid.closure (frameClearGens h) := by
  refine Submonoid.closure_mono ?_ (frameMatEnd_mem_closure j hT)
  rintro F (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact frameTauU_mem_clearGens j k
  · exact frameTauV_mem_clearGens j k

/-- `θ_w = diag(w, w⁻¹)` lies in `A(P,h)` (memo §5.2's consumed instance). -/
theorem frameTheta_mem_clearGens (j : Fin h) (w : ℤ_[2]ˣ) :
    frameEnd (frameTheta j w) ∈ Submonoid.closure (frameClearGens h) := by
  refine frameMatEnd_mem_clearGens j ?_
  rw [planeDiag, Matrix.det_fin_two]
  norm_num [← Units.val_mul]

/-- The intra-handle `S`-move lies in `A(P,h)` (memo §4.4). -/
theorem frameS_mem_clearGens (j : Fin h) :
    frameEnd (frameS j) ∈ Submonoid.closure (frameClearGens h) := by
  refine frameMatEnd_mem_clearGens j ?_
  rw [planeS, Matrix.det_fin_two]
  norm_num

theorem frameSinv_mem_clearGens (j : Fin h) :
    frameEnd (frameSinv j) ∈ Submonoid.closure (frameClearGens h) := by
  refine frameMatEnd_mem_clearGens j ?_
  rw [planeSinv, Matrix.det_fin_two]
  norm_num

/-- **The pure Eichler element is in `A(P,h)`** — HM3's normalisation
`E_j = τ_c(−1) ∘ τ_{v_j}(1) ∘ Φ_j`, read as a product of three generators. -/
theorem frameEichlerU_one_mem_clearGens (j : Fin h) :
    frameEnd (frameEichlerU j (1 : ℤ_[2])) ∈ Submonoid.closure (frameClearGens h) := by
  have heq : frameEnd (frameEichlerU j (1 : ℤ_[2]))
      = frameEnd (frameTauD (-1)) * frameEnd (frameTauU j 1) * frameEnd (frameMixAdd j) :=
    funext fun m => frameEichlerU_one_eq j m
  rw [heq]
  exact mul_mem (mul_mem (Submonoid.subset_closure (frameTauD_mem_clearGens _))
    (Submonoid.subset_closure (frameTauU_mem_clearGens _ _)))
    (Submonoid.subset_closure (frameMixAdd_mem_clearGens _))

/-- **Every 2-adic Eichler coefficient is in `A(P,h)`** (memo §5.2's conclusion, in the
`Submonoid` vocabulary): HM3's `exists_frameEichlerU_theta_conj` writes `E_j^x` as an integer
power of the integral `E_j` conjugated by a `θ_w`, and all three factors are generators. -/
theorem frameEichlerU_mem_clearGens (j : Fin h) (x : ℤ_[2]) :
    frameEnd (frameEichlerU j x) ∈ Submonoid.closure (frameClearGens h) := by
  obtain ⟨n, w, hnw⟩ := exists_frameEichlerU_theta_conj (M := ℤ_[2]) j x
  have heq : frameEnd (frameEichlerU j x)
      = frameEnd (frameTheta j w⁻¹) * frameEnd (frameEichlerU j (1 : ℤ_[2])) ^ n
        * frameEnd (frameTheta j w) :=
    funext fun m => (hnw m).symm
  rw [heq]
  exact mul_mem (mul_mem (frameTheta_mem_clearGens _ _)
    (pow_mem (frameEichlerU_one_mem_clearGens j) n)) (frameTheta_mem_clearGens _ _)

/-- The `v̄_j`-side mirror (memo §5.3 step 2): `E'_j^x` is the `S`-move conjugate of `E_j^x`. -/
theorem frameEichlerV_mem_clearGens (j : Fin h) (x : ℤ_[2]) :
    frameEnd (frameEichlerV j x) ∈ Submonoid.closure (frameClearGens h) := by
  have heq : frameEnd (frameEichlerV j x)
      = frameEnd (frameSinv j) * frameEnd (frameEichlerU j x) * frameEnd (frameS j) :=
    funext fun m => frameEichlerV_eq_conj j m x
  rw [heq]
  exact mul_mem (mul_mem (frameSinv_mem_clearGens _) (frameEichlerU_mem_clearGens _ _))
    (frameS_mem_clearGens _)

end ClearGens

/-! ## §2 The ν-clearing  (memo §5.3) -/

section NuClear

variable {h : ℕ}

/-- **Memo §5.3's two steps at a single handle**: `E_j^x` with `x = −ν'(ū_j)/ν'(c̄)` kills the
`ū_j`-coordinate, then `(E'_j)^y` with `y = −ν'(v̄_j)/ν'(c̄)` kills the `v̄_j`-coordinate without
undoing step 1 (`E'_j` fixes `ū_j`).  Neither step touches `c̄` or any other handle, which is
what makes the induction of `exists_frameClear_lt` go through. -/
theorem exists_frameClear_one (j : Fin h) (v : Fin (coreRank h) → ℤ_[2]) (w : ℤ_[2]ˣ)
    (hw : (w : ℤ_[2]) = v 2) :
    ∃ φ ∈ Submonoid.closure (frameClearGens h),
      φ v (handleIdxU j) = 0 ∧ φ v (handleIdxV j) = 0 ∧ φ v 2 = v 2
        ∧ (∀ i : Fin h, i ≠ j → φ v (handleIdxU i) = v (handleIdxU i))
        ∧ (∀ i : Fin h, i ≠ j → φ v (handleIdxV i) = v (handleIdxV i)) := by
  have hwi : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (v 2) = 1 := by
    rw [← hw, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set x : ℤ_[2] := -v (handleIdxU j) * ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hx
  set y : ℤ_[2] := -v (handleIdxV j) * ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hy
  refine ⟨frameEnd (frameEichlerV j y) * frameEnd (frameEichlerU j x),
    mul_mem (frameEichlerV_mem_clearGens _ _) (frameEichlerU_mem_clearGens _ _), ?_, ?_, ?_,
    ?_, ?_⟩
  · show frameEichlerV j y (frameEichlerU j x v) (handleIdxU j) = 0
    rw [frameEichlerV_handleU, frameEichlerU_handleU_self, hx, smul_eq_mul, mul_assoc, hwi]
    ring
  · show frameEichlerV j y (frameEichlerU j x v) (handleIdxV j) = 0
    rw [frameEichlerV_handleV_self, frameEichlerU_handleV, frameEichlerU_two, hy, smul_eq_mul,
      mul_assoc, hwi]
    ring
  · show frameEichlerV j y (frameEichlerU j x v) 2 = v 2
    rw [frameEichlerV_two, frameEichlerU_two]
  · intro i hij
    show frameEichlerV j y (frameEichlerU j x v) (handleIdxU i) = v (handleIdxU i)
    rw [frameEichlerV_handleU, frameEichlerU_handleU_of_ne _ _ _ hij]
  · intro i hij
    show frameEichlerV j y (frameEichlerU j x v) (handleIdxV i) = v (handleIdxV i)
    rw [frameEichlerV_of_ne _ _ _ (fun hc => hij (handleIdxV_injective hc))
      (handleIdxV_ne_three i), frameEichlerU_handleV]

/-- **The ν-clearing, by induction on the handles cleared so far** (memo §5.3's `2h` steps): the
composite of the first `n` two-step blocks kills the `ū`- and `v̄`-coordinates of every handle of
index `< n` and fixes `c̄`.  The invariant that carries the induction is precisely that `E_j^x`
and `(E'_j)^y` are invisible to the handles other than the `j`-th. -/
theorem exists_frameClear_lt (v : Fin (coreRank h) → ℤ_[2]) (w : ℤ_[2]ˣ)
    (hw : (w : ℤ_[2]) = v 2) (n : ℕ) :
    ∃ φ ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, (j : ℕ) < n → φ v (handleIdxU j) = 0 ∧ φ v (handleIdxV j) = 0)
        ∧ φ v 2 = v 2 := by
  induction n with
  | zero => exact ⟨1, one_mem _, fun j hj => absurd hj (by omega), rfl⟩
  | succ n ih =>
    obtain ⟨φ, hφ, hclear, h2⟩ := ih
    by_cases hn : n < h
    · obtain ⟨ψ, hψ, hU, hV, h2', hUne, hVne⟩ :=
        exists_frameClear_one (⟨n, hn⟩ : Fin h) (φ v) w (by rw [hw, h2])
      refine ⟨ψ * φ, mul_mem hψ hφ, ?_, ?_⟩
      · intro j hj
        by_cases hjn : (j : ℕ) = n
        · have hje : j = (⟨n, hn⟩ : Fin h) := Fin.ext hjn
          subst hje
          exact ⟨hU, hV⟩
        · have hjne : j ≠ (⟨n, hn⟩ : Fin h) := fun hc => hjn (by rw [hc])
          obtain ⟨hcU, hcV⟩ := hclear j (by omega)
          exact ⟨(hUne j hjne).trans hcU, (hVne j hjne).trans hcV⟩
      · show ψ (φ v) 2 = v 2
        rw [h2', h2]
    · refine ⟨φ, hφ, fun j hj => hclear j ?_, h2⟩
      have := j.isLt
      omega

/-- **The ν-clearing theorem** (memo §5.3, the payoff of the spike): for every ν-frame vector
whose `c̄`-coordinate is a 2-adic **unit** there is a frame move in `A(P,h)` after which the whole
handle plane is annihilated, and the `c̄`-coordinate is untouched.

This is memo §5.3 verbatim, and it is *stronger* than what S2.4 §6.4 asked for: S2.4's single
move needs `ν'(ū₁)` itself to be a unit (so that its `k` is odd), whereas §1's family realizes
**every** `ν'(ū_j) ∈ ℤ₂`.  The unit hypothesis on `c̄` is the one input the recipe needs, and on
the `M` side it is memo §6.4's residue 2 (`ν'(c̄) ∈ ℤ₂ˣ`). -/
theorem exists_frameClear (v : Fin (coreRank h) → ℤ_[2]) (hv : IsUnit (v 2)) :
    ∃ φ ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, φ v (handleIdxU j) = 0) ∧ (∀ j : Fin h, φ v (handleIdxV j) = 0)
        ∧ φ v 2 = v 2 := by
  obtain ⟨φ, hφ, hclear, h2⟩ := exists_frameClear_lt v hv.unit hv.unit_spec h
  exact ⟨φ, hφ, fun j => (hclear j j.isLt).1, fun j => (hclear j j.isLt).2, h2⟩

end NuClear

/-! ## §3 The `τ` families as automorphisms of the marked cores  (memo §5.1) -/

section TauMark

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- `x ^ (0 : ℤ₂) = 1` — the exponent-zero companion of `zpowZtwo_one_exp`, which the inverse of
each `τ` family needs. -/
theorem zpowZtwo_zero_exp (hP : IsProP 2 P) (x : P) : zpowZtwo hP x 0 = 1 := by
  have hx := zpowZtwo_natCast hP x 0
  rw [Nat.cast_zero] at hx
  rw [hx, pow_zero]

/-- **Memo §5.1's `τ_{v_j}(k)` as a substitution on markings**: `u_j ↦ v_j^k·u_j`, exact for
*every* 2-adic `k` (HM1's `commute_zpowZtwo_self`).  Its ν-frame action is `frameTauU j k`
(HM3's `nuFrame_tau_handleU`). -/
noncomputable def tauUMark (hP : IsProP 2 P) (j : Fin h) (k : ℤ_[2])
    (m : Fin (coreRank h) → P) : Fin (coreRank h) → P :=
  Function.update m (handleIdxU j) (zpowZtwo hP (m (handleIdxV j)) k * m (handleIdxU j))

/-- **Memo §5.1's `τ_{u_j}(k)`**: `v_j ↦ u_j^k·v_j`, ν-frame action `frameTauV j k`. -/
noncomputable def tauVMark (hP : IsProP 2 P) (j : Fin h) (k : ℤ_[2])
    (m : Fin (coreRank h) → P) : Fin (coreRank h) → P :=
  Function.update m (handleIdxV j) (zpowZtwo hP (m (handleIdxU j)) k * m (handleIdxV j))

/-- **Memo §5.1's `τ_c(k)`**: `d ↦ c^k·d`, the one core-side transvection both rank-four
relators admit (HM1's `mWord_tau_d`/`nWord_tau_d`; there is no `τ_d`-mirror for `M`, memo §6.4's
residue 2).  ν-frame action `frameTauD k`. -/
noncomputable def tauDMark (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  Function.update m 3 (zpowZtwo hP (m 2) k * m 3)

variable (hP : IsProP 2 P) (j : Fin h) (k l : ℤ_[2]) (m : Fin (coreRank h) → P)

@[simp] theorem tauUMark_handleU_self :
    tauUMark hP j k m (handleIdxU j)
      = zpowZtwo hP (m (handleIdxV j)) k * m (handleIdxU j) := Function.update_self _ _ _

theorem tauUMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ handleIdxU j) :
    tauUMark hP j k m i = m i := Function.update_of_ne hi _ _

@[simp] theorem tauUMark_handleV (i : Fin h) : tauUMark hP j k m (handleIdxV i) = m (handleIdxV i) :=
  tauUMark_of_ne _ _ _ _ (Ne.symm (handleIdxU_ne_handleIdxV j i))

@[simp] theorem tauVMark_handleV_self :
    tauVMark hP j k m (handleIdxV j)
      = zpowZtwo hP (m (handleIdxU j)) k * m (handleIdxV j) := Function.update_self _ _ _

theorem tauVMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ handleIdxV j) :
    tauVMark hP j k m i = m i := Function.update_of_ne hi _ _

@[simp] theorem tauVMark_handleU (i : Fin h) : tauVMark hP j k m (handleIdxU i) = m (handleIdxU i) :=
  tauVMark_of_ne _ _ _ _ (handleIdxU_ne_handleIdxV i j)

@[simp] theorem tauDMark_three : tauDMark hP k m 3 = zpowZtwo hP (m 2) k * m 3 :=
  Function.update_self _ _ _

theorem tauDMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ 3) : tauDMark hP k m i = m i :=
  Function.update_of_ne hi _ _

@[simp] theorem tauDMark_two : tauDMark hP k m 2 = m 2 := tauDMark_of_ne _ _ _ coreTwo_ne_three

/-! ### Each `τ` family is a one-parameter group of substitutions -/

theorem tauUMark_tauUMark : tauUMark hP j k (tauUMark hP j l m) = tauUMark hP j (k + l) m := by
  funext i
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [tauUMark_handleU_self, tauUMark_handleV, tauUMark_handleU_self, tauUMark_handleU_self,
      zpowZtwo_add, mul_assoc]
  rw [tauUMark_of_ne _ _ _ _ hi, tauUMark_of_ne _ _ _ _ hi, tauUMark_of_ne _ _ _ _ hi]

theorem tauVMark_tauVMark : tauVMark hP j k (tauVMark hP j l m) = tauVMark hP j (k + l) m := by
  funext i
  by_cases hi : i = handleIdxV j
  · subst hi
    rw [tauVMark_handleV_self, tauVMark_handleU, tauVMark_handleV_self, tauVMark_handleV_self,
      zpowZtwo_add, mul_assoc]
  rw [tauVMark_of_ne _ _ _ _ hi, tauVMark_of_ne _ _ _ _ hi, tauVMark_of_ne _ _ _ _ hi]

theorem tauDMark_tauDMark : tauDMark hP k (tauDMark hP l m) = tauDMark hP (k + l) m := by
  funext i
  by_cases hi : i = 3
  · subst hi
    rw [tauDMark_three, tauDMark_two, tauDMark_three, tauDMark_three, zpowZtwo_add, mul_assoc]
  rw [tauDMark_of_ne _ _ _ hi, tauDMark_of_ne _ _ _ hi, tauDMark_of_ne _ _ _ hi]

@[simp] theorem tauUMark_zero : tauUMark hP j 0 m = m := by
  funext i
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [tauUMark_handleU_self, zpowZtwo_zero_exp, one_mul]
  rw [tauUMark_of_ne _ _ _ _ hi]

@[simp] theorem tauVMark_zero : tauVMark hP j 0 m = m := by
  funext i
  by_cases hi : i = handleIdxV j
  · subst hi
    rw [tauVMark_handleV_self, zpowZtwo_zero_exp, one_mul]
  rw [tauVMark_of_ne _ _ _ _ hi]

@[simp] theorem tauDMark_zero : tauDMark hP (0 : ℤ_[2]) m = m := by
  funext i
  by_cases hi : i = 3
  · subst hi
    rw [tauDMark_three, zpowZtwo_zero_exp, one_mul]
  rw [tauDMark_of_ne _ _ _ hi]

end TauMark

/-! ### Naturality (what turns the marking identities into hom identities) -/

section TauMarkNaturality

variable {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] {h : ℕ}

variable (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)

theorem map_tauUMark (j : Fin h) (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (tauUMark hP j k m i) = tauUMark hQ j k (fun i => f (m i)) i := by
  by_cases hi : i = handleIdxU j
  · subst hi
    rw [tauUMark_handleU_self, tauUMark_handleU_self, map_mul, map_zpowZtwo hP hQ]
  rw [tauUMark_of_ne _ _ _ _ hi, tauUMark_of_ne _ _ _ _ hi]

theorem map_tauVMark (j : Fin h) (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (tauVMark hP j k m i) = tauVMark hQ j k (fun i => f (m i)) i := by
  by_cases hi : i = handleIdxV j
  · subst hi
    rw [tauVMark_handleV_self, tauVMark_handleV_self, map_mul, map_zpowZtwo hP hQ]
  rw [tauVMark_of_ne _ _ _ _ hi, tauVMark_of_ne _ _ _ _ hi]

theorem map_tauDMark (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (tauDMark hP k m i) = tauDMark hQ k (fun i => f (m i)) i := by
  by_cases hi : i = 3
  · subst hi
    rw [tauDMark_three, tauDMark_three, map_mul, map_zpowZtwo hP hQ]
  rw [tauDMark_of_ne _ _ _ hi, tauDMark_of_ne _ _ _ hi]

end TauMarkNaturality

/-! ### Relator invariance: the missing `τ_c` row at the level of the full relators

HM1 lands `τ_c(k)` on the two **core words** (`mWord_tau_d`, `nWord_tau_d`) and the two handle
transvections on the two **relators** (`mRelWord_tau_handleU`/`V`).  The missing pair — `τ_c(k)`
on the relators — needs only the index bookkeeping of a one-slot update at the letter `3`. -/

section RelWordUpdateThree

variable {G : Type*} [Group G] {h : ℕ}

/-- A core letter below index `3` is not the letter `3`. -/
theorem coreVal_lt_three_ne {i : Fin (coreRank h)} (hi : (i : ℕ) < 3) :
    i ≠ (3 : Fin (coreRank h)) := by
  intro hc
  rw [hc, coreVal_three] at hi
  omega

/-- **Structure of a one-slot update of the `M_α` relator at the letter `3`**: the other three
core letters and the whole handle block are untouched. -/
theorem mRelWord_update_three (α : ℕ) (m : Fin (coreRank h) → G) (w : G) :
    mRelWord α (Function.update m 3 w)
      = mWord α (m 0) (m 1) (m 2) w
        * handleWord (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) := by
  have hU : (fun i => Function.update m 3 w (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i => Function.update_of_ne (handleIdxU_ne_three i) _ _
  have hV : (fun i => Function.update m 3 w (handleIdxV i)) = fun i => m (handleIdxV i) :=
    funext fun i => Function.update_of_ne (handleIdxV_ne_three i) _ _
  rw [mRelWord, Function.update_self, hU, hV,
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_zero]; omega)),
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_one]; omega)),
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_two]; omega))]

/-- **Structure of a one-slot update of the `N_α` relator at the letter `3`**. -/
theorem nRelWord_update_three (α : ℕ) (m : Fin (coreRank h) → G) (w : G) :
    nRelWord α (Function.update m 3 w)
      = nWord α (m 0) (m 1) (m 2) w
        * handleWord (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) := by
  have hU : (fun i => Function.update m 3 w (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i => Function.update_of_ne (handleIdxU_ne_three i) _ _
  have hV : (fun i => Function.update m 3 w (handleIdxV i)) = fun i => m (handleIdxV i) :=
    funext fun i => Function.update_of_ne (handleIdxV_ne_three i) _ _
  rw [nRelWord, Function.update_self, hU, hV,
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_zero]; omega)),
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_one]; omega)),
    Function.update_of_ne (coreVal_lt_three_ne (by rw [coreVal_two]; omega))]

end RelWordUpdateThree

section RelWordTau

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

variable (hP : IsProP 2 P) (α : ℕ) (m : Fin (coreRank h) → P) (j : Fin h) (k : ℤ_[2])

theorem mRelWord_tauUMark : mRelWord α (tauUMark hP j k m) = mRelWord α m :=
  mRelWord_tau_handleU hP α m j k

theorem mRelWord_tauVMark : mRelWord α (tauVMark hP j k m) = mRelWord α m :=
  mRelWord_tau_handleV hP α m j k

theorem nRelWord_tauUMark : nRelWord α (tauUMark hP j k m) = nRelWord α m :=
  nRelWord_tau_handleU hP α m j k

theorem nRelWord_tauVMark : nRelWord α (tauVMark hP j k m) = nRelWord α m :=
  nRelWord_tau_handleV hP α m j k

/-- **`τ_c(k)` fixes the `M_α` relator** — HM1's `mWord_tau_d` at the full relator. -/
theorem mRelWord_tauDMark : mRelWord α (tauDMark hP k m) = mRelWord α m := by
  rw [tauDMark, mRelWord_update_three, mWord_tau_d hP, mRelWord]

/-- **`τ_c(k)` fixes the `N_α` relator** — HM1's `nWord_tau_d` at the full relator. -/
theorem nRelWord_tauDMark : nRelWord α (tauDMark hP k m) = nRelWord α m := by
  rw [tauDMark, nRelWord_update_three, nWord_tau_d hP, nRelWord]

end RelWordTau

/-! ### The assembly, per core (HM2 §3's `thetaEquiv` pattern, in one-parameter-family form) -/

section Assembly

variable (α h : ℕ)

/-- Two continuous endomorphisms of `D_M` inverting each other on the marked generators invert
each other everywhere — HM2 §3's extensionality step, isolated. -/
theorem dm_leftInverse (φ ψ : ContinuousMonoidHom (DM α h : Type) (DM α h : Type))
    (hgen : ∀ i, ψ (φ (dmGen α h i)) = dmGen α h i) (x : (DM α h : Type)) : ψ (φ x) = x := by
  have hext : ψ.comp φ = (⟨MonoidHom.id _, continuous_id⟩ :
      ContinuousMonoidHom (DM α h : Type) (DM α h : Type)) := dm_hom_ext _ _ hgen
  exact DFunLike.congr_fun hext x

theorem dn_leftInverse (φ ψ : ContinuousMonoidHom (DN α h : Type) (DN α h : Type))
    (hgen : ∀ i, ψ (φ (dnGen α h i)) = dnGen α h i) (x : (DN α h : Type)) : ψ (φ x) = x := by
  have hext : ψ.comp φ = (⟨MonoidHom.id _, continuous_id⟩ :
      ContinuousMonoidHom (DN α h : Type) (DN α h : Type)) := dn_hom_ext _ _ hgen
  exact DFunLike.congr_fun hext x

/-- **HM2 §3's assembly for a one-parameter family**: a family `L` of continuous endomorphisms of
`D_M` classified by a family `S` of marking substitutions that is *additive* in the parameter and
*natural* consists of automorphisms, the inverse at `k` being the member at `−k`.  Used three
times below (`τ_{v_j}`, `τ_{u_j}`, `τ_c`); HM2 built `Φ_j`'s equiv by hand because its inverse is
a different substitution. -/
noncomputable def dmParamEquiv
    (L : ℤ_[2] → ContinuousMonoidHom (DM α h : Type) (DM α h : Type))
    (S : ℤ_[2] → (Fin (coreRank h) → (DM α h : Type)) → Fin (coreRank h) → (DM α h : Type))
    (hL : ∀ k i, L k (dmGen α h i) = S k (dmGen α h) i)
    (hnat : ∀ (k : ℤ_[2]) (f : ContinuousMonoidHom (DM α h : Type) (DM α h : Type))
      (m : Fin (coreRank h) → (DM α h : Type)) i, f (S k m i) = S k (fun i => f (m i)) i)
    (hadd : ∀ (k l : ℤ_[2]) m, S k (S l m) = S (k + l) m) (hzero : ∀ m, S 0 m = m)
    (k : ℤ_[2]) : ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  continuousMulEquivOfBijective (L k) (Function.bijective_iff_has_inverse.mpr
    ⟨L (-k),
      dm_leftInverse α h (L k) (L (-k)) fun i => by
        have hg : (fun i => L (-k) (dmGen α h i)) = S (-k) (dmGen α h) := funext (hL (-k))
        rw [hL, hnat, hg, hadd, add_neg_cancel, hzero],
      dm_leftInverse α h (L (-k)) (L k) fun i => by
        have hg : (fun i => L k (dmGen α h i)) = S k (dmGen α h) := funext (hL k)
        rw [hL, hnat, hg, hadd, neg_add_cancel, hzero]⟩)

/-- The `N`-mirror of `dmParamEquiv`. -/
noncomputable def dnParamEquiv
    (L : ℤ_[2] → ContinuousMonoidHom (DN α h : Type) (DN α h : Type))
    (S : ℤ_[2] → (Fin (coreRank h) → (DN α h : Type)) → Fin (coreRank h) → (DN α h : Type))
    (hL : ∀ k i, L k (dnGen α h i) = S k (dnGen α h) i)
    (hnat : ∀ (k : ℤ_[2]) (f : ContinuousMonoidHom (DN α h : Type) (DN α h : Type))
      (m : Fin (coreRank h) → (DN α h : Type)) i, f (S k m i) = S k (fun i => f (m i)) i)
    (hadd : ∀ (k l : ℤ_[2]) m, S k (S l m) = S (k + l) m) (hzero : ∀ m, S 0 m = m)
    (k : ℤ_[2]) : ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  continuousMulEquivOfBijective (L k) (Function.bijective_iff_has_inverse.mpr
    ⟨L (-k),
      dn_leftInverse α h (L k) (L (-k)) fun i => by
        have hg : (fun i => L (-k) (dnGen α h i)) = S (-k) (dnGen α h) := funext (hL (-k))
        rw [hL, hnat, hg, hadd, add_neg_cancel, hzero],
      dn_leftInverse α h (L (-k)) (L k) fun i => by
        have hg : (fun i => L k (dnGen α h i)) = S k (dnGen α h) := funext (hL k)
        rw [hL, hnat, hg, hadd, neg_add_cancel, hzero]⟩)

/-! #### The three `τ` families on `D_M` -/

/-- `τ_{v_j}(k)` on `D_M`. -/
noncomputable def dmTauUHom (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (tauUMark (isProP_DM α h) j k (dmGen α h))
    (by rw [mRelWord_tauUMark]; exact dm_relation α h)

/-- `τ_{u_j}(k)` on `D_M`. -/
noncomputable def dmTauVHom (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (tauVMark (isProP_DM α h) j k (dmGen α h))
    (by rw [mRelWord_tauVMark]; exact dm_relation α h)

/-- `τ_c(k)` on `D_M`. -/
noncomputable def dmTauDHom (k : ℤ_[2]) :
    ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (tauDMark (isProP_DM α h) k (dmGen α h))
    (by rw [mRelWord_tauDMark]; exact dm_relation α h)

@[simp] theorem dmTauUHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauUHom α h j k (dmGen α h i) = tauUMark (isProP_DM α h) j k (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

@[simp] theorem dmTauVHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauVHom α h j k (dmGen α h i) = tauVMark (isProP_DM α h) j k (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

@[simp] theorem dmTauDHom_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauDHom α h k (dmGen α h i) = tauDMark (isProP_DM α h) k (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

/-- **`τ_{v_j}(k)` as a continuous automorphism of `D_M`**, for every `k : ℤ_[2]`. -/
noncomputable def dmTauUEquiv (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  dmParamEquiv α h (dmTauUHom α h j) (tauUMark (isProP_DM α h) j) (dmTauUHom_gen α h j)
    (fun k f m i => map_tauUMark (isProP_DM α h) (isProP_DM α h) f j k m i)
    (fun k l m => tauUMark_tauUMark _ j k l m) (fun m => tauUMark_zero _ j m) k

/-- **`τ_{u_j}(k)` as a continuous automorphism of `D_M`**. -/
noncomputable def dmTauVEquiv (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  dmParamEquiv α h (dmTauVHom α h j) (tauVMark (isProP_DM α h) j) (dmTauVHom_gen α h j)
    (fun k f m i => map_tauVMark (isProP_DM α h) (isProP_DM α h) f j k m i)
    (fun k l m => tauVMark_tauVMark _ j k l m) (fun m => tauVMark_zero _ j m) k

/-- **`τ_c(k)` as a continuous automorphism of `D_M`**. -/
noncomputable def dmTauDEquiv (k : ℤ_[2]) :
    ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  dmParamEquiv α h (dmTauDHom α h) (tauDMark (isProP_DM α h)) (dmTauDHom_gen α h)
    (fun k f m i => map_tauDMark (isProP_DM α h) (isProP_DM α h) f k m i)
    (fun k l m => tauDMark_tauDMark _ k l m) (fun m => tauDMark_zero _ m) k

@[simp] theorem dmTauUEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauUEquiv α h j k (dmGen α h i) = tauUMark (isProP_DM α h) j k (dmGen α h) i :=
  dmTauUHom_gen α h j k i

@[simp] theorem dmTauVEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauVEquiv α h j k (dmGen α h i) = tauVMark (isProP_DM α h) j k (dmGen α h) i :=
  dmTauVHom_gen α h j k i

@[simp] theorem dmTauDEquiv_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dmTauDEquiv α h k (dmGen α h i) = tauDMark (isProP_DM α h) k (dmGen α h) i :=
  dmTauDHom_gen α h k i

/-! #### The three `τ` families on `D_N` -/

/-- `τ_{v_j}(k)` on `D_N`. -/
noncomputable def dnTauUHom (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (tauUMark (isProP_DN α h) j k (dnGen α h))
    (by rw [nRelWord_tauUMark]; exact dn_relation α h)

/-- `τ_{u_j}(k)` on `D_N`. -/
noncomputable def dnTauVHom (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (tauVMark (isProP_DN α h) j k (dnGen α h))
    (by rw [nRelWord_tauVMark]; exact dn_relation α h)

/-- `τ_σ(k)` on `D_N` — memo §5.1's `τ_σ` proper, since for `N` the pair `(c,d)` is `(σ, x₂)`. -/
noncomputable def dnTauDHom (k : ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (tauDMark (isProP_DN α h) k (dnGen α h))
    (by rw [nRelWord_tauDMark]; exact dn_relation α h)

@[simp] theorem dnTauUHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauUHom α h j k (dnGen α h i) = tauUMark (isProP_DN α h) j k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnTauVHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauVHom α h j k (dnGen α h i) = tauVMark (isProP_DN α h) j k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnTauDHom_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauDHom α h k (dnGen α h i) = tauDMark (isProP_DN α h) k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

/-- **`τ_{v_j}(k)` as a continuous automorphism of `D_N`**. -/
noncomputable def dnTauUEquiv (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  dnParamEquiv α h (dnTauUHom α h j) (tauUMark (isProP_DN α h) j) (dnTauUHom_gen α h j)
    (fun k f m i => map_tauUMark (isProP_DN α h) (isProP_DN α h) f j k m i)
    (fun k l m => tauUMark_tauUMark _ j k l m) (fun m => tauUMark_zero _ j m) k

/-- **`τ_{u_j}(k)` as a continuous automorphism of `D_N`**. -/
noncomputable def dnTauVEquiv (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  dnParamEquiv α h (dnTauVHom α h j) (tauVMark (isProP_DN α h) j) (dnTauVHom_gen α h j)
    (fun k f m i => map_tauVMark (isProP_DN α h) (isProP_DN α h) f j k m i)
    (fun k l m => tauVMark_tauVMark _ j k l m) (fun m => tauVMark_zero _ j m) k

/-- **`τ_σ(k)` as a continuous automorphism of `D_N`**. -/
noncomputable def dnTauDEquiv (k : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  dnParamEquiv α h (dnTauDHom α h) (tauDMark (isProP_DN α h)) (dnTauDHom_gen α h)
    (fun k f m i => map_tauDMark (isProP_DN α h) (isProP_DN α h) f k m i)
    (fun k l m => tauDMark_tauDMark _ k l m) (fun m => tauDMark_zero _ m) k

@[simp] theorem dnTauUEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauUEquiv α h j k (dnGen α h i) = tauUMark (isProP_DN α h) j k (dnGen α h) i :=
  dnTauUHom_gen α h j k i

@[simp] theorem dnTauVEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauVEquiv α h j k (dnGen α h i) = tauVMark (isProP_DN α h) j k (dnGen α h) i :=
  dnTauVHom_gen α h j k i

@[simp] theorem dnTauDEquiv_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauDEquiv α h k (dnGen α h i) = tauDMark (isProP_DN α h) k (dnGen α h) i :=
  dnTauDHom_gen α h k i

end Assembly

end MarkedCore

end Dyadic

end GQ2
