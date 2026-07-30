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

end MarkedCore

end Dyadic

end GQ2
