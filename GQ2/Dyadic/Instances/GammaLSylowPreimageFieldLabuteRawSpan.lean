/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageHandles

/-!
# The raw variable-rank Labute span

This file separates the presentation-theoretic raw span problem from every cyclotomic
character condition.  The generic two-central-series step generates `Z_k` from independent
square atoms `p²` and bracket atoms `[p,g]`, with `p` of depth `k-1`.  The literal improved
square relator supplies every bracket row, including all handle rows, but its `x₁` coordinate
is the diagonal atom `p²[p,x₁]`.  Consequently the exact mismatch with generic tower
generation is the ability to recover the pure square atoms from the raw shift span.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## Raw depth corrections and their literal shift -/

/-- A depth-`k-1` correction with no cyclotomic character constraint. -/
structure RawDepthCorrection
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) where
  correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)

@[ext]
theorem RawDepthCorrection.ext
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} {V V' : RawDepthCorrection G h k}
    (H : V.correction = V'.correction) : V = V' := by
  cases V
  cases V'
  cases H
  rfl

protected noncomputable def RawDepthCorrection.one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} : RawDepthCorrection G h k where
  correction _ := 1
  depth _ := Subgroup.one_mem _

protected noncomputable def RawDepthCorrection.mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (V V' : RawDepthCorrection G h k) : RawDepthCorrection G h k where
  correction i := V.correction i * V'.correction i
  depth i := Subgroup.mul_mem _ (V.depth i) (V'.depth i)

protected noncomputable def RawDepthCorrection.inv
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (V : RawDepthCorrection G h k) : RawDepthCorrection G h k where
  correction i := (V.correction i)⁻¹
  depth i := Subgroup.inv_mem _ (V.depth i)

noncomputable instance
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} : Group (RawDepthCorrection G h k) where
  one := RawDepthCorrection.one
  mul := RawDepthCorrection.mul
  inv := RawDepthCorrection.inv
  mul_assoc V₁ V₂ V₃ := by ext i; exact mul_assoc _ _ _
  one_mul V := by ext i; exact one_mul _
  mul_one V := by ext i; exact mul_one _
  inv_mul_cancel V := by ext i; exact inv_mul_cancel _

@[simp] theorem RawDepthCorrection.one_correction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (i : Fin (SqCore.sqRank h)) :
    (1 : RawDepthCorrection G h k).correction i = 1 := rfl

@[simp] theorem RawDepthCorrection.mul_correction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (V V' : RawDepthCorrection G h k) (i : Fin (SqCore.sqRank h)) :
    (V * V').correction i = V.correction i * V'.correction i := rfl

/-- The literal improved-relator shift on all raw depth corrections. -/
noncomputable def rawDepthShiftHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) : RawDepthCorrection G h k →* zLayer G k where
  toFun V := ⟨sqCoreHandleDbarWord base V.correction,
    sqCoreHandleDbarWord_mem_zLayer h k hk base V.correction V.depth⟩
  map_one' := by
    apply Subtype.ext
    exact sqCoreHandleDbarWord_one base
  map_mul' V V' := by
    apply Subtype.ext
    exact sqCoreHandleDbarWord_mul h k hk base V.depth V'.depth

/-- A raw correction supported at one generator coordinate. -/
noncomputable def rawDepthCoordinateCorrection
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (i : Fin (SqCore.sqRank h))
    (p : lambdaImage G (k - 1) (k + 1)) : RawDepthCorrection G h k where
  correction j := if j = i then p.1 else 1
  depth j := by
    by_cases hji : j = i
    · simpa [hji] using p.2
    · simp [hji]

@[simp] theorem rawDepthCoordinateCorrection_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (i j : Fin (SqCore.sqRank h))
    (p : lambdaImage G (k - 1) (k + 1)) :
    (rawDepthCoordinateCorrection i p : RawDepthCorrection G h k).correction j =
      if j = i then p.1 else 1 := rfl

/-! ## Exact one-coordinate rows -/

/-- The raw `σ`-correction row is `[p,x₀]`. -/
theorem rawDepthShiftHom_zero_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom base hk) (rawDepthCoordinateCorrection 0 p)).1 =
      commP p.1 (base 1) := by
  have hu0 : ∀ j : Fin h, SqCore.sqHandleIdxU j ≠ (0 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_zero] at hv
    omega
  have hv0 : ∀ j : Fin h, SqCore.sqHandleIdxV j ≠ (0 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_zero] at hv
    omega
  have h10 : (1 : Fin (SqCore.sqRank h)) ≠ 0 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_one, SqCore.sqVal_zero] at hv
    omega
  have h20 : (2 : Fin (SqCore.sqRank h)) ≠ 0 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_two, SqCore.sqVal_zero] at hv
    omega
  have hhandle : sqHandleDbarWord base
      (rawDepthCoordinateCorrection 0 p : RawDepthCorrection G h k).correction = 1 := by
    simp [sqHandleDbarWord, rawDepthCoordinateCorrection_apply, hu0, hv0, commP]
  change sqCoreHandleDbarWord base
      (rawDepthCoordinateCorrection 0 p : RawDepthCorrection G h k).correction = _
  rw [sqCoreHandleDbarWord, hhandle, mul_one]
  simp [rawDepthCoordinateCorrection_apply, dbarWordR2, commP, h10, h20]

/-- The raw `x₀`-correction row is `[p,σ]`. -/
theorem rawDepthShiftHom_one_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom base hk) (rawDepthCoordinateCorrection 1 p)).1 =
      commP p.1 (base 0) := by
  have hu1 : ∀ j : Fin h, SqCore.sqHandleIdxU j ≠ (1 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_one] at hv
    omega
  have hv1 : ∀ j : Fin h, SqCore.sqHandleIdxV j ≠ (1 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_one] at hv
    omega
  have h01 : (0 : Fin (SqCore.sqRank h)) ≠ 1 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_zero, SqCore.sqVal_one] at hv
    omega
  have h21 : (2 : Fin (SqCore.sqRank h)) ≠ 1 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_two, SqCore.sqVal_one] at hv
    omega
  have hhandle : sqHandleDbarWord base
      (rawDepthCoordinateCorrection 1 p : RawDepthCorrection G h k).correction = 1 := by
    simp [sqHandleDbarWord, rawDepthCoordinateCorrection_apply, hu1, hv1, commP]
  change sqCoreHandleDbarWord base
      (rawDepthCoordinateCorrection 1 p : RawDepthCorrection G h k).correction = _
  rw [sqCoreHandleDbarWord, hhandle, mul_one]
  simp [rawDepthCoordinateCorrection_apply, dbarWordR2, commP, h01, h21]

/-- The raw `x₁`-correction row is the inseparable diagonal `p²[p,x₁]`. -/
theorem rawDepthShiftHom_two_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom base hk) (rawDepthCoordinateCorrection 2 p)).1 =
      p.1 ^ 2 * commP p.1 (base 2) := by
  have hu2 : ∀ j : Fin h, SqCore.sqHandleIdxU j ≠ (2 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_two] at hv
    omega
  have hv2 : ∀ j : Fin h, SqCore.sqHandleIdxV j ≠ (2 : Fin (SqCore.sqRank h)) := by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_two] at hv
    omega
  have h02 : (0 : Fin (SqCore.sqRank h)) ≠ 2 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_zero, SqCore.sqVal_two] at hv
    omega
  have h12 : (1 : Fin (SqCore.sqRank h)) ≠ 2 := by
    intro hj
    have hv := congrArg Fin.val hj
    rw [SqCore.sqVal_one, SqCore.sqVal_two] at hv
    omega
  have hhandle : sqHandleDbarWord base
      (rawDepthCoordinateCorrection 2 p : RawDepthCorrection G h k).correction = 1 := by
    simp [sqHandleDbarWord, rawDepthCoordinateCorrection_apply, hu2, hv2, commP]
  change sqCoreHandleDbarWord base
      (rawDepthCoordinateCorrection 2 p : RawDepthCorrection G h k).correction = _
  rw [sqCoreHandleDbarWord, hhandle, mul_one]
  simp [rawDepthCoordinateCorrection_apply, dbarWordR2, commP, h02, h12]

/-- A finite product with a unique nontrivial factor evaluates to that factor. -/
private theorem list_map_prod_eq_single_of_nodup_raw
    {H Ι : Type*} [Monoid H] (l : List Ι) (j : Ι) (f : Ι → H)
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

/-- The raw `U_j` handle row is `[p,V_j]`. -/
theorem rawDepthShiftHom_handleU_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (j : Fin h) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom base hk)
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j) p)).1 =
      commP p.1 (base (SqCore.sqHandleIdxV j)) := by
  let correction := (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j) p :
    RawDepthCorrection G h k).correction
  have hVU : ∀ l : Fin h,
      SqCore.sqHandleIdxV l ≠ SqCore.sqHandleIdxU j := by
    intro l hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqHandleIdxV_val, SqCore.sqHandleIdxU_val] at hv
    omega
  have hUU : ∀ l : Fin h, l ≠ j →
      SqCore.sqHandleIdxU l ≠ SqCore.sqHandleIdxU j := by
    intro l hlj hEq
    apply hlj
    apply Fin.ext
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqHandleIdxU_val, SqCore.sqHandleIdxU_val] at hv
    omega
  have h0 : (0 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxU j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_zero, SqCore.sqHandleIdxU_val] at hv
    omega
  have h1 : (1 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxU j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_one, SqCore.sqHandleIdxU_val] at hv
    omega
  have h2 : (2 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxU j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_two, SqCore.sqHandleIdxU_val] at hv
    omega
  have hcore : dbarWordR2 (base 0) (base 1) (base 2)
      ![correction 0, correction 1, correction 2] = 1 := by
    simp [correction, rawDepthCoordinateCorrection_apply, dbarWordR2, commP,
      h0, h1, h2]
  let f := fun l : Fin h ↦
    commP (correction (SqCore.sqHandleIdxV l))
        (base (SqCore.sqHandleIdxU l)) *
      commP (correction (SqCore.sqHandleIdxU l))
        (base (SqCore.sqHandleIdxV l))
  have hf : ∀ l ∈ List.finRange h, l ≠ j → f l = 1 := by
    intro l _ hlj
    simp [f, correction, rawDepthCoordinateCorrection_apply, hVU l,
      hUU l hlj, commP]
  have hprod : ((List.finRange h).map f).prod = f j :=
    list_map_prod_eq_single_of_nodup_raw (List.finRange h) j f
      (by simp) (List.nodup_finRange h) hf
  have hhandle : sqHandleDbarWord base correction =
      commP p.1 (base (SqCore.sqHandleIdxV j)) := by
    rw [sqHandleDbarWord]
    change ((List.finRange h).map f).prod = _
    rw [hprod]
    simp [f, correction, rawDepthCoordinateCorrection_apply, hVU j, commP]
  change sqCoreHandleDbarWord base correction = _
  rw [sqCoreHandleDbarWord, hcore, one_mul, hhandle]

/-- The raw `V_j` handle row is `[p,U_j]`. -/
theorem rawDepthShiftHom_handleV_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (j : Fin h) (p : lambdaImage G (k - 1) (k + 1)) :
    ((rawDepthShiftHom base hk)
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j) p)).1 =
      commP p.1 (base (SqCore.sqHandleIdxU j)) := by
  let correction := (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j) p :
    RawDepthCorrection G h k).correction
  have hUV : ∀ l : Fin h,
      SqCore.sqHandleIdxU l ≠ SqCore.sqHandleIdxV j := by
    intro l hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqHandleIdxU_val, SqCore.sqHandleIdxV_val] at hv
    omega
  have hVV : ∀ l : Fin h, l ≠ j →
      SqCore.sqHandleIdxV l ≠ SqCore.sqHandleIdxV j := by
    intro l hlj hEq
    apply hlj
    apply Fin.ext
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqHandleIdxV_val, SqCore.sqHandleIdxV_val] at hv
    omega
  have h0 : (0 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxV j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_zero, SqCore.sqHandleIdxV_val] at hv
    omega
  have h1 : (1 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxV j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_one, SqCore.sqHandleIdxV_val] at hv
    omega
  have h2 : (2 : Fin (SqCore.sqRank h)) ≠ SqCore.sqHandleIdxV j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rw [SqCore.sqVal_two, SqCore.sqHandleIdxV_val] at hv
    omega
  have hcore : dbarWordR2 (base 0) (base 1) (base 2)
      ![correction 0, correction 1, correction 2] = 1 := by
    simp [correction, rawDepthCoordinateCorrection_apply, dbarWordR2, commP,
      h0, h1, h2]
  let f := fun l : Fin h ↦
    commP (correction (SqCore.sqHandleIdxV l))
        (base (SqCore.sqHandleIdxU l)) *
      commP (correction (SqCore.sqHandleIdxU l))
        (base (SqCore.sqHandleIdxV l))
  have hf : ∀ l ∈ List.finRange h, l ≠ j → f l = 1 := by
    intro l _ hlj
    simp [f, correction, rawDepthCoordinateCorrection_apply, hUV l,
      hVV l hlj, commP]
  have hprod : ((List.finRange h).map f).prod = f j :=
    list_map_prod_eq_single_of_nodup_raw (List.finRange h) j f
      (by simp) (List.nodup_finRange h) hf
  have hhandle : sqHandleDbarWord base correction =
      commP p.1 (base (SqCore.sqHandleIdxU j)) := by
    rw [sqHandleDbarWord]
    change ((List.finRange h).map f).prod = _
    rw [hprod]
    simp [f, correction, rawDepthCoordinateCorrection_apply, hUV j, commP]
  change sqCoreHandleDbarWord base correction = _
  rw [sqCoreHandleDbarWord, hcore, one_mul, hhandle]

/-! ## The raw span and the exact central-tower mismatch -/

/-- The raw literal-shift image, viewed as a subgroup of the ambient level quotient. -/
noncomputable def rawShiftSpan
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) : Subgroup (levelQuot G (k + 1)) :=
  Subgroup.map (zLayer G k).subtype (rawDepthShiftHom base hk).range

/-- Every literal raw shift lies in the raw shift span. -/
theorem rawDepthShift_mem_rawShiftSpan
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (V : RawDepthCorrection G h k) :
    ((rawDepthShiftHom base hk) V).1 ∈ rawShiftSpan base hk := by
  exact ⟨(rawDepthShiftHom base hk) V, ⟨V, rfl⟩, rfl⟩

/-- The raw shift span is contained in the central defect layer. -/
theorem rawShiftSpan_le_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) : rawShiftSpan base hk ≤ zLayer G k := by
  rintro z ⟨q, _, rfl⟩
  exact q.2

/-- The sole extra atom family not separated by the literal improved `r₂` rows: every
pure square of a depth-`k-1` element belongs to the raw shift span. -/
def RawPureSquareSpanSupply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) : Prop :=
  ∀ p : lambdaImage G (k - 1) (k + 1), p.1 ^ 2 ∈ rawShiftSpan base hk

/-- Under the pure-square supply, every bracket against a displayed generator lies in the
raw shift span.  The handle cases use the literal improved handle rows; the `x₁` case
divides its diagonal row by the supplied square. -/
theorem rawBracket_base_mem_rawShiftSpan
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k) (Hsq : RawPureSquareSpanSupply base hk)
    (p : lambdaImage G (k - 1) (k + 1))
    (i : Fin (SqCore.sqRank h)) :
    commP p.1 (base i) ∈ rawShiftSpan base hk := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h := rawDepthShift_mem_rawShiftSpan base hk
      (rawDepthCoordinateCorrection 1 p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_one_apply base hk p] at h
  · have h := rawDepthShift_mem_rawShiftSpan base hk
      (rawDepthCoordinateCorrection 0 p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_zero_apply base hk p] at h
  · have hdiag := rawDepthShift_mem_rawShiftSpan base hk
      (rawDepthCoordinateCorrection 2 p : RawDepthCorrection G h k)
    rw [rawDepthShiftHom_two_apply base hk p] at hdiag
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Hsq p)) hdiag
    simpa only [inv_mul_cancel_left] using h
  · have hmem := rawDepthShift_mem_rawShiftSpan base hk
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j) p :
        RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_handleV_apply base hk j p] at hmem
  · have hmem := rawDepthShift_mem_rawShiftSpan base hk
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j) p :
        RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_handleU_apply base hk j p] at hmem

open scoped commutatorElement in
private theorem commutatorElement_eq_commP_inv_raw
    {H : Type*} [Group H] (v g : H) : ⁅v, g⁆ = commP v⁻¹ g⁻¹ := by
  simp only [commutatorElement_def, commP, inv_inv]

/-- Generic square/commutator generation now closes the whole central layer.  No
cyclotomic character statement is used: the only additional input is the pure-square
family isolated above. -/
theorem rawShiftSpan_eq_zLayer_of_pureSquares
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hbase : Subgroup.closure (Set.range base) = ⊤)
    (Hsq : RawPureSquareSpanSupply base hk) :
    rawShiftSpan base hk = zLayer G k := by
  apply le_antisymm (rawShiftSpan_le_zLayer base hk)
  intro q hq
  have hq' : q ∈ lambdaImage G (k - 1 + 1) (k + 1) := by
    rwa [show k - 1 + 1 = k by omega]
  refine lambdaImage_induction G hfg hpro (j := k - 1) (by omega)
    (p := fun z ↦ z ∈ rawShiftSpan base hk) ?_ ?_
    (Subgroup.one_mem _) (fun _ _ ↦ Subgroup.mul_mem _) (fun _ ↦ Subgroup.inv_mem _) hq'
  · intro v hv
    let p : lambdaImage G (k - 1) (k + 1) :=
      ⟨levelMk G (k + 1) v, ⟨v, hv, rfl⟩⟩
    simpa only [map_pow] using Hsq p
  · intro v hv g
    let p : lambdaImage G (k - 1) (k + 1) :=
      ⟨(levelMk G (k + 1) v)⁻¹, ⟨v⁻¹, Subgroup.inv_mem _ hv, by rw [map_inv]⟩⟩
    have hp : ∀ z : levelQuot G (k + 1),
        commP p.1 z ∈ rawShiftSpan base hk := by
      intro z
      have hz : z ∈ Subgroup.closure (Set.range base) := by rw [hbase]; trivial
      refine Subgroup.closure_induction
        (p := fun x _ ↦ commP p.1 x ∈ rawShiftSpan base hk) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        exact rawBracket_base_mem_rawShiftSpan base hk Hsq p i
      · simp [commP]
      · intro x y _ _ hx hy
        rw [commP_mul_right_of_mem k hk p.2 x y]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [commP_inv_right_of_mem k hk p.2 x]
        exact Subgroup.inv_mem _ hx
    rw [map_commutatorElement, commutatorElement_eq_commP_inv_raw]
    exact hp (levelMk G (k + 1) g)⁻¹

/-- With a generating displayed tuple, the pure-square family is not just sufficient but
equivalent to raw shift surjectivity onto the central layer.  This pinpoints the exact gap
between `finite_levelQuot_step`-style square/bracket generation and the literal `r₂` shift. -/
theorem rawPureSquareSpanSupply_iff_rawShiftSpan_eq_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ} (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hbase : Subgroup.closure (Set.range base) = ⊤) :
    RawPureSquareSpanSupply base hk ↔ rawShiftSpan base hk = zLayer G k := by
  constructor
  · exact rawShiftSpan_eq_zLayer_of_pureSquares base hk hfg hpro hbase
  · intro hspan p
    rw [hspan]
    exact sq_mem_zLayer k hk p.2

/-! ## Specialization to a variable-rank field stage -/

namespace SqCyclotomicStageTuple

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The pure-square mismatch for the canonical lift of a field-stage tuple. -/
def RawPureSquareSpanSupplyAt {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) : Prop :=
  RawPureSquareSpanSupply
    (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk

/-- Raw defect reachability is exactly membership of the current inverse defect in the
literal raw shift span.  This equivalence has no character refinement hidden in it. -/
theorem sqRawDefectReachable_iff_defect_mem_rawShiftSpan
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    sqRawDefectReachable (maxProPQuotient 2 (GalK K)) h k T.generators ↔
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ ∈
        rawShiftSpan
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk := by
  let G := maxProPQuotient 2 (GalK K)
  let base : Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i)
  constructor
  · rintro ⟨correction, hdepth, hkill⟩
    let V : RawDepthCorrection G h k := ⟨correction, hdepth⟩
    have hmem := rawDepthShift_mem_rawShiftSpan base hk V
    change sqCoreHandleDbarWord base correction ∈ rawShiftSpan base hk at hmem
    have hword : sqCoreHandleDbarWord base correction =
        (sqStageDefect G h k T.generators)⁻¹ := by
      rw [sqCoreHandleDbarWord,
        ← stageShift_eq_dbarWordR2_mul_sqHandleDbarWord
          h k hk base correction hdepth, hkill]
    rw [hword] at hmem
    exact hmem
  · intro hmem
    obtain ⟨z, ⟨V, hV⟩, hz⟩ := hmem
    subst z
    refine ⟨V.correction, V.depth, ?_⟩
    rw [stageShift_eq_dbarWordR2_mul_sqHandleDbarWord
      h k hk base V.correction V.depth]
    change (rawDepthShiftHom base hk V).1 = _
    exact hz

/-- The pure-square supply is exactly enough for variable-rank raw defect reachability.
This is an honest reduction: generic tower generation handles all square/bracket atoms,
and the literal handle formulas handle every added hyperbolic pair. -/
theorem sqRawDefectReachable_of_pureSquareSpan
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hsq : RawPureSquareSpanSupplyAt T hk) :
    sqRawDefectReachable (maxProPQuotient 2 (GalK K)) h k T.generators := by
  let G := maxProPQuotient 2 (GalK K)
  let base : Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i)
  have hbase : Subgroup.closure (Set.range base) = ⊤ := by
    refine eq_top_of_map_levelProj_eq_top G hfg isProP_maxProPQuotient (by omega) ?_
    have himg : (GQ2.Roe.Labute.levelProj G k) '' Set.range base =
        Set.range T.generators := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i ↦ levelProj_canonLift G k (T.generators i))
    rw [MonoidHom.map_closure, himg, T.topGen]
  have hspan : rawShiftSpan base hk = zLayer G k :=
    rawShiftSpan_eq_zLayer_of_pureSquares base hk hfg isProP_maxProPQuotient
      hbase Hsq
  have hdefect : (sqStageDefect G h k T.generators)⁻¹ ∈ rawShiftSpan base hk := by
    rw [hspan]
    exact Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation)
  obtain ⟨z, ⟨V, hV⟩, hz⟩ := hdefect
  subst z
  refine ⟨V.correction, V.depth, ?_⟩
  rw [stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base V.correction V.depth]
  change (rawDepthShiftHom base hk V).1 = _
  exact hz

end SqCyclotomicStageTuple

#print axioms rawDepthShiftHom_handleU_apply
#print axioms rawDepthShiftHom_handleV_apply
#print axioms rawShiftSpan_eq_zLayer_of_pureSquares
#print axioms rawPureSquareSpanSupply_iff_rawShiftSpan_eq_zLayer
#print axioms SqCyclotomicStageTuple.sqRawDefectReachable_iff_defect_mem_rawShiftSpan
#print axioms SqCyclotomicStageTuple.sqRawDefectReachable_of_pureSquareSpan

end

end GQ2.Dyadic.LSquare
