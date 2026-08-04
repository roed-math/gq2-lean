/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteRawSpan

/-!
# The variable-rank raw span step

This file generalizes the square-transport and tail-absorption part of the fixed-rank
`SpanStep.r2` proof.  The target is the literal variable-rank raw shift image together with
the `2^(k-1)` tails at every generator except the twisted `x₁` slot (index `2`).

The successor step is uniform in the rank: the three core coordinates use the existing
`dbarWordR2_sq` identity and every hyperbolic handle is transported by the same bracket-square
identity.  The cubic base case remains a separate proposition; this matches the architecture
of the existing fixed-rank proof, where `span_base_r2` is a substantial calculation independent
of `span_step_r2`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## Layer helpers -/

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {h : ℕ}

private theorem sq_mem_lambdaImage_succ_raw {j m : ℕ} {q : levelQuot G m}
    (hq : q ∈ lambdaImage G j m) : q ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, by rw [map_pow]⟩

open scoped commutatorElement in
private theorem commP_mem_lambdaImage_add_raw {a b m : ℕ}
    {v g : levelQuot G m} (hv : v ∈ lambdaImage G a m)
    (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have hcomm : commP x y = ⁅x⁻¹, y⁻¹⁆ := by
    simp only [commutatorElement_def, commP, inv_inv]
  rw [hcomm]
  exact commutator_mem_twoCentralSeries_add G
    ((twoCentralSeries G a).inv_mem hx) ((twoCentralSeries G b).inv_mem hy)

private theorem lambdaImage_one_eq_top_raw (m : ℕ) :
    lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

private theorem commP_mem_lambdaImage_succ_raw {j m : ℕ}
    {v : levelQuot G m} (hv : v ∈ lambdaImage G j m) (g : levelQuot G m) :
    commP v g ∈ lambdaImage G (j + 1) m :=
  commP_mem_lambdaImage_add_raw hv (by rw [lambdaImage_one_eq_top_raw]; trivial)

private theorem dbarWordR2_mem_lambdaImage_succ_raw {j m : ℕ}
    (s x y : levelQuot G m) {w : Fin 3 → levelQuot G m}
    (hw : ∀ i, w i ∈ lambdaImage G j m) :
    dbarWordR2 s x y w ∈ lambdaImage G (j + 1) m := by
  simp only [dbarWordR2]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (sq_mem_lambdaImage_succ_raw (hw 2))
        (commP_mem_lambdaImage_succ_raw (hw 2) y))
      (commP_mem_lambdaImage_succ_raw (hw 0) x))
    (commP_mem_lambdaImage_succ_raw (hw 1) s)

/-! ## Square transport for the full improved word -/

private theorem list_prod_sq_of_mem_lambdaImage_pred
    {k : ℕ} (hk : 3 ≤ k) {Ι : Type*} (l : List Ι)
    (f : Ι → levelQuot G (k + 1))
    (hf : ∀ i ∈ l, f i ∈ lambdaImage G (k - 1) (k + 1)) :
    (l.map f).prod ^ 2 = (l.map fun i ↦ f i ^ 2).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hi := hf i (by simp)
      have htail : (l.map f).prod ∈ lambdaImage G (k - 1) (k + 1) := by
        apply Subgroup.list_prod_mem
        intro z hz
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        exact hf j (List.mem_cons_of_mem _ hj)
      rw [List.map_cons, List.prod_cons,
        sq_mul_of_mem_lambdaImage_pred k hk hi htail,
        ih (fun j hj ↦ hf j (List.mem_cons_of_mem _ hj)),
        List.map_cons, List.prod_cons]

/-- The entire improved handle block satisfies the same square-transport identity as one
bracket row. -/
theorem sqHandleDbarWord_sq
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 4 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 2) (k + 1)) :
    sqHandleDbarWord base correction ^ 2 =
      sqHandleDbarWord base (fun i ↦ correction i ^ 2) := by
  let f := fun j : Fin h ↦
    commP (correction (SqCore.sqHandleIdxV j))
        (base (SqCore.sqHandleIdxU j)) *
      commP (correction (SqCore.sqHandleIdxU j))
        (base (SqCore.sqHandleIdxV j))
  have hfactor : ∀ j ∈ List.finRange h,
      f j ∈ lambdaImage G (k - 1) (k + 1) := by
    intro j _
    exact Subgroup.mul_mem _
      (by
        have hmem := commP_mem_lambdaImage_succ_raw
          (hdepth (SqCore.sqHandleIdxV j)) (base (SqCore.sqHandleIdxU j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem)
      (by
        have hmem := commP_mem_lambdaImage_succ_raw
          (hdepth (SqCore.sqHandleIdxU j)) (base (SqCore.sqHandleIdxV j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem)
  rw [sqHandleDbarWord, list_prod_sq_of_mem_lambdaImage_pred (by omega)
    (List.finRange h) f hfactor, sqHandleDbarWord]
  congr 1
  apply List.map_congr_left
  intro j _
  dsimp only [f]
  rw [sq_mul_of_mem_lambdaImage_pred k (by omega)
      (by
        have hmem := commP_mem_lambdaImage_succ_raw
          (hdepth (SqCore.sqHandleIdxV j)) (base (SqCore.sqHandleIdxU j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem)
      (by
        have hmem := commP_mem_lambdaImage_succ_raw
          (hdepth (SqCore.sqHandleIdxU j)) (base (SqCore.sqHandleIdxV j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth (SqCore.sqHandleIdxV j)),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth (SqCore.sqHandleIdxU j))]

/-- Square transport for the complete core-plus-handle shift.  This is the exact
variable-rank replacement for the fixed-rank use of `dbarWordR2_sq`. -/
theorem sqCoreHandleDbarWord_sq
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 4 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 2) (k + 1)) :
    sqCoreHandleDbarWord base correction ^ 2 =
      sqCoreHandleDbarWord base (fun i ↦ correction i ^ 2) := by
  have hcoreDepth : ∀ i : Fin 3,
      ![correction 0, correction 1, correction 2] i ∈
        lambdaImage G (k - 2) (k + 1) := by
    intro i
    fin_cases i
    · exact hdepth 0
    · exact hdepth 1
    · exact hdepth 2
  have hcore : dbarWordR2 (base 0) (base 1) (base 2)
      ![correction 0, correction 1, correction 2] ∈
        lambdaImage G (k - 1) (k + 1) := by
    have hmem := dbarWordR2_mem_lambdaImage_succ_raw (G := G)
      (base 0) (base 1) (base 2) hcoreDepth
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  have hhandle : sqHandleDbarWord base correction ∈
      lambdaImage G (k - 1) (k + 1) := by
    rw [sqHandleDbarWord]
    apply Subgroup.list_prod_mem
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨j, _, rfl⟩ := hz
    exact Subgroup.mul_mem _
      (by
        have hmem := commP_mem_lambdaImage_succ_raw (G := G)
          (hdepth (SqCore.sqHandleIdxV j)) (base (SqCore.sqHandleIdxU j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem)
      (by
        have hmem := commP_mem_lambdaImage_succ_raw (G := G)
          (hdepth (SqCore.sqHandleIdxU j)) (base (SqCore.sqHandleIdxV j))
        rwa [show k - 2 + 1 = k - 1 by omega] at hmem)
  rw [sqCoreHandleDbarWord,
    sq_mul_of_mem_lambdaImage_pred k (by omega) hcore hhandle,
    dbarWordR2_sq k hk _ _ _ hcoreDepth,
    sqHandleDbarWord_sq h k hk base correction hdepth,
    sqCoreHandleDbarWord]
  rfl

/-- Projection through the tower commutes with the full literal shift word. -/
theorem levelProj_sqCoreHandleDbarWord
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 2)) :
    levelProj G (k + 1) (sqCoreHandleDbarWord base correction) =
      sqCoreHandleDbarWord (fun i ↦ levelProj G (k + 1) (base i))
        (fun i ↦ levelProj G (k + 1) (correction i)) := by
  rw [sqCoreHandleDbarWord, sqCoreHandleDbarWord, map_mul, map_dbarWordR2]
  have hcoreCorrection :
      (fun i : Fin 3 ↦ levelProj G (k + 1)
        (![correction 0, correction 1, correction 2] i)) =
      ![levelProj G (k + 1) (correction 0),
        levelProj G (k + 1) (correction 1),
        levelProj G (k + 1) (correction 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoreCorrection]
  rw [sqHandleDbarWord, sqHandleDbarWord, map_list_prod, List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, commP, map_mul, map_inv]

/-! ## The augmented variable-rank target -/

/-- The coherent displayed tuple in `Q_(k+1)` associated to fixed ambient generators. -/
noncomputable def rawMarkedBase
    (generators : Fin (SqCore.sqRank h) → G) (k : ℕ) :
    Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
  fun i ↦ levelMk G (k + 1) (generators i)

/-- Relator-adapted tails: every generator except the twisted `x₁` slot. -/
def rawTailAtomSet
    (generators : Fin (SqCore.sqRank h) → G) (k : ℕ) :
    Set (levelQuot G (k + 1)) :=
  {z | ∃ i : Fin (SqCore.sqRank h), i ≠ 2 ∧
    z = rawMarkedBase generators k i ^ 2 ^ (k - 1)}

/-- The span of the non-twisted tails. -/
noncomputable def rawTailSpan
    (generators : Fin (SqCore.sqRank h) → G) (k : ℕ) :
    Subgroup (levelQuot G (k + 1)) :=
  Subgroup.closure (rawTailAtomSet generators k)

/-- The variable-rank `r₂` target: literal raw shifts plus every non-twisted tail. -/
noncomputable def rawAugmentedSpan
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (levelQuot G (k + 1)) :=
  rawShiftSpan (rawMarkedBase generators k) hk ⊔ rawTailSpan generators k

/-- The cubic base proposition isolated from the uniform successor step. -/
def RawAugmentedSpanBaseSupply
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G) : Prop :=
  zLayer G 3 ≤ rawAugmentedSpan generators 3 (by omega)

/-! ## Tail and raw-shift inclusions -/

theorem rawShiftSpan_le_rawAugmentedSpan
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G) {k : ℕ} (hk : 3 ≤ k) :
    rawShiftSpan (rawMarkedBase generators k) hk ≤ rawAugmentedSpan generators k hk :=
  le_sup_left

theorem rawTailSpan_le_rawAugmentedSpan
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G) {k : ℕ} (hk : 3 ≤ k) :
    rawTailSpan generators k ≤ rawAugmentedSpan generators k hk :=
  le_sup_right

theorem rawTail_mem_rawAugmentedSpan
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G) {k : ℕ} (hk : 3 ≤ k)
    (i : Fin (SqCore.sqRank h)) (hi : i ≠ 2) :
    rawMarkedBase generators k i ^ 2 ^ (k - 1) ∈ rawAugmentedSpan generators k hk :=
  rawTailSpan_le_rawAugmentedSpan generators hk
    (Subgroup.subset_closure ⟨i, hi, rfl⟩)

/-! ## The lift-with-square engine -/

/-- Classes at level `k+1` which possess a depth-`k` lift whose square lies in `T`. -/
private noncomputable def rawLiftSq (k : ℕ) (hk : 3 ≤ k)
    (T : Subgroup (levelQuot G (k + 2))) : Subgroup (levelQuot G (k + 1)) where
  carrier := {q | ∃ q' ∈ lambdaImage G k (k + 2),
    levelProj G (k + 1) q' = q ∧ q' ^ 2 ∈ T}
  one_mem' := ⟨1, Subgroup.one_mem _, map_one _, by simp⟩
  mul_mem' := by
    rintro x y ⟨x', hx', hxp, hxs⟩ ⟨y', hy', hyp, hys⟩
    refine ⟨x' * y', Subgroup.mul_mem _ hx' hy', by rw [map_mul, hxp, hyp], ?_⟩
    rw [sq_mul_of_mem_lambdaImage_pred (k + 1) (by omega) hx' hy']
    exact Subgroup.mul_mem _ hxs hys
  inv_mem' := by
    rintro x ⟨x', hx', hxp, hxs⟩
    exact ⟨x'⁻¹, Subgroup.inv_mem _ hx', by rw [map_inv, hxp], by
      rw [inv_pow]
      exact Subgroup.inv_mem _ hxs⟩

private theorem sqCoreHandleDbarWord_mem_lambdaImage_next
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 1 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 2))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 2)) :
    sqCoreHandleDbarWord base correction ∈ lambdaImage G k (k + 2) := by
  rw [sqCoreHandleDbarWord]
  apply Subgroup.mul_mem
  · have hcore := dbarWordR2_mem_lambdaImage_succ_raw (G := G)
      (base 0) (base 1) (base 2) (w := ![correction 0, correction 1, correction 2])
      (fun i ↦ by
        fin_cases i
        · exact hdepth 0
        · exact hdepth 1
        · exact hdepth 2)
    rwa [show k - 1 + 1 = k by omega] at hcore
  · rw [sqHandleDbarWord]
    apply Subgroup.list_prod_mem
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨j, _, rfl⟩ := hz
    exact Subgroup.mul_mem _
      (by
        have hmem := commP_mem_lambdaImage_succ_raw (G := G)
          (hdepth (SqCore.sqHandleIdxV j)) (base (SqCore.sqHandleIdxU j))
        rwa [show k - 1 + 1 = k by omega] at hmem)
      (by
        have hmem := commP_mem_lambdaImage_succ_raw (G := G)
          (hdepth (SqCore.sqHandleIdxU j)) (base (SqCore.sqHandleIdxV j))
        rwa [show k - 1 + 1 = k by omega] at hmem)

private theorem rawTail_mem_rawLiftSq
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (k : ℕ) (hk : 3 ≤ k) (i : Fin (SqCore.sqRank h)) (hi : i ≠ 2) :
    rawMarkedBase generators k i ^ 2 ^ (k - 1) ∈
      rawLiftSq k hk (rawAugmentedSpan generators (k + 1) (by omega)) := by
  refine ⟨rawMarkedBase generators (k + 1) i ^ 2 ^ (k - 1), ?_, ?_, ?_⟩
  · have hmem := pow_two_pow_mem_lambdaImage
      (rawMarkedBase generators (k + 1) i) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at hmem
  · simp [rawMarkedBase]
  · rw [← pow_mul, show (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]]
    exact rawTail_mem_rawAugmentedSpan generators (by omega) i hi

/-- Every old raw-shift value lifts to a depth-`k` element whose square is a next-level
raw-shift value.  This is the handle-general square-transport step. -/
private theorem rawShiftSpan_le_rawLiftSq
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (k : ℕ) (hk : 3 ≤ k) :
    rawShiftSpan (rawMarkedBase generators k) hk ≤
      rawLiftSq k hk (rawAugmentedSpan generators (k + 1) (by omega)) := by
  rintro _ ⟨_, ⟨V, rfl⟩, rfl⟩
  choose correction' hdepth' hproj using fun i ↦
    exists_levelProj_preimage_lambdaImage (k - 1) (k + 1) (V.depth i)
  let shift' := sqCoreHandleDbarWord (rawMarkedBase generators (k + 1)) correction'
  refine ⟨shift', sqCoreHandleDbarWord_mem_lambdaImage_next h k (by omega)
    (rawMarkedBase generators (k + 1)) correction' hdepth', ?_, ?_⟩
  · change levelProj G (k + 1)
      (sqCoreHandleDbarWord (rawMarkedBase generators (k + 1)) correction') =
        sqCoreHandleDbarWord (rawMarkedBase generators k) V.correction
    rw [levelProj_sqCoreHandleDbarWord]
    have hbaseProj :
        (fun i ↦ levelProj G (k + 1) (rawMarkedBase generators (k + 1) i)) =
          rawMarkedBase generators k := by
      funext i
      rfl
    have hcorrectionProj :
        (fun i ↦ levelProj G (k + 1) (correction' i)) = V.correction := by
      funext i
      exact hproj i
    rw [hbaseProj, hcorrectionProj]
  · have hsqDepth : ∀ i, correction' i ^ 2 ∈ lambdaImage G k (k + 2) := by
      intro i
      have hmem := sq_mem_lambdaImage_succ_raw (hdepth' i)
      rwa [show k - 1 + 1 = k by omega] at hmem
    let Vnext : RawDepthCorrection G h (k + 1) :=
      ⟨fun i ↦ correction' i ^ 2, hsqDepth⟩
    have hmem := rawDepthShift_mem_rawShiftSpan
      (rawMarkedBase generators (k + 1)) (by omega) Vnext
    have hmem' := rawShiftSpan_le_rawAugmentedSpan generators (by omega) hmem
    rw [show shift' ^ 2 =
        sqCoreHandleDbarWord (rawMarkedBase generators (k + 1))
          (fun i ↦ correction' i ^ 2) by
      exact sqCoreHandleDbarWord_sq h (k + 1) (by omega)
        (rawMarkedBase generators (k + 1)) correction' hdepth']
    exact hmem'

/-- The whole old augmented target is contained in the lift-with-square subgroup. -/
private theorem rawAugmentedSpan_le_rawLiftSq
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (k : ℕ) (hk : 3 ≤ k) :
    rawAugmentedSpan generators k hk ≤
      rawLiftSq k hk (rawAugmentedSpan generators (k + 1) (by omega)) := by
  apply sup_le
  · exact rawShiftSpan_le_rawLiftSq generators k hk
  · rw [rawTailSpan, Subgroup.closure_le]
    rintro z ⟨i, hi, rfl⟩
    exact rawTail_mem_rawLiftSq generators k hk i hi

/-- The induction hypothesis at layer `k` supplies all pure-square atoms needed at layer
`k+1`. -/
theorem rawSquare_mem_augmentedSpan_succ
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer G k ≤ rawAugmentedSpan generators k hk) :
    ∀ v ∈ twoCentralSeries G k,
      levelMk G (k + 2) (v ^ 2) ∈
        rawAugmentedSpan generators (k + 1) (by omega) := by
  intro v hv
  have hold : levelMk G (k + 1) v ∈ rawAugmentedSpan generators k hk :=
    prev ⟨v, hv, rfl⟩
  obtain ⟨q', hq'depth, hq'proj, hq'sq⟩ :=
    rawAugmentedSpan_le_rawLiftSq generators k hk hold
  have hproj : levelProj G (k + 1) (levelMk G (k + 2) v) =
      levelProj G (k + 1) q' := by
    rw [levelProj_levelMk, hq'proj]
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul hproj
  rw [map_pow, hzeq, (zLayer_commute hz q').eq,
    sq_mul_zLayer (k + 1) hz]
  exact hq'sq

private theorem rawBracket_base_mem_augmentedSpan
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (k : ℕ) (hk : 3 ≤ k)
    (Hsq : ∀ p : lambdaImage G (k - 1) (k + 1),
      p.1 ^ 2 ∈ rawAugmentedSpan generators k hk)
    (p : lambdaImage G (k - 1) (k + 1))
    (i : Fin (SqCore.sqRank h)) :
    commP p.1 (rawMarkedBase generators k i) ∈ rawAugmentedSpan generators k hk := by
  have hraw : rawShiftSpan (rawMarkedBase generators k) hk ≤
      rawAugmentedSpan generators k hk := rawShiftSpan_le_rawAugmentedSpan generators hk
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · apply hraw
    have hmem := rawDepthShift_mem_rawShiftSpan (rawMarkedBase generators k) hk
      (rawDepthCoordinateCorrection 1 p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_one_apply (rawMarkedBase generators k) hk p] at hmem
  · apply hraw
    have hmem := rawDepthShift_mem_rawShiftSpan (rawMarkedBase generators k) hk
      (rawDepthCoordinateCorrection 0 p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_zero_apply (rawMarkedBase generators k) hk p] at hmem
  · have hdiag : p.1 ^ 2 * commP p.1 (rawMarkedBase generators k 2) ∈
        rawAugmentedSpan generators k hk := by
      apply hraw
      have hmem := rawDepthShift_mem_rawShiftSpan (rawMarkedBase generators k) hk
        (rawDepthCoordinateCorrection 2 p : RawDepthCorrection G h k)
      rwa [rawDepthShiftHom_two_apply (rawMarkedBase generators k) hk p] at hmem
    have hmem := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Hsq p)) hdiag
    simpa only [inv_mul_cancel_left] using hmem
  · apply hraw
    have hmem := rawDepthShift_mem_rawShiftSpan (rawMarkedBase generators k) hk
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j) p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_handleV_apply (rawMarkedBase generators k) hk j p] at hmem
  · apply hraw
    have hmem := rawDepthShift_mem_rawShiftSpan (rawMarkedBase generators k) hk
      (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j) p : RawDepthCorrection G h k)
    rwa [rawDepthShiftHom_handleU_apply (rawMarkedBase generators k) hk j p] at hmem

open scoped commutatorElement in
private theorem commutatorElement_eq_commP_inv_step
    {H : Type*} [Group H] (v g : H) : ⁅v, g⁆ = commP v⁻¹ g⁻¹ := by
  simp only [commutatorElement_def, commP, inv_inv]

/-- Uniform variable-rank successor step.  The only induction hypothesis is the preceding
augmented span inclusion; the handle rows require no additional assumption. -/
theorem rawAugmentedSpan_step
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (k : ℕ) (hk : 3 ≤ k)
    (hgen : Subgroup.closure (Set.range (rawMarkedBase generators (k + 1))) = ⊤)
    (prev : zLayer G k ≤ rawAugmentedSpan generators k hk) :
    zLayer G (k + 1) ≤ rawAugmentedSpan generators (k + 1) (by omega) := by
  intro q hq
  refine lambdaImage_induction G hfg hpro (j := k) (by omega)
    (p := fun z ↦ z ∈ rawAugmentedSpan generators (k + 1) (by omega)) ?_ ?_
    (Subgroup.one_mem _) (fun _ _ ↦ Subgroup.mul_mem _) (fun _ ↦ Subgroup.inv_mem _) hq
  · exact rawSquare_mem_augmentedSpan_succ generators k hk prev
  · intro v hv g
    let p : lambdaImage G k (k + 2) :=
      ⟨(levelMk G (k + 2) v)⁻¹, ⟨v⁻¹, Subgroup.inv_mem _ hv, by rw [map_inv]⟩⟩
    have Hsq : ∀ p : lambdaImage G k (k + 2),
        p.1 ^ 2 ∈ rawAugmentedSpan generators (k + 1) (by omega) := by
      rintro ⟨p, hp⟩
      obtain ⟨x, hx, hxp⟩ := hp
      subst p
      simpa only [map_pow] using
        rawSquare_mem_augmentedSpan_succ generators k hk prev x hx
    have hp : ∀ z : levelQuot G (k + 2),
        commP p.1 z ∈ rawAugmentedSpan generators (k + 1) (by omega) := by
      intro z
      have hz : z ∈ Subgroup.closure
          (Set.range (rawMarkedBase generators (k + 1))) := by rw [hgen]; trivial
      refine Subgroup.closure_induction
        (p := fun x _ ↦ commP p.1 x ∈
          rawAugmentedSpan generators (k + 1) (by omega)) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        exact rawBracket_base_mem_augmentedSpan generators (k + 1) (by omega) Hsq p i
      · simp [commP]
      · intro x y _ _ hx hy
        rw [commP_mul_right_of_mem (k + 1) (by omega) p.2 x y]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [commP_inv_right_of_mem (k + 1) (by omega) p.2 x]
        exact Subgroup.inv_mem _ hx
    rw [map_commutatorElement, commutatorElement_eq_commP_inv_step]
    exact hp (levelMk G (k + 2) g)⁻¹

/-- The base proposition plus the uniform step give all augmented span inclusions.  The
per-level generation hypothesis is kept explicit so this theorem applies both to free
generators and to any coherent displayed tuple. -/
theorem rawAugmentedSpan_of_base_of_step
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (generators : Fin (SqCore.sqRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hgen : ∀ k, 3 ≤ k →
      Subgroup.closure (Set.range (rawMarkedBase generators (k + 1))) = ⊤)
    (hbase : RawAugmentedSpanBaseSupply generators) :
    ∀ (k : ℕ) (hk : 3 ≤ k), zLayer G k ≤ rawAugmentedSpan generators k hk := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => simpa only [RawAugmentedSpanBaseSupply] using hbase
  | succ n ih =>
      have hkn : 3 ≤ 3 + n := by omega
      simpa only [Nat.add_succ] using
        rawAugmentedSpan_step generators hfg hpro (3 + n) hkn
          (hgen (3 + n) hkn) (ih hkn)

#print axioms sqCoreHandleDbarWord_sq
#print axioms rawSquare_mem_augmentedSpan_succ
#print axioms rawAugmentedSpan_step
#print axioms rawAugmentedSpan_of_base_of_step

end


end GQ2.Dyadic.LSquare
