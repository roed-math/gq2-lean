/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage

/-!
# Hyperbolic-handle linearization for the variable-rank Labute stage

This file exposes the exact rank-general shift word hidden behind the abstract
`ActualDefectSpanSupply` interface.  A depth-`k-1` correction of a handle pair contributes

`[v_j', u_j] * [u_j', v_j]`

in the central layer.  Consequently the literal improved-word shift is the product of the
existing rank-three core word `dbarWordR2` and these handle contributions.  This identifies
the remaining arithmetic theorem without suppressing any handle coordinate or replacing the
actual `sqRelWord` defect by a surrogate graded value.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Linearization of one handle -/

/-- Every commutator in a lower two-central quotient belongs to the image of `λ₂`. -/
theorem commP_mem_lambdaImage_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (m : ℕ) (x y : levelQuot G m) :
    commP x y ∈ lambdaImage G 2 m := by
  have hx : x ∈ lambdaImage G 1 m := by
    rw [lambdaImage_one_eq_top]
    trivial
  have hy : y ∈ lambdaImage G 1 m := by
    rw [lambdaImage_one_eq_top]
    trivial
  exact commP_mem_lambdaImage_add hx hy

/-- Conjugation by a depth-`k-1` correction fixes every element coming from `λ₂`. -/
theorem conj_lambdaImage_two_eq_self_of_depth
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1))
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    v⁻¹ * c * v = c := by
  apply conj_eq_self_of_commP_eq_one
  have h := commP_mem_lambdaImage_add hc hv
  rw [show 2 + (k - 1) = k + 1 by omega, lambdaImage_self] at h
  simpa using h

/-- A simultaneous depth correction of a hyperbolic handle linearizes into its two bracket
atoms.  Both atoms lie in the central involutive layer, which removes the apparent inverse
in the first atom. -/
theorem handlePair_mul_lambdaImage
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 3 ≤ k)
    (u v : levelQuot G (k + 1))
    {p q : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (u * p) (v * q) =
      commP u v * (commP q u * commP p v) := by
  have hqu : commP q u ∈ zLayer G k := commP_mem_zLayer k hk hq u
  have hpu : commP p v ∈ zLayer G k := commP_mem_zLayer k hk hp v
  have huq : commP u q = commP q u := by
    calc
      commP u q = (commP q u)⁻¹ := by
        simp only [commP]
        group
      _ = commP q u := zLayer_inv_self hqu
  have huv : commP u v ∈ lambdaImage G 2 (k + 1) :=
    commP_mem_lambdaImage_two (k + 1) u v
  have huq2 : commP u q ∈ lambdaImage G 2 (k + 1) :=
    lambdaImage_le_of_le (by omega) (huq ▸ hqu)
  have hconjQUV : q⁻¹ * commP u v * q = commP u v :=
    conj_lambdaImage_two_eq_self_of_depth k hk huv hq
  have hconjQPV : q⁻¹ * commP p v * q = commP p v := by
    calc
      q⁻¹ * commP p v * q = q⁻¹ * (commP p v * q) := by group
      _ = q⁻¹ * (q * commP p v) := by rw [(zLayer_commute hpu q).eq]
      _ = commP p v := by group
  have hpq : commP p q = 1 :=
    commP_eq_one_of_mul_comm (mul_comm_lambdaImage k hk hp hq)
  have hprod : commP u q * commP u v ∈ lambdaImage G 2 (k + 1) :=
    Subgroup.mul_mem _ huq2 huv
  have hconjP : p⁻¹ * (commP u q * commP u v) * p =
      commP u q * commP u v :=
    conj_lambdaImage_two_eq_self_of_depth k hk hprod hp
  rw [commP_mul_left, commP_mul_right, commP_mul_right,
    hconjQUV, hpq, one_mul, hconjQPV, hconjP, huq]
  rw [(zLayer_commute hqu (commP u v)).eq]
  group

/-! ## The full handle block -/

private theorem list_prod_mul_of_right_central
    {H Ι : Type*} [Group H] (l : List Ι) (a d : Ι → H)
    (hd : ∀ i t, d i * t = t * d i) :
    (l.map fun i ↦ a i * d i).prod = (l.map a).prod * (l.map d).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      calc
        a i * d i * ((List.map a l).prod * (List.map d l).prod) =
            a i * (d i * (List.map a l).prod) * (List.map d l).prod := by group
        _ = a i * ((List.map a l).prod * d i) * (List.map d l).prod := by
          rw [hd i]
        _ = (a i * (List.map a l).prod) * (d i * (List.map d l).prod) := by group

/-- The explicit linearized contribution of every hyperbolic handle.  For the `j`-th pair,
the `V`-correction brackets with the old `U`-slot and the `U`-correction brackets with the
old `V`-slot. -/
def sqHandleDbarWord
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  ((List.finRange h).map fun j ↦
    commP (correction (SqCore.sqHandleIdxV j)) (base (SqCore.sqHandleIdxU j)) *
      commP (correction (SqCore.sqHandleIdxU j)) (base (SqCore.sqHandleIdxV j))).prod

/-- The full handle product factors into its old value and the explicit linearized handle
word. -/
theorem handleWord_mul_lambdaImage
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    GQ2.Dyadic.MarkedCore.handleWord
        (fun j ↦ base (SqCore.sqHandleIdxU j) * correction (SqCore.sqHandleIdxU j))
        (fun j ↦ base (SqCore.sqHandleIdxV j) * correction (SqCore.sqHandleIdxV j)) =
      GQ2.Dyadic.MarkedCore.handleWord
          (fun j ↦ base (SqCore.sqHandleIdxU j))
          (fun j ↦ base (SqCore.sqHandleIdxV j)) *
        sqHandleDbarWord base correction := by
  rw [GQ2.Dyadic.MarkedCore.handleWord, GQ2.Dyadic.MarkedCore.handleWord,
    sqHandleDbarWord]
  simp_rw [handlePair_mul_lambdaImage k hk _ _
    (hdepth (SqCore.sqHandleIdxU _)) (hdepth (SqCore.sqHandleIdxV _))]
  apply list_prod_mul_of_right_central
  intro j t
  have hz : commP (correction (SqCore.sqHandleIdxV j))
          (base (SqCore.sqHandleIdxU j)) *
        commP (correction (SqCore.sqHandleIdxU j))
          (base (SqCore.sqHandleIdxV j)) ∈ zLayer G k :=
    Subgroup.mul_mem _
      (commP_mem_zLayer k hk (hdepth (SqCore.sqHandleIdxV j)) _)
      (commP_mem_zLayer k hk (hdepth (SqCore.sqHandleIdxU j)) _)
  exact (zLayer_commute hz t).eq

/-! ## Literal full-word factorization -/

/-- The literal improved-relator shift is exactly the old rank-three `dbarWordR2` multiplied
by the linearized contributions of all handles.  This is an equality in `Q_(k+1)`, not merely
an equality in an associated graded quotient. -/
theorem stageShift_eq_dbarWordR2_mul_sqHandleDbarWord
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    SqCyclotomicStageTuple.stageShift (h := h) (k := k) base correction =
      dbarWordR2 (base 0) (base 1) (base 2)
          ![correction 0, correction 1, correction 2] *
        sqHandleDbarWord base correction := by
  have hcoreDepth : ∀ i : Fin 3,
      (![correction 0, correction 1, correction 2] :
        Fin 3 → levelQuot G (k + 1)) i ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact hdepth 0
    · exact hdepth 1
    · exact hdepth 2
  have hcoreZ : dbarWordR2 (base 0) (base 1) (base 2)
      ![correction 0, correction 1, correction 2] ∈ zLayer G k :=
    dbarWordR2_mem_zLayer k hk _ _ _ hcoreDepth
  have hcoreShift : drWord (base 0 * correction 0) (base 1 * correction 1)
      (base 2 * correction 2) = drWord (base 0) (base 1) (base 2) *
        dbarWordR2 (base 0) (base 1) (base 2)
          ![correction 0, correction 1, correction 2] := by
    simpa using drWord_mul_lambdaImage k hk (base 0) (base 1) (base 2) hcoreDepth
  rw [SqCyclotomicStageTuple.stageShift, SqCore.sqRelWord, SqCore.sqRelWord,
    SqCore.sqWord_eq_drWord, SqCore.sqWord_eq_drWord]
  simp only [SqCyclotomicStageTuple.stageModified]
  rw [hcoreShift, handleWord_mul_lambdaImage h k hk base correction hdepth]
  let C := drWord (base 0) (base 1) (base 2)
  let H := GQ2.Dyadic.MarkedCore.handleWord
    (fun j ↦ base (SqCore.sqHandleIdxU j))
    (fun j ↦ base (SqCore.sqHandleIdxV j))
  let d := dbarWordR2 (base 0) (base 1) (base 2)
    ![correction 0, correction 1, correction 2]
  let D := sqHandleDbarWord base correction
  change (C * H)⁻¹ * ((C * d) * (H * D)) = d * D
  calc
    (C * H)⁻¹ * ((C * d) * (H * D)) =
        (C * H)⁻¹ * ((C * (d * H)) * D) := by group
    _ = (C * H)⁻¹ * ((C * (H * d)) * D) := by
      rw [(zLayer_commute hcoreZ H).eq]
    _ = d * D := by group

/-! ## The remaining one-point span statement -/

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Every stage coordinate has an exact representative whose character is the corresponding
generator value of the square-core orientation.  This packages the three exceptional rows and
both handle families into one rank-general statement. -/
theorem exists_exactStageRepresentative {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (i : Fin (SqCore.sqRank h)) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = SqCore.chiSq h (SqCore.sqGen h i) ∧
        T.generators i = levelMk (maxProPQuotient 2 (GalK K)) k x := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show SqCore.sqGen h 0 = SqCore.dsqSigma h from rfl,
      SqCore.chiSq_sigma]
    exact T.sigma
  · rw [show SqCore.sqGen h 1 = SqCore.dsqX0 h from rfl,
      SqCore.chiSq_x0]
    exact T.x0
  · rw [show SqCore.sqGen h 2 = SqCore.dsqX1 h from rfl,
      SqCore.chiSq_x1]
    exact T.x1
  · obtain ⟨x, hxchi, hx⟩ := T.handleU j
    refine ⟨x, ?_, hx⟩
    rw [MonoidHom.mem_ker] at hxchi
    simpa using hxchi
  · obtain ⟨x, hxchi, hx⟩ := T.handleV j
    refine ⟨x, ?_, hx⟩
    rw [MonoidHom.mem_ker] at hxchi
    simpa using hxchi

/-- The affine domain of exact-fibre depth corrections is never empty.  Rebase the exact
representatives already carried by `T` against the chosen `canonLift`; their difference is in
`Z_k`, hence in the required depth-`k-1` image. -/
theorem admissibleCorrection_nonempty {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) :
    Nonempty (AdmissibleCorrection T) := by
  choose x hxchi hxgen using fun i ↦ exists_exactStageRepresentative T i
  let G := maxProPQuotient 2 (GalK K)
  let base : Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i)
  let next : Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
    fun i ↦ levelMk G (k + 1) (x i)
  let correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1) :=
    fun i ↦ (base i)⁻¹ * next i
  have hmodified : stageModified (h := h) (k := k) base correction = next := by
    funext i
    dsimp only [stageModified, correction]
    group
  have hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i
    apply lambdaImage_le_of_le (Nat.sub_le k 1)
    change correction i ∈ zLayer G k
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker]
    simp only [correction, map_mul, map_inv, base, levelProj_canonLift, next,
      levelProj_levelMk]
    rw [← hxgen i, inv_mul_cancel]
  refine ⟨{
    correction := correction
    depth := hdepth
    sigma := ?_
    x0 := ?_
    x1 := ?_
    handleU := ?_
    handleV := ?_ }⟩
  · refine ⟨x 0, ?_, ?_⟩
    · exact (hxchi 0).trans (SqCore.chiSq_sigma h)
    · rw [congrFun hmodified 0]
  · refine ⟨x 1, ?_, ?_⟩
    · exact (hxchi 1).trans (SqCore.chiSq_x0 h)
    · rw [congrFun hmodified 1]
  · refine ⟨x 2, ?_, ?_⟩
    · exact (hxchi 2).trans (SqCore.chiSq_x1 h)
    · rw [congrFun hmodified 2]
  · intro j
    refine ⟨x (SqCore.sqHandleIdxU j), ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      exact (hxchi (SqCore.sqHandleIdxU j)).trans (SqCore.chiSq_handleU h j)
    · rw [congrFun hmodified (SqCore.sqHandleIdxU j)]
  · intro j
    refine ⟨x (SqCore.sqHandleIdxV j), ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      exact (hxchi (SqCore.sqHandleIdxV j)).trans (SqCore.chiSq_handleV h j)
    · rw [congrFun hmodified (SqCore.sqHandleIdxV j)]

/-- Consequently the finite sharp-admissible correction domain is also nonempty.  Exact
fibre representatives determine the extra character digit automatically. -/
theorem sharpAdmissibleCorrection_nonempty {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 1 ≤ k) :
    Nonempty (SharpAdmissibleCorrection T hk) := by
  obtain ⟨W⟩ := admissibleCorrection_nonempty T
  refine ⟨{
    correction := W.correction
    depth := W.depth
    sigma := exactFibre_implies_sharpChiLevel (by omega) W.sigma
    x0 := exactFibre_implies_sharpChiLevel (by omega) W.x0
    x1 := exactFibre_implies_sharpChiLevel (by omega) W.x1
    handleU := ?_
    handleV := ?_ }⟩
  · intro j
    obtain ⟨x, hxchi, hx⟩ := W.handleU j
    have H : ∃ x : maxProPQuotient 2 (GalK K),
        chiCycKTwo (K := K) x = 1 ∧
          stageModified
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            W.correction (SqCore.sqHandleIdxU j) =
              levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x :=
      ⟨x, MonoidHom.mem_ker.mp hxchi, hx⟩
    simpa using exactFibre_implies_sharpChiLevel (by omega) H
  · intro j
    obtain ⟨x, hxchi, hx⟩ := W.handleV j
    have H : ∃ x : maxProPQuotient 2 (GalK K),
        chiCycKTwo (K := K) x = 1 ∧
          stageModified
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            W.correction (SqCore.sqHandleIdxV j) =
              levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x :=
      ⟨x, MonoidHom.mem_ker.mp hxchi, hx⟩
    simpa using exactFibre_implies_sharpChiLevel (by omega) H

/-- The finite, handle-sensitive statement still needed from a variable-rank Labute
calculation.  It asks for one sharp-admissible correction hitting the current actual defect
through the explicit core-plus-handle word; it does not assert unnecessary surjectivity onto
the whole graded layer. -/
structure CoreHandleSharpActualDefectSupply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) where
  correction : SharpAdmissibleCorrection T (by omega)
  hitsDefect :
    let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
    dbarWordR2 (base 0) (base 1) (base 2)
        ![correction.correction 0, correction.correction 1, correction.correction 2] *
      sqHandleDbarWord base correction.correction =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹

/-- The explicit core-plus-handle one-point span statement supplies the abstract
`ActualDefectSpanSupply` as soon as sharp exact fibre lifting is available. -/
noncomputable def CoreHandleSharpActualDefectSupply.toActualDefectSpanSupply
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (S : CoreHandleSharpActualDefectSupply T hk)
    (Hlift : SharpExactLevelFibreLiftSupply
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    ActualDefectSpanSupply T where
  Parameter := PUnit
  correction _ := S.correction.toAdmissible Hlift
  shiftValue _ := ⟨(sqStageDefect (maxProPQuotient 2 (GalK K)) h k
      T.generators)⁻¹, Subgroup.inv_mem _
        (sqStageDefect_mem_zLayer h k T.relation)⟩
  realizes _ := by
    change stageShift
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      S.correction.correction =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹
    rw [stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk _ _
      S.correction.depth]
    exact S.hitsDefect
  hitsDefect := ⟨PUnit.unit, rfl⟩

/-- Hence the remaining explicit one-point span statement implies the exact stage premise
consumed by the variable-rank induction. -/
theorem CoreHandleSharpActualDefectSupply.toDefectReachable
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (S : CoreHandleSharpActualDefectSupply T hk)
    (Hlift : SharpExactLevelFibreLiftSupply
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    DefectReachable T :=
  (S.toActualDefectSpanSupply Hlift).toDefectReachable

end SqCyclotomicStageTuple

#print axioms handlePair_mul_lambdaImage
#print axioms handleWord_mul_lambdaImage
#print axioms stageShift_eq_dbarWordR2_mul_sqHandleDbarWord
#print axioms SqCyclotomicStageTuple.exists_exactStageRepresentative
#print axioms SqCyclotomicStageTuple.admissibleCorrection_nonempty
#print axioms SqCyclotomicStageTuple.sharpAdmissibleCorrection_nonempty
#print axioms SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply.toDefectReachable

end


end GQ2.Dyadic.LSquare
