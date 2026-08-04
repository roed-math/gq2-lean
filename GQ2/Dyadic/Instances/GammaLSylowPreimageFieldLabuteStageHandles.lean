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

/-- For a depth-`k-1` element, the bracket with a fixed ambient element is multiplicative
in the correction coordinate.  This is the one-coordinate linearity used below. -/
theorem commP_mul_left_of_depth
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 3 ≤ k) {p p' u : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (p * p') u = commP p u * commP p' u := by
  rw [commP_mul_left, conj_eq_self_of_commP_eq_one
    (commP_eq_one_of_mul_comm
      (zLayer_commute (commP_mem_zLayer k hk hp u) p').eq)]

/-- The linearized contribution of one handle pair is multiplicative under pointwise
multiplication of two depth corrections. -/
theorem handlePairDbar_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 3 ≤ k) (u v : levelQuot G (k + 1))
    {p q p' q' : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1))
    (_hp' : p' ∈ lambdaImage G (k - 1) (k + 1))
    (hq' : q' ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (q * q') u * commP (p * p') v =
      (commP q u * commP p v) * (commP q' u * commP p' v) := by
  rw [commP_mul_left_of_depth k hk hq, commP_mul_left_of_depth k hk hp]
  have hq'u : commP q' u ∈ zLayer G k := commP_mem_zLayer k hk hq' u
  calc
    (commP q u * commP q' u) * (commP p v * commP p' v) =
        commP q u * (commP q' u * commP p v) * commP p' v := by group
    _ = commP q u * (commP p v * commP q' u) * commP p' v := by
      rw [(zLayer_commute hq'u (commP p v)).eq]
    _ = (commP q u * commP p v) * (commP q' u * commP p' v) := by group

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

/-- The complete handle contribution lands in the central involutive layer. -/
theorem sqHandleDbarWord_mem_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    sqHandleDbarWord base correction ∈ zLayer G k := by
  rw [sqHandleDbarWord]
  apply Subgroup.list_prod_mem
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨j, _hj, rfl⟩ := hz
  exact Subgroup.mul_mem _
    (commP_mem_zLayer k hk (hdepth (SqCore.sqHandleIdxV j)) _)
    (commP_mem_zLayer k hk (hdepth (SqCore.sqHandleIdxU j)) _)

/-- The zero handle correction has trivial handle shift. -/
theorem sqHandleDbarWord_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    sqHandleDbarWord base (fun _ ↦ 1) = 1 := by
  simp [sqHandleDbarWord, commP]

/-- The entire handle block is multiplicative in the depth correction.  Thus every handle
pair contributes a genuine linear coordinate in the central graded layer. -/
theorem sqHandleDbarWord_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    {correction correction' : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, correction' i ∈ lambdaImage G (k - 1) (k + 1)) :
    sqHandleDbarWord base (fun i ↦ correction i * correction' i) =
      sqHandleDbarWord base correction * sqHandleDbarWord base correction' := by
  rw [sqHandleDbarWord, sqHandleDbarWord, sqHandleDbarWord]
  simp_rw [handlePairDbar_mul k hk _ _
    (hdepth (SqCore.sqHandleIdxU _)) (hdepth (SqCore.sqHandleIdxV _))
    (hdepth' (SqCore.sqHandleIdxU _)) (hdepth' (SqCore.sqHandleIdxV _))]
  apply list_prod_mul_of_right_central
  intro j t
  have hz : commP (correction' (SqCore.sqHandleIdxV j))
          (base (SqCore.sqHandleIdxU j)) *
        commP (correction' (SqCore.sqHandleIdxU j))
          (base (SqCore.sqHandleIdxV j)) ∈ zLayer G k :=
    Subgroup.mul_mem _
      (commP_mem_zLayer k hk (hdepth' (SqCore.sqHandleIdxV j)) _)
      (commP_mem_zLayer k hk (hdepth' (SqCore.sqHandleIdxU j)) _)
  exact (zLayer_commute hz t).eq

/-- The full explicit core-plus-handle shift map. -/
def sqCoreHandleDbarWord
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  dbarWordR2 (base 0) (base 1) (base 2)
      ![correction 0, correction 1, correction 2] *
    sqHandleDbarWord base correction

/-- The full linearized shift lands in the central defect layer. -/
theorem sqCoreHandleDbarWord_mem_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    sqCoreHandleDbarWord base correction ∈ zLayer G k := by
  apply Subgroup.mul_mem
  · exact dbarWordR2_mem_zLayer k hk _ _ _ fun i ↦ by
      fin_cases i
      · exact hdepth 0
      · exact hdepth 1
      · exact hdepth 2
  · exact sqHandleDbarWord_mem_zLayer h k hk base correction hdepth

/-- The zero correction has trivial full shift. -/
theorem sqCoreHandleDbarWord_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    sqCoreHandleDbarWord base (fun _ ↦ 1) = 1 := by
  rw [sqCoreHandleDbarWord, sqHandleDbarWord_one, mul_one]
  exact dbarWordR2_one _ _ _

/-- The full explicit core-plus-handle shift is a homomorphism on depth corrections.  This
reduces the remaining span problem to the images of individual core and handle coordinates. -/
theorem sqCoreHandleDbarWord_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 3 ≤ k)
    (base : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    {correction correction' : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, correction' i ∈ lambdaImage G (k - 1) (k + 1)) :
    sqCoreHandleDbarWord base (fun i ↦ correction i * correction' i) =
      sqCoreHandleDbarWord base correction * sqCoreHandleDbarWord base correction' := by
  have hcoreDepth : ∀ i : Fin 3,
      ![correction 0, correction 1, correction 2] i ∈
        lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact hdepth 0
    · exact hdepth 1
    · exact hdepth 2
  have hcoreDepth' : ∀ i : Fin 3,
      ![correction' 0, correction' 1, correction' 2] i ∈
        lambdaImage G (k - 1) (k + 1) := by
    intro i
    fin_cases i
    · exact hdepth' 0
    · exact hdepth' 1
    · exact hdepth' 2
  rw [sqCoreHandleDbarWord, sqCoreHandleDbarWord, sqCoreHandleDbarWord,
    show ![correction 0 * correction' 0, correction 1 * correction' 1,
        correction 2 * correction' 2] =
      fun i ↦ ![correction 0, correction 1, correction 2] i *
        ![correction' 0, correction' 1, correction' 2] i by
          funext i
          fin_cases i <;> rfl,
    dbarWordR2_mul k hk _ _ _ hcoreDepth hcoreDepth',
    sqHandleDbarWord_mul h k hk base hdepth hdepth']
  have hcore' : dbarWordR2 (base 0) (base 1) (base 2)
      ![correction' 0, correction' 1, correction' 2] ∈ zLayer G k :=
    dbarWordR2_mem_zLayer k hk _ _ _ hcoreDepth'
  calc
    (_ * _) * (_ * _) =
        dbarWordR2 (base 0) (base 1) (base 2)
            ![correction 0, correction 1, correction 2] *
          (dbarWordR2 (base 0) (base 1) (base 2)
              ![correction' 0, correction' 1, correction' 2] *
            sqHandleDbarWord base correction) *
          sqHandleDbarWord base correction' := by group
    _ = dbarWordR2 (base 0) (base 1) (base 2)
            ![correction 0, correction 1, correction 2] *
          (sqHandleDbarWord base correction *
            dbarWordR2 (base 0) (base 1) (base 2)
              ![correction' 0, correction' 1, correction' 2]) *
          sqHandleDbarWord base correction' := by
      rw [(zLayer_commute hcore' (sqHandleDbarWord base correction)).eq]
    _ = (_ * _) * (_ * _) := by group

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

/-- A homogeneous depth correction which preserves every sharp cyclotomic row.  These are
the linear directions of the affine space of sharp-admissible corrections. -/
structure SharpNeutralCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 1 ≤ k) where
  correction : Fin (SqCore.sqRank h) →
    levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)
  depth : ∀ i, correction i ∈
    lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)
  sharpKernel : ∀ i, sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
    (correction i) = 1

@[ext]
theorem SharpNeutralCorrection.ext {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    {V V' : SharpNeutralCorrection T hk}
    (H : V.correction = V'.correction) : V = V' := by
  cases V
  cases V'
  cases H
  rfl

protected noncomputable def SharpNeutralCorrection.one {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k} :
    SharpNeutralCorrection T hk where
  correction _ := 1
  depth _ := Subgroup.one_mem _
  sharpKernel _ := map_one _

protected noncomputable def SharpNeutralCorrection.mul {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (V V' : SharpNeutralCorrection T hk) : SharpNeutralCorrection T hk where
  correction i := V.correction i * V'.correction i
  depth i := Subgroup.mul_mem _ (V.depth i) (V'.depth i)
  sharpKernel i := by rw [map_mul, V.sharpKernel, V'.sharpKernel, one_mul]

protected noncomputable def SharpNeutralCorrection.inv {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (V : SharpNeutralCorrection T hk) : SharpNeutralCorrection T hk where
  correction i := (V.correction i)⁻¹
  depth i := Subgroup.inv_mem _ (V.depth i)
  sharpKernel i := by rw [map_inv, V.sharpKernel, inv_one]

noncomputable instance {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k} :
    Group (SharpNeutralCorrection T hk) where
  one := SharpNeutralCorrection.one
  mul := SharpNeutralCorrection.mul
  inv := SharpNeutralCorrection.inv
  mul_assoc V₁ V₂ V₃ := by
    ext i
    exact mul_assoc _ _ _
  one_mul V := by
    ext i
    exact one_mul _
  mul_one V := by
    ext i
    exact mul_one _
  inv_mul_cancel V := by
    ext i
    exact inv_mul_cancel _

@[simp] theorem SharpNeutralCorrection.one_correction {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (i : Fin (SqCore.sqRank h)) :
    (1 : SharpNeutralCorrection T hk).correction i = 1 := rfl

@[simp] theorem SharpNeutralCorrection.mul_correction {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (V V' : SharpNeutralCorrection T hk) (i : Fin (SqCore.sqRank h)) :
    (V * V').correction i = V.correction i * V'.correction i := rfl

@[simp] theorem SharpNeutralCorrection.inv_correction {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (V : SharpNeutralCorrection T hk) (i : Fin (SqCore.sqRank h)) :
    V⁻¹.correction i = (V.correction i)⁻¹ := rfl

/-- The literal core-plus-handle shift as a homomorphism from the group of neutral depth
directions into the central defect layer. -/
noncomputable def sharpNeutralShiftHom {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    SharpNeutralCorrection T (by omega) →* zLayer
      (maxProPQuotient 2 (GalK K)) k where
  toFun V := ⟨sqCoreHandleDbarWord
    (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
    V.correction, sqCoreHandleDbarWord_mem_zLayer h k hk _ _ V.depth⟩
  map_one' := by
    apply Subtype.ext
    change sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      (fun _ ↦ 1) = 1
    exact sqCoreHandleDbarWord_one _
  map_mul' V V' := by
    apply Subtype.ext
    change sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      (fun i ↦ V.correction i * V'.correction i) =
      sqCoreHandleDbarWord
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
          V.correction *
        sqCoreHandleDbarWord
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
          V'.correction
    exact sqCoreHandleDbarWord_mul h k hk _ V.depth V'.depth

/-- The subgroup of depth-`k-1` corrections in one coordinate which preserve the sharp
cyclotomic row.  The full neutral correction group is the finite product of copies of this
subgroup, one for each core or handle coordinate. -/
noncomputable def sharpNeutralCoordinateSubgroup {k : ℕ} (hk : 1 ≤ k) :
    Subgroup (levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :=
  lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) ⊓
    (sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)).ker

/-- Insert a one-coordinate neutral correction into the full correction vector. -/
noncomputable def sharpNeutralCoordinateHom {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 1 ≤ k)
    (i : Fin (SqCore.sqRank h)) :
    sharpNeutralCoordinateSubgroup (K := K) hk →*
      SharpNeutralCorrection T hk where
  toFun p := {
    correction := fun j ↦ if j = i then p.1 else 1
    depth := by
      intro j
      by_cases hji : j = i
      · simpa [hji] using p.2.1
      · simp [hji]
    sharpKernel := by
      intro j
      by_cases hji : j = i
      · simpa [hji] using MonoidHom.mem_ker.mp p.2.2
      · simp [hji] }
  map_one' := by
    apply SharpNeutralCorrection.ext
    funext j
    by_cases hji : j = i <;> simp [hji]
  map_mul' p q := by
    apply SharpNeutralCorrection.ext
    funext j
    by_cases hji : j = i <;> simp [hji]

@[simp] theorem sharpNeutralCoordinateHom_correction {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 1 ≤ k)
    (i j : Fin (SqCore.sqRank h))
    (p : sharpNeutralCoordinateSubgroup (K := K) hk) :
    (sharpNeutralCoordinateHom T hk i p).correction j =
      if j = i then p.1 else 1 := rfl

/-- The image in the defect layer of a neutral correction supported on one coordinate. -/
noncomputable def sharpNeutralCoordinateShiftHom {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (i : Fin (SqCore.sqRank h)) :
    sharpNeutralCoordinateSubgroup (K := K)
      (le_trans (by decide : 1 ≤ 3) hk) →*
      zLayer (maxProPQuotient 2 (GalK K)) k :=
  (sharpNeutralShiftHom T hk).comp
    (sharpNeutralCoordinateHom T (le_trans (by decide : 1 ≤ 3) hk) i)

/-- Every one-coordinate shift lies in the range of the full neutral shift. -/
theorem sharpNeutralCoordinateShiftHom_range_le {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (i : Fin (SqCore.sqRank h)) :
    (sharpNeutralCoordinateShiftHom T hk i).range ≤
      (sharpNeutralShiftHom T hk).range := by
  rintro y ⟨p, rfl⟩
  exact ⟨sharpNeutralCoordinateHom T (le_trans (by decide : 1 ≤ 3) hk) i p, rfl⟩

/-- Surjectivity of even one coordinate shift is a sufficient (usually stronger than
necessary) finite-rank criterion for surjectivity of the full neutral shift. -/
theorem sharpNeutralShiftHom_surjective_of_coordinate {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (i : Fin (SqCore.sqRank h))
    (Hsurj : Function.Surjective (sharpNeutralCoordinateShiftHom T hk i)) :
    Function.Surjective (sharpNeutralShiftHom T hk) := by
  intro y
  obtain ⟨p, hp⟩ := Hsurj y
  exact ⟨sharpNeutralCoordinateHom T (le_trans (by decide : 1 ≤ 3) hk) i p, hp⟩

/-- The first core coordinate contributes exactly its crossed bracket with the old `x₀`
coordinate.  In particular, none of the improved handle factors is lost in the definition:
they are all literally trivial for a correction supported at core coordinate zero. -/
theorem sharpNeutralCoordinateShiftHom_zero_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (p : sharpNeutralCoordinateSubgroup (K := K)
      (le_trans (by decide : 1 ≤ 3) hk)) :
    ((sharpNeutralCoordinateShiftHom T hk 0) p).1 =
      commP p.1
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)) := by
  let base := fun i ↦
    canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
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
      (sharpNeutralCoordinateHom T
        (le_trans (by decide : 1 ≤ 3) hk) 0 p).correction = 1 := by
    simp [sqHandleDbarWord, sharpNeutralCoordinateHom_correction, hu0, hv0, commP]
  change sqCoreHandleDbarWord base
      (sharpNeutralCoordinateHom T
        (le_trans (by decide : 1 ≤ 3) hk) 0 p).correction = commP p.1 (base 1)
  rw [sqCoreHandleDbarWord, hhandle, mul_one]
  simp [sharpNeutralCoordinateHom_correction, dbarWordR2, commP, h10, h20]

/-- Pointwise multiplication by a sharp-neutral correction preserves sharp admissibility. -/
noncomputable def SharpAdmissibleCorrection.mulNeutral {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (W : SharpAdmissibleCorrection T hk) (V : SharpNeutralCorrection T hk) :
    SharpAdmissibleCorrection T hk where
  correction i := W.correction i * V.correction i
  depth i := Subgroup.mul_mem _ (W.depth i) (V.depth i)
  sigma := by
    have hW := W.sigma
    dsimp only [stageModified] at hW
    dsimp only [stageModified]
    rw [← mul_assoc, map_mul, hW, V.sharpKernel, mul_one]
  x0 := by
    have hW := W.x0
    dsimp only [stageModified] at hW
    dsimp only [stageModified]
    rw [← mul_assoc, map_mul, hW, V.sharpKernel, mul_one]
  x1 := by
    have hW := W.x1
    dsimp only [stageModified] at hW
    dsimp only [stageModified]
    rw [← mul_assoc, map_mul, hW, V.sharpKernel, mul_one]
  handleU j := by
    have hW := W.handleU j
    dsimp only [stageModified] at hW
    dsimp only [stageModified]
    rw [← mul_assoc, map_mul, hW, V.sharpKernel, one_mul]
  handleV j := by
    have hW := W.handleV j
    dsimp only [stageModified] at hW
    dsimp only [stageModified]
    rw [← mul_assoc, map_mul, hW, V.sharpKernel, one_mul]

/-- The explicit shift of a sharp correction acted on by a neutral direction is the product
of the old shift and the neutral direction's linear value. -/
theorem SharpAdmissibleCorrection.sqCoreHandleDbarWord_mulNeutral
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (V : SharpNeutralCorrection T (by omega)) :
    let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
    sqCoreHandleDbarWord base (W.mulNeutral V).correction =
      sqCoreHandleDbarWord base W.correction *
        sqCoreHandleDbarWord base V.correction := by
  dsimp only [SharpAdmissibleCorrection.mulNeutral]
  exact sqCoreHandleDbarWord_mul h k hk _ W.depth V.depth

/-- If two right modifications of the same base have the same sharp character, their
coordinatewise quotient is sharp-neutral. -/
theorem sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {n : ℕ} {hn : 2 ≤ n}
    {a p q : levelQuot G n}
    (H : sharpChiLevel chi n hn (a * p) = sharpChiLevel chi n hn (a * q)) :
    sharpChiLevel chi n hn (p⁻¹ * q) = 1 := by
  rw [map_mul, map_mul] at H
  have hpq : sharpChiLevel chi n hn p = sharpChiLevel chi n hn q :=
    mul_left_cancel H
  rw [map_mul, map_inv, hpq, inv_mul_cancel]

/-- The quotient of any two points in the sharp-admissible affine space is a neutral
direction. -/
noncomputable def SharpAdmissibleCorrection.differenceNeutral {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (W W' : SharpAdmissibleCorrection T hk) : SharpNeutralCorrection T hk where
  correction i := (W.correction i)⁻¹ * W'.correction i
  depth i := Subgroup.mul_mem _ (Subgroup.inv_mem _ (W.depth i)) (W'.depth i)
  sharpKernel i := by
    rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · apply sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
      simpa only [stageModified] using W.sigma.trans W'.sigma.symm
    · apply sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
      simpa only [stageModified] using W.x0.trans W'.x0.symm
    · apply sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
      simpa only [stageModified] using W.x1.trans W'.x1.symm
    · apply sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
      simpa only [stageModified] using (W.handleU j).trans (W'.handleU j).symm
    · apply sharpChiLevel_inv_mul_eq_one_of_base_mul_eq
      simpa only [stageModified] using (W.handleV j).trans (W'.handleV j).symm

/-- Acting by the quotient neutral direction recovers the second affine point literally. -/
theorem SharpAdmissibleCorrection.mulNeutral_difference_correction {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} {hk : 1 ≤ k}
    (W W' : SharpAdmissibleCorrection T hk) :
    (W.mulNeutral (W.differenceNeutral W')).correction = W'.correction := by
  funext i
  dsimp only [SharpAdmissibleCorrection.mulNeutral,
    SharpAdmissibleCorrection.differenceNeutral]
  group

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

/-- Relative to one point of the nonempty sharp-admissible affine space, the remaining
problem is linear: a sharp-neutral direction must hit the residual defect. -/
def SharpNeutralResidualReachable {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) : Prop :=
  ∃ V : SharpNeutralCorrection T (by omega),
    let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
    sqCoreHandleDbarWord base V.correction =
      (sqCoreHandleDbarWord base W.correction)⁻¹ *
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹

/-- The residual target as an element of the central defect layer. -/
noncomputable def sharpNeutralResidualElement {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) :
    zLayer (maxProPQuotient 2 (GalK K)) k :=
  ⟨(let base := fun i ↦
      canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
    (sqCoreHandleDbarWord base W.correction)⁻¹ *
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹),
    Subgroup.mul_mem _
      (Subgroup.inv_mem _ (sqCoreHandleDbarWord_mem_zLayer h k hk _ _ W.depth))
      (Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation))⟩

/-- Neutral residual reachability is exactly membership in the range of the explicit shift
homomorphism. -/
theorem sharpNeutralResidualReachable_iff_mem_range
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    SharpNeutralResidualReachable T hk W ↔
      sharpNeutralResidualElement T hk W ∈
        (sharpNeutralShiftHom T hk).range := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V, ?_⟩
    apply Subtype.ext
    exact hV
  · rintro ⟨V, hV⟩
    refine ⟨V, ?_⟩
    exact congrArg Subtype.val hV

/-- It is enough to hit the concrete residual using a single coordinate shift.  This is the
one-point version of the coordinate reduction and avoids assuming full surjectivity. -/
theorem sharpNeutralResidualReachable_of_mem_coordinate_range
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (i : Fin (SqCore.sqRank h))
    (Hmem : sharpNeutralResidualElement T hk W ∈
      (sharpNeutralCoordinateShiftHom T hk i).range) :
    SharpNeutralResidualReachable T hk W :=
  (sharpNeutralResidualReachable_iff_mem_range W).mpr
    (sharpNeutralCoordinateShiftHom_range_le T hk i Hmem)

/-- A neutral direction hitting the residual defect produces the required affine correction. -/
noncomputable def CoreHandleSharpActualDefectSupply.ofNeutralResidual
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (H : SharpNeutralResidualReachable T hk W) :
    CoreHandleSharpActualDefectSupply T hk := by
  let V := H.choose
  have hV := H.choose_spec
  refine {
    correction := W.mulNeutral V
    hitsDefect := ?_ }
  let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
  change sqCoreHandleDbarWord base (W.mulNeutral V).correction =
    (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹
  have hmul := W.sqCoreHandleDbarWord_mulNeutral (hk := hk) V
  dsimp only at hmul hV
  rw [hmul, hV]
  group

/-- A one-coordinate witness for the residual already supplies the required affine
correction.  No claim of surjectivity onto the whole graded layer is needed. -/
noncomputable def CoreHandleSharpActualDefectSupply.ofCoordinateResidual
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (i : Fin (SqCore.sqRank h))
    (Hmem : sharpNeutralResidualElement T hk W ∈
      (sharpNeutralCoordinateShiftHom T hk i).range) :
    CoreHandleSharpActualDefectSupply T hk :=
  CoreHandleSharpActualDefectSupply.ofNeutralResidual W
    (sharpNeutralResidualReachable_of_mem_coordinate_range W i Hmem)

/-- The stronger full-surjectivity form of the neutral span theorem implies the required
one-point actual-defect supply. -/
noncomputable def CoreHandleSharpActualDefectSupply.ofNeutralShiftSurjective
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (Hsurj : Function.Surjective (sharpNeutralShiftHom T hk)) :
    CoreHandleSharpActualDefectSupply T hk := by
  let W : SharpAdmissibleCorrection T (by omega) :=
    Classical.choice (sharpAdmissibleCorrection_nonempty T (by omega))
  have Hmem : sharpNeutralResidualElement T hk W ∈
      (sharpNeutralShiftHom T hk).range := by
    obtain ⟨V, hV⟩ := Hsurj (sharpNeutralResidualElement T hk W)
    exact ⟨V, hV⟩
  exact CoreHandleSharpActualDefectSupply.ofNeutralResidual W
    ((sharpNeutralResidualReachable_iff_mem_range W).mpr Hmem)

/-- Conversely, any successful affine correction differs from any chosen sharp-admissible
base point by a neutral direction hitting exactly the stated residual. -/
theorem CoreHandleSharpActualDefectSupply.toNeutralResidual
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (S : CoreHandleSharpActualDefectSupply T hk)
    (W : SharpAdmissibleCorrection T (by omega)) :
    SharpNeutralResidualReachable T hk W := by
  let V : SharpNeutralCorrection T (by omega) :=
    W.differenceNeutral S.correction
  refine ⟨V, ?_⟩
  dsimp only
  let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
  change sqCoreHandleDbarWord base V.correction =
    (sqCoreHandleDbarWord base W.correction)⁻¹ *
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹
  have hmul := W.sqCoreHandleDbarWord_mulNeutral (hk := hk) V
  dsimp only at hmul
  have hrecover := W.mulNeutral_difference_correction S.correction
  have hfactor : sqCoreHandleDbarWord base S.correction.correction =
      sqCoreHandleDbarWord base W.correction *
        sqCoreHandleDbarWord base V.correction := by
    rw [← hrecover]
    exact hmul
  have hS : sqCoreHandleDbarWord base S.correction.correction =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ :=
    S.hitsDefect
  calc
    sqCoreHandleDbarWord base V.correction =
        (sqCoreHandleDbarWord base W.correction)⁻¹ *
          (sqCoreHandleDbarWord base W.correction *
            sqCoreHandleDbarWord base V.correction) := by group
    _ = (sqCoreHandleDbarWord base W.correction)⁻¹ *
          sqCoreHandleDbarWord base S.correction.correction := by rw [hfactor]
    _ = (sqCoreHandleDbarWord base W.correction)⁻¹ *
          (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by rw [hS]

/-- The affine actual-defect theorem is equivalent to the neutral residual statement from
any chosen sharp-admissible base point. -/
theorem nonempty_coreHandleSharpActualDefectSupply_iff_neutralResidual
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    Nonempty (CoreHandleSharpActualDefectSupply T hk) ↔
      SharpNeutralResidualReachable T hk W := by
  constructor
  · rintro ⟨S⟩
    exact S.toNeutralResidual W
  · intro H
    exact ⟨CoreHandleSharpActualDefectSupply.ofNeutralResidual W H⟩

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
#print axioms handlePairDbar_mul
#print axioms handleWord_mul_lambdaImage
#print axioms sqHandleDbarWord_mul
#print axioms sqCoreHandleDbarWord_mul
#print axioms stageShift_eq_dbarWordR2_mul_sqHandleDbarWord
#print axioms SqCyclotomicStageTuple.exists_exactStageRepresentative
#print axioms SqCyclotomicStageTuple.admissibleCorrection_nonempty
#print axioms SqCyclotomicStageTuple.sharpAdmissibleCorrection_nonempty
#print axioms SqCyclotomicStageTuple.SharpAdmissibleCorrection.mulNeutral
#print axioms SqCyclotomicStageTuple.SharpAdmissibleCorrection.differenceNeutral
#print axioms SqCyclotomicStageTuple.sharpNeutralShiftHom
#print axioms SqCyclotomicStageTuple.sharpNeutralCoordinateHom
#print axioms SqCyclotomicStageTuple.sharpNeutralCoordinateShiftHom
#print axioms SqCyclotomicStageTuple.sharpNeutralCoordinateShiftHom_zero_apply
#print axioms SqCyclotomicStageTuple.sharpNeutralResidualReachable_iff_mem_range
#print axioms SqCyclotomicStageTuple.sharpNeutralResidualReachable_of_mem_coordinate_range
#print axioms SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply.ofNeutralResidual
#print axioms SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply.ofCoordinateResidual
#print axioms SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply.ofNeutralShiftSurjective
#print axioms SqCyclotomicStageTuple.nonempty_coreHandleSharpActualDefectSupply_iff_neutralResidual
#print axioms SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply.toDefectReachable

end


end GQ2.Dyadic.LSquare
