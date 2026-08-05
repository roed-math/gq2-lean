/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDigitFlipNeutral

/-!
# The flip damage decomposition and the bracket-square residual

This file validates the recorded design of the handle-digit repair and reduces the neutral
damage supply one step further.

* **The square collapse** (`stageDamage_decomposition`): the flip damage
  `[σ̄^(2^(k-2)), z]` equals `B² · [B, σ̄^(2^(k-3))]` exactly in `Q_(k+1)`, where
  `B = [σ̄^(2^(k-3)), z]` has depth `k-1` — the group form of
  `[σ^(2^(k-2)), V] = (ad σ)^(2^(k-2))(V)` modulo brackets of the bracket.
* **The junk term is neutral** (`stageDamage_junk_mem_neutralShiftSpan`): for `k ≥ 4` it
  vanishes outright (its second argument is a square against a depth-`k-1` first argument),
  and for `k = 3` it is the literal `x₀`-row of `B`, a core-slot shift.
* Hence the neutral damage supply reduces to the **bracket-square residual**
  (`SqStageBracketSquareNeutralSupply`): the squares `B²` of the `2h` half-damage brackets
  lie in the neutral shift span.  Through the diagonal row this is equivalent to neutrality
  of the twisted brackets `[B, x̄₁]` (`stageDamage_sq_mem_iff_twistedBracket`) — the exact
  point where the mod-two functional calculus gives nothing (χ of a commutator is `1`).
* **Functional invisibility** (`stageDamage_mem_derivKer`): every coordinate derivation of a
  family kills the flip damage, so by the span criterion the damage already lies in the full
  raw shift span; the open content of the residual is digit control, not existence.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Index disequalities and the ambient power lemma -/

private theorem stageDamage_hU_ne_one {h : ℕ} (l : Fin h) :
    SqCore.sqHandleIdxU l ≠ (1 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_one] at hv
  omega

private theorem stageDamage_hV_ne_one {h : ℕ} (l : Fin h) :
    SqCore.sqHandleIdxV l ≠ (1 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_one] at hv
  omega

private theorem stageDamage_hU_ne_two {h : ℕ} (l : Fin h) :
    SqCore.sqHandleIdxU l ≠ (2 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_two] at hv
  omega

private theorem stageDamage_hV_ne_two {h : ℕ} (l : Fin h) :
    SqCore.sqHandleIdxV l ≠ (2 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_two] at hv
  omega

private theorem stageDamage_pow_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (g : G) (n : ℕ) : g ^ 2 ^ n ∈ twoCentralSeries G (1 + n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_one, Nat.add_zero, twoCentralSeries_one]
    exact Subgroup.mem_top g
  | succ n ih =>
    have hEq : g ^ 2 ^ (n + 1) = (g ^ 2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [hEq, show 1 + (n + 1) = 1 + n + 1 from rfl]
    exact sq_mem_twoCentralSeries_succ G ih

/-! ## The exact square collapse -/

/-- The exact first-argument square split of the repository commutator: against a central
bracket-of-the-bracket, `[x², z] = [x, z]² · [[x, z], x]`. -/
private theorem stageDamage_commP_sq_split {H : Type*} [Group H] (x z : H)
    (hcen : ∀ t : H, Commute (commP (commP x z) x) t) :
    commP (x ^ 2) z = commP x z ^ 2 * commP (commP x z) x := by
  have hval : commP (x ^ 2) z = commP x z * commP (commP x z) x * commP x z := by
    simp only [commP, pow_two]
    group
  rw [hval, mul_assoc, (hcen (commP x z)).eq, ← mul_assoc, ← pow_two]

/-- A depth-`k-1` element brackets trivially against every square. -/
private theorem stageDamage_commP_sq_right {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {k : ℕ} (hk : 3 ≤ k) {B : levelQuot G (k + 1)}
    (hB : B ∈ lambdaImage G (k - 1) (k + 1)) (y : levelQuot G (k + 1)) :
    commP B (y ^ 2) = 1 := by
  have hz := commP_mem_zLayer k hk hB y
  have hcomm : ∀ t, Commute (commP B y) t := fun t ↦ zLayer_commute hz t
  have hexp : commP B (y ^ 2) = commP B y * (y⁻¹ * (commP B y * y)) := by
    simp only [commP, pow_two]
    group
  rw [hexp, (hcomm y).eq, inv_mul_cancel_left, ← pow_two]
  exact zLayer_sq G hz

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The half-power damage bracket has depth `k-1`. -/
theorem stageDamage_halfBracket_mem {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) (z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) z ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
  have hx : (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3) ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 2) (k + 1) := by
    have hmem := pow_two_pow_mem_lambdaImage
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) (k - 3)
    rwa [show 1 + (k - 3) = k - 2 by omega] at hmem
  have hz1 : z ∈ lambdaImage (maxProPQuotient 2 (GalK K)) 1 (k + 1) := by
    rw [lambdaImage_one_eq_top]
    trivial
  have hadd := commP_mem_lambdaImage_add hx hz1
  rwa [show k - 2 + 1 = k - 1 by omega] at hadd

/-- **The flip damage decomposition.**  The damage bracket of the σ-power flip splits
exactly as the square of the half-power bracket times the bracket of that bracket against
the half power: the group form of the recorded `(ad σ)^(2^(k-2))` identity. -/
theorem stageDamage_decomposition {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) (z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2)) z =
      commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3))
          z ^ 2 *
        commP (commP
            ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) z)
          ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) := by
  have hxsq : ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^
      2 ^ (k - 3)) ^ 2 =
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2) := by
    rw [← pow_mul, show 2 ^ (k - 3) * 2 = 2 ^ (k - 2) by
      rw [← pow_succ]
      congr 1
      omega]
  have hJz : commP (commP
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) z)
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) ∈
      zLayer (maxProPQuotient 2 (GalK K)) k :=
    commP_mem_zLayer k hk (stageDamage_halfBracket_mem T hk z) _
  rw [← hxsq]
  exact stageDamage_commP_sq_split _ z (fun t ↦ zLayer_commute hJz t)

/-- **The junk term is neutral.**  For `k ≥ 4` the bracket of the half-damage bracket
against the half power vanishes outright; for `k = 3` it is the literal `x₀`-slot row of the
half-damage bracket, hence a core-slot shift. -/
theorem stageDamage_junk_mem_neutralShiftSpan {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) (z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :
    commP (commP
        ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) z)
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3)) ∈
      stageNeutralShiftSpan T hk := by
  have hB := stageDamage_halfBracket_mem T hk z
  by_cases hk4 : 4 ≤ k
  · obtain ⟨y, hy⟩ : ∃ y : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3) =
          y ^ 2 := by
      refine ⟨(canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 4), ?_⟩
      rw [← pow_mul, show 2 ^ (k - 4) * 2 = 2 ^ (k - 3) by
        rw [← pow_succ]
        congr 1
        omega]
    rw [hy] at hB ⊢
    rw [stageDamage_commP_sq_right hk hB y]
    exact Subgroup.one_mem _
  · have hk3 : k = 3 := by omega
    subst hk3
    rw [show (2 : ℕ) ^ (3 - 3) = 1 from rfl, pow_one] at hB ⊢
    exact ⟨(rawDepthShiftHom
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators i)) hk)
          (rawDepthCoordinateCorrection 1 ⟨_, hB⟩),
      ⟨_, stageNeutral_coordinate_mem stageDamage_hU_ne_one stageDamage_hV_ne_one _, rfl⟩,
      rawDepthShiftHom_one_apply
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) 3 (T.generators i)) hk ⟨_, hB⟩⟩

/-! ## The bracket-square residual -/

/-- **The bracket-square residual supply**: the squares of the `2h` half-damage brackets lie
in the neutral shift span.  This is the exact remaining content of the neutral damage
supply, and the point where a graded-Lie span argument must take over. -/
def SqStageBracketSquareNeutralSupply {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) : Prop :=
  ∀ j : Fin h,
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3))
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxV j))) ^ 2 ∈ stageNeutralShiftSpan T hk ∧
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 3))
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxU j))) ^ 2 ∈ stageNeutralShiftSpan T hk

/-- At handle count zero the bracket-square residual is vacuous. -/
theorem sqStageBracketSquareNeutralSupply_of_rank_zero {k : ℕ}
    (T : SqCyclotomicStageTuple K 0 k) (hk : 3 ≤ k) :
    SqStageBracketSquareNeutralSupply T hk :=
  fun j ↦ j.elim0

/-- **The neutral damage supply from the bracket-square residual**, through the exact
square collapse and neutrality of the junk. -/
theorem sqStageNeutralDamageSupply_of_bracketSquare {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (Hsq : SqStageBracketSquareNeutralSupply T hk) :
    SqStageNeutralDamageSupply T hk := by
  intro j
  constructor
  · rw [stageDamage_decomposition T hk]
    exact Subgroup.mul_mem _ (Hsq j).1 (stageDamage_junk_mem_neutralShiftSpan T hk _)
  · rw [stageDamage_decomposition T hk]
    exact Subgroup.mul_mem _ (Hsq j).2 (stageDamage_junk_mem_neutralShiftSpan T hk _)

/-- **The twisted-bracket normal form of the residual.**  Through the diagonal row, the
square of any depth-`k-1` class is neutral exactly when its bracket against the twisted
letter `x̄₁` is: the residual lives entirely on the twisted slot, where the cyclotomic
character of a commutator carries no information. -/
theorem stageDamage_sq_mem_iff_twistedBracket {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    {B : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hB : B ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)) :
    B ^ 2 ∈ stageNeutralShiftSpan T hk ↔
      commP B (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 2)) ∈
        stageNeutralShiftSpan T hk := by
  have hdiag : B ^ 2 *
      commP B (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 2)) ∈
      stageNeutralShiftSpan T hk :=
    ⟨(rawDepthShiftHom
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk)
          (rawDepthCoordinateCorrection 2 ⟨B, hB⟩),
      ⟨_, stageNeutral_coordinate_mem stageDamage_hU_ne_two stageDamage_hV_ne_two _, rfl⟩,
      rawDepthShiftHom_two_apply
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk ⟨B, hB⟩⟩
  constructor
  · intro hsq
    have hmem := Subgroup.mul_mem _ (Subgroup.inv_mem _ hsq) hdiag
    simpa using hmem
  · intro hbr
    have hmem := Subgroup.mul_mem _ hdiag (Subgroup.inv_mem _ hbr)
    simpa using hmem

/-! ## Functional invisibility of the damage -/

/-- **Every family functional kills the flip damage.**  The damage is the class of an
ambient bracket of a depth-`k-1` power against a kernel-fibre letter, so the crossed
derivation row computation annihilates it; with the span criterion this places the damage in
the full raw shift span, pinning the residual's open content to digit control alone. -/
theorem stageDamage_mem_derivKer {h k : ℕ} {T : SqCyclotomicStageTuple K h k}
    (hk : 3 ≤ k) (F : SqStageCoordinateDerivationFamily T)
    (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2)
    {t : Fin (SqCore.sqRank h)} (ht : sqStageChiTargetUnit h t = 1) :
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators t)) ∈
      derivKer (F.deriv i₀ hi₀) k := by
  obtain ⟨a, ha, -⟩ := stageFlip_exists_canonLift_witness T (by omega) 0
  obtain ⟨b, hb, hbdvd⟩ := stageFlip_exists_canonLift_witness T (by omega) t
  rw [ht] at hbdvd
  have hb4 : (2 : ℤ_[2]) ^ 2 ∣ ((chiCycKTwo (K := K) b : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hweak := dvd_trans (pow_dvd_pow (2 : ℤ_[2]) (by omega : 2 ≤ k + 1)) hbdvd
    simpa using hweak
  have hword : commP
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators t)) =
      levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (commP (a ^ 2 ^ (k - 2)) b) := by
    rw [show levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (commP (a ^ 2 ^ (k - 2)) b) =
        commP (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (a ^ 2 ^ (k - 2)))
          (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) b) from
        Marking.map_commP (levelMk (maxProPQuotient 2 (GalK K)) (k + 1)) _ _,
      map_pow, ha, hb]
  rw [hword]
  refine stageDeriv_commP_row_mem_derivKer hk (F.deriv_base i₀ hi₀) ?_ b hb4
  have hmem := stageDamage_pow_mem a (k - 2)
  rwa [show 1 + (k - 2) = k - 1 by omega] at hmem

/-- With a coordinate derivation family, the flip damage lies in the full raw shift span:
the residual is exclusively about realizing it *neutrally*. -/
theorem stageDamage_mem_rawShiftSpan {h k : ℕ} {T : SqCyclotomicStageTuple K h k}
    (hk : 3 ≤ k) (F : SqStageCoordinateDerivationFamily T)
    {t : Fin (SqCore.sqRank h)} (ht : sqStageChiTargetUnit h t = 1) :
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators t)) ∈
      rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk := by
  have hzmem : commP
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators t)) ∈
      zLayer (maxProPQuotient 2 (GalK K)) k := by
    apply commP_mem_zLayer k hk
    have hmem := pow_two_pow_mem_lambdaImage
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at hmem
  rw [F.mem_rawShiftSpan_iff hk hzmem]
  intro i₀ hi₀
  exact stageDamage_mem_derivKer hk F i₀ hi₀ ht

/-! ## Assembly -/

/-- **The kernel-adapted supply from a family and the bracket-square residual.** -/
theorem sqKernelAdaptedDefectSupply_of_family_of_bracketSquare {h : ℕ}
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      Nonempty (SqStageCoordinateDerivationFamily T))
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k), ∀ T : SqCyclotomicStageTuple K h k,
      SqStageBracketSquareNeutralSupply T hk) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_family_of_neutralDamage Hfam
    (fun k hk T ↦ sqStageNeutralDamageSupply_of_bracketSquare hk (Hsq k hk T))

/-- **The forward presentation theorem over the family and the bracket-square residual.** -/
theorem nonempty_orientedEquiv_oddDegree_of_family_of_bracketSquare
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hfam : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        Nonempty (SqStageCoordinateDerivationFamily T))
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageBracketSquareNeutralSupply T hk) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply hodd
    (sqKernelAdaptedDefectSupply_of_family_of_bracketSquare Hfam Hsq)

#print axioms stageDamage_decomposition
#print axioms stageDamage_junk_mem_neutralShiftSpan
#print axioms sqStageNeutralDamageSupply_of_bracketSquare
#print axioms stageDamage_sq_mem_iff_twistedBracket
#print axioms stageDamage_mem_derivKer
#print axioms stageDamage_mem_rawShiftSpan
#print axioms sqKernelAdaptedDefectSupply_of_family_of_bracketSquare
#print axioms nonempty_orientedEquiv_oddDegree_of_family_of_bracketSquare

end

end GQ2.Dyadic.LSquare
