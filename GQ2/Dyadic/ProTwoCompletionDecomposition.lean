/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MultiplicativeDecomposition
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.ProPCompletionFunctor
import GQ2.ProPCompletionOddIndex

/-!
# Splitting the pro-2 completion of a dyadic multiplicative group

Combining `K× ≃ O_K× × ℤ` with functoriality and product preservation gives

`(K×)^(2) ≃ (O_K×)^(2) × ℤ₂`.

The valuation factor is torsion-free.  Consequently the source-side torsion theorem needed by
the Demushkin-q calculation reduces exactly to the corresponding theorem for norm units.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-! ## Passing from principal units to all norm units -/

omit [FiniteDimensional ℚ_[2] K] in
/-- Every positive-depth unit is a norm-one unit. -/
theorem depthUnits_one_le_normUnits (FF : DyadicUnitFiltration K) :
    depthUnits K FF.π 1 ≤ normUnits K :=
  fun _ hu ↦ ((mem_depthUnits K FF.π 1 _).mp hu).1

omit [FiniteDimensional ℚ_[2] K] in
/-- The residue-unit index `2^f - 1` is odd. -/
theorem odd_two_pow_f_sub_one (FF : DyadicUnitFiltration K) : Odd (2 ^ FF.f - 1) := by
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, Nat.one_le_iff_ne_zero.mp FF.hf_pos⟩) odd_one

/-- `U¹`, regarded as a subgroup of the norm-one units. -/
def normUnitsDepthOneSubgroup (FF : DyadicUnitFiltration K) : Subgroup ↥(normUnits K) :=
  (depthUnits K FF.π 1).subgroupOf (normUnits K)

omit [FiniteDimensional ℚ_[2] K] in
/-- Lagrange in the residue-unit quotient: every norm unit raised to `2^f - 1` lies in
`U¹`. -/
theorem normUnits_pow_residueIndex_mem_depthOne (FF : DyadicUnitFiltration K)
    (u : ↥(normUnits K)) : u ^ (2 ^ FF.f - 1) ∈ normUnitsDepthOneSubgroup FF := by
  let H := normUnitsDepthOneSubgroup FF
  have hcard : Nat.card (↥(normUnits K) ⧸ H) = 2 ^ FF.f - 1 := FF.card_gr_zero
  have hgpow : (QuotientGroup.mk' H u) ^ Nat.card (↥(normUnits K) ⧸ H) = 1 :=
    pow_card_eq_one'
  rw [hcard, ← map_pow] at hgpow
  change u ^ (2 ^ FF.f - 1) ∈ H
  exact (QuotientGroup.eq_one_iff _).mp hgpow

/-- Forgetting the redundant norm-unit membership identifies the subgroup form of `U¹` with
the original depth-unit group. -/
noncomputable def normUnitsDepthOneSubgroupEquiv (FF : DyadicUnitFiltration K) :
    normUnitsDepthOneSubgroup FF ≃* ↥(depthUnits K FF.π 1) :=
  Subgroup.subgroupOfEquivOfLe (depthUnits_one_le_normUnits FF)

/-- **Odd-index completion bridge.**  Inclusion `U¹ ↪ O_Kˣ` induces an equivalence on
abstract pro-2 completions. -/
noncomputable def proTwoCompletionDepthOneEquivNormUnits
    (FF : DyadicUnitFiltration K) :
    ContinuousMulEquiv (proPCompletion 2 ↥(depthUnits K FF.π 1))
      (proPCompletion 2 ↥(normUnits K)) := by
  exact (proPCompletionCongr (p := 2) (normUnitsDepthOneSubgroupEquiv FF).symm).trans
    (proTwoCompletionSubgroupEquivOfOddPowerMem (normUnitsDepthOneSubgroup FF)
      (2 ^ FF.f - 1) (odd_two_pow_f_sub_one FF)
      (normUnits_pow_residueIndex_mem_depthOne FF))

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem proTwoCompletionDepthOneEquivNormUnits_mk
    (FF : DyadicUnitFiltration K) (u : ↥(depthUnits K FF.π 1)) :
    proTwoCompletionDepthOneEquivNormUnits FF
        (proPCompletionMk 2 ↥(depthUnits K FF.π 1) u) =
      proPCompletionMk 2 ↥(normUnits K)
        ⟨u.1, (depthUnits_one_le_normUnits FF) u.2⟩ := by
  rw [proTwoCompletionDepthOneEquivNormUnits, ContinuousMulEquiv.trans_apply,
    proPCompletionCongr_mk, proTwoCompletionSubgroupEquivOfOddPowerMem_mk]
  rfl

/-- Completion-level form of `K× ≃ O_K× × ℤ`. -/
def proTwoCompletionUnitsEquiv :
    ContinuousMulEquiv (proPCompletion 2 ((↥K)ˣ))
      (proPCompletion 2 ↥(normUnits K) × proPCompletion 2 (Multiplicative ℤ)) :=
  (proPCompletionCongr (p := 2) (unitsEquivNormUnitsProdInt (dyadicUnitFiltration K))).trans
    (proPCompletionProdEquiv (p := 2))

@[simp] theorem proTwoCompletionUnitsEquiv_mk (x : (↥K)ˣ) :
    proTwoCompletionUnitsEquiv (K := K) (proPCompletionMk 2 ((↥K)ˣ) x) =
      (proPCompletionMk 2 ↥(normUnits K) (normalizedUnit (dyadicUnitFiltration K) x),
        proPCompletionMk 2 (Multiplicative ℤ)
          (Multiplicative.ofAdd (dyadicValuation (dyadicUnitFiltration K) x))) := by
  rw [proTwoCompletionUnitsEquiv, ContinuousMulEquiv.trans_apply,
    proPCompletionCongr_mk, proPCompletionProdEquiv_mk]
  rfl

/-- The valuation factor is the usual additive `ℤ₂`, written multiplicatively. -/
def proTwoCompletionMultiplicativeIntEquivPadic :
    ContinuousMulEquiv (proPCompletion 2 (Multiplicative ℤ)) (Multiplicative ℤ_[2]) := by
  change ContinuousMulEquiv (maxProPQuotient 2 Zhat) (Multiplicative ℤ_[2])
  exact ztwoEquivPadic

/-- The pro-2 completion of the integer valuation group is torsion-free. -/
theorem isMulTorsionFree_proTwoCompletion_multiplicativeInt :
    IsMulTorsionFree (proPCompletion 2 (Multiplicative ℤ)) := by
  constructor
  intro n hn x y hxy
  apply (proTwoCompletionMultiplicativeIntEquivPadic).injective
  apply IsMulTorsionFree.pow_left_injective hn
  simpa only [map_pow] using congrArg proTwoCompletionMultiplicativeIntEquivPadic hxy

/-- A torsion point in `(K×)^(2)` has trivial valuation coordinate. -/
theorem proTwoCompletionUnitsEquiv_snd_eq_one_of_isOfFinOrder
    (x : proPCompletion 2 ((↥K)ˣ)) (hx : IsOfFinOrder x) :
    (proTwoCompletionUnitsEquiv (K := K) x).2 = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hx
  obtain ⟨n, hn, hxn⟩ := hx
  letI := isMulTorsionFree_proTwoCompletion_multiplicativeInt
  apply IsMulTorsionFree.pow_left_injective (Nat.ne_of_gt hn)
  have hmap := congrArg Prod.snd
    (map_pow (proTwoCompletionUnitsEquiv (K := K)) x n)
  change (proTwoCompletionUnitsEquiv (K := K) (x ^ n)).2 =
    (proTwoCompletionUnitsEquiv (K := K) x).2 ^ n at hmap
  calc
    (proTwoCompletionUnitsEquiv (K := K) x).2 ^ n =
        (proTwoCompletionUnitsEquiv (K := K) (x ^ n)).2 := hmap.symm
    _ = 1 := by rw [hxn, map_one, Prod.snd_one]
    _ = 1 ^ n := (one_pow n).symm

/-- A 2-primary root of unity, regarded as a norm-one unit. -/
def twoPowerRootNormUnit (x : TwoPowerRoots K) : ↥(normUnits K) :=
  ⟨twoPowerRootUnit x, by
    rw [mem_normUnits]
    obtain ⟨n, hn⟩ := x.2
    have hxfin : IsOfFinOrder x.1 :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ n, by positivity, hn⟩
    exact hxfin.norm_eq_one⟩

@[simp] theorem dyadicValuation_twoPowerRootUnit (x : TwoPowerRoots K) :
    dyadicValuation (dyadicUnitFiltration K) (twoPowerRootUnit x) = 0 := by
  apply dyadicValuation_eq_of_norm_eq_zpow _ _ 0
  rw [show ‖(((twoPowerRootUnit x : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ = 1 from
    (mem_normUnits K (twoPowerRootNormUnit x).1).mp (twoPowerRootNormUnit x).2, zpow_zero]

@[simp] theorem normalizedUnit_twoPowerRootUnit (x : TwoPowerRoots K) :
    normalizedUnit (dyadicUnitFiltration K) (twoPowerRootUnit x) = twoPowerRootNormUnit x := by
  apply Subtype.ext
  change twoPowerRootUnit x * uniformizerK K (dyadicUnitFiltration K) ^
      (-dyadicValuation (dyadicUnitFiltration K) (twoPowerRootUnit x)) = twoPowerRootUnit x
  rw [dyadicValuation_twoPowerRootUnit, neg_zero, zpow_zero, mul_one]

/-- Torsion in the norm-unit completion is generated by actual 2-primary field roots. -/
def NormUnitsProTwoCompletionTorsionGeneratedByFieldRoots : Prop :=
  ∀ y : {y : proPCompletion 2 ↥(normUnits K) // IsOfFinOrder y},
    ∃ x : TwoPowerRoots K,
      proPCompletionMk 2 ↥(normUnits K) (twoPowerRootNormUnit x) = y.1

/-- **Torsion theorem for completed norm units.**  Every finite-order point of the abstract
pro-2 completion of `O_Kˣ` is the canonical image of an actual 2-primary root of unity in
`K`.

The proof transports the point across `(O_Kˣ)^(2) ≃ (U¹)^(2) ≃ U¹`.  Its pullback is killed
by a power of `2` because `(U¹)^(2)` is pro-2, and hence gives the required field root. -/
theorem normUnitsProTwoCompletionTorsionGeneratedByFieldRoots :
    NormUnitsProTwoCompletionTorsionGeneratedByFieldRoots (K := K) := by
  intro y
  let FF := dyadicUnitFiltration K
  let E := proTwoCompletionDepthOneEquivNormUnits FF
  let D := depthUnitsEquivProTwoCompletion FF (i := 1) (by omega)
  have hzfin : IsOfFinOrder (E.symm y.1) := E.symm.toMonoidHom.isOfFinOrder y.2
  obtain ⟨k, hzk⟩ := exists_twoPower_pow_eq_one_of_isOfFinOrder
    isProP_maxProPQuotient (E.symm y.1) hzfin
  let u : ↥(depthUnits K FF.π 1) := D.symm (E.symm y.1)
  have hDu : D u = E.symm y.1 := by
    exact D.apply_symm_apply _
  have huPow : u ^ (2 ^ k) = 1 := by
    apply D.injective
    rw [map_pow, map_one, hDu]
    exact hzk
  let x : TwoPowerRoots K :=
    ⟨(u.1 : ↥K), ⟨k, by
      have huUnits : (u.1 : (↥K)ˣ) ^ (2 ^ k) = 1 := congrArg Subtype.val huPow
      exact congrArg Units.val huUnits⟩⟩
  let uNorm : ↥(normUnits K) :=
    ⟨u.1, (depthUnits_one_le_normUnits FF) u.2⟩
  have hxunit : twoPowerRootNormUnit x = uNorm := by
    apply Subtype.ext
    apply Units.ext
    rfl
  refine ⟨x, ?_⟩
  rw [hxunit]
  calc
    proPCompletionMk 2 ↥(normUnits K) uNorm =
        E (proPCompletionMk 2 ↥(depthUnits K FF.π 1) u) :=
      (proTwoCompletionDepthOneEquivNormUnits_mk FF u).symm
    _ = E (D u) := by rfl
    _ = E (E.symm y.1) := by rw [hDu]
    _ = y.1 := E.apply_symm_apply _

/-- **Exact remaining source-side reduction.**  Once torsion in the norm-unit completion is
generated by field roots, the same is true in the full multiplicative completion; the
valuation factor contributes no torsion. -/
theorem proTwoCompletionTorsionGeneratedByFieldRoots_of_normUnits
    (hU : NormUnitsProTwoCompletionTorsionGeneratedByFieldRoots (K := K)) :
    ProTwoCompletionTorsionGeneratedByFieldRoots K := by
  intro y
  let E := proTwoCompletionUnitsEquiv (K := K)
  have hfirst : IsOfFinOrder (E y.1).1 := by
    have hy := y.2
    rw [isOfFinOrder_iff_pow_eq_one] at hy ⊢
    obtain ⟨n, hn, hyn⟩ := hy
    refine ⟨n, hn, ?_⟩
    have hmap := congrArg Prod.fst (map_pow E y.1 n)
    change (E (y.1 ^ n)).1 = (E y.1).1 ^ n at hmap
    calc
      (E y.1).1 ^ n = (E (y.1 ^ n)).1 := hmap.symm
      _ = 1 := by rw [hyn, map_one, Prod.fst_one]
  obtain ⟨x, hx⟩ := hU ⟨(E y.1).1, hfirst⟩
  refine ⟨x, Subtype.ext ?_⟩
  apply E.injective
  change E (proPCompletionMk 2 ((↥K)ˣ) (twoPowerRootUnit x)) = E y.1
  rw [proTwoCompletionUnitsEquiv_mk, normalizedUnit_twoPowerRootUnit,
    dyadicValuation_twoPowerRootUnit,
    show Multiplicative.ofAdd (0 : ℤ) = 1 from rfl, map_one]
  apply Prod.ext
  · simpa using hx
  · simpa using
      (proTwoCompletionUnitsEquiv_snd_eq_one_of_isOfFinOrder y.1 y.2).symm

/-- **Source-side local completion theorem.**  All torsion in the abstract pro-2 completion
of `K×` comes from actual 2-primary roots of unity in `K`. -/
theorem proTwoCompletionTorsionGeneratedByFieldRoots :
    ProTwoCompletionTorsionGeneratedByFieldRoots K :=
  proTwoCompletionTorsionGeneratedByFieldRoots_of_normUnits
    (normUnitsProTwoCompletionTorsionGeneratedByFieldRoots (K := K))

#print axioms proTwoCompletionUnitsEquiv
#print axioms isMulTorsionFree_proTwoCompletion_multiplicativeInt
#print axioms normUnitsProTwoCompletionTorsionGeneratedByFieldRoots
#print axioms proTwoCompletionTorsionGeneratedByFieldRoots_of_normUnits
#print axioms proTwoCompletionTorsionGeneratedByFieldRoots

end

end GQ2.Dyadic
