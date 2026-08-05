/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteBracketSquareNeutral
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageKummerCocycle
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse

/-!
# The twisted-cocycle parity supply for odd-degree fields

This file proves `SqStageTwistedCocycleParitySupply T` for every stage tuple of every
odd-degree field at every level `k ≥ 3`, discharging the parity half of the campaign's
remaining L-row gap.

The construction composes the two halves already available:

* **the prescription** (this file): on the `n + 2 = sqRank h`-dimensional character group
  of `G_K(2)`, evaluation at the exact-fibre stage lifts is injective — every continuous
  mod-2 character kills `λ₂ ⊇ λ_k` and the level-`k` classes of the lifts generate — and
  the source and target have the same cardinality `2^(n+2)` by the Demushkin `H¹` count,
  so evaluation is a bijection (`stageKummer_exists_dual_character`).  The dual-basis
  character with odd value exactly at slot `i₀` is realized as the mod-2 Kummer class of
  some `a ∈ Kˣ` by Kummer surjectivity (`stageKummer_exists_kummer_of_character`);
* **the lift** (previous file): the χ-twisted higher Kummer cocycle of that `a` at a
  `2^(k+1)`-th root is a continuous χ-twisted one-cocycle on `G_K(2)` whose value
  parities at classes from `G_K` are the mod-2 Kummer signs of `a`.

With the bracket-square residual, the endpoint
`nonempty_orientedEquiv_oddDegree_of_bracketSquare` delivers the forward presentation
theorem for every odd-degree field; composing with the bracket-square tower collapse,
`nonempty_orientedEquiv_oddDegree_of_cubicNeutralDamage` reduces the whole forward route
to the mod-16 neutral damage supply at the single cubic stage.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH
open ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## The character count at odd degree -/

omit [T2Space (GalK K)] in
/-- At odd degree `n = 2h + 1`, the continuous mod-2 characters of `G_K(2)` are counted by
the improved presentation's rank: `2^(n+2) = 2^(sqRank h)`. -/
theorem stageKummer_card_characters (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    Nat.card (ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
        (Multiplicative (ZMod 2))) =
      Nat.card (Fin (SqCore.sqRank h) → Multiplicative (ZMod 2)) := by
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo (maxProPQuotient 2 (GalK K))
  rw [Count.card_hom_eq_card_Z1,
    show Nat.card ↥(Z1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
        Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) from
      (Nat.card_congr (H1equivZ1OfTrivial Count.smul_zmod2).toEquiv).symm,
    card_H1_zmodTwo_maxProTwoGalK (K := K),
    Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  congr 1
  simp only [SqCore.sqRank, hdeg]
  omega

/-! ## Evaluation at the stage lifts is injective -/

/-- Two continuous mod-2 characters of `G_K(2)` agreeing at ambient lifts of a stage
tuple's generators agree: characters kill `λ_k`, and the generators generate level `k`. -/
theorem stageKummer_characters_ext {h k : ℕ} (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple K h k)
    {lifts : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)}
    (hlvl : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i)
    {c₁ c₂ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
      (Multiplicative (ZMod 2))}
    (hev : ∀ i, c₁ (lifts i) = c₂ (lifts i)) : c₁ = c₂ := by
  have hle₁ : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ c₁.toMonoidHom.ker :=
    le_trans (twoCentralSeries_antitone _ (by omega : 2 ≤ k))
      (twoCentralSeries_two_le_continuousCharacter_ker c₁)
  have hle₂ : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ c₂.toMonoidHom.ker :=
    le_trans (twoCentralSeries_antitone _ (by omega : 2 ≤ k))
      (twoCentralSeries_two_le_continuousCharacter_ker c₂)
  set f₁ := quotientLift (twoCentralSeries (maxProPQuotient 2 (GalK K)) k) c₁ hle₁
  set f₂ := quotientLift (twoCentralSeries (maxProPQuotient 2 (GalK K)) k) c₂ hle₂
  have heqOn : Set.EqOn ⇑f₁.toMonoidHom ⇑f₂.toMonoidHom (Set.range T.generators) := by
    rintro x ⟨i, rfl⟩
    rw [← hlvl i]
    show c₁ (lifts i) = c₂ (lifts i)
    exact hev i
  have hclosure := MonoidHom.eqOn_closure heqOn
  ext g
  have hg : levelMk (maxProPQuotient 2 (GalK K)) k g ∈
      (Subgroup.closure (Set.range T.generators) : Set _) := by
    rw [T.topGen]
    trivial
  exact hclosure hg

/-! ## The dual-basis character -/

/-- **The dual-basis character at a slot.**  At odd degree, evaluation of the character
group at the stage lifts is a bijection onto all value patterns, so each slot has a
character odd exactly there. -/
theorem stageKummer_exists_dual_character {h k : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple K h k)
    {lifts : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)}
    (hlvl : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i)
    (i₀ : Fin (SqCore.sqRank h)) :
    ∃ c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      Multiplicative.toAdd (c (lifts i₀)) = 1 ∧
        ∀ j : Fin (SqCore.sqRank h), j ≠ i₀ →
          Multiplicative.toAdd (c (lifts j)) = 0 := by
  have hbij : Function.Bijective
      (fun (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
        (Multiplicative (ZMod 2))) (i : Fin (SqCore.sqRank h)) ↦ c (lifts i)) := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨fun c₁ c₂ hcc ↦ stageKummer_characters_ext hk T hlvl
        (fun i ↦ congrFun hcc i),
      stageKummer_card_characters h hdeg⟩
  obtain ⟨c, hc⟩ := hbij.2
    (fun j ↦ if j = i₀ then Multiplicative.ofAdd 1 else 1)
  refine ⟨c, ?_, ?_⟩
  · have h1 : c (lifts i₀) = Multiplicative.ofAdd 1 := by
      have h2 := congrFun hc i₀
      simpa using h2
    rw [h1]
    rfl
  · intro j hj
    have h1 : c (lifts j) = 1 := by
      have h2 := congrFun hc j
      simpa [hj] using h2
    rw [h1]
    rfl

/-! ## Kummer realization of a character of `G_K(2)` -/

omit [T2Space (GalK K)] in
/-- **Kummer realization.**  Every continuous mod-2 character of `G_K(2)` is, on classes
from `G_K`, the mod-2 Kummer sign cocycle of some `a ∈ Kˣ`: inflate to `G_K` and apply
Kummer surjectivity; the class equality is a cocycle equality since `B¹` vanishes for the
trivial action. -/
theorem stageKummer_exists_kummer_of_character
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    ∃ a : (↥K)ˣ, ∀ g : ↥(K.fixingSubgroup),
      Kummer.kummerCocycleFun (sqrtCl (((a : ↥K) : ℚ̄₂)))
          (g : Kummer.GaloisGroup ℚ_[2]) =
        Multiplicative.toAdd (c (maxProPMk 2 (GalK K) g)) := by
  set cG : ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2)) :=
    c.comp (maxProPMk 2 (GalK K)) with hcG
  obtain ⟨a, ha⟩ := kummerClassK_surjective K (H1mk _ _ (Count.homEquivZ1 cG))
  refine ⟨a, fun g ↦ ?_⟩
  rw [kummerClassK] at ha
  have hsub := QuotientAddGroup.eq_iff_sub_mem.mp ha
  rw [AddSubgroup.mem_addSubgroupOf,
    B1_eq_bot_of_trivial (fun (_ : ↥(K.fixingSubgroup)) (_ : ZMod 2) ↦ rfl),
    AddSubgroup.mem_bot] at hsub
  have hz : (fun g : ↥(K.fixingSubgroup) ↦
        Kummer.kummerCocycleFun (sqrtCl (((a : ↥K) : ℚ̄₂)))
          (g : Kummer.GaloisGroup ℚ_[2])) -
      ((Count.homEquivZ1 cG : ↥(Z1 ↥(K.fixingSubgroup) (ZMod 2))) :
        ↥(K.fixingSubgroup) → ZMod 2) = 0 := by
    simpa using hsub
  have hfun := sub_eq_zero.mp hz
  exact congrFun hfun g

/-! ## The parity supply -/

/-- **The twisted-cocycle parity supply at exact odd degree.**  For
`[K : ℚ₂] = 2h + 1`, every stage tuple at every level `k ≥ 3` has the supply: the
dual-basis character of each non-twisted slot is the Kummer class of some `a ∈ Kˣ`, and
the χ-twisted higher Kummer cocycle of `a` at a `2^(k+1)`-th root realizes the required
parities. -/
theorem sqStageTwistedCocycleParitySupply_of_finrank {h k : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple K h k) :
    SqStageTwistedCocycleParitySupply T := by
  obtain ⟨lifts, hchi, hlvl⟩ := T.exists_exactChiLift
  refine ⟨lifts, hchi, hlvl, ?_⟩
  intro i₀ hi₀
  have hsurj : Function.Surjective (maxProPMk 2 (GalK K)) := quotientMk_surjective _
  choose gs hgs using fun i ↦ hsurj (lifts i)
  obtain ⟨c, hcd, hco⟩ := stageKummer_exists_dual_character hdeg hk T hlvl i₀
  obtain ⟨a, ha⟩ := stageKummer_exists_kummer_of_character c
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄₂ (2 ^ (k + 1))
  have h2p : (2 : ℕ) ^ (k + 1) ≠ 0 := by positivity
  have hzu : IsPrimitiveRoot ((hz.isUnit h2p).unit) (2 ^ (k + 1)) :=
    hz.isUnit_unit h2p
  have halpha := higherRootUnit_pow (2 ^ (k + 1)) a
  have hN1 : 1 ≤ k + 1 := by omega
  have hval : ∀ i, (chiTwistedKummerDescent hzu a halpha hN1 (lifts i)).u =
      chiTwistedKummerFun hzu a halpha (gs i) := by
    intro i
    rw [← hgs i, chiTwistedKummerDescent_u_mk]
  refine ⟨fun q ↦ (chiTwistedKummerDescent hzu a halpha hN1 q).u,
    isChiTwistedCocycle_chiTwistedKummerDescent hzu a halpha hN1, ?_, ?_⟩
  · intro hdvd
    have hdvd' : (2 : ZMod (2 ^ (k + 1))) ∣
        (chiTwistedKummerDescent hzu a halpha hN1 (lifts i₀)).u := hdvd
    rw [hval i₀] at hdvd'
    have h0 := (chiTwistedKummerFun_parity hzu a halpha hN1 (gs i₀)).mp hdvd'
    rw [ha (gs i₀), hgs i₀, hcd] at h0
    exact one_ne_zero h0
  · intro j hj2 hji
    show (2 : ZMod (2 ^ (k + 1))) ∣ (chiTwistedKummerDescent hzu a halpha hN1 (lifts j)).u
    rw [hval j]
    refine (chiTwistedKummerFun_parity hzu a halpha hN1 (gs j)).mpr ?_
    rw [ha (gs j), hgs j]
    exact hco j hji

/-- **The twisted-cocycle parity supply for odd-degree fields**, in the handle count
`(n - 1)/2` used by the campaign endpoint. -/
theorem sqStageTwistedCocycleParitySupply_oddDegree
    (hodd : Odd (Module.finrank ℚ_[2] K)) {k : ℕ} (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k) :
    SqStageTwistedCocycleParitySupply T :=
  sqStageTwistedCocycleParitySupply_of_finrank
    (by obtain ⟨m, hm⟩ := hodd; omega) hk T

/-! ## The campaign endpoint over the bracket-square residual -/

/-- **The kernel-adapted supply over the bracket-square residual alone**: the cocycle
parity half is now a theorem. -/
theorem sqKernelAdaptedDefectSupply_of_bracketSquare {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k), ∀ T : SqCyclotomicStageTuple K h k,
      SqStageBracketSquareNeutralSupply T hk) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_cocycleParity_of_bracketSquare
    (fun _ hk T ↦ sqStageTwistedCocycleParitySupply_of_finrank hdeg hk T) Hsq

/-- **The forward presentation theorem over the bracket-square residual.**  For every
odd-degree field, the neutral realizations of the `2h` half-damage bracket squares at
every stage are the campaign's entire remaining L-row gap: the twisted-cocycle parity
supply is now unconditional. -/
theorem nonempty_orientedEquiv_oddDegree_of_bracketSquare
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hsq : ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageBracketSquareNeutralSupply T hk) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_cocycleParity_of_bracketSquare hodd
    (fun _ hk T ↦ sqStageTwistedCocycleParitySupply_oddDegree hodd hk T) Hsq

/-- **The forward presentation theorem over the cubic residual alone.**  Combining the now
unconditional parity supply with the bracket-square tower collapse: for every odd-degree
field, the mod-16 neutral damage supply at the single cubic stage delivers the oriented
presentation equivalence. -/
theorem nonempty_orientedEquiv_oddDegree_of_cubicNeutralDamage
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hcubic : SqCubicNeutralDamageSupply K ((Module.finrank ℚ_[2] K - 1) / 2)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_family_of_cubicNeutralDamage hodd
    (fun _ hk T ↦ nonempty_family_of_twistedCocycleParitySupply
      (sqStageTwistedCocycleParitySupply_oddDegree hodd hk T))
    Hcubic

#print axioms stageKummer_card_characters
#print axioms stageKummer_characters_ext
#print axioms stageKummer_exists_dual_character
#print axioms stageKummer_exists_kummer_of_character
#print axioms sqStageTwistedCocycleParitySupply_of_finrank
#print axioms sqStageTwistedCocycleParitySupply_oddDegree
#print axioms sqKernelAdaptedDefectSupply_of_bracketSquare
#print axioms nonempty_orientedEquiv_oddDegree_of_bracketSquare
#print axioms nonempty_orientedEquiv_oddDegree_of_cubicNeutralDamage

end

end GQ2.Dyadic.LSquare
