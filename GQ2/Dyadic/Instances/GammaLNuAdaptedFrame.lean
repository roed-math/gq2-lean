/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLNuAdaptedKappaValue
import GQ2.Dyadic.Instances.GammaLOddDegreePresentingFrame

/-!
# The fully `ν`-adapted frame, and the odd-degree row over **one** binder

`GammaLNuAdaptedPlacement` settles the dimension count (the whole marking fits inside the Witt
adaptation, over two `𝔽₂` cup values) and `GammaLNuAdaptedKappaValue` discharges the second of
those values.  The first is already discharged (`NuKummer.nuUrOmegaCupOne_of_odd`).  This file
runs the construction and cashes it in.

## What is proved

* **§2 `exists_isCupAdapted_fullNuEvals_of_cupData`** — for every odd-degree `K` a cup-adapted
  Frattini frame on which `ν̄` is the `σ`-**dual basis vector**: value `1` at the `σ`-generator
  and `0` at *every* other generator, `x₁` and all `2h` handle letters included.  This is
  `MarkedFrame.exists_isCupAdapted_evals_of_cupOne` with the hyperbolic partner of `τ` taken to
  be `ν̄` itself, which is legitimate exactly over the two cup values.
* **§3 `exists_isCupAdapted_fullNuRows_of_evals`** — the exact `ℤ₂` rows from the mod-two rows,
  by one Frattini-coset square shift at *every* index (the two-slot shift of the frame file,
  run uniformly).  Wave 38's warning is respected: the shift happens at construction time,
  before any relator claim is made about the frame, and no invariant is asked to survive it.
* **§4 `sqFullNuForwardSupply_of_fullNuFrame`** — the conversion.  A frame with the full marking
  which *presents* gives `MarkingAudit.SqFullNuForwardSupply` outright: rigidity turns the frame
  into an equivalence sending `sqGen i ↦ generators i`, and `SqCore.nu_eq_nuSq_of_core`
  propagates the four generator rows to every point of `D_sq(h)` (the `x₁`-row is forced).
* **§5 `gammaR_lSq_equiv_galK_oddDegree_of_frameRelator`** — the payoff.  `Γ_{R_K} ≅ G_K` for
  every odd-degree ramified `K` over the **single** binder `SqCupAdaptedFrameRelator K`.  The
  χ-free clearing binder `SqCore.SqNuClearHypothesis h` — the hypothesis the two banked machine
  searches were aimed at — is **gone** from the odd-degree row: it was only ever the
  two-rows-to-all-rows bridge, and the frame now carries all rows by construction.

## What is not proved

`SqCupAdaptedFrameRelator K` itself.  `GammaLOddDegreePresentingFrame` builds a frame that
*does* carry the relator unconditionally (`frameOfOrientedEquiv`), but that frame is not known
to be cup-adapted, and the two horns are still joined only by the reconciliation described
there.  What this file changes is which horn is missing: after it, the odd-degree residual is a
statement with **no `ν` in it at all**.

## Axioms

Std-3 plus the census members already carried by the frame lane: `tateDualityAt` (**B6**),
`hilbertSymbol_normCriterion_finiteDyadic` (**B11a**),
`absGalQ2_isTopologicallyFinitelyGenerated` (**B1**), `absGalQ2_localEulerCharacteristic`
(**B7**), and — in §5 only, inherited from the grand assembly — the remaining bundle members.
No `sorry`, no new axiom, no `native_decide`.  Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic ContCoh SqCore
open GQ2.Roe.Labute
open GQ2.Dyadic.Certificates.LSqStokes
open FrattiniFrameSupply
open MarkedFrame

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

/-! ## §1 The `σ`-dual model vector, read at every coordinate

`(0, ((1, 0), 0))` is the coordinate vector of the first dual basis vector: `1` at the `σ`-slot
and `0` at the `x₀`-slot, the `x₁`-slot (the `⟨1⟩` factor) and every handle slot. -/

section ModelCoords

/-- The `σ`-dual model vector reads `0` at every coordinate but the `σ`-one. -/
theorem modelCoordAt_sigmaDual_eq_zero (k : ℕ) {s : Fin 3 ⊕ (Fin k × Fin 2)}
    (hs : s ≠ Sum.inl 0) :
    modelCoordAt k s ((0 : ZMod 2), (((1 : ZMod 2), (0 : ZMod 2)),
      (0 : Fin k → ZMod 2 × ZMod 2))) = 0 := by
  rcases s with a | p
  · have ha : a ≠ 0 := fun hcon ↦ hs (by rw [hcon])
    simp only [modelCoordAt, Sum.elim_inl]
    rw [if_neg ha]
    split_ifs <;> rfl
  · simp only [modelCoordAt, Sum.elim_inr]
    split_ifs <;> rfl

/-- Only the `σ`-index of the frame alphabet hits the `σ`-slot. -/
theorem sqInitialAlphabetEquiv_ne_inl_zero {k : ℕ} {i : Fin (SqCore.sqRank k)} (hi : i ≠ 0) :
    GQ2.ContCoh.sqInitialAlphabetEquiv k i ≠ Sum.inl 0 := by
  intro hcon
  refine hi ((GQ2.ContCoh.sqInitialAlphabetEquiv k).injective ?_)
  rw [hcon, GQ2.ContCoh.sqInitialAlphabetEquiv_zero]

/-- The `x₀`-index is not the `σ`-index. -/
theorem sqOne_ne_zero (k : ℕ) : (1 : Fin (SqCore.sqRank k)) ≠ 0 := by
  intro hcon
  have hval := congrArg Fin.val hcon
  rw [SqCore.sqVal_zero, SqCore.sqVal_one] at hval
  exact absurd hval (by decide)

/-- The `x₁`-index is not the `σ`-index. -/
theorem sqTwo_ne_zero (k : ℕ) : (2 : Fin (SqCore.sqRank k)) ≠ 0 := by
  intro hcon
  have hval := congrArg Fin.val hcon
  rw [SqCore.sqVal_zero, SqCore.sqVal_two] at hval
  exact absurd hval (by decide)

/-- No handle index is the `σ`-index. -/
theorem sqHandleIdxU_ne_zero {k : ℕ} (j : Fin k) : SqCore.sqHandleIdxU j ≠ 0 :=
  SqCore.sqHandleIdxU_ne_of_val_lt j (by rw [SqCore.sqVal_zero]; norm_num)

/-- The same for the second handle letter. -/
theorem sqHandleIdxV_ne_zero {k : ℕ} (j : Fin k) : SqCore.sqHandleIdxV j ≠ 0 :=
  SqCore.sqHandleIdxV_ne_of_val_lt j (by rw [SqCore.sqVal_zero]; norm_num)

end ModelCoords

/-! ## §2 The cup-adapted frame carrying **every** mod-two row of `ν̄` -/

section FullEvals

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The fully `ν`-adapted frame, mod two.**  Over the two `𝔽₂` cup data there is a cup-adapted
Frattini frame whose dual basis has `ν̄` as its *first vector*: the unramified class evaluates to
`1` on the `σ`-generator and to `0` on every other generator.

This is `MarkedFrame.exists_isCupAdapted_evals_of_cupOne` with `frattiniFrameAdaptedModelEquiv`
replaced by its fully placed refinement — the hyperbolic partner of `τ` is `ν̄` itself. -/
theorem exists_isCupAdapted_fullNuEvals_of_cupData (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hcup : NuUrOmegaCupOne B)
    (hkappa : NuUrKappaCupZero B) :
    ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2), F.IsCupAdapted ∧
      frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) = 1 ∧
        ∀ i, i ≠ 0 → frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators i) = 0 := by
  classical
  obtain ⟨k, hk⟩ := id hodd
  rw [show (Module.finrank ℚ_[2] K - 1) / 2 = k from by omega]
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * k + 3) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K),
      show Module.finrank ℚ_[2] K + 2 = 2 * k + 3 from by omega]
  have hnt : frattiniFrameCup (K := K) (nuUrModTwoClassKTwo B)
      (cyclotomicModEightOmegaClassKTwo (K := K)) = 1 := by
    rw [(isCupFormFp2_frattiniFrameCup (K := K)).symm]
    exact hcup
  obtain ⟨Φ, hGram, hΦκ, hΦτ, hΦν⟩ :=
    frattiniFrameAdaptedModelEquiv_fullPlaced (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (frattiniFrameCup_kappa_self (K := K) hodd) (frattiniFrameCup_omega_modFour (K := K))
      hkappa hnt hcard
  choose gens' hgens' using fun i : Fin (SqCore.sqRank k) ↦
    frattiniFrameEval_realizable (K := K) hfin
      ((modelCoordL k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x ↦ hgens' i x
  have hsupply := SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply B hodd
  have hmatch4 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦκ]
    exact frattiniFrame_match_parity k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  have hmatch8 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦτ]
    exact frattiniFrame_match_omega k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  choose gens hχ hlevel using fun i : Fin (SqCore.sqRank k) ↦
    frattiniFrameExactLift (K := K) hsupply (gens' i) (frattiniFrameTarget k i)
      (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x ↦
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hχ 0, frattiniFrameTarget_zero]
  · rw [hχ 1, frattiniFrameTarget_one]
  · rw [hχ 2, frattiniFrameTarget_two]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxU j)) = 1
    rw [hχ (SqCore.sqHandleIdxU j), frattiniFrameTarget_handleU]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxV j)) = 1
    rw [hχ (SqCore.sqHandleIdxV j), frattiniFrameTarget_handleV]
  · by_contra hne
    haveI hFfin : Finite (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      finite_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient 2
    haveI hFdisc : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
        isProP_maxProPQuotient 2
    obtain ⟨c, hcH, hcne⟩ := frattiniFrame_exists_modTwo_character
      (frattiniFrame_levelTwo_mul_comm (maxProPQuotient 2 (GalK K)))
      (frattiniFrame_levelTwo_sq (maxProPQuotient 2 (GalK K))) hne
    set cQ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
      ⟨c.comp (levelMk (maxProPQuotient 2 (GalK K)) 2), by
        have h1 : Continuous c := continuous_of_discreteTopology
        exact h1.comp (continuous_levelMk (maxProPQuotient 2 (GalK K)) 2)⟩ with hcQ
    have hvanish : ∀ i, frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) (gens i) = 0 := by
      intro i
      rw [frattiniFrameEval_characterClass]
      show Multiplicative.toAdd (c (levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i))) = 0
      rw [hcH _ (Subgroup.subset_closure ⟨i, rfl⟩)]
      rfl
    have hΦ0 : Φ (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) = 0 := by
      apply modelCoordAt_eq_zero
      intro s
      have hs := hvanish ((GQ2.ContCoh.sqInitialAlphabetEquiv k).symm s)
      rw [hD2] at hs
      rwa [Equiv.apply_symm_apply] at hs
    have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
      have hs := congrArg Φ.symm hΦ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    apply hcne
    apply MonoidHom.ext
    intro f
    obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 f
    have hg : frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) g =
          Multiplicative.toAdd (cQ g) := frattiniFrameEval_characterClass cQ g
    rw [hcc0, frattiniFrameEval_zero] at hg
    show c (levelMk (maxProPQuotient 2 (GalK K)) 2 g) = 1
    have hone : cQ g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hg]
      rfl
    exact hone
  · show ∀ c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      FieldData.cupFormK K
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) =
        GQ2.ContCoh.sqRelatorQuadraticInitialGram k
          (fun i j ↦ Multiplicative.toAdd (c (gens i)) * Multiplicative.toAdd (d (gens j)))
    intro c d
    have h1 := hGram (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) d)
    refine h1.trans ?_
    rw [← sqRelatorQuadraticInitialGram_modelCoord]
    congr 1
    funext i j
    rw [← hD2 i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
      ← hD2 j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
      frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]
  · show frattiniFrameEval (nuUrModTwoClassKTwo B) (gens 0) = 1
    rw [hD2 0, hΦν, GQ2.ContCoh.sqInitialAlphabetEquiv_zero, modelCoordAt_inl_zero]
  · intro i hi
    show frattiniFrameEval (nuUrModTwoClassKTwo B) (gens i) = 0
    rw [hD2 i, hΦν]
    exact modelCoordAt_sigmaDual_eq_zero k (sqInitialAlphabetEquiv_ne_inl_zero hi)

end FullEvals

/-! ## §3 From all the mod-two rows to all the exact rows

One Frattini-coset square shift per index, not two: the `σ`-index goes to the exact value `1`
and every other index to the exact value `0`.  Cup-adaptation and the cyclotomic table survive
by `MarkedFrame.isCupAdapted_squareShiftFrame` and `squareShiftFrame`'s own construction. -/

section ExactRows

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **All the exact rows from all the mod-two rows.**  A cup-adapted frame whose unramified
evaluations are the `σ`-dual pattern can be square-shifted to one carrying the *exact* rows
`ν(σ) = 1` and `ν(g) = 0` at every other generator. -/
theorem exists_isCupAdapted_fullNuRows_of_evals (B : MarkedRecip R K) (hr : B.r = 0) {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hsigma : frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) = 1)
    (hrest : ∀ i, i ≠ 0 → frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators i) = 0) :
    ∃ F' : SqCyclotomicFrattiniFrame K h, F'.IsCupAdapted ∧
      nuUrKTwo B (F'.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        ∀ i, i ≠ 0 → nuUrKTwo B (F'.generators i) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
  classical
  have hex : ∀ i : Fin (SqCore.sqRank h), ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (F.generators i * (g * g)) = chiCycKTwo (K := K) (F.generators i) ∧
        nuUrKTwo B (F.generators i * (g * g)) =
          (if i = 0 then Multiplicative.ofAdd (1 : ℤ_[2])
            else Multiplicative.ofAdd (0 : ℤ_[2])) := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      obtain ⟨g, hg1, hg2⟩ := exists_squareShift_nuUrKTwo_eq_one B hr (F.generators 0)
        (isUnit_toAdd_nuUrKTwo_of_eval_eq_one B hsigma)
      exact ⟨g, hg1, by rw [if_pos rfl]; exact hg2⟩
    · obtain ⟨m, hm⟩ := even_toAdd_nuUrKTwo_of_eval_eq_zero B (hrest i h0)
      obtain ⟨g, hg1, hg2⟩ := exists_squareShift_nuUrKTwo_eq_zero B hr (F.generators i) m hm
      exact ⟨g, hg1, by rw [if_neg h0]; exact hg2⟩
  choose s hchi hnu using hex
  refine ⟨squareShiftFrame F s hchi, isCupAdapted_squareShiftFrame F s hchi hcup, ?_, ?_⟩
  · rw [squareShiftFrame_generators]
    have hz := hnu 0
    rwa [if_pos rfl] at hz
  · intro i hi
    rw [squareShiftFrame_generators]
    have hz := hnu i
    rwa [if_neg hi] at hz

/-- **The fully `ν`-adapted frame supply.**  For every odd-degree `K` there is a cup-adapted
Frattini frame carrying the **whole** standard marking: `ν(σ) = 1` and `ν = 0` on every other
generator, `x₁` and all `2h` handle letters included.  Both `𝔽₂` cup data are theorems
(`NuKummer.nuUrOmegaCupOne_of_odd`, `nuUrKappaCupZero_of_odd`) and the type-`L` level clause
`B.r = 0` is forced by odd degree (`MarkedRecip.level_eq_zero_of_odd_finrank`), so this costs no
residual at all. -/
theorem exists_isCupAdapted_fullNuRows_oddDegree (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2), F.IsCupAdapted ∧
      nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        ∀ i, i ≠ 0 → nuUrKTwo B (F.generators i) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank (dyadicUnitFiltration K) hodd
  obtain ⟨F, hFcup, hFsigma, hFrest⟩ := exists_isCupAdapted_fullNuEvals_of_cupData B hodd
    (NuKummer.nuUrOmegaCupOne_of_odd B hodd hr) (nuUrKappaCupZero_of_odd B hodd)
  exact exists_isCupAdapted_fullNuRows_of_evals B hr F hFcup hFsigma hFrest

end ExactRows

/-! ## §4 The conversion: a presenting fully `ν`-adapted frame **is** the full-row supply -/

section Conversion

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **A presenting fully `ν`-adapted frame gives an oriented equivalence carrying the whole
marking.**  Rigidity makes the frame's forward map an equivalence sending `sqGen i` to
`generators i`; the cyclotomic table is the frame's own five rows read through
`orientationMatches_chiSq_iff_generatorValues`, and the four unramified generator rows `σ`, `x₀`,
`u_j`, `v_j` propagate to every point of `D_sq(h)` by `SqCore.nu_eq_nuSq_of_core`, the `x₁`-row
coming for free from the forced row of the improved relator's abelianization.

Cup-adaptation is **not** used: only the relator and the rows. -/
theorem exists_orientedEquiv_fullNu_of_fullNuFrame (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2))
    (hrel : SqCore.sqRelWord F.generators = 1)
    (hsigma : nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hrest : ∀ i, i ≠ 0 → nuUrKTwo B (F.generators i) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    ∃ f : ContinuousMulEquiv (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
        (maxProPQuotient 2 (GalK K)),
      (∀ x, chiCycKTwo (K := K) (f x) = SqCore.chiSq _ x) ∧
        ∀ x, nuUrKTwo B (f x) = SqCore.nuSq _ x := by
  obtain ⟨D, hD⟩ : ∃ D : SqCyclotomicForwardGeneratorData ((Module.finrank ℚ_[2] K - 1) / 2)
      (chiCycKTwo (K := K)), D.generators = F.generators :=
    ⟨forwardGeneratorDataOfFrame F hrel (sqCyclotomicFrattiniFrame_topologicalClosure_eq_top F),
      rfl⟩
  have hgenD : ∀ i, D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.sqGen _ i) =
      D.generators i := fun i ↦ D.forward_gen isProP_maxProPQuotient i
  have hgen : ∀ i, D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.sqGen _ i) =
      F.generators i := fun i ↦ (hgenD i).trans (congrFun hD i)
  have hσ : transportedNuUr B (D.forwardContinuousMulEquiv_oddDegree hodd)
      (SqCore.dsqSigma _) = Multiplicative.ofAdd (1 : ℤ_[2]) := by
    show nuUrKTwo B (D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.dsqSigma _)) = _
    rw [SqCore.dsqSigma, hgen]
    exact hsigma
  have hx0 : transportedNuUr B (D.forwardContinuousMulEquiv_oddDegree hodd)
      (SqCore.dsqX0 _) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
    show nuUrKTwo B (D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.dsqX0 _)) = _
    rw [SqCore.dsqX0, hgen]
    exact hrest 1 (sqOne_ne_zero _)
  have hU : ∀ j, transportedNuUr B (D.forwardContinuousMulEquiv_oddDegree hodd)
      (SqCore.sqGen _ (SqCore.sqHandleIdxU j)) = 1 := by
    intro j
    show nuUrKTwo B
      (D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.sqGen _ (SqCore.sqHandleIdxU j))) = 1
    rw [hgen, ← ofAdd_zero]
    exact hrest _ (sqHandleIdxU_ne_zero j)
  have hV : ∀ j, transportedNuUr B (D.forwardContinuousMulEquiv_oddDegree hodd)
      (SqCore.sqGen _ (SqCore.sqHandleIdxV j)) = 1 := by
    intro j
    show nuUrKTwo B
      (D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.sqGen _ (SqCore.sqHandleIdxV j))) = 1
    rw [hgen, ← ofAdd_zero]
    exact hrest _ (sqHandleIdxV_ne_zero j)
  have hall := SqCore.nu_eq_nuSq_of_core
    (transportedNuUr B (D.forwardContinuousMulEquiv_oddDegree hodd)) hσ hx0 hU hV
  refine ⟨D.forwardContinuousMulEquiv_oddDegree hodd, ?_, fun x ↦ hall x⟩
  refine (orientationMatches_chiSq_iff_generatorValues (chiCycKTwo (K := K)) _).2 ?_
  exact
    { sigma := by rw [SqCore.dsqSigma, hgenD]; exact D.sigma
      x0 := by rw [SqCore.dsqX0, hgenD]; exact D.x0
      x1 := by rw [SqCore.dsqX1, hgenD]; exact D.x1
      handleU := fun j ↦ by rw [hgenD]; exact D.handleU j
      handleV := fun j ↦ by rw [hgenD]; exact D.handleV j }

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **A presenting fully `ν`-adapted frame is the full-row supply**, the orientation forgotten. -/
theorem sqFullNuForwardSupply_of_fullNuFrame (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2))
    (hrel : SqCore.sqRelWord F.generators = 1)
    (hsigma : nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hrest : ∀ i, i ≠ 0 → nuUrKTwo B (F.generators i) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    MarkingAudit.SqFullNuForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) := by
  obtain ⟨f, _, hnu⟩ := exists_orientedEquiv_fullNu_of_fullNuFrame B hodd F hrel hsigma hrest
  exact ⟨f, hnu⟩

end Conversion

/-! ## §5 The odd-degree row over one binder

The frame of §3 is fully `ν`-adapted and unconditional; §4 turns it into the full-row supply as
soon as it presents.  So the whole odd-degree row now hangs on the relator clause alone, and the
χ-free clearing binder is retired from it. -/

section OneBinder

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The full-row supply over the relator clause alone.**  No clearing binder, no cup datum, no
`ν`-hypothesis of any kind: the frame constructed in §3 carries the whole marking, and the only
thing asked of it is that a cup-adapted frame kill the improved relator. -/
theorem sqFullNuForwardSupply_of_frameRelator (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hrel : SqCupAdaptedFrameRelator K) :
    MarkingAudit.SqFullNuForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) := by
  obtain ⟨F, hFcup, hFsigma, hFrest⟩ := exists_isCupAdapted_fullNuRows_oddDegree B hodd
  exact sqFullNuForwardSupply_of_fullNuFrame B hodd F (hrel _ F hFcup) hFsigma hFrest

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The same with the handle count normalized to `h`. -/
theorem sqFullNuForwardSupply_of_frameRelator' (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hrel : SqCupAdaptedFrameRelator K) : MarkingAudit.SqFullNuForwardSupply B h := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hsup := sqFullNuForwardSupply_of_frameRelator B hodd hrel
  rwa [hh] at hsup

/-- **THE ODD-DEGREE ROW OVER ONE BINDER.**  `Γ_{R_K} ≅ G_K` for every odd-degree ramified `K` at
the type-`L` level `r = 0`, over the single hypothesis `SqCupAdaptedFrameRelator K` — a statement
about the improved relator on cup-adapted frames, with **no `ν` in it**.

Compare `gammaR_lSq_equiv_galK_oddDegree_of_relator`, which carries the same relator clause *and*
the χ-free clearing binder `SqCore.SqNuClearHypothesis h`.  That binder was exactly the
two-rows-to-all-rows bridge (`MarkingAudit.sqFullNuForwardSupply_of_clear`); the frame of §3
carries all rows by construction, so the bridge is no longer needed. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_frameRelator (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hrel : SqCupAdaptedFrameRelator K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_frameRelator' B hdeg hrel) ramifiedData

end OneBinder

/-! ## §6 The residual, minimized and characterized

`SqCupAdaptedFrameRelator K` quantifies over *all* cup-adapted frames at *all* handle counts.
§3 constructs one particular frame, and §4 needs the relator only there — so the honest residual
is the existential statement `SqNuAdaptedFrameRelator`, which drops cup-adaptation entirely.
§6 also says exactly what that statement is: **the full-row supply, realized by an oriented
equivalence**.  So after this file the odd-degree gap is one word long — *orientation*. -/

section MinimalResidual

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Every non-`σ` letter of the standard marking is `0`. -/
theorem nuSq_sqGen_eq_zero_of_ne_zero {k : ℕ} {i : Fin (SqCore.sqRank k)} (hi : i ≠ 0) :
    SqCore.nuSq k (SqCore.sqGen k i) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact absurd rfl hi
  · exact SqCore.nuSq_x0 k
  · exact SqCore.nuSq_x1 k
  · rw [SqCore.nuSq_handleU]
    exact ofAdd_zero.symm
  · rw [SqCore.nuSq_handleV]
    exact ofAdd_zero.symm

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The minimal residual of the odd-degree row**, as a `def`-shaped `Prop` (never an axiom):
*some* Frattini frame kills the improved relator **and** carries the whole standard marking.

Strictly weaker than the committed binder `SqCupAdaptedFrameRelator K` in three ways: one frame
rather than all, one handle count rather than all, and no cup-adaptation clause. -/
def SqNuAdaptedFrameRelator (B : MarkedRecip Rec K) : Prop :=
  ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2),
    SqCore.sqRelWord F.generators = 1 ∧
      nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        ∀ i, i ≠ 0 → nuUrKTwo B (F.generators i) = Multiplicative.ofAdd (0 : ℤ_[2])

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The committed binder implies the minimal one: §3's frame is cup-adapted. -/
theorem sqNuAdaptedFrameRelator_of_frameRelator (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hrel : SqCupAdaptedFrameRelator K) : SqNuAdaptedFrameRelator B := by
  obtain ⟨F, hFcup, hFsigma, hFrest⟩ := exists_isCupAdapted_fullNuRows_oddDegree B hodd
  exact ⟨F, hrel _ F hFcup, hFsigma, hFrest⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The minimal residual already gives the full-row supply. -/
theorem sqFullNuForwardSupply_of_nuAdaptedFrameRelator (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (H : SqNuAdaptedFrameRelator B) :
    MarkingAudit.SqFullNuForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) := by
  obtain ⟨F, hrel, hsigma, hrest⟩ := H
  exact sqFullNuForwardSupply_of_fullNuFrame B hodd F hrel hsigma hrest

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **What the residual actually says.**  A frame killing the relator and carrying the marking is
the same thing as an **oriented** equivalence carrying the marking: forwards by §4, backwards by
`frameOfOrientedEquiv`, whose relator is free.

Since `MarkingAudit.SqFullNuForwardSupply` is the *un*oriented version of the right-hand side,
the entire remaining odd-degree gap is the orientation clause — and orientation on its own is
free (`orientedEquiv_of_oddDegree`).  What is missing is one equivalence carrying **both**. -/
theorem sqNuAdaptedFrameRelator_iff_orientedFullNu (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    SqNuAdaptedFrameRelator B ↔
      ∃ f : ContinuousMulEquiv (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
          (maxProPQuotient 2 (GalK K)),
        (∀ x, chiCycKTwo (K := K) (f x) = SqCore.chiSq _ x) ∧
          ∀ x, nuUrKTwo B (f x) = SqCore.nuSq _ x := by
  constructor
  · rintro ⟨F, hrel, hsigma, hrest⟩
    exact exists_orientedEquiv_fullNu_of_fullNuFrame B hodd F hrel hsigma hrest
  · rintro ⟨f, horient, hnu⟩
    refine ⟨frameOfOrientedEquiv f horient, sqRelWord_frameOfOrientedEquiv f horient, ?_, ?_⟩
    · rw [frameOfOrientedEquiv_generators, hnu]
      exact SqCore.nuSq_sigma _
    · intro i hi
      rw [frameOfOrientedEquiv_generators, hnu]
      exact nuSq_sqGen_eq_zero_of_ne_zero hi

/-- **The odd-degree row over the minimal residual.**  Same conclusion as §5, over the strictly
weaker hypothesis. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_nuAdaptedFrameRelator (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqNuAdaptedFrameRelator B)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hsup := sqFullNuForwardSupply_of_nuAdaptedFrameRelator B hodd H
  rw [hh] at hsup
  exact gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg hsup ramifiedData

end MinimalResidual

end NuAdapted

end

#print axioms NuAdapted.modelCoordAt_sigmaDual_eq_zero
#print axioms NuAdapted.sqInitialAlphabetEquiv_ne_inl_zero
#print axioms NuAdapted.sqHandleIdxU_ne_zero
#print axioms NuAdapted.sqHandleIdxV_ne_zero
#print axioms NuAdapted.exists_isCupAdapted_fullNuEvals_of_cupData
#print axioms NuAdapted.exists_isCupAdapted_fullNuRows_of_evals
#print axioms NuAdapted.exists_isCupAdapted_fullNuRows_oddDegree
#print axioms NuAdapted.exists_orientedEquiv_fullNu_of_fullNuFrame
#print axioms NuAdapted.sqFullNuForwardSupply_of_fullNuFrame
#print axioms NuAdapted.sqFullNuForwardSupply_of_frameRelator
#print axioms NuAdapted.sqFullNuForwardSupply_of_frameRelator'
#print axioms NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_frameRelator
#print axioms NuAdapted.nuSq_sqGen_eq_zero_of_ne_zero
#print axioms NuAdapted.SqNuAdaptedFrameRelator
#print axioms NuAdapted.sqNuAdaptedFrameRelator_of_frameRelator
#print axioms NuAdapted.sqFullNuForwardSupply_of_nuAdaptedFrameRelator
#print axioms NuAdapted.sqNuAdaptedFrameRelator_iff_orientedFullNu
#print axioms NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_nuAdaptedFrameRelator

end GQ2.Dyadic.LSquare
