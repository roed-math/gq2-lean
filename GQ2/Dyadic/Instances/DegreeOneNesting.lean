/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotSeedD0
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteCubicNeutral
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFrattiniFrame
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeBase
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteVariableStageTwo
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldRigidity

/-!
# `B5-K` off the odd-degree forward route: the degree-one nesting check

`docs/dyadic/owner-items-2026-08-05.md` §1b asks whether the odd-degree endpoint reached through
the general-`K` machine, specialized to `[K : ℚ₂] = 1`, has an axiom print **nested** inside the
frozen `ℚ₂` capstone's nine.  The committed milestone
`NuAdapted.gammaR_lSq_equiv_galK_degreeOne` does not: it prints the nine **plus**
`markedRecipAt` (B5-K).

This file measures why, and removes the cause.

## The finding

`markedRecipAt` is **not mathematically load-bearing** anywhere on that route.  Exactly three
declarations in the whole reachable closure apply it, and all three apply it *at the ambient
field* `K`, as the argument of a lemma that is generic in the bundle:

| consumer | applies |
| --- | --- |
| `oddDegreeGalKSq_allStagePrimitiveResidualVanishing` | `chiCycKTwo_surjective_of_odd_finrank K (markedRecipAt K) hodd` |
| `nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply` | `SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply (markedRecipAt K) hodd` |
| `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` | both of the above, plus `cyclotomicModEightOmegaClassKTwo_ne_zero (markedRecipAt K) hodd` |

Each of those three lemmas takes `{R : LocalReciprocity} (B : MarkedRecip R K)` and prints the
standard three.  The axiom is summoned only because the three consumers do not carry a bundle
binder of their own — the first two because their statements simply never took one, the third
because `OddDegreeSqCyclotomicFrattiniFrameSupply` quantifies over *every* `K` internally, so no
`K`-indexed bundle can be in scope.

`markedRecipAt`'s entire contribution to the odd-degree forward route is therefore surjectivity
of `chiCycKTwo` (and its two consequences), which the caller's own `B` supplies for free.

## What this file does

§0 restates the third consumer at **one** field with a bundle in scope; §1–§3 re-derive the
forward route over the caller's `B : MarkedRecip Rec K`.  The three declarations that touch the
axiom (§0, §1, §2a) are the committed proofs verbatim with `(markedRecipAt K)` replaced by `B`;
the rest (§2b, §2c, §3, §4) are the committed compositions re-pointed at those three, with a
level-three base threaded where the committed chain calls the ∀-`K` supply.  §4 carries the
result to the odd-degree endpoint, §5 to `[K : ℚ₂] = 1` (where the two one-parameter pivot
subgroups are theorems — `SqCore.sqPivotTranslation_zero`, `SqCore.sqPivotScaling_zero`), and §6
discharges §4–§5's level-three base from §0.

The headline is `gammaR_lSq_equiv_galK_degreeOne_nested_unconditional`.  It has **exactly** the
committed milestone's type (§7 pins that, twice) and prints

    std-3 + {B1, B3c, B6, B7, B8, B9, B11a}

= the frozen `ℚ₂` capstone's nine **minus** `localReciprocity` (B5) and `tameQuotient` (B10): a
strict subset.  So the degree-one check nests.  `B3c` and `B8` arrive with the two pivot
subgroups (`prop_3_8_lift` and the Labute-orientation transport) and are inside the nine, so
they cost the nesting nothing.

**What the route does and does not assume**, measured rather than asserted.  No declaration here
depends on the `ℚ₂` presentation theorem (`main_presentation_literal_roe_unconditional`,
`Dyadic.QTwo.candidateGroup_lSq_equiv_absGalQ2`, `candidate_equiv_absoluteGalois`,
`Roe.gammaR_lSq_equiv_roe`, `eq_154_R`), so the check is not circular against the theorem it is
checking.  It *does* depend on `GQ2.Roe.Labute.bLab` — but so does the committed milestone, and
by the same route (the two pivot subgroups at `h = 0`), so that is not a difference between them.

The difference from the one pre-existing `B5-K`-free degree-one route
(`nonempty_orientedEquiv_bot_of_forwardStageRigidity`, print std-3 + {B1, B3c, B6, B7}) is which
step of the machine gets exercised: that route obtains its level-three base from
`sqCyclotomicStageTuple_bot_three_nonempty`, i.e. by transporting the `D₀` classification of
`G_ℚ₂(2)` itself, whereas §0 builds the base by the general-`K` Frattini-frame construction.
Both are honest theorems; only the second tests the general-`K` machinery at degree one.

## Axioms

Every declaration prints std-3 plus a subset of {B1, B3c, B6, B7, B8, B9, B11a}.  `markedRecipAt`
(B5-K) and `localReciprocity` (B5) appear in **no** print in this file — that is its point.
No `sorry`, no new axiom, no `native_decide`.  Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace Nesting

open NuAdapted

/-! ## §0 The cup-adapted Frattini frame, over the caller's bundle

`oddDegreeSqCyclotomicFrattiniFrameSupply_holds`, stated at **one** field with a bundle in scope
instead of over every field with none.  The proof below is that theorem's proof verbatim, with
its two occurrences of `markedRecipAt K` replaced by `B` and its leading `intro K _ _ _ _ hodd`
dropped; nothing else changes, which is the file's central claim made checkable.

⚠ **Temporary duplicate — delete it when the upstream binder lands.**  The durable form of this
is the same two-token change made *in place*, once
`OddDegreeSqCyclotomicFrattiniFrameSupply` (`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean`)
carries a bundle binder; then §6 routes through `oddDegree_sqCyclotomicStageTuple_levelThree`
instead and this section goes away.  The migration is spelled out in the §1b update of
`docs/dyadic/owner-items-2026-08-05.md`. -/

section FrameSupply

open FrattiniFrameSupply ContCoh GQ2.Roe.Labute

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **§0.**  The odd-degree cup-adapted Frattini-frame supply at a single field, over the
caller's marked bundle rather than B5-K. -/
theorem exists_cupAdaptedFrattiniFrame_of_markedRecip (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2), F.IsCupAdapted := by
  classical
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  obtain ⟨k, hk⟩ := id hodd
  rw [show (Module.finrank ℚ_[2] K - 1) / 2 = k from by omega]
  -- finiteness and cardinality of `H¹(G_K(2), 𝔽₂)`
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * k + 3) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K),
      show Module.finrank ℚ_[2] K + 2 = 2 * k + 3 from by omega]
  -- the adapted Witt coordinates
  obtain ⟨Φ, hGram, hΦκ, hΦτ⟩ :=
    frattiniFrameAdaptedModelEquiv (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (frattiniFrameCup_kappa_self (K := K) hodd) (frattiniFrameCup_omega_modFour (K := K))
      (cyclotomicModEightOmegaClassKTwo_ne_zero B hodd) hcard
  -- realize the adapted coordinate functionals by group elements
  choose gens' hgens' using fun i : Fin (SqCore.sqRank k) =>
    frattiniFrameEval_realizable (K := K) hfin
      ((modelCoordL k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x =>
    hgens' i x
  -- exact cyclotomic values in each dual Frattini coset
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
  choose gens hχ hlevel using fun i : Fin (SqCore.sqRank k) =>
    frattiniFrameExactLift (K := K) hsupply (gens' i) (frattiniFrameTarget k i)
      (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x =>
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · -- Frattini generation, by duality
    by_contra hne
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
  · -- cup adaptation
    show ∀ c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      FieldData.cupFormK K
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) =
        GQ2.ContCoh.sqRelatorQuadraticInitialGram k
          (fun i j => Multiplicative.toAdd (c (gens i)) * Multiplicative.toAdd (d (gens j)))
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

/-- **§0b.**  The arbitrary odd-degree level-three stage base, over the caller's bundle: §0's
frame plus the (B5-K-free) transgression realization. -/
theorem sqCyclotomicStageTuple_levelThree_of_markedRecip (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3) := by
  obtain ⟨F, hcup⟩ := exists_cupAdaptedFrattiniFrame_of_markedRecip B hodd
  exact ⟨F.toLevelThree (oddDegreeSqLevelThreeRelationRealization K hodd F hcup)⟩

end FrameSupply

/-! ## §1 The all-stage primitive residual, over the caller's bundle

`oddDegreeGalKSq_allStagePrimitiveResidualVanishing` with `markedRecipAt K` replaced by `B`. -/

section Stages

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **§1.**  The complete `∀ k ≥ 3` premise of the forward presentation capstone, over the
caller's marked bundle rather than B5-K.  Odd-degree marked reciprocity is used only through
`chiCycKTwo_surjective_of_odd_finrank`, which is generic in the bundle. -/
theorem allStagePrimitiveResidualVanishing_of_markedRecip (B : MarkedRecip Rec K) {h : ℕ}
    (hodd : Odd (Module.finrank ℚ_[2] K)) (Hsupply : SqKernelAdaptedDefectSupply K h) :
    ∀ (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k),
      ∃ W : SqCyclotomicStageTuple.SharpAdmissibleCorrection T (by omega),
        SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing T hk W
          (maxProTwoGalK_isTopologicallyFinGen K) :=
  fun k hk T ↦ stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply
    (chiCycKTwo_surjective_of_odd_finrank K B hodd) Hsupply k hk T

end Stages

/-! ## §2 The rigidity capstone, over the caller's bundle

`nonempty_orientedEquiv_oddDegree_of_stageBase_and_{actualDefectSupply,
primitiveResidualVanishing}` with `markedRecipAt K` replaced by `B`. -/

section Rigidity

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **§2a.**  Sharp exact fibre lifting is supplied by the caller's bundle, not by B5-K. -/
theorem orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (base : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3)
    (Hactual : ∀ (k : ℕ) (hk : 3 ≤ k)
      (T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k),
      Nonempty (SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply T hk)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2)) (chiCycKTwo (K := K))) := by
  apply nonempty_orientedEquiv_oddDegree_of_stageBase_and_corrections hodd base
  intro k hk T
  obtain ⟨S⟩ := Hactual k hk T
  exact S.toDefectReachable
    (SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply B hodd)

/-- **§2b.**  The chain-level boundary form, over the caller's bundle. -/
theorem orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing
    (B : MarkedRecip Rec K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (base : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3)
    (Hprimitive : ∀ (k : ℕ) (hk : 3 ≤ k)
      (T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k),
      ∃ W : SqCyclotomicStageTuple.SharpAdmissibleCorrection T (by omega),
        SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing
          T hk W (maxProTwoGalK_isTopologicallyFinGen K)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2)) (chiCycKTwo (K := K))) := by
  apply orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply B hodd base
  intro k hk T
  obtain ⟨W, hprimitive⟩ := Hprimitive k hk T
  have hcompat :=
    SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing
      W (maxProTwoGalK_isTopologicallyFinGen K) hprimitive
  have hmem :=
    (SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan
      W (maxProTwoGalK_isTopologicallyFinGen K)).mp hcompat
  exact
    (SqCyclotomicStageTuple.nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan
      W).mpr hmem

/-- **§2c.**  The forward presentation theorem over a level-three base, `B5-K`-free: the
kernel-adapted supply is a theorem at odd degree (`sqKernelAdaptedDefectSupply_of_finrank`), so
the base is the only input beyond the bundle. -/
theorem nonempty_orientedEquiv_oddDegree_of_base (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (base : SqCyclotomicStageTuple K h 3) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2)) (chiCycKTwo (K := K))) := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  refine orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing B hodd
    (by rw [hh]; exact base) ?_
  rw [hh]
  exact allStagePrimitiveResidualVanishing_of_markedRecip B hodd
    (sqKernelAdaptedDefectSupply_of_finrank hdeg)

/-- **§3.**  `orientedEquiv_of_oddDegree` over the caller's bundle and a level-three base: an
oriented equivalence `D_sq(h) ≃ₜ* G_K(2)` with the handle count normalized to `h`. -/
theorem orientedEquiv_of_oddDegree_of_base (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (base : SqCyclotomicStageTuple K h 3) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hne := nonempty_orientedEquiv_oddDegree_of_base B hdeg base
  rw [hh] at hne
  obtain ⟨e⟩ := hne
  exact ⟨e.1, e.2⟩

end Rigidity

/-! ## §4 The bridge and the odd-degree endpoint

`NuAdapted.exists_orientedEquiv_fullNu_of_orientedClear` and its two successors, over §3's
oriented equivalence instead of `orientedEquiv_of_oddDegree`. -/

section Bridge

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **§4a.**  One equivalence carrying the orientation *and* the whole marking, over §3. -/
theorem exists_orientedEquiv_fullNu_of_orientedClear_of_base (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (base : SqCyclotomicStageTuple K h 3) (hclear : SqCore.SqNuOrientedClear h) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      (∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) ∧
        ∀ x, nuUrKTwo B (f x) = nuSq h x := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree_of_base B hdeg base
  obtain ⟨Ψ, hchi, hnu⟩ := hclear (transportedNuUr B f)
    (fun u y => jointSurjective_transportedNuUr B hodd hr f horient u y)
  refine ⟨Ψ.trans f, fun x => ?_, fun x => hnu x⟩
  show chiCycKTwo (K := K) (f (Ψ x)) = chiSq h x
  rw [horient (Ψ x), hchi x]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **§4b.**  The odd-degree residual `SqNuAdaptedFrameRelator B`, over §4a. -/
theorem sqNuAdaptedFrameRelator_of_orientedClear_of_base (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (base : SqCyclotomicStageTuple K h 3) (hclear : SqCore.SqNuOrientedClear h) :
    SqNuAdaptedFrameRelator B := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  subst hh
  exact (sqNuAdaptedFrameRelator_iff_orientedFullNu B hodd).2
    (exists_orientedEquiv_fullNu_of_orientedClear_of_base B FF hdeg base hclear)

/-- **§4c.**  The odd-degree endpoint `Γ_{R_K} ≅ G_K` over the model-side clearing statement, a
level-three base, and the packet's structural pair — with **no** `B5-K`. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_of_base (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (base : SqCyclotomicStageTuple K h 3)
    (hclear : SqCore.SqNuOrientedClear h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_nuAdaptedFrameRelator B T D hdeg
    (sqNuAdaptedFrameRelator_of_orientedClear_of_base B FF hdeg base hclear) ramifiedData

end Bridge

/-! ## §5 The degree-one endpoint, nested -/

section DegreeOne

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **THE NESTED DEGREE-ONE ENDPOINT.**  `Γ_{R_K} ≅ G_K` at `[K : ℚ₂] = 1`, through the
general-`K` machine, over a level-three stage base and nothing else: at `h = 0` both
one-parameter pivot subgroups are theorems, so `SqCore.SqNuOrientedClear 0` is discharged
exactly as in the committed milestone.

The difference from `NuAdapted.gammaR_lSq_equiv_galK_degreeOne` is the route, not the
statement: the oriented equivalence is built from the caller's `B` (§3) instead of from
`markedRecipAt K`, and the print drops `markedRecipAt` (B5-K), `localReciprocity` (B5),
`dyadicOrientation` (B3c), `peripheralCyclotomicAction` (B8) and `tameQuotient` (B10). -/
theorem gammaR_lSq_equiv_galK_degreeOne_nested (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (base : SqCyclotomicStageTuple K 0 3)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_of_base B FF T D (by omega) base
    (SqCore.sqNuOrientedClear_zero_of_two_subgroups SqCore.sqPivotTranslation_zero
      (fun _ ha => SqCore.sqPivotScaling_zero ha)) ramifiedData

end DegreeOne

/-! ## §6 The endpoints with the base discharged

§0b supplies the level-three base from the caller's bundle, so §4c and §5 hold with no binder
beyond the packet the committed statements already carry. -/

section Unconditional

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **§6a.**  The odd-degree endpoint over the model-side clearing statement alone — the
committed `NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear` restated with the
oriented equivalence rebuilt from `B`, hence without B5-K or B5. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_nested (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuOrientedClear h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  obtain ⟨base⟩ := sqCyclotomicStageTuple_levelThree_of_markedRecip B hodd
  rw [hh] at base
  exact gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_of_base B FF T D hdeg base hclear
    ramifiedData

/-- **THE NESTED DEGREE-ONE MILESTONE.**  Statement-for-statement the committed
`NuAdapted.gammaR_lSq_equiv_galK_degreeOne`: at `[K : ℚ₂] = 1` the odd-degree row of the
general-`K` machine holds outright, `Γ_{R_K} ≅ G_K`.  Only the route differs — every use of
`markedRecipAt` is replaced by the caller's own bundle `B` — and the print drops five census
members, landing strictly inside the frozen `ℚ₂` capstone's nine.  §7 pins that. -/
theorem gammaR_lSq_equiv_galK_degreeOne_nested_unconditional (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_nested B FF T D (by omega)
    (SqCore.sqNuOrientedClear_zero_of_two_subgroups SqCore.sqPivotTranslation_zero
      (fun _ ha => SqCore.sqPivotScaling_zero ha)) ramifiedData

end Unconditional

/-! ## §7 Nesting pins

The two statements below are the ticket's deliverable in Lean: the nested milestone has the
committed milestone's type, and the committed milestone follows from it. -/

section Pins

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **Type identity.**  The nested endpoint inhabits the committed milestone's type: same
binders, same conclusion.  So the print comparison in the `#print axioms` block below is
like-for-like, not a comparison against a weakened statement. -/
example : (∀ (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
      (_T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF),
      Module.finrank ℚ_[2] K = 1 →
      (∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
        [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
        (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
        (rho : ContinuousMonoidHom (GalK K) Dg),
        (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
          Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) →
      Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K))) :=
  fun B FF _T D hdeg ramifiedData =>
    gammaR_lSq_equiv_galK_degreeOne_nested_unconditional B FF _T D hdeg ramifiedData

/-- …and it *is* the committed milestone, reproved. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (hdeg : Module.finrank ℚ_[2] K = 1)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_degreeOne_nested_unconditional B FF T D hdeg ramifiedData

end Pins

end Nesting

end

#print axioms GQ2.Dyadic.LSquare.Nesting.exists_cupAdaptedFrattiniFrame_of_markedRecip
#print axioms GQ2.Dyadic.LSquare.Nesting.sqCyclotomicStageTuple_levelThree_of_markedRecip
#print axioms GQ2.Dyadic.LSquare.Nesting.allStagePrimitiveResidualVanishing_of_markedRecip
#print axioms
  GQ2.Dyadic.LSquare.Nesting.orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply
#print axioms GQ2.Dyadic.LSquare.Nesting.nonempty_orientedEquiv_oddDegree_of_base
#print axioms GQ2.Dyadic.LSquare.Nesting.orientedEquiv_of_oddDegree_of_base
#print axioms GQ2.Dyadic.LSquare.Nesting.sqNuAdaptedFrameRelator_of_orientedClear_of_base
#print axioms GQ2.Dyadic.LSquare.Nesting.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_of_base
#print axioms GQ2.Dyadic.LSquare.Nesting.gammaR_lSq_equiv_galK_degreeOne_nested
#print axioms GQ2.Dyadic.LSquare.Nesting.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear_nested
#print axioms GQ2.Dyadic.LSquare.Nesting.gammaR_lSq_equiv_galK_degreeOne_nested_unconditional

-- The frozen `ℚ₂` capstone's print, for side-by-side reading.
#print axioms GQ2.main_presentation_literal_roe_unconditional

end GQ2.Dyadic.LSquare
