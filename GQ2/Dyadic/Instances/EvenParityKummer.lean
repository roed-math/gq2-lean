/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenFamilyStatus
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageKummerParity

/-!
# W66-PARITY: the even twisted-cocycle parity supply, at every even-degree field

## What this file is

The discharge of `EvenFamParitySupply`, the even route's single remaining statement after
wave 65.  Wave 65 proved that at a real field the whole even route is equivalent, per branch,
to this one arithmetic supply; this file proves the supply outright, for **every** field of
even degree over `ℚ₂`, at every level `k ≥ 3`, for every stage tuple of every even word datum.

## The argument

It is the odd route's argument, whose every step is generic in the value table and in the
slot count, run against the even rank bookkeeping.  Two numbers meet:

* the Demushkin `H¹` count `|H¹(G_K(2), 𝔽₂)| = 2^([K : ℚ₂] + 2)`
  (`card_H1_zmodTwo_maxProTwoGalK`, committed); and
* the even core rank `coreRank h = 4 + 2h`, which at even degree `[K : ℚ₂] = 2 + 2h` is
  exactly `[K : ℚ₂] + 2`.

So on the `𝔽₂`-vector space of continuous mod-2 characters of `G_K(2)`, evaluation at the
exact-fibre lifts of a stage tuple is injective (a character kills `λ₂ ⊇ λ_k`, and the level-`k`
classes of the lifts generate the level) between two sets of the same finite cardinality, hence
bijective: every Kronecker value pattern on the lifts is realized by a character (§3).  Mod-2
Kummer surjectivity turns that character into an element `a ∈ Kˣ` (`kummerClassK_surjective`,
committed, reused through the odd route's `stageKummer_exists_kummer_of_character`, which is
already generic), and the χ-twisted higher Kummer cocycle of `a` at a `2^(k+1)`-th root is a
continuous χ-twisted one-cocycle at precision `2^(k+1)` whose value parities at classes from
`G_K` are the mod-2 Kummer signs of `a` (`isChiTwistedCocycle_chiTwistedKummerDescent` and
`chiTwistedKummerFun_parity`, committed).  That is the supply (§4).

The odd route's own count needed `sqRank h = 3 + 2h = [K : ℚ₂] + 2` at odd degree, so the two
routes use the *same* Demushkin count on complementary degree parities.  Nothing here is new
arithmetic: what was missing was only the observation that the even rank bookkeeping closes
the same numerical gap.

## What it buys

`EvenFamParitySupply` at every even-degree field feeds the wave-65 equivalences directly, so
`Hfam` becomes a theorem at every even-degree field, and the even oriented equivalence follows
from the branch identification `hrange` alone (`EvenParityModel.lean`).  The memo's residual
"higher Kummer theory at `K`" is therefore closed; the even route's remaining input is the
cyclotomic branch identification, which is a statement about `χ_cyc` and not about cocycles.

## Numbering

1. exact-fibre lifts of a generic even stage tuple;
2. the character count at even degree;
3. evaluation at the lifts is bijective, and the dual-basis character;
4. the parity supply;
5. axiom pins.
-/

namespace GQ2.Dyadic.EvenParity

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH
open ContCoh
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenFamily
open GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## §1 Exact-fibre lifts of an even stage tuple

The generic `Tuple` carries its exact-fibre rows as an existential per slot; `choose` turns
them into a single lift function, the even analogue of `SqCyclotomicStageTuple.exists_exactChiLift`.
Stated for an arbitrary ambient group so that it is available wherever the even tuples are. -/

section Lifts

variable {n : ℕ} {W : StageWord n} {v : Fin n → ℤ_[2]ˣ} {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **Exact-fibre lifts of a stage tuple.**  Every even stage tuple has a family of ambient
lifts sitting in the exact `chi`-fibres of the value table and marking the tuple's generators
at level `k`.  This is the tuple's `rows` field with the per-slot choice made once. -/
theorem evenParity_exists_lifts {k : ℕ} (T : Tuple W v G chi k) :
    ∃ lifts : Fin n → G, (∀ i, chi (lifts i) = v i) ∧
      ∀ i, levelMk G k (lifts i) = T.generators i := by
  choose lifts hchi hlvl using T.rows
  exact ⟨lifts, hchi, fun i ↦ (hlvl i).symm⟩

end Lifts

/-! ## §2 The character count at even degree

At even degree `[K : ℚ₂] = 2 + 2h` the continuous mod-2 characters of `G_K(2)` are counted by
the even core rank: `2^([K:ℚ₂] + 2) = 2^(coreRank h)`.  The odd route's
`stageKummer_card_characters` with `sqRank h = 3 + 2h` replaced by `coreRank h = 4 + 2h`; the
`H¹` count it rests on is the same committed Demushkin theorem. -/

omit [T2Space (GalK K)] in
/-- **The even character count.**  For `[K : ℚ₂] = 2 + 2h`, the continuous mod-2 characters of
`G_K(2)` are equinumerous with the mod-2 value patterns on `coreRank h` slots. -/
theorem evenParity_card_characters (h : ℕ)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nat.card (ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
        (Multiplicative (ZMod 2))) =
      Nat.card (Fin (MarkedCore.coreRank h) → Multiplicative (ZMod 2)) := by
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo (maxProPQuotient 2 (GalK K))
  rw [Count.card_hom_eq_card_Z1,
    show Nat.card ↥(Z1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
        Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) from
      (Nat.card_congr (H1equivZ1OfTrivial Count.smul_zmod2).toEquiv).symm,
    card_H1_zmodTwo_maxProTwoGalK (K := K),
    Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  congr 1
  simp only [MarkedCore.coreRank, hev]
  omega

/-! ## §3 Evaluation at the lifts, and the dual-basis character

A continuous mod-2 character of `G_K(2)` kills the second two-central term, hence kills `λ_k`
for `k ≥ 2`, so it factors through level `k`; the tuple's generators generate that level, so a
character is determined by its values at any lifts of the generators.  Evaluation at the lifts
is therefore injective, and by §2 it is a map between finite sets of equal cardinality, hence
bijective: every Kronecker pattern is realized. -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **Characters are determined at the lifts.**  Two continuous mod-2 characters of `G_K(2)`
agreeing at ambient lifts of an even stage tuple's generators are equal.  Generic in the word
datum, the value table, and the orientation character. -/
theorem evenParity_characters_ext {n k : ℕ} (hk : 3 ≤ k) {W : StageWord n}
    {v : Fin n → ℤ_[2]ˣ}
    {chi : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) chi k)
    {lifts : Fin n → maxProPQuotient 2 (GalK K)}
    (hlvl : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i)
    {c₁ c₂ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
      (Multiplicative (ZMod 2))}
    (hval : ∀ i, c₁ (lifts i) = c₂ (lifts i)) : c₁ = c₂ := by
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
    exact hval i
  have hclosure := MonoidHom.eqOn_closure heqOn
  ext g
  have hg : levelMk (maxProPQuotient 2 (GalK K)) k g ∈
      (Subgroup.closure (Set.range T.generators) : Set _) := by
    rw [T.topGen]
    trivial
  exact hclosure hg

omit [T2Space (GalK K)] in
/-- **The dual-basis character at a slot.**  At even degree, evaluation of the mod-2 character
group of `G_K(2)` at any lifts of an even stage tuple's generators is a bijection onto all value
patterns, so each slot carries a character odd exactly there.  Only the level condition on the
lifts is used; the exact-fibre condition is not needed here.  This is the Kronecker dual whose
Kummer realization drives §4. -/
theorem evenParity_exists_dual_character {h k : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (hk : 3 ≤ k)
    {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    {chi : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) chi k)
    {lifts : Fin (MarkedCore.coreRank h) → maxProPQuotient 2 (GalK K)}
    (hlvl : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i)
    (i₀ : Fin (MarkedCore.coreRank h)) :
    ∃ c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      Multiplicative.toAdd (c (lifts i₀)) = 1 ∧
        ∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
          Multiplicative.toAdd (c (lifts j)) = 0 := by
  have hbij : Function.Bijective
      (fun (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
        (Multiplicative (ZMod 2))) (i : Fin (MarkedCore.coreRank h)) ↦ c (lifts i)) := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨fun c₁ c₂ hcc ↦ evenParity_characters_ext hk T hlvl (fun i ↦ congrFun hcc i),
      evenParity_card_characters h hev⟩
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

/-! ## §4 The parity supply

The headline.  For each non-twisted slot `i₀ ≠ 1`, §3 gives a continuous mod-2 character odd
exactly at the `i₀`-lift; mod-2 Kummer surjectivity realizes it as the Kummer sign cocycle of
some `a ∈ Kˣ` (the odd route's `stageKummer_exists_kummer_of_character`, already generic in the
character); and the χ-twisted higher Kummer cocycle of `a` at a `2^(k+1)`-th root of unity is a
continuous χ-twisted one-cocycle at precision `2^(k+1)` whose value parities at classes from
`G_K` are exactly those signs.  The twisted slot `1` is never used, so no constraint on it is
needed. -/

omit [T2Space (GalK K)] in
/-- **THE EVEN TWISTED-COCYCLE PARITY SUPPLY, AT EVERY EVEN-DEGREE FIELD.**  For
`[K : ℚ₂] = 2 + 2h`, every stage tuple of every even word datum at every level `k ≥ 3` has the
supply: exact-fibre lifts of the generators, and for each non-twisted slot a continuous
`χ`-twisted one-cocycle at precision `2^(k+1)` odd at that lift and even at the other
non-twisted lifts.  This is wave 65's named residual, discharged with no hypothesis beyond the
degree parity.  Generic in the word datum `W` and the value table `v`, so it covers both
branches at once.

`T2Space (GalK K)` is not needed: the Kummer construction descends through the finite word-lift
group, and the counting is cohomological. -/
theorem evenParity_paritySupply_of_finrank {h k : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (hk : 3 ≤ k)
    {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    EvenFamParitySupply T := by
  obtain ⟨lifts, hchi, hlvl⟩ := evenParity_exists_lifts T
  refine ⟨lifts, hchi, hlvl, ?_⟩
  intro i₀ _
  have hsurj : Function.Surjective (maxProPMk 2 (GalK K)) := quotientMk_surjective _
  choose gs hgs using fun i ↦ hsurj (lifts i)
  obtain ⟨c, hcd, hco⟩ := evenParity_exists_dual_character hev hk T hlvl i₀
  obtain ⟨a, ha⟩ := stageKummer_exists_kummer_of_character (K := K) c
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄₂ (2 ^ (k + 1))
  have h2p : (2 : ℕ) ^ (k + 1) ≠ 0 := by positivity
  have hzu : IsPrimitiveRoot ((hz.isUnit h2p).unit) (2 ^ (k + 1)) := hz.isUnit_unit h2p
  have halpha := higherRootUnit_pow (2 ^ (k + 1)) a
  have hN1 : 1 ≤ k + 1 := by omega
  have hvalu : ∀ i, (chiTwistedKummerDescent hzu a halpha hN1 (lifts i)).u =
      chiTwistedKummerFun hzu a halpha (gs i) := by
    intro i
    rw [← hgs i, chiTwistedKummerDescent_u_mk]
  refine ⟨fun q ↦ (chiTwistedKummerDescent hzu a halpha hN1 q).u,
    isChiTwistedCocycle_chiTwistedKummerDescent hzu a halpha hN1, ?_, ?_⟩
  · intro hdvd
    have hdvd' : (2 : ZMod (2 ^ (k + 1))) ∣
        (chiTwistedKummerDescent hzu a halpha hN1 (lifts i₀)).u := hdvd
    rw [hvalu i₀] at hdvd'
    have h0 := (chiTwistedKummerFun_parity hzu a halpha hN1 (gs i₀)).mp hdvd'
    rw [ha (gs i₀), hgs i₀, hcd] at h0
    exact one_ne_zero h0
  · intro j _ hji
    show (2 : ZMod (2 ^ (k + 1))) ∣ (chiTwistedKummerDescent hzu a halpha hN1 (lifts j)).u
    rw [hvalu j]
    refine (chiTwistedKummerFun_parity hzu a halpha hN1 (gs j)).mpr ?_
    rw [ha (gs j), hgs j]
    exact hco j hji

omit [T2Space (GalK K)] in
/-- **The parity supply at even degree**, in the handle count `(n - 2)/2` the campaign uses at
the endpoint.  ⚠ It carries `2 ≤ [K : ℚ₂]` as an explicit hypothesis, where the corresponding
`EvenParityModel.parityFinal_evenClassification_evenDegree` takes positivity from
`Module.finrank_pos` instead and so carries the degree parity alone. -/
theorem evenParity_paritySupply_evenDegree (hpos : 2 ≤ Module.finrank ℚ_[2] K)
    (heven : Even (Module.finrank ℚ_[2] K)) {k : ℕ} (hk : 3 ≤ k)
    {W : StageWord (MarkedCore.coreRank ((Module.finrank ℚ_[2] K - 2) / 2))}
    {v : Fin (MarkedCore.coreRank ((Module.finrank ℚ_[2] K - 2) / 2)) → ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    EvenFamParitySupply T :=
  evenParity_paritySupply_of_finrank (by obtain ⟨m, hm⟩ := heven; omega) hk T

end

/-! ## §5 Axiom pins

Printed side by side with the odd route's `sqStageTwistedCocycleParitySupply_of_finrank`, whose
argument this file clones: the even supply must not exceed what the odd one already carries. -/

section AxiomPins

open GQ2.Dyadic.EvenParity

-- §1 to §3
#print axioms evenParity_exists_lifts
#print axioms evenParity_card_characters
#print axioms evenParity_characters_ext
#print axioms evenParity_exists_dual_character

-- §4 the headline
#print axioms evenParity_paritySupply_of_finrank
#print axioms evenParity_paritySupply_evenDegree

-- the odd route's analogue, for the side-by-side
#print axioms GQ2.Dyadic.LSquare.sqStageTwistedCocycleParitySupply_of_finrank

end AxiomPins

end GQ2.Dyadic.EvenParity
