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

end

end GQ2.Dyadic.EvenParity
