/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenParityKummer
import GQ2.Dyadic.Instances.EvenCyclotomicRange

/-!
# W66-PARITY: the even classification at the fields

## What this file is

The consumption of `EvenParityKummer.lean` through the committed wave-58 endpoints and the
wave-65 equivalences.  Three statements, in increasing finality.

1. **`Hfam` is a theorem at every even-degree field** (§1).  The supply of the previous file
   feeds `evenFam_nonempty_family_of_paritySupply`, and the relator kill is free
   (`evenFam_relatorKill{N,M}`), so the even route's carried input holds at every field of even
   degree over `ℚ₂`, on both branches, at every level and every stage tuple.  By wave 65 this
   is the strongest possible form: `Hfam` at a field *is* the even classification there.

2. **The classification follows from the branch identification alone** (§2).  Feeding §1 into
   `hfamFinal_status{N,M}_atDepth` (equivalently the committed
   `evenRouteFinal_orientedEquiv{N,M}_atDepth`), the even oriented equivalence at a field is
   implied by the range identity `range χ_cyc = imChi{N,M} α` and the degree alone.

3. **The even classification, over the committed reciprocity binders** (§3).  The range identity
   is itself committed, up to the branch, whenever `K(i)/K` is ramified: `evenRange_range_eq`
   produces some `α ≥ 2` with `range χ_cyc = imChiM α` or `= imChiN α`.  So for every finite
   `K/ℚ₂` of even degree with `K(i)/K` ramified and a marked reciprocity bundle, `G_K(2)` is
   oriented-isomorphic to an even presented core at some depth `α ≥ 2` on one of the two
   branches.  No supply remains.

§4 lands it at the three model fields, where the ramification binder is a committed theorem;
`KSqrtNegTwo` and `KSqrtTwo` are quadratic (`h = 0`), `KQuarticN` is quartic (`h = 1`).  §5
records the wave-58 artefacts, now carried.

## What is left

Only the branch *label* and the depth *value*: §3 gives `∃ α ≥ 2` and a disjunction of the two
branches, and pinning which branch and which `α` at a named field is the measurement the
campaign has always treated separately (wave-56 census, `scripts/w57_model/`).  Every statement
below whose conclusion names a specific `α` and branch carries the corresponding `hrange` as a
hypothesis, honestly; the statements that do not name them carry no supply at all.

## Numbering

1. `Hfam` at every even-degree field;
2. the endpoint from the range identity;
3. the even classification over the reciprocity binders;
4. the three model fields;
5. the wave-58 artefacts;
6. axiom pins.
-/

namespace GQ2.Dyadic.EvenParity

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenFamily
open GQ2.Dyadic.EvenRouteFinal

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## §1 `Hfam` at every even-degree field

The parity supply gives the derivation family (`evenFam_nonempty_family_of_paritySupply`,
wave 65), and the relator kill is free on both branches (`evenFam_relatorKill{N,M}`, wave 65).
So the even route's carried input `Hfam` is a theorem at even degree, with no hypothesis beyond
the degree parity and `α ≥ 1` to name the word datum. -/

/-- **`Hfam` AT EVERY EVEN-DEGREE FIELD, `N` BRANCH.**  For `[K : ℚ₂] = 2 + 2h`, every stage
tuple of the `N` word data at every level `k ≥ 3` carries a derivation family killing the
relator.  This is the supply the campaign carried for twelve waves, discharged. -/
theorem evenParity_hfamN_of_finrank {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (nStageWord alpha h halpha) (vN alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  intro k hk T
  obtain ⟨F⟩ := evenFam_nonempty_family_of_paritySupply
    (evenParity_paritySupply_of_finrank hev hk T)
  exact ⟨F, evenFam_relatorKillN F⟩

/-- **`Hfam` AT EVERY EVEN-DEGREE FIELD, `M` BRANCH.** -/
theorem evenParity_hfamM_of_finrank {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ∀ (k : ℕ), 3 ≤ k →
      ∀ T : Tuple (mStageWord alpha h halpha) (vM alpha)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  intro k hk T
  obtain ⟨F⟩ := evenFam_nonempty_family_of_paritySupply
    (evenParity_paritySupply_of_finrank hev hk T)
  exact ⟨F, evenFam_relatorKillM F⟩

/-! ## §2 The endpoint from the range identity

Feeding §1 into the wave-58 endpoint.  Note the shape: the only remaining hypotheses are the
range identity and the degree, both statements about `K` and `χ_cyc` alone. -/

/-- **THE EVEN CLASSIFICATION AT A FIELD FROM THE RANGE IDENTITY, `N` BRANCH.**  If the
cyclotomic image on `G_K(2)` is `imChiN α` for some `α ≥ 2` and `[K : ℚ₂] = 2 + 2h`, then
`G_K(2)` is oriented-isomorphic to the `N` core at `(α, h)`.  No supply. -/
theorem parityFinal_orientedEquivN_of_range {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenRouteFinal_orientedEquivN_atDepth halpha hrange hev
    (evenParity_hfamN_of_finrank (Nat.le_of_succ_le halpha) hev)

/-- **THE EVEN CLASSIFICATION AT A FIELD FROM THE RANGE IDENTITY, `M` BRANCH.** -/
theorem parityFinal_orientedEquivM_of_range {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenRouteFinal_orientedEquivM_atDepth halpha hrange hev
    (evenParity_hfamM_of_finrank (Nat.le_of_succ_le halpha) hev)

end

end GQ2.Dyadic.EvenParity
