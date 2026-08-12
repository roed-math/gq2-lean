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

§4 lands the CLASSIFICATION at the two QUADRATIC model fields, where the ramification binder is a
committed theorem, and records the branch-pinned endpoints at all three model fields;
`KSqrtNegTwo` and `KSqrtTwo` are quadratic (`h = 0`), the quartic `KQuarticN` has `h = 1`.
§5 records the wave-58 artefacts, now carried.

## How to read the word "alone" below

Every statement in this file carries, in addition to the hypotheses named in its docstring, the
standing profinite instance binders the whole even route carries: `FiniteDimensional ℚ_[2] K`,
`CompactSpace (GalK K)`, `T2Space (GalK K)`, `TotallyDisconnectedSpace (GalK K)`, and in §4 the
ambient `CompactSpace AbsGalQ2` and `TotallyDisconnectedSpace AbsGalQ2`.  These are load bearing
and have no global instances in the tree.  "Alone" below always means "and nothing else beyond
those binders"; in particular it means no supply `Prop`, which is the thing this wave removed.

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
open GQ2.Dyadic.Fields

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

/-! ## §3 The even classification over the reciprocity binders

The range identity is not an open question up to the branch: `evenRange_range_eq` (committed)
produces some `α ≥ 2` with `range χ_cyc = imChiM α` or `= imChiN α`, from a marked reciprocity
bundle and the ramified-`K(i)` binder alone.  Composing with §2 removes every supply. -/

section Classification

variable {R : LocalReciprocity}

/-- **THE EVEN CLASSIFICATION.**  For every finite `K/ℚ₂` of even degree `2 + 2h` with `K(i)/K`
ramified and a marked reciprocity bundle, `G_K(2)` is oriented-isomorphic to an even presented
core at some depth `α ≥ 2`, on the `M` branch or on the `N` branch.  No supply, no residual
family, no parity hypothesis: only the two binders the committed range identity already
carries. -/
theorem parityFinal_evenClassification (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) {h : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) ∨
        Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))) := by
  obtain ⟨alpha, halpha, hr⟩ :=
    GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq B deltaI hdeltaI hram
  refine ⟨alpha, halpha, ?_⟩
  rcases hr with hr | hr
  · exact Or.inl (parityFinal_orientedEquivM_of_range halpha hr hev)
  · exact Or.inr (parityFinal_orientedEquivN_of_range halpha hr hev)

/-- **The even classification stated on the degree parity**, with the handle count read off the
degree as `(n - 2)/2`. -/
theorem parityFinal_evenClassification_evenDegree (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (heven : Even (Module.finrank ℚ_[2] K)) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (Nonempty (OrientedContinuousMulEquiv
          (chiM alpha ((Module.finrank ℚ_[2] K - 2) / 2)) (chiCycKTwo (K := K))) ∨
        Nonempty (OrientedContinuousMulEquiv
          (chiN alpha ((Module.finrank ℚ_[2] K - 2) / 2)) (chiCycKTwo (K := K)))) := by
  refine parityFinal_evenClassification B deltaI hdeltaI hram ?_
  have hpos : 0 < Module.finrank ℚ_[2] K := Module.finrank_pos
  obtain ⟨m, hm⟩ := heven
  omega

end Classification

/-! ## §4 The three model fields

At the two QUADRATIC model fields the ramification binder is a committed theorem
(`not_hasEqualNormValueGroups_KSqrtNegTwo`, `..._KSqrtTwo`), so §3 applies there with only the
reciprocity bundle carried.

⚠ At the quartic it is NOT.  The tree holds no `not_hasEqualNormValueGroups_KQuarticN`, and no
route reaches it from the degree: `not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank`
needs ODD degree and `not_hasEqualNormValueGroups_quadField` a quadratic field, and `KQuarticN`
is neither.  So the quartic carries NO classification statement here, only its branch-pinned
endpoint.

The branch-pinned forms, at the depths the wave-56 census measured, are recorded at all three
model fields: those carry `hrange` and nothing else beyond the standing instance binders.
(Superseded at wave 67: `EvenRangeModelFields.lean` discharges `hrange` at the two quadratic
fields, `hrangeFinal_orientedEquivN_sqrtNegTwo` closing `ℚ₂(√−2)` unconditionally and the
`ℚ₂(√2)` twin closing over a base reciprocity bundle; the quartic's `hrange` stays open with
its two costs named there.) -/

section Models

open GQ2.Dyadic.EvenRouteModel

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- A chosen fourth root of unity in `ℚ̄₂`, for the ramification binder. -/
theorem evenParity_sqrtIn_neg_one_sq :
    sqrtIn (-1) ^ 2 = (-1 : ℚ̄₂) := by
  rw [sqrtIn_sq]
  push_cast
  ring

/-- **THE EVEN CLASSIFICATION AT `ℚ₂(√−2)`.**  The first even field the campaign closes.
Over a marked reciprocity bundle and the standing profinite instance binders, and nothing else,
`G_K(2)` for `K = ℚ₂(√−2)` is oriented-isomorphic to an even core at handle count `0` and some
depth `α ≥ 2`, on one of the two branches.  The bundle is a datum, not a supply: it is
parametrized here rather than instantiated, so `markedRecipAt` is not carried. -/
theorem parityFinal_classification_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (Nonempty (OrientedContinuousMulEquiv (chiM alpha 0)
          (chiCycKTwo (K := KSqrtNegTwo))) ∨
        Nonempty (OrientedContinuousMulEquiv (chiN alpha 0)
          (chiCycKTwo (K := KSqrtNegTwo)))) :=
  parityFinal_evenClassification (h := 0) B _ evenParity_sqrtIn_neg_one_sq
    (not_hasEqualNormValueGroups_KSqrtNegTwo _ evenParity_sqrtIn_neg_one_sq)
    (by rw [finrank_KSqrtNegTwo])

/-- **THE EVEN CLASSIFICATION AT `ℚ₂(√2)`.** -/
theorem parityFinal_classification_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      (Nonempty (OrientedContinuousMulEquiv (chiM alpha 0)
          (chiCycKTwo (K := KSqrtTwo))) ∨
        Nonempty (OrientedContinuousMulEquiv (chiN alpha 0)
          (chiCycKTwo (K := KSqrtTwo)))) :=
  parityFinal_evenClassification (h := 0) B _ evenParity_sqrtIn_neg_one_sq
    (not_hasEqualNormValueGroups_KSqrtTwo _ evenParity_sqrtIn_neg_one_sq)
    (by rw [finrank_KSqrtTwo])

/-- **The `N` endpoint at `ℚ₂(√−2)` at the measured depth `2`**, over the branch identification
and the standing instance binders.  The wave-55 pilot statement with both of its supplies
discharged: wave 56 refuted its flip input and wave 65 showed its family input was the
conclusion; this is the conclusion. -/
theorem parityFinal_orientedEquivN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 0) (chiCycKTwo (K := KSqrtNegTwo))) :=
  parityFinal_orientedEquivN_of_range (le_refl 2) hrange
    (by rw [finrank_KSqrtNegTwo])

/-- **The `M` endpoint at `ℚ₂(√2)` at the measured depth `3`**, over the branch identification
and the standing instance binders. -/
theorem parityFinal_orientedEquivM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3) :
    Nonempty (OrientedContinuousMulEquiv (chiM 3 0) (chiCycKTwo (K := KSqrtTwo))) :=
  parityFinal_orientedEquivM_of_range (by omega) hrange
    (by rw [finrank_KSqrtTwo])

/-- **The `N` endpoint at the quartic `ℚ₂(β)` at the measured depth `3` and handle count `1`**,
over the branch identification and the standing instance binders.  The field wave 56's census
singled out. -/
theorem parityFinal_orientedEquivN_quartic [T2Space (GalK KQuarticN)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom = imChiN 3) :
    Nonempty (OrientedContinuousMulEquiv (chiN 3 1) (chiCycKTwo (K := KQuarticN))) :=
  parityFinal_orientedEquivN_of_range (by omega) hrange
    finrank_KQuarticN_even

end Models

/-! ## §5 The wave-58 artefacts, now carried

`EvenRouteFinalCarried{N,M}` was the even route's packaged conclusion, guarded by the family
supply.  Wave 65 proved it equivalent to the endpoint; §2 proves the endpoint from the range
identity, so the artefact now follows from the range identity and the degree. -/

section Artefacts

/-- **The wave-58 `N` artefact from the range identity and the degree.** -/
theorem parityFinal_carriedN_of_range {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalCarriedN h K :=
  (hfamFinal_carriedN_iff_orientedEquiv halpha hrange hev).mpr
    (parityFinal_orientedEquivN_of_range halpha hrange hev)

/-- **The wave-58 `M` artefact from the range identity and the degree.** -/
theorem parityFinal_carriedM_of_range {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalCarriedM h K :=
  (hfamFinal_carriedM_iff_orientedEquiv halpha hrange hev).mpr
    (parityFinal_orientedEquivM_of_range halpha hrange hev)

/-- **The artefact holds on one of the two branches at every even-degree field** with `K(i)/K`
ramified, over the reciprocity bundle and the standing instance binders. -/
theorem parityFinal_carried_evenClassification {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI) {h : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteFinalCarriedM h K ∨ EvenRouteFinalCarriedN h K := by
  obtain ⟨alpha, halpha, hr⟩ :=
    GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq B deltaI hdeltaI hram
  rcases hr with hr | hr
  · exact Or.inl (parityFinal_carriedM_of_range halpha hr hev)
  · exact Or.inr (parityFinal_carriedN_of_range halpha hr hev)

end Artefacts

end

/-! ## §6 Axiom pins

The lane's endpoints printed side by side with the committed even endpoints they consume and
with the odd route's parity supply whose argument this wave clones.  Nothing here may exceed the
committed endpoint set. -/

section AxiomPins

open GQ2.Dyadic.EvenParity

-- §1 `Hfam` at every even-degree field
#print axioms evenParity_hfamN_of_finrank
#print axioms evenParity_hfamM_of_finrank

-- §2 the endpoint from the range identity
#print axioms parityFinal_orientedEquivN_of_range
#print axioms parityFinal_orientedEquivM_of_range

-- §3 the even classification
#print axioms parityFinal_evenClassification
#print axioms parityFinal_evenClassification_evenDegree

-- §4 the model fields
#print axioms parityFinal_classification_sqrtNegTwo
#print axioms parityFinal_classification_sqrtTwo
#print axioms parityFinal_orientedEquivN_sqrtNegTwo
#print axioms parityFinal_orientedEquivM_sqrtTwo
#print axioms parityFinal_orientedEquivN_quartic

-- §5 the artefacts
#print axioms parityFinal_carriedN_of_range
#print axioms parityFinal_carriedM_of_range
#print axioms parityFinal_carried_evenClassification

-- the committed endpoints consumed, for the side-by-side
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.EvenRouteFinal.evenRouteFinal_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.EvenFamily.hfamFinal_carriedN_iff_orientedEquiv
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq

end AxiomPins

end GQ2.Dyadic.EvenParity
