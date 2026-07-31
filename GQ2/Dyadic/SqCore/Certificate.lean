/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.MarkedCore.Certificate
import GQ2.Dyadic.SqCore.PivotLemma
import GQ2.Dyadic.SqCore.Rank3

/-!
# SQ4 — the `L_sq` marked-core certificate (packet §7 at the square-commutator core)

**Ticket SQ4** of the dyadic campaign (lane SQ), the MC5 seam.  MC5
(`GQ2/Dyadic/MarkedCore/Certificate.lean`) landed the certificate layer for the `M`/`N` cores
and, in its §6, redid S2.4 §6.4's handle-mixing analysis in the `L_sq` frame.  This file is the
`L_sq` side of that seam: it discharges MC5's `SqMixPivot` obligation, states the certificate
record for the `L_sq` family, proves the marked-matching reduction, and instantiates the
certificate at rank three over `ℚ₂` (where it is *unconditional*).

## Contents

* **§1** the exponent datum, **PROVED** (`sqMixPivot`, via `SqCore/PivotLemma.lean`), and the
  canonical pivot `w = σ·x₀^{−c}` with its `χ`/`ν` rows;
* **§2** the `ν`-frame of the `L_sq` core: the pivot functional, the **forced row**
  `ν(x₁) = 2ν(x₀)`, and the generator-wise recognition lemma for `ν_sq`;
* **§3** `MarkedCoreCertificateSq`, the certificate record (MC5's five ledger fields at the
  `L_sq` core), and the orientation contraction `chiSq_matching`;
* **§4** the two lifting strata and the marked-matching reduction `sqMarkedMatching`, then the
  abstract-slot productions and the `K`-facing layer (AX3's `MarkedRecip` bundle);
* **§5** the rank-three seam: `marked_square_core_rank3_certificate`, SQ3's theorem reshaped
  into the certificate's field list at the arithmetic slot `G_{ℚ₂}(2)`;
* **§6** stress pins.

## The binder inventory (the SQ4 supply list of record)

Per core, what the production theorems consume:

| slot | supplied by | status |
|---|---|---|
| `f : D_sq ≅ G`, `horient`, continuity of the transported `ν` | AS1 / the `MarkedRecip` bundle | slots |
| marked data `ν'(w) = 1` (the pivot row) | packet Prop. 7.2's `markedDataEq` at this core | hypothesis |
| handle stratum `SqHandleMixHypothesis h c` | MC5's binder — the errata-item-1 change of variables | **binder** |
| core stratum `SqCoreShearHypothesis h c` | *new*, see below | **binder** |
| exponent datum `∃ c ∈ ℤ₂ˣ, X^c = S` | `SqCore/PivotLemma.lean` | **theorem** |

### Why a second binder — the `w`-shear stratum (SQ4 finding)

MC5's `SqHandleMixHypothesis` clears the handle plane and preserves the **pivot row**
`ν'(w)`, `w = σ·x₀^{−c}`; that is exactly what the frame analysis of MC5 §6 licenses, and it
is *not* enough to pin the two core coordinates.  On the `L_sq` frame the χ-preserving,
pivot-row-preserving moves act on `(a, b) = (ν'(σ̄), ν'(x̄₀))` by the one-parameter shear

```text
(a, b) ↦ (a + cμ·d, b + μ·d),      d = a − c·b = ν'(w),      μ ∈ ℤ₂
```

(the `t`-component is excluded because `χ(t) = −1 ≠ 1`, and `λ = cμ` is forced by
`ν'(Ψ w) = ν'(w)`).  So: the reachable set from a marking with `d = 1` is exactly
`{(1 + cμ, μ)}`, which contains the target `ν_sq = (1, 0)` — at `μ = 0` — but a *general*
transported marking sits at some `μ ≠ 0` and needs the shear to get back.  The `L_sq` family
has no core-stratum move set in the repository (the analogue of MC3/MC4's S1/S2/S3 families
for the `M`/`N` cores; the SQ lane's SQ5 is deferred to AS4), so the shear is threaded as the
binder `SqCoreShearHypothesis` — a `def`, never an axiom, non-vacuously satisfied by the
standard marking (`sqCoreShearHypothesis_nonvacuous`) and **discharged outright** whenever the
handle move happens to fix the `x₀`-row (`sqCoreShear_of_nu_x0`).

Two consequences worth recording for the CoV/WL tickets:

1. **The recommended strengthening.**  MC-HM's construction (board log 2026-07-30: *"the unique
   `|A| ≤ 6` mixing solution fixes `x₀/σ/v` literally"*) delivers handle moves that fix the core
   letters on the nose.  If the eventual discharge of `SqHandleMixHypothesis` is stated in that
   stronger form — `ν'(Ψ σ) = ν'(σ)` and `ν'(Ψ x₀) = ν'(x₀)` in place of the pivot-row clause —
   then `sqCoreShear_of_nu_x0` makes the shear binder unnecessary and the `L_sq` certificate
   needs **one** binder, matching the `N`-core's inventory.  That is a statement change in
   MC5's file, which SQ4 does not own.
2. `d = 1` **exactly**, not `IsUnit d`, is the right marked-data clause here: the shear cannot
   change `d`, so a unit-but-not-one pivot row is unreachable from `ν_sq`.  MC5's
   `nuSq_sqMixPivotElem` (the exact unit row `ν_sq(w) = 1`) is what makes the clause
   satisfiable, and it is the `L_sq` analogue of the `M`-side `IsUnit ν'(C̄₀)` data check.

## Shape: the `L_sq` core needed its own record (recorded)

MC5's `MarkedCoreCertificateM`/`N` are typed at `DM α h`/`DN α h` with `chiM`/`chiN`,
`nuM`/`nuN` — the abstract slot is only the *target* `(G, chiG, nuG)`, not the source — so the
`L_sq` core cannot be plugged into either production.  What is reused is the *pattern* (SD1's
Q4 abstract marked pro-2 slot: plain `MonoidHom`s, continuity in the production hypotheses, the
`MarkedRecip`-parametrized `K` layer), field for field.  `MarkedCoreCertificateSq` is therefore
a new record with MC5's five ledger fields.

## Plain-import header (recorded deviation)

`GQ2/Dyadic/SqCore/Rank3.lean` is a plain-import file (SQ3, by design — it reaches into the
frozen `GQ2/Roe/` tail), and a `module` file may not import a non-module one, so this file is
plain-import too, exactly as `sq-design.md` §6 prescribes for SQ4.  `SqCore/PivotLemma.lean` is
module-style; nothing here forces that back.

## Axiom hygiene

Every declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`) *except* the
rank-three seam of §5, which consumes SQ3's `marked_square_core_rank3` and therefore prints
std-3 + `dyadicOrientation` (**B3c**) + `peripheralCyclotomicAction` (**B8**) — both
pre-existing census entries, census unchanged at **11**.  The B3c/B8 print is confined to the
two §5 declarations that name the arithmetic slot:

```text
marked_square_core_rank3_certificate : std-3 + dyadicOrientation + peripheralCyclotomicAction
sqCertificateRankThree_nu_ur         : std-3 + dyadicOrientation + peripheralCyclotomicAction
MarkedCoreCertificateSq              : std-3        -- the record, and all of §1–§4
sqMixPivot / sqPivotExp / sqPivot    : std-3
sqMarkedMatching                     : std-3
marked_matching_certificate_sq       : std-3
sqEquivDRMarked + its value lemmas   : std-3        -- the h = 0 identification is axiom-free
```

as recorded in the SQ23 precedent (the *structure* never carries what the *discharge* does).
Prints are verified out of band (`GQ2/AxiomLedger.lean` + `scripts/check_axioms.sh`); no
`#print axioms` is committed, per the lane idiom.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The exponent datum, and the canonical clearing pivot

MC5 §6 identified the corrected clearing pivot `w = σ·x₀^{−c}` where `X^c = S`, and recorded
the existence of `c` as the SQ4 supply obligation.  `SqCore/PivotLemma.lean` proves it; here it
is packaged as MC5's record and as a canonical exponent, so that downstream statements can name
one pivot rather than quantifying over exponents. -/

section Pivot

/-- **MC5's `SqMixPivot` obligation, DISCHARGED** — no longer a hypothesis anywhere. -/
theorem sqMixPivot : MarkedCore.SqMixPivot :=
  ⟨exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit⟩

/-- **The canonical `L_sq` pivot exponent**: a choice of `c ∈ ℤ₂ˣ` with `X^c = S`.  The choice
is harmless — `zpowZtwo_injective_of_exact_level` makes `c` unique — and naming it lets the
certificate quantify over nothing. -/
noncomputable def sqPivotExp : ℤ_[2] := exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit.choose

/-- The canonical exponent is a unit. -/
theorem isUnit_sqPivotExp : IsUnit sqPivotExp :=
  exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit.choose_spec.1

/-- The defining relation of the canonical exponent: `X ^ c = S`. -/
theorem zpowZtwo_rootXUnit_sqPivotExp :
    zpowZtwo isProP_two_unitsPadicInt rootXUnit sqPivotExp = SvalUnit :=
  exists_isUnit_zpowZtwo_rootXUnit_eq_SvalUnit.choose_spec.2

/-- **The canonical clearing pivot** `w = σ · x₀^{−c}` of the `L_sq` frame, at the canonical
exponent (MC5's `sqMixPivotElem`). -/
noncomputable def sqPivot (h : ℕ) : (DSq h : Type) := sqMixPivotElem h sqPivotExp

/-- The canonical pivot is χ-trivial — the row that licenses the Eichler clearing moves. -/
theorem chiSq_sqPivot (h : ℕ) : chiSq h (sqPivot h) = 1 :=
  chiSq_sqMixPivotElem h zpowZtwo_rootXUnit_sqPivotExp

/-- **The `L_sq` unit row at the canonical pivot**: `ν_sq(w) = 1` exactly. -/
theorem nuSq_sqPivot (h : ℕ) : nuSq h (sqPivot h) = ofAdd (1 : ℤ_[2]) :=
  nuSq_sqMixPivotElem h sqPivotExp

/-- The canonical pivot's `ν`-row is a unit (the form MC5's binder consumes). -/
theorem isUnit_nuSq_sqPivot (h : ℕ) : IsUnit (toAdd (nuSq h (sqPivot h))) :=
  isUnit_nuSq_sqMixPivotElem h sqPivotExp

end Pivot

/-! ## §2 The `ν`-frame of the `L_sq` core

Three h-generic facts about an arbitrary continuous `ℤ₂`-marking of `D_sq`: the value at the
pivot, the **forced row** on `x₁`, and the resulting generator-wise recognition of `ν_sq`. -/

section NuFrame

variable {h : ℕ}

/-- The index split of `Fin (sqRank h)` — three core letters and `h` handle pairs (the `L_sq`
analogue of MC4's `nCoreIdx_cases`). -/
theorem sqIdx_cases (i : Fin (sqRank h)) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ (∃ j : Fin h, i = sqHandleIdxU j) ∨
      ∃ j : Fin h, i = sqHandleIdxV j := by
  have hlt : (i : ℕ) < 3 + 2 * h := i.isLt
  by_cases h0 : (i : ℕ) = 0
  · exact Or.inl (Fin.val_injective (by rw [h0, sqVal_zero]))
  by_cases h1 : (i : ℕ) = 1
  · exact Or.inr (Or.inl (Fin.val_injective (by rw [h1, sqVal_one])))
  by_cases h2 : (i : ℕ) = 2
  · exact Or.inr (Or.inr (Or.inl (Fin.val_injective (by rw [h2, sqVal_two]))))
  have hj : ((i : ℕ) - 3) / 2 < h := by omega
  by_cases hpar : (i : ℕ) % 2 = 1
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨((i : ℕ) - 3) / 2, hj⟩, Fin.val_injective ?_⟩)))
    rw [sqHandleIdxU_val]
    show (i : ℕ) = 3 + 2 * (((i : ℕ) - 3) / 2)
    omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨((i : ℕ) - 3) / 2, hj⟩, Fin.val_injective ?_⟩)))
    rw [sqHandleIdxV_val]
    show (i : ℕ) = 4 + 2 * (((i : ℕ) - 3) / 2)
    omega

/-- **The pivot functional**: `ν'(w) = ν'(σ) − c·ν'(x₀)` for every marking and every exponent —
the frame row MC5 §6 computes, in Lean. -/
theorem toAdd_nu_sqMixPivotElem (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (c : ℤ_[2]) : toAdd (nu' (sqMixPivotElem h c))
      = toAdd (nu' (dsqSigma h)) - c * toAdd (nu' (dsqX0 h)) := by
  rw [sqMixPivotElem, map_mul, map_inv, toAdd_mul, toAdd_inv,
    toAdd_map_zpowZtwo (isProP_DSq h) nu' (dsqX0 h) c]
  ring

/-- **The forced row of the `L_sq` core**: `ν(x₁) = 2·ν(x₀)` for *every* continuous `ℤ₂`-marking
— the abelianized relation `ρ_sq = −4x̄₀ + 2x̄₁` divided by the torsion-free `2`.  (Unlike the
`M`-core there is no forced row on a *marked* letter: `σ̄` is a free coordinate.) -/
theorem toAdd_nu_dsqX1 (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (dsqX1 h)) = 2 * toAdd (nu' (dsqX0 h)) := by
  have hrel : sqRelWord (fun i => nu' (sqGen h i)) = 1 := by
    rw [← map_sqRelWord nu' (sqGen h), dsq_relation h, map_one]
  rw [sqRelWord_comm] at hrel
  have hval := congrArg toAdd hrel
  rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_one] at hval
  simp only [nsmul_eq_mul] at hval
  push_cast at hval
  refine mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) ?_
  show (2 : ℤ_[2]) * toAdd (nu' (sqGen h 2)) = 2 * (2 * toAdd (nu' (sqGen h 1)))
  linear_combination hval

/-- **Recognition of `ν_sq`**: a marking that takes the standard values on `σ` and `x₀` and is
trivial on the handle letters **is** `ν_sq` — the `x₁`-row comes for free from the forced row.
This is the step the marked-matching reduction closes with. -/
theorem nu_eq_nuSq_of_core (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hσ : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hU : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hV : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxV j)) = 1) :
    ∀ x, nu' x = nuSq h x := by
  have hx1 : nu' (dsqX1 h) = ofAdd (0 : ℤ_[2]) := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nu_dsqX1, hx0, toAdd_ofAdd, mul_zero]
  have hext : nu' = nuSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show sqGen h 0 = dsqSigma h from rfl, hσ, nuSq_sigma]
    · rw [show sqGen h 1 = dsqX0 h from rfl, hx0, nuSq_x0]
    · rw [show sqGen h 2 = dsqX1 h from rfl, hx1, nuSq_x1]
    · rw [hU j, nuSq_handleU]
    · rw [hV j, nuSq_handleV]
  exact fun x => DFunLike.congr_fun hext x

/-- **Orientation contraction, `L_sq` side** (MC5's `chiM_matching`/`chiN_matching` analogue):
a continuous character with the three Hensel values on the core letters and `1` on the handle
letters **is** `χ_sq`.  The `L_sq` core needs no Labute-datum uniqueness step: `sqLiftHom`'s
values are the datum. -/
theorem chiSq_matching (χ' : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ)
    (hσ : χ' (dsqSigma h) = SvalUnit) (hx0 : χ' (dsqX0 h) = rootXUnit)
    (hx1 : χ' (dsqX1 h) = YvalUnit)
    (hU : ∀ j : Fin h, χ' (sqGen h (sqHandleIdxU j)) = 1)
    (hV : ∀ j : Fin h, χ' (sqGen h (sqHandleIdxV j)) = 1) :
    ∀ x, χ' x = chiSq h x := by
  have hext : χ' = chiSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show sqGen h 0 = dsqSigma h from rfl, hσ, chiSq_sigma]
    · rw [show sqGen h 1 = dsqX0 h from rfl, hx0, chiSq_x0]
    · rw [show sqGen h 2 = dsqX1 h from rfl, hx1, chiSq_x1]
    · rw [hU j, chiSq_handleU]
    · rw [hV j, chiSq_handleV]
  exact fun x => DFunLike.congr_fun hext x

end NuFrame

/-! ## §3 `MarkedCoreCertificateSq` (packet Def. 7.1 / ledger §5.1, at the `L_sq` core)

MC5's five ledger fields, on the abstract marked pro-2 slot `(G, chiG, nuG)`: the certificate
stores pointwise equalities, so no continuity is stored and the characters are plain monoid
homs; continuity of the transported marking lives in the production hypotheses (discharged by
the `MarkedRecip` bundle at the `K`-instantiation). -/

/-- **The marked-core certificate for the `L_sq` family** at handle count `h`. -/
structure MarkedCoreCertificateSq (h : ℕ) {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  /-- Item 1: the abstract Demushkin isomorphism (Labute's classification; at `h = 0` this is
  `bLab`, whose `BLabHypothesis` is specialized to this very core). -/
  abstractEquiv : ContinuousMulEquiv (DSq h : Type) G
  /-- Item 2: the intrinsic orientation matches the canonical one through the isomorphism. -/
  orientation : ∀ x, chiG (abstractEquiv x) = chiSq h x
  /-- Item 3a: the marking-correcting automorphism. -/
  correction : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)
  /-- Item 3b: the correction preserves the canonical orientation. -/
  correction_chi : ∀ x, chiSq h (correction x) = chiSq h x
  /-- Item 3c: the corrected isomorphism matches the unramified markings. -/
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) = nuSq h x

/-! ## §4 The lifting strata and the marked-matching reduction (packet Prop. 7.2)

The handle stratum is MC5's binder; the core stratum is the `w`-shear (see the module
docstring).  Everything else is a theorem. -/

section Strata

/-- **The `L_sq` core-plane shear stratum** (a `def`, never an axiom): for every marking whose
pivot row is exactly `1`, a χ-preserving continuous automorphism normalizes the two core
coordinates to the standard values and leaves the handle values alone.

This is the `L_sq` analogue of MC3/MC4's core strata (S1/S2/S3) — the one move family the
`L_sq` frame still needs and the repository does not have.  It is stated in the *outcome* form
(as MC5 states `SqHandleMixHypothesis`), so its eventual discharge is a statement about
automorphisms of `D_sq`, not about a monoid of frame endomorphisms. -/
def SqCoreShearHypothesis (h : ℕ) (c : ℤ_[2]) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x)
          ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
          ∧ nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
          ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = nu' (sqGen h (sqHandleIdxU j)))
          ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = nu' (sqGen h (sqHandleIdxV j)))

/-- **The shear is free when the `x₀`-row is already standard**: the identity works, because the
pivot row then *is* the `σ`-row (`ν'(w) = ν'(σ) − c·0`).  Consequently, if the discharge of
`SqHandleMixHypothesis` is stated in MC-HM's stronger "fixes `x₀` literally" form, the shear
binder disappears — see the module docstring. -/
theorem sqCoreShear_of_nu_x0 {h : ℕ} {c : ℤ_[2]}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hpiv : nu' (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
        ∧ nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = nu' (sqGen h (sqHandleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = nu' (sqGen h (sqHandleIdxV j))) := by
  refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, ?_, hx0, fun _ => rfl, fun _ => rfl⟩
  show nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])
  refine Multiplicative.toAdd.injective ?_
  have hp := toAdd_nu_sqMixPivotElem nu' c
  rw [hpiv, hx0, toAdd_ofAdd, toAdd_ofAdd, mul_zero, sub_zero] at hp
  rw [← hp, toAdd_ofAdd]

/-- The standard marking meets the shear binder's hypothesis at every `(h, c)` — the binder is
never vacuously quantified (the `L_sq` mirror of MC5's `sqHandleMix_hypothesis_nonvacuous`). -/
theorem sqCoreShearHypothesis_nonvacuous (h : ℕ) (c : ℤ_[2]) :
    nuSq h (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2]) := nuSq_sqMixPivotElem h c

/-- At `h = 0` **and** at the standard marking the shear binder's conclusion is a theorem: the
identity already normalizes both core rows. -/
theorem sqCoreShear_nuSq (h : ℕ) (c : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ nuSq h (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
        ∧ nuSq h (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
        ∧ (∀ j : Fin h, nuSq h (Ψ (sqGen h (sqHandleIdxU j))) = nuSq h (sqGen h (sqHandleIdxU j)))
        ∧ (∀ j : Fin h,
            nuSq h (Ψ (sqGen h (sqHandleIdxV j))) = nuSq h (sqGen h (sqHandleIdxV j))) :=
  sqCoreShear_of_nu_x0 (nuSq h) (nuSq_sqMixPivotElem h c) (nuSq_x0 h)

end Strata

section Reduction

/-- **The marked-matching reduction at the `L_sq` core** (packet Prop. 7.2): under the two
strata binders, every transported marking whose pivot row is exactly `1` admits a χ-preserving
correction `u` with `ν' ∘ u = ν_sq` **on all of `D_sq`**.

Composition: clear the handle plane with MC5's binder (its hypothesis is the pivot row, which
the marked-data clause supplies), then normalize the core plane with the shear — which does not
disturb the cleared handles — and close by the §2 recognition lemma, whose `x₁`-row is the
forced row. -/
theorem sqMarkedMatching {h : ℕ} {c : ℤ_[2]} (hMix : SqHandleMixHypothesis h c)
    (hShear : SqCoreShearHypothesis h c)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hpiv : nu' (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2])) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nu' (u x) = nuSq h x := by
  obtain ⟨Ψ₁, hΨ₁chi, hU₁, hV₁, hpivfix⟩ :=
    hMix nu' (by rw [hpiv, toAdd_ofAdd]; exact isUnit_one)
  have hpiv₁ : (nu'.comp (autHom Ψ₁)) (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2]) := by
    show nu' (Ψ₁ (sqMixPivotElem h c)) = ofAdd (1 : ℤ_[2])
    rw [hpivfix, hpiv]
  obtain ⟨Ψ₂, hΨ₂chi, hσ₂, hx0₂, hU₂, hV₂⟩ := hShear (nu'.comp (autHom Ψ₁)) hpiv₁
  refine ⟨Ψ₂.trans Ψ₁, fun x => ?_, ?_⟩
  · show chiSq h (Ψ₁ (Ψ₂ x)) = chiSq h x
    rw [hΨ₁chi, hΨ₂chi]
  · have hcomp : ∀ x, (nu'.comp (autHom (Ψ₂.trans Ψ₁))) x = nuSq h x := by
      refine nu_eq_nuSq_of_core _ hσ₂ hx0₂ (fun j => ?_) (fun j => ?_)
      · show nu' (Ψ₁ (Ψ₂ (sqGen h (sqHandleIdxU j)))) = 1
        rw [show nu' (Ψ₁ (Ψ₂ (sqGen h (sqHandleIdxU j))))
          = (nu'.comp (autHom Ψ₁)) (Ψ₂ (sqGen h (sqHandleIdxU j))) from rfl, hU₂ j]
        exact hU₁ j
      · show nu' (Ψ₁ (Ψ₂ (sqGen h (sqHandleIdxV j)))) = 1
        rw [show nu' (Ψ₁ (Ψ₂ (sqGen h (sqHandleIdxV j))))
          = (nu'.comp (autHom Ψ₁)) (Ψ₂ (sqGen h (sqHandleIdxV j))) from rfl, hV₂ j]
        exact hV₁ j
    exact fun x => hcomp x

/-- The reduction at the **canonical** pivot exponent (the exponent datum is a theorem, so it is
not a hypothesis): the binder surface is exactly the two strata. -/
theorem sqMarkedMatching_canonical {h : ℕ} (hMix : SqHandleMixHypothesis h sqPivotExp)
    (hShear : SqCoreShearHypothesis h sqPivotExp)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hpiv : nu' (sqPivot h) = ofAdd (1 : ℤ_[2])) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nu' (u x) = nuSq h x :=
  sqMarkedMatching hMix hShear nu' hpiv

/-- The reduction's hypothesis set is inhabited: at the standard marking the pivot row is
exactly `1`, so the correction exists (with the identity as witness on both strata). -/
theorem sqMarkedMatching_nuSq {h : ℕ} {c : ℤ_[2]} (hMix : SqHandleMixHypothesis h c)
    (hShear : SqCoreShearHypothesis h c) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nuSq h (u x) = nuSq h x :=
  sqMarkedMatching hMix hShear (nuSq h) (nuSq_sqMixPivotElem h c)

end Reduction

/-! ### The abstract-slot productions -/

section Production

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Certificate production at the `L_sq` core** (packet Prop. 7.2 assembled): from the
abstract isomorphism (item 1), the orientation matching (item 2), the continuity of the
transported marking, the marked-data pivot row, and the two strata binders, the full
certificate exists. -/
theorem marked_matching_certificate_sq (h : ℕ) (c : ℤ_[2])
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (horient : ∀ x, chiG (f x) = chiSq h x)
    (hcont : Continuous fun x : (DSq h : Type) => nuG (f x))
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hpiv : nuG (f (sqMixPivotElem h c)) = ofAdd (1 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateSq h chiG nuG) := by
  set nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    { toFun := fun x => nuG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hcont } with hnu'
  obtain ⟨u, huchi, hunu⟩ := sqMarkedMatching hMix hShear nu' hpiv
  exact ⟨⟨f, horient, u, huchi, fun x => hunu x⟩⟩

/-- Certificate production with the orientation supplied in **generator-value form** (the shape
a `K`-side computation produces), contracted by §2's `chiSq_matching`. -/
theorem marked_matching_certificate_sq_of_values (h : ℕ) (c : ℤ_[2])
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (hχcont : Continuous fun x : (DSq h : Type) => chiG (f x))
    (hσ : chiG (f (dsqSigma h)) = SvalUnit) (hx0 : chiG (f (dsqX0 h)) = rootXUnit)
    (hx1 : chiG (f (dsqX1 h)) = YvalUnit)
    (hUχ : ∀ j : Fin h, chiG (f (sqGen h (sqHandleIdxU j))) = 1)
    (hVχ : ∀ j : Fin h, chiG (f (sqGen h (sqHandleIdxV j))) = 1)
    (hcont : Continuous fun x : (DSq h : Type) => nuG (f x))
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hpiv : nuG (f (sqMixPivotElem h c)) = ofAdd (1 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateSq h chiG nuG) := by
  set χ' : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
    { toFun := fun x => chiG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hχcont } with hχ'
  have horient : ∀ x, chiG (f x) = chiSq h x := chiSq_matching χ' hσ hx0 hx1 hUχ hVχ
  exact marked_matching_certificate_sq h c chiG nuG f horient hcont hMix hShear hpiv

end Production

/-! ### The `K`-facing instantiation layer (AX3's `MarkedRecip` bundle)

Exactly MC5 §5's pattern: the `K`-side characters live on `GalKab K` and are read through an
abelianization slot `π : G →* GalKab K`, so the layer stays bundle-parametrized and axiom-free
(`markedRecipAt` is never named). -/

section KLayer

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The `K`-instantiated `L_sq` certificate**: the abstract certificate at the bundle's marked
characters, read through the abelianization slot `π`. -/
abbrev MarkedCoreCertificateKSq (B : MarkedRecip R K) (h : ℕ) (π : G →* GalKab K) :=
  MarkedCoreCertificateSq h ((chiCycKAb K).comp π) (B.nu_ur.comp π)

/-- **The `K`-side production for the `L_sq` family**: the bundle's `continuous_nu_ur`
discharges the marking-continuity hypothesis, so the inputs are the abstract isomorphism, the
continuity of the slot, the orientation matching, the marked-data pivot row, and the two
strata binders. -/
theorem marked_matching_certificate_KSq (B : MarkedRecip R K) (h : ℕ) (c : ℤ_[2])
    (π : G →* GalKab K) (hπ : Continuous π)
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (horient : ∀ x, chiCycKAb K (π (f x)) = chiSq h x)
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hpiv : B.nu_ur (π (f (sqMixPivotElem h c))) = ofAdd (1 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateKSq B h π) :=
  marked_matching_certificate_sq h c ((chiCycKAb K).comp π) (B.nu_ur.comp π) f horient
    (B.continuous_nu_ur.comp (hπ.comp f.continuous_toFun)) hMix hShear hpiv

end KLayer

/-! ## §5 The rank-three seam

At `h = 0` the `L_sq` core **is** `D_R` (SQ2's `dsq_zero`), and SQ3 discharged the rank-three
marked-core theorem `marked_square_core_rank3` unconditionally.  This section reshapes that
theorem into the certificate's field list at the arithmetic slot `G_{ℚ₂}(2)`.

The identification used here is **not** `dsqEquivDR` (whose `cast` is opaque to the
elaborator): it is rebuilt from the two universal properties, so that the generator values are
theorems (`sqEquivDRMarked_sigma` and friends) rather than transports.  That construction is
axiom-free; only the two declarations that name the arithmetic slot carry B3c + B8. -/

section RankThree

/-- The marking of `D_R` by the `L_sq` generators — the relation is `dsq_relation` read through
`sqRelWord_zero`. -/
private theorem drWord_dsqGen : drWord (dsqSigma 0) (dsqX0 0) (dsqX1 0) = 1 := by
  have h := dsq_relation 0
  rwa [sqRelWord_zero] at h

/-- `D_sq(0) → D_R`, by the universal property of `D_sq` at the marking `(s, x, y)`. -/
noncomputable def sqToDR : ContinuousMonoidHom (DSq 0 : Type) (DR : Type) :=
  sqLiftHom 0 isProP_DR (sqMark drS drX drY) (by rw [sqRelWord_sqMark]; exact dr_relation)

/-- `D_R → D_sq(0)`, by the universal property of `D_R` at the marking `(σ, x₀, x₁)`. -/
noncomputable def drToSq : ContinuousMonoidHom (DR : Type) (DSq 0 : Type) :=
  drLiftHom (isProP_DSq 0) ![dsqSigma 0, dsqX0 0, dsqX1 0] drWord_dsqGen

@[simp] theorem sqToDR_sigma : sqToDR (dsqSigma 0) = drS :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

@[simp] theorem sqToDR_x0 : sqToDR (dsqX0 0) = drX :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

@[simp] theorem sqToDR_x1 : sqToDR (dsqX1 0) = drY :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

@[simp] theorem drToSq_drS : drToSq drS = dsqSigma 0 := drLiftHom_S _ _ _

@[simp] theorem drToSq_drX : drToSq drX = dsqX0 0 := drLiftHom_X _ _ _

@[simp] theorem drToSq_drY : drToSq drY = dsqX1 0 := drLiftHom_Y _ _ _

theorem drToSq_sqToDR (x : (DSq 0 : Type)) : drToSq (sqToDR x) = x := by
  have hext : drToSq.comp sqToDR = ContinuousMonoidHom.id (DSq 0 : Type) := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, _⟩ | ⟨j, _⟩
    · show drToSq (sqToDR (dsqSigma 0)) = dsqSigma 0
      rw [sqToDR_sigma, drToSq_drS]
    · show drToSq (sqToDR (dsqX0 0)) = dsqX0 0
      rw [sqToDR_x0, drToSq_drX]
    · show drToSq (sqToDR (dsqX1 0)) = dsqX1 0
      rw [sqToDR_x1, drToSq_drY]
    · exact absurd j.2 (by omega)
    · exact absurd j.2 (by omega)
  exact DFunLike.congr_fun hext x

theorem sqToDR_drToSq (y : (DR : Type)) : sqToDR (drToSq y) = y := by
  have hext : sqToDR.comp drToSq = ContinuousMonoidHom.id (DR : Type) := by
    refine dr_hom_ext _ _ ?_ ?_ ?_
    · show sqToDR (drToSq drS) = drS
      rw [drToSq_drS, sqToDR_sigma]
    · show sqToDR (drToSq drX) = drX
      rw [drToSq_drX, sqToDR_x0]
    · show sqToDR (drToSq drY) = drY
      rw [drToSq_drY, sqToDR_x1]
  exact DFunLike.congr_fun hext y

/-- **The marked `h = 0` identification** `D_sq(0) ≅ D_R`, built from the two universal
properties so that its generator values are theorems (SQ2's `dsqEquivDR` is the same map — both
are *the* identification — but its `cast` presentation carries no value lemmas). -/
noncomputable def sqEquivDRMarked : ContinuousMulEquiv (DSq 0 : Type) (DR : Type) :=
  continuousMulEquivOfBijective sqToDR
    (Function.bijective_iff_has_inverse.mpr ⟨drToSq, drToSq_sqToDR, sqToDR_drToSq⟩)

@[simp] theorem sqEquivDRMarked_apply (x : (DSq 0 : Type)) : sqEquivDRMarked x = sqToDR x := rfl

/-- **The orientation transports**: `χ_R ∘ (D_sq(0) ≅ D_R) = χ_sq(0)`. -/
theorem chiR_sqEquivDRMarked (x : (DSq 0 : Type)) : chiR (sqEquivDRMarked x) = chiSq 0 x := by
  have hext : chiR.comp sqToDR = chiSq 0 := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, _⟩ | ⟨j, _⟩
    · show chiR (sqToDR (dsqSigma 0)) = chiSq 0 (dsqSigma 0)
      rw [sqToDR_sigma, chiR_drS, chiSq_sigma]
    · show chiR (sqToDR (dsqX0 0)) = chiSq 0 (dsqX0 0)
      rw [sqToDR_x0, chiR_drX, chiSq_x0]
    · show chiR (sqToDR (dsqX1 0)) = chiSq 0 (dsqX1 0)
      rw [sqToDR_x1, chiR_drY, chiSq_x1]
    · exact absurd j.2 (by omega)
    · exact absurd j.2 (by omega)
  exact DFunLike.congr_fun hext x

/-- **The marking transports**: `ι ∘ ν_R ∘ (D_sq(0) ≅ D_R) = ν_sq(0)`, for the `Ztwo`-
normalization `ι` pinned on the generator (the one `markedPro2_R` delivers). -/
theorem nuDR_sqEquivDRMarked (ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]))
    (hι : ι ztwoOne = ofAdd ((1 : ℤ) : ℤ_[2])) (x : (DSq 0 : Type)) :
    ι (nuDR (sqEquivDRMarked x)) = nuSq 0 x := by
  have hext : (⟨ι.toMulEquiv.toMonoidHom, ι.continuous_toFun⟩ :
      ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp (nuDR.comp sqToDR) = nuSq 0 := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, _⟩ | ⟨j, _⟩
    · show ι (nuDR (sqToDR (dsqSigma 0))) = nuSq 0 (dsqSigma 0)
      rw [sqToDR_sigma, nuDR_drS, hι, nuSq_sigma]
      norm_num
    · show ι (nuDR (sqToDR (dsqX0 0))) = nuSq 0 (dsqX0 0)
      rw [sqToDR_x0, nuDR_drX, map_one, nuSq_x0]
      rfl
    · show ι (nuDR (sqToDR (dsqX1 0))) = nuSq 0 (dsqX1 0)
      rw [sqToDR_x1, nuDR_drY, map_one, nuSq_x1]
      rfl
    · exact absurd j.2 (by omega)
    · exact absurd j.2 (by omega)
  exact DFunLike.congr_fun hext x

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The orientation slot of the rank-three certificate: `χ_R` read on `G_{ℚ₂}(2)` through the
marked identification `e`. -/
noncomputable def sqChiSlot (e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)) :
    maxProPQuotient 2 AbsGalQ2 →* ℤ_[2]ˣ :=
  chiR.toMonoidHom.comp e.toMulEquiv.toMonoidHom

/-- The marking slot of the rank-three certificate: `ν_R` read on `G_{ℚ₂}(2)` through `e`,
normalized by `ι`.  `sqCertificateRankThree_nu_ur` identifies it with the *arithmetic*
unramified character of `R`. -/
noncomputable def sqNuSlot (ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]))
    (e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)) :
    maxProPQuotient 2 AbsGalQ2 →* Multiplicative ℤ_[2] :=
  ι.toMulEquiv.toMonoidHom.comp (nuDR.toMonoidHom.comp e.toMulEquiv.toMonoidHom)

/-- **The rank-three `L_sq` certificate, UNCONDITIONALLY** — SQ3's `marked_square_core_rank3`
in MC5's certificate shape, at the arithmetic slot `G = G_{ℚ₂}(2)`.

Both binders are absent at `h = 0`: there is no handle plane to clear and the marking
correction is already absorbed into `markedPro2_R`'s identification, so the certificate's
`correction` field is the identity.  **Axioms: std-3 + B3c + B8** (through SQ3), census
unchanged at 11. -/
theorem marked_square_core_rank3_certificate (R : LocalReciprocity) :
    ∃ (ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]))
      (e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)),
      Nonempty (MarkedCoreCertificateSq 0 (sqChiSlot e) (sqNuSlot ι e)) := by
  obtain ⟨C⟩ := marked_square_core_rank3 R
  refine ⟨C.iota, C.markedEquiv, ⟨⟨sqEquivDRMarked.trans C.markedEquiv.symm, fun x => ?_,
    ContinuousMulEquiv.refl _, fun _ => rfl, fun x => ?_⟩⟩⟩
  · show chiR (C.markedEquiv (C.markedEquiv.symm (sqEquivDRMarked x))) = chiSq 0 x
    rw [C.markedEquiv.apply_symm_apply, chiR_sqEquivDRMarked]
  · show C.iota (nuDR (C.markedEquiv (C.markedEquiv.symm (sqEquivDRMarked x)))) = nuSq 0 x
    rw [C.markedEquiv.apply_symm_apply, nuDR_sqEquivDRMarked C.iota C.iota_one]

/-- **The rank-three slot's marking IS the arithmetic unramified character**: for the `(ι, e)`
of `marked_square_core_rank3_certificate`, `ν_ur` of the reciprocity data is read on lifts by
the certificate's `nuG` slot.  Without this clause the certificate would be about an invented
marking; with it, it is the packet's.  **Axioms: std-3 + B3c + B8.** -/
theorem marked_square_core_rank3_certificate_nu_ur (R : LocalReciprocity) :
    ∃ (ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]))
      (e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)),
      Nonempty (MarkedCoreCertificateSq 0 (sqChiSlot e) (sqNuSlot ι e)) ∧
        ∀ g : AbsGalQ2, R.nu_ur (toAb g) = sqNuSlot ι e (maxProPMk 2 AbsGalQ2 g) := by
  obtain ⟨C⟩ := marked_square_core_rank3 R
  refine ⟨C.iota, C.markedEquiv, ⟨⟨sqEquivDRMarked.trans C.markedEquiv.symm, fun x => ?_,
    ContinuousMulEquiv.refl _, fun _ => rfl, fun x => ?_⟩⟩, fun g => C.marked_nu g⟩
  · show chiR (C.markedEquiv (C.markedEquiv.symm (sqEquivDRMarked x))) = chiSq 0 x
    rw [C.markedEquiv.apply_symm_apply, chiR_sqEquivDRMarked]
  · show C.iota (nuDR (C.markedEquiv (C.markedEquiv.symm (sqEquivDRMarked x)))) = nuSq 0 x
    rw [C.markedEquiv.apply_symm_apply, nuDR_sqEquivDRMarked C.iota C.iota_one]

end RankThree

/-! ## §6 Stress pins

`h = 0` and `h = 1` per the lane idiom: every pin instantiates a §1–§5 statement at concrete
numerals, so that a later reshaping cannot silently become vacuous. -/

section StressTests

/-- The exponent datum is a theorem, not a binder — MC5's record, inhabited. -/
example : MarkedCore.SqMixPivot := sqMixPivot

/-- The canonical exponent is a unit and solves `X^c = S`. -/
example : IsUnit sqPivotExp ∧
    zpowZtwo isProP_two_unitsPadicInt rootXUnit sqPivotExp = SvalUnit :=
  ⟨isUnit_sqPivotExp, zpowZtwo_rootXUnit_sqPivotExp⟩

/-- The `L_sq` unit row at one handle, at the canonical pivot: exactly `1`. -/
example : nuSq 1 (sqPivot 1) = ofAdd (1 : ℤ_[2]) := nuSq_sqPivot 1

/-- The canonical pivot is χ-trivial where the collector's `σ̄` is χ-obstructed (MC5's SQ1-R1
refutation, one handle). -/
example : chiSq 1 (sqPivot 1) = 1 ∧ chiSq 1 (dsqSigma 1) ≠ 1 :=
  ⟨chiSq_sqPivot 1, chiSq_sigma_ne_one 1⟩

/-- The forced row at one handle: every marking has `ν(x₁) = 2ν(x₀)`. -/
example (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (dsqX1 1)) = 2 * toAdd (nu' (dsqX0 1)) := toAdd_nu_dsqX1 nu'

/-- The pivot functional at one handle: `ν(w) = ν(σ) − c·ν(x₀)`. -/
example (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (c : ℤ_[2]) :
    toAdd (nu' (sqMixPivotElem 1 c)) = toAdd (nu' (dsqSigma 1)) - c * toAdd (nu' (dsqX0 1)) :=
  toAdd_nu_sqMixPivotElem nu' c

/-- The reduction at one handle, written out: two binders, one marked-data clause. -/
example (hMix : SqHandleMixHypothesis 1 sqPivotExp) (hShear : SqCoreShearHypothesis 1 sqPivotExp)
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]))
    (hpiv : nu' (sqPivot 1) = ofAdd (1 : ℤ_[2])) :
    ∃ u : ContinuousMulEquiv (DSq 1 : Type) (DSq 1 : Type),
      (∀ x, chiSq 1 (u x) = chiSq 1 x) ∧ ∀ x, nu' (u x) = nuSq 1 x :=
  sqMarkedMatching_canonical hMix hShear nu' hpiv

/-- The reduction is inhabited by the standard marking at one handle. -/
example (hMix : SqHandleMixHypothesis 1 sqPivotExp)
    (hShear : SqCoreShearHypothesis 1 sqPivotExp) :
    ∃ u : ContinuousMulEquiv (DSq 1 : Type) (DSq 1 : Type),
      (∀ x, chiSq 1 (u x) = chiSq 1 x) ∧ ∀ x, nuSq 1 (u x) = nuSq 1 x :=
  sqMarkedMatching_nuSq hMix hShear

/-- At `h = 0` MC5's handle binder is a theorem, so the certificate's only residual binder there
is the shear — which the standard marking also satisfies. -/
example : SqHandleMixHypothesis 0 sqPivotExp := sqHandleMixHypothesis_zero sqPivotExp

/-- The `h = 0` identification is marked: it carries the three generators across. -/
example : sqEquivDRMarked (dsqSigma 0) = drS ∧ sqEquivDRMarked (dsqX0 0) = drX ∧
    sqEquivDRMarked (dsqX1 0) = drY :=
  ⟨sqToDR_sigma, sqToDR_x0, sqToDR_x1⟩

/-- Stress: SQ2's `dsq_zero` and this file's marked identification are about the same object —
the `L_sq` rank-three core *is* `D_R`. -/
example : DSq 0 = DR := dsq_zero

end StressTests

end SqCore

end Dyadic

end GQ2
