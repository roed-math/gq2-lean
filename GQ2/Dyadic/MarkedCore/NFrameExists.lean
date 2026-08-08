/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.MarkedCore.N
public import GQ2.Dyadic.MarkedCore.MFrameExists
public import GQ2.Reconstruction

@[expose] public section

/-!
# W51-MFRAME2 follow-on: existence of the general-`h` `N`-frame, `Nonempty (NFrame α h)`

**Ticket W51-MFRAME2 (F1).**  `GQ2/Dyadic/MarkedCore/N.lean` §1 builds the general-`h`
`N`-frame `NFrame α h` and everything read off it (`NFrame.toNDecomposition`,
`demushkinQ_DN_nFrame`), and its §1 preamble leaves existence out in the same words the `M`
side used:

> As with MC2's `NDecomposition` (the `h = 0` case), the existence theorem (`phiEquiv` route)
> is *not* in scope: consumers take the frame as a hypothesis.

This file closes that gap, and is the `N` twin of `GQ2/Dyadic/MarkedCore/MFrameExists.lean`.

## The sharp hypothesis is `α ≥ 2`, and both smaller values fail for different reasons

This is the one place where the two cores genuinely part company, and the answer is **not** the
`M`-side answer.  On the `M` side `MFrame α h` is inhabited exactly for `α ≥ 1`.  On the `N`
side the relation vector is `ρ_N = (2 + 2^α)·x̄₀` (`dn_abRel`), and

  `2 + 2^α = 2·(1 + 2^{α−1})`,

so what matters is the 2-adic valuation `v₂(2 + 2^α)`, which is `0`, `2`, `1, 1, 1, …` at
`α = 0, 1, 2, 3, …`.  The factor `1 + 2^{α−1}` is a *unit* of `ℤ₂` only once `α ≥ 2`.  Hence
three regimes, all three settled here:

* **`α = 0`**: `ρ_N = 3·x̄₀` with `3 ∈ ℤ₂ˣ`, so `x̄₀ = 0` in `D_N^{ab}`: the torsion generator is
  **trivial**.  A frame demands `x̄₀ ↦ (1,0,0,0,0) ≠ 1`, so `NFrame 0 h` is empty
  (`nFrameExists_isEmpty_zero`).
* **`α = 1`**: `ρ_N = 4·x̄₀`, valuation **2**.  Now `x̄₀` is not trivial but it is not 2-torsion
  either: it has order `4`.  A frame would force `x̄₀² = 1` (its image squares to
  `(2·1, 0, 0, 0, 0) = 0` in `ℤ/2 ⊕ ℤ₂^{3+2h}` and `e` is injective), and a `ℤ/4`-valued
  coordinate hom refutes that.  So `NFrame 1 h` is empty too
  (`nFrameExists_isEmpty_one`), for a **different** reason.
* **`α ≥ 2`**: `1 + 2^{α−1}` is odd, the unit cancels, `x̄₀² = 1`, and the frame exists
  (`nonempty_nFrame`).

`nFrameExists_nonempty_iff` packages the three: `Nonempty (NFrame α h) ↔ 2 ≤ α`, at every `h`.
This is the machine-checked form of `N.lean`'s standing "everything is uniform in `α ≥ 2`", and
it shows that hypothesis is forced by the frame layer itself rather than inherited from the
shared Gram, which is where the `M` side's `α ≥ 2` comes from.

## The one missing upstream fact, restated privately

The `M` proof finishes by quoting `dm_torsionGen_sq` (`Cores.lean:1813`).  Its `N` analogue
`x̄₀² = 1` is **not in the repo**; `dn_abRel` gives only `x̄₀^{2+2^α} = 1`.  `dnTorsionGen_sq`
below is that lemma, proved here as a **private** restatement via the unit-power cancellation
`zpowZtwo_bijective` (`GQ2/ZtwoPowering.lean:423`).

**Hoist request F1 (still owed, unchanged)**: `dn_torsionGen_sq : (abMk (dnX0 α h))^2 = 1` for
`α ≥ 2` belongs upstream in `Cores.lean` §5 beside `dm_torsionGen_sq` and `dn_abRel`.  Note the
hypothesis is `2 ≤ α`, not the `1 ≤ α` that F1 was provisionally scoped with: `α = 1` is a
genuine counterexample, since `x̄₀` has order 4 there.

**Hoist request H2 (new)**: this file imports `MFrameExists.lean` only for helpers that are
*generic* despite their `m`-prefix, namely `mHandleIdx`, `mHandleMark`, `coreMark_apply`,
`mCoreVal_ne_*`, `mIdx_cases`, `mProd_single`/`mProd_pair` and the two `toAdd` helpers.  None
of them mentions `D_M`.  They should move to a core-neutral home and lose the `m`; until then
an `N`-side file importing an `M`-side one is the lesser evil against duplicating 125 lines of
verified code.

## Contents

* **§1** Local instance restatements and `nIsProP_two_topAb_DN`.
* **§2** The torsion generator at all three regimes: the private `dnTorsionGen_sq` (`α ≥ 2`),
  `dnX0_eq_one_zero` (`α = 0`) and `dnX0_sq_ne_one_one` (`α = 1`).
* **§3** The coordinate homs through one builder `nCoordHom`, whose relator obligation is the
  abelian collapse `m 0 ^ (2 + 2^α) = 1`: `nTHom`, `nBHom`, `nCHom`, `nDHom`, `nHHom k`.
* **§4** Coordinate surjectivity `nDNab_coord`.
* **§5** The five word-evaluation formulas.
* **§6** The combined hom `nPhiHom`, injectivity, surjectivity, generator values.
* **§7** `nFrameExists_phiEquiv`, `nonempty_nFrame`, the two emptiness theorems and the sharp
  `nFrameExists_nonempty_iff`, plus the unlocks `nFrameExists_nDecomposition` and
  `nFrameExists_demushkinQ_DN`.
* **§8** Axiom pins.

## Why the `N` side is shorter than the `M` side

Two structural simplifications, both consequences of "no forced row" (memo V1/§7.1(2)).  First,
every one of the five markings is supported at a **single** generator slot, so `mProd_pair` is
never needed and all five word formulas go through `mProd_single`; the `M` side needed a pair
for `C̄₀` because the `Ā`-row is forced.  Second, `nSurjVec` needs no compensation term: the
`M` side's `C̄₀`-exponent had to absorb `+2^{α−1}·a` to cancel the forced `Ā`-row, and here the
four core exponents are simply the four target coordinates.

## Variance (MC-VAR discipline)

As in `MFrameExists.lean`, and for the same reason: the proof stays entirely in the
**abelianization layer**.  No cup form, no Gram matrix, no bilinear pairing occurs in any
statement or proof here, so the `M`/`N` row-vs-column dictionary
(`GQ2/Dyadic/MarkedCore/Variance.lean`) is **not** invoked and no transposition arises.  The
`Finset.prod` over `Fin (coreRank h)` in §4 is a product in an abelian group, not a matrix
product.  The dictionary re-enters only downstream, where a consumer feeds
`NFrame.toNDecomposition` to `nMatOf`, in the `N` variance, unchanged.

## Axiom scope (measured)

**Every declaration in this file prints at most `[propext, Classical.choice, Quot.sound]`**; see
§8.  No census axiom, and none of the cited inputs contributes one.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §1 The `topAbelianization` instances, and pro-2-ness of `D_N^{ab}`

Restated `local` exactly as in `MFrameExists.lean` §1 (they are file-scoped there, so importing
that file does not bring them along).  Hoist request **H1** stands and now covers five copies. -/

/-- `G^{ab}` is commutative (local restatement). -/
noncomputable local instance instCommGroupTopAbNFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

/-- `G^{ab}` is compact (local restatement). -/
local instance instCompactSpaceTopAbNFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

/-- `G^{ab}` is Hausdorff (local restatement). -/
local instance instT2SpaceTopAbNFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

/-- `G^{ab}` is totally disconnected (local restatement). -/
local instance instTotDiscTopAbNFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

/-- **`D_N^{ab}` is pro-2**, the image of the pro-2 group `D_N` under `abMk`; the `N` twin of
`mIsProP_two_topAb_DM`.  It is what licenses `ℤ₂`-powering inside `D_N^{ab}`, and in particular
the unit cancellation of §2. -/
theorem nIsProP_two_topAb_DN (α h : ℕ) : IsProP 2 (topAbelianization (DN α h : Type)) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective (isProP_DN α h)

/-! ## §2 The torsion generator `x̄₀`, in all three regimes

`dn_abRel` says `x̄₀^{2+2^α} = 1` and nothing more.  What that buys depends entirely on
`v₂(2 + 2^α)`, and the three cases below are the three values it takes. -/

/-- **The missing upstream fact** (hoist request F1), restated privately: for `α ≥ 2` the marked
torsion generator `x̄₀` is 2-torsion.  Proof: `2 + 2^α = 2·(1 + 2^{α−1})` with `1 + 2^{α−1}`
**odd** once `α ≥ 2`, so `(x̄₀²)^{1+2^{α−1}} = 1 = 1^{1+2^{α−1}}`, and raising to an odd
`ℤ₂`-exponent is injective on a pro-2 group (`zpowZtwo_bijective`).

This is the `N` analogue of `dm_torsionGen_sq` (`Cores.lean:1813`), and the hypothesis really is
`2 ≤ α`: at `α = 1` the statement is **false** (`dnX0_sq_ne_one_one`). -/
private theorem dnTorsionGen_sq {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    (abMk (dnX0 α h)) ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
  obtain ⟨u, hu⟩ := isUnit_intCast_of_odd (m := 1 + 2 * 2 ^ k) ⟨2 ^ k, by ring⟩
  refine (zpowZtwo_bijective (nIsProP_two_topAb_DN (k + 2) h) u).injective ?_
  show zpowZtwo (nIsProP_two_topAb_DN (k + 2) h) ((abMk (dnX0 (k + 2) h)) ^ 2) ((u : ℤ_[2]))
    = zpowZtwo (nIsProP_two_topAb_DN (k + 2) h) 1 ((u : ℤ_[2]))
  rw [zpowZtwo_one_base, hu, zpowZtwo_intCast,
    ← zpow_natCast (abMk (dnX0 (k + 2) h)) 2, ← zpow_mul,
    show ((2 : ℕ) : ℤ) * (1 + 2 * 2 ^ k) = ((2 + 2 ^ (k + 2) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, dn_abRel]

/-- **The `α = 0` obstruction**: the relation vector is `3·x̄₀` and `3` is a unit of `ℤ₂`, so
`x̄₀` is **trivial** in `D_N^{ab}` (not merely torsion).  Contrast the `M` side, where `α = 0`
fails because the forced `Ā`-row reads `−1 = 0`; here the model is fine and it is the torsion
generator that collapses. -/
private theorem dnX0_eq_one_zero (h : ℕ) : abMk (dnX0 0 h) = 1 := by
  obtain ⟨u, hu⟩ := isUnit_intCast_of_odd (m := 3) ⟨1, by ring⟩
  refine (zpowZtwo_bijective (nIsProP_two_topAb_DN 0 h) u).injective ?_
  show zpowZtwo (nIsProP_two_topAb_DN 0 h) (abMk (dnX0 0 h)) ((u : ℤ_[2]))
    = zpowZtwo (nIsProP_two_topAb_DN 0 h) 1 ((u : ℤ_[2]))
  rw [zpowZtwo_one_base, hu, zpowZtwo_intCast,
    show ((3 : ℤ)) = ((2 + 2 ^ 0 : ℕ) : ℤ) by norm_num, zpow_natCast, dn_abRel]

/-- `Multiplicative (ZMod 4)` is pro-2 (a finite 2-group of order 4), the target that detects
the `α = 1` obstruction.  The `isProP_two_multZMod2` argument at `n = 2`. -/
private theorem nIsProP_two_multZMod4 : IsProP 2 (Multiplicative (ZMod 4)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 2)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- The `ℤ/4`-valued coordinate hom at `α = 1`, with `x̄₀ ↦ 1` and every other generator `↦ 0`.
Its relator check is `4·1 = 0` in `ℤ/4`, which is exactly why it exists only here: at `α ≥ 2`
the relator would read `(2 + 2^α)·1 ≠ 0` in `ℤ/4`. -/
private noncomputable def nZ4Hom (h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN 1 h : Type)) (Multiplicative (ZMod 4)) :=
  abLiftG (nLiftHom 1 h nIsProP_two_multZMod4 (coreMark (ofAdd (1 : ZMod 4)) 1 1 1) (by
    rw [nRelWord_comm, coreMark_zero, ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1))

/-- **The `α = 1` obstruction**: the relation vector is `4·x̄₀`, of valuation `2`, so `x̄₀` has
order `4` and is **not** 2-torsion.  Witnessed by `nZ4Hom`, which sends `x̄₀²` to
`2 ≠ 0` in `ℤ/4`.  This is the case that makes the sharp `N`-side hypothesis `α ≥ 2` rather
than the `M`-side's `α ≥ 1`. -/
private theorem dnX0_sq_ne_one_one (h : ℕ) : (abMk (dnX0 1 h)) ^ 2 ≠ 1 := by
  intro hc
  have himg : nZ4Hom h ((abMk (dnX0 1 h)) ^ 2) = ofAdd (2 : ZMod 4) := by
    rw [map_pow, nZ4Hom, abLiftG_abMk, dnX0, nLiftHom_gen, coreMark_zero, ← ofAdd_nsmul]
    congr 1
  rw [hc, map_one] at himg
  exact absurd himg.symm (by decide)

/-! ## §3 The coordinate homs

One builder, as on the `M` side, but the relator obligation is now `m 0 ^ (2 + 2^α) = 1`
(`nRelWord_comm`): it constrains **only** the `x̄₀`-value.  Since `x̄₀` is the torsion slot and
the other four coordinates put `0` there, four of the five families discharge it by `1^n = 1`,
and only `nTHom` has anything to check. -/

section CoordHoms

variable {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **The `N`-side coordinate hom builder**: a marking of a commutative pro-2 group whose
`x̄₀`-value kills the relation vector `(2 + 2^α)·x̄₀` classifies a continuous hom
`D_N^{ab} → H`, by `nLiftHom` then `abLiftG`.  The `N` twin of `mCoordHom`. -/
noncomputable def nCoordHom (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : m 0 ^ (2 + 2 ^ α) = 1) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) H :=
  abLiftG (nLiftHom α h hH m (by rw [nRelWord_comm]; exact hrel))

@[simp] theorem nCoordHom_gen (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : m 0 ^ (2 + 2 ^ α) = 1) (i : Fin (coreRank h)) :
    nCoordHom α h hH m hrel (abMk (dnGen α h i)) = m i := by
  rw [nCoordHom, abLiftG_abMk, nLiftHom_gen]

end CoordHoms

/-- **The torsion coordinate** `x̄₀ ↦ 1` into `ZMod 2`, everything else `↦ 0`.  Its relator
check is `(2 + 2^α)·1 = 0` in `ℤ/2`, i.e. `2 + 2^α` **even**, i.e. `α ≥ 1`.

So the hypothesis here is `1 ≤ α`, weaker than the file's `2 ≤ α`, and the gap is exactly the
`α = 1` regime: at `α = 1` this hom exists perfectly well, which is why `α = 1` cannot be
refuted the way `α = 0` is.  What fails at `α = 1` is not the existence of a `ℤ/2`-valued
torsion coordinate but its **injectivity** on the torsion, and that is what `nZ4Hom` detects.
At `α = 0` the check fails outright: `2 + 1 = 3` is odd. -/
noncomputable def nTHom {α : ℕ} (hα : 1 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) (Multiplicative (ZMod 2)) :=
  nCoordHom α h isProP_two_multZMod2 (coreMark (ofAdd (1 : ZMod 2)) 1 1 1) (by
    obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
    rw [coreMark_zero, ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    show ((2 + 2 ^ (k + 1)) : ℕ) • (1 : ZMod 2) = 0
    rw [show (2 + 2 ^ (k + 1)) = (1 + 2 ^ k) * 2 by ring, mul_smul,
      show (2 : ℕ) • (1 : ZMod 2) = 0 from by decide, smul_zero])

/-- `x̄₁ ↦ 1`, everything else `↦ 0`.  Relator check: `0^{2+2^α} = 0`, at every `α`. -/
noncomputable def nBHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) (Multiplicative ℤ_[2]) :=
  nCoordHom α h PropOneOne.isProP_two_multPadicInt (coreMark 1 (ofAdd (1 : ℤ_[2])) 1 1) (by
    rw [coreMark_zero, one_pow])

/-- `σ̄ ↦ 1`, everything else `↦ 0`. -/
noncomputable def nCHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) (Multiplicative ℤ_[2]) :=
  nCoordHom α h PropOneOne.isProP_two_multPadicInt (coreMark 1 1 (ofAdd (1 : ℤ_[2])) 1) (by
    rw [coreMark_zero, one_pow])

/-- `x̄₂ ↦ 1`, everything else `↦ 0`. -/
noncomputable def nDHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) (Multiplicative ℤ_[2]) :=
  nCoordHom α h PropOneOne.isProP_two_multPadicInt (coreMark 1 1 1 (ofAdd (1 : ℤ_[2]))) (by
    rw [coreMark_zero, one_pow])

/-- The `2h` handle coordinates.  As on the `M` side the relator check is vacuous
(`mHandleMark_core`), so these exist at every `α` and every `h`: handles never interact with the
relation vector. -/
noncomputable def nHHom (α : ℕ) {h : ℕ} (k : Fin (2 * h)) :
    ContinuousMonoidHom (topAbelianization (DN α h : Type)) (Multiplicative ℤ_[2]) :=
  nCoordHom α h PropOneOne.isProP_two_multPadicInt (mHandleMark k (ofAdd (1 : ℤ_[2]))) (by
    rw [mHandleMark_core k _ (by rw [coreVal_zero]; omega), one_pow])

/-! ## §4 Coordinate surjectivity of `D_N^{ab}`

Verbatim the `M` argument with `dn_topGen` in place of `dm_topGen`. -/

section Coord

variable (α h : ℕ)

/-- The `ℤ₂`-power word `∏ᵢ ḡᵢ^{cᵢ}` in the marked generators of `D_N^{ab}`. -/
noncomputable def nAbWord (c : Fin (coreRank h) → ℤ_[2]) : topAbelianization (DN α h : Type) :=
  ∏ i, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) (c i)

/-- `nAbWord` as a monoid hom out of `ℤ₂^{4+2h}`. -/
noncomputable def nAbWordHom :
    Multiplicative (Fin (coreRank h) → ℤ_[2]) →* topAbelianization (DN α h : Type) where
  toFun c := nAbWord α h c.toAdd
  map_one' := by
    refine Finset.prod_eq_one fun i _ => ?_
    show zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) 0 = 1
    exact zpowZtwo_zero _ _
  map_mul' c d := by
    show ∏ i, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) (c.toAdd i + d.toAdd i)
      = (∏ i, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) (c.toAdd i))
        * ∏ i, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) (d.toAdd i)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => zpowZtwo_add _ _ _ _

theorem continuous_nAbWordHom : Continuous (nAbWordHom α h) := by
  show Continuous fun c : Multiplicative (Fin (coreRank h) → ℤ_[2]) =>
    ∏ i, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h i)) (c.toAdd i)
  exact continuous_finsetProd _ fun i _ =>
    (continuous_zpowZtwo _ _).comp ((continuous_apply i).comp continuous_toAdd)

theorem nAbWordHom_single (i : Fin (coreRank h)) :
    nAbWordHom α h (ofAdd (Pi.single i (1 : ℤ_[2]))) = abMk (dnGen α h i) := by
  show ∏ j, zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h j))
    ((Pi.single i (1 : ℤ_[2]) : Fin (coreRank h) → ℤ_[2]) j) = _
  rw [Finset.prod_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, zpowZtwo_zero]) (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [Pi.single_eq_same, zpowZtwo_one_exp]

/-- **Coordinate surjectivity of `D_N^{ab}`**: every element is a `ℤ₂`-power word
`x̄₀^{c₀}·x̄₁^{c₁}·σ̄^{c₂}·x̄₂^{c₃}·∏ⱼ …` in the marked generators.  The `N` twin of
`mDMab_coord`. -/
theorem nDNab_coord (z : topAbelianization (DN α h : Type)) :
    ∃ c : Fin (coreRank h) → ℤ_[2], z = nAbWord α h c := by
  have hgen : (Subgroup.closure (⇑abMk '' Set.range (dnGen α h))).topologicalClosure = ⊤ := by
    have := abMk_surjective.denseRange.topologicalClosure_map_subgroup
      (continuous_abMk (G := (DN α h : Type))) (dn_topGen α h)
    rwa [MonoidHom.map_closure] at this
  have hclosed : IsClosed ((nAbWordHom α h).range : Set (topAbelianization (DN α h : Type))) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_nAbWordHom α h)).isClosed
  have hsub : Subgroup.closure (⇑abMk '' Set.range (dnGen α h)) ≤ (nAbWordHom α h).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨ofAdd (Pi.single i 1), nAbWordHom_single α h i⟩
  have htop : (nAbWordHom α h).range = ⊤ :=
    eq_top_iff.mpr (hgen ▸ Subgroup.topologicalClosure_minimal _ hsub hclosed)
  have hz : z ∈ (nAbWordHom α h).range := by rw [htop]; exact Subgroup.mem_top z
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hz
  exact ⟨p.toAdd, hp.symm⟩

end Coord

/-! ## §5 Reading a coordinate hom off a word

Every `N`-side marking is supported at a **single** slot (no forced row), so all five formulas
go through `mProd_single` and `mProd_pair` is never needed.  This is the first of the two places
the `N` proof is shorter than the `M` proof. -/

section Words

variable (α h : ℕ) (c : Fin (coreRank h) → ℤ_[2])

/-- A coordinate hom on a `ℤ₂`-power word: apply the marking slotwise. -/
theorem nCoordHom_word {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] (hH : IsProP 2 H)
    (m : Fin (coreRank h) → H) (hrel : m 0 ^ (2 + 2 ^ α) = 1) :
    nCoordHom α h hH m hrel (nAbWord α h c) = ∏ i, zpowZtwo hH (m i) (c i) := by
  rw [nAbWord, map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [map_zpowZtwo (nIsProP_two_topAb_DN α h) hH, nCoordHom_gen]

/-- The `x̄₁`-coordinate of a word is its `x̄₁`-exponent. -/
theorem nBHom_word : nBHom α h (nAbWord α h c) = ofAdd (c 1) := by
  rw [nBHom, nCoordHom_word, mProd_single _ _ _ 1 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_one hi
    split_ifs <;> rfl), coreMark_one, zpowZtwo_ofAdd, one_mul]

/-- The `σ̄`-coordinate of a word is its `σ̄`-exponent. -/
theorem nCHom_word : nCHom α h (nAbWord α h c) = ofAdd (c 2) := by
  rw [nCHom, nCoordHom_word, mProd_single _ _ _ 2 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_two hi
    split_ifs <;> rfl), coreMark_two, zpowZtwo_ofAdd, one_mul]

/-- The `x̄₂`-coordinate of a word is its `x̄₂`-exponent. -/
theorem nDHom_word : nDHom α h (nAbWord α h c) = ofAdd (c 3) := by
  rw [nDHom, nCoordHom_word, mProd_single _ _ _ 3 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_three hi
    split_ifs <;> rfl), coreMark_three, zpowZtwo_ofAdd, one_mul]

/-- The `k`-th handle coordinate of a word is its `k`-th handle exponent. -/
theorem nHHom_word {h : ℕ} (α : ℕ) (c : Fin (coreRank h) → ℤ_[2]) (k : Fin (2 * h)) :
    nHHom α k (nAbWord α h c) = ofAdd (c (mHandleIdx k)) := by
  rw [nHHom, nCoordHom_word,
    mProd_single _ _ _ (mHandleIdx k) (fun i hi => mHandleMark_of_ne k _ hi),
    mHandleMark_self, zpowZtwo_ofAdd, one_mul]

/-- The torsion coordinate of a word: only the `x̄₀`-exponent contributes, through `ZMod 2`.
Unlike the `M` side there is no second slot: the torsion generator is a marked generator. -/
theorem nTHom_word {α : ℕ} (hα : 1 ≤ α) (h : ℕ) (c : Fin (coreRank h) → ℤ_[2]) :
    nTHom hα h (nAbWord α h c)
      = zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (c 0) := by
  rw [nTHom, nCoordHom_word, mProd_single _ _ _ 0 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_zero hi
    split_ifs <;> first | rfl | omega), coreMark_zero]

end Words

/-! ## §6 The combined coordinate hom `φ_N`, and its bijectivity -/

section Phi

variable {α : ℕ} (hα : 2 ≤ α) (h : ℕ)

/-- **The combined coordinate hom** `φ_N : D_N^{ab} → ℤ/2 ⊕ ℤ₂³ ⊕ ℤ₂^{2h}`, the `N` twin of
`mPhiHom`.  It is stated with the file's `2 ≤ α` even though its torsion component needs only
`1 ≤ α`: the extra strength is what makes it *injective*, not what makes it exist. -/
noncomputable def nPhiHom : topAbelianization (DN α h : Type) →* NFrameModel h where
  toFun z := ofAdd ((nTHom (by omega : 1 ≤ α) h z).toAdd, (nBHom α h z).toAdd,
    (nCHom α h z).toAdd, (nDHom α h z).toAdd, fun k => (nHHom α k z).toAdd)
  map_one' := by
    simp only [map_one, toAdd_one]
    rfl
  map_mul' x y := by
    simp only [map_mul, toAdd_mul]
    rw [← ofAdd_add]
    rfl

theorem continuous_nPhiHom : Continuous (nPhiHom hα h) := by
  show Continuous fun z => ofAdd ((nTHom (by omega : 1 ≤ α) h z).toAdd, (nBHom α h z).toAdd,
    (nCHom α h z).toAdd, (nDHom α h z).toAdd, fun k => (nHHom α k z).toAdd)
  exact continuous_ofAdd.comp
    ((continuous_toAdd.comp (nTHom (by omega : 1 ≤ α) h).continuous_toFun).prodMk
      ((continuous_toAdd.comp (nBHom α h).continuous_toFun).prodMk
        ((continuous_toAdd.comp (nCHom α h).continuous_toFun).prodMk
          ((continuous_toAdd.comp (nDHom α h).continuous_toFun).prodMk
            (continuous_pi fun k => continuous_toAdd.comp (nHHom α k).continuous_toFun)))))

/-- `φ_N` on a `ℤ₂`-power word, all five coordinates at once.  Compare `mPhiHom_word`: the
`M`-side third slot reads `−2^{α−1}c₀ + c₂`, here it is simply `c₂`. -/
theorem nPhiHom_word (c : Fin (coreRank h) → ℤ_[2]) :
    nPhiHom hα h (nAbWord α h c)
      = ofAdd ((zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (c 0)).toAdd, c 1, c 2, c 3,
          fun k => c (mHandleIdx k)) := by
  show ofAdd (_, _, _, _, _) = _
  rw [nTHom_word, nBHom_word, nCHom_word, nDHom_word]
  simp only [toAdd_ofAdd]
  congr 1
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _
    (funext fun k => by rw [nHHom_word, toAdd_ofAdd]))))

/-! ### §6.1 Injectivity

Simpler than the `M` case: with no forced row, killing the four non-torsion coordinates leaves
a word supported at the single slot `x̄₀`, and `dnTorsionGen_sq` finishes it. -/

/-- A word whose exponents vanish off the `x̄₀`-slot is that single factor. -/
theorem nAbWord_single (α h : ℕ) (c : Fin (coreRank h) → ℤ_[2])
    (hc : ∀ i, i ≠ 0 → c i = 0) :
    nAbWord α h c = zpowZtwo (nIsProP_two_topAb_DN α h) (abMk (dnGen α h 0)) (c 0) :=
  Finset.prod_eq_single 0 (fun j _ hj => by rw [hc j hj, zpowZtwo_zero])
    (fun hi => absurd (Finset.mem_univ (0 : Fin (coreRank h))) hi)

theorem nPhiHom_injective : Function.Injective (nPhiHom hα h) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨c, rfl⟩ := nDNab_coord α h z
  rw [nPhiHom_word] at hz
  have hv := Multiplicative.ofAdd.injective (hz.trans
    (show (1 : NFrameModel h) = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2])) from rfl))
  rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hv
  obtain ⟨hvt, hv1, hv2, hv3, hvh⟩ := hv
  -- every exponent off the torsion slot vanishes
  have hc0 : ∀ i, i ≠ 0 → c i = 0 := by
    intro i hi0
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · exact absurd rfl hi0
    · exact hv1
    · exact hv2
    · exact hv3
    · exact congrFun hvh k
  -- the torsion coordinate says the surviving exponent is even, and `x̄₀² = 1`
  have hval0 : (PadicInt.toZModPow 1 (c 0)).val = 0 := by
    rw [zpowZtwo_of_sq_eq_one isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (by decide) (c 0)] at hvt
    have hlt : (PadicInt.toZModPow (p := 2) 1 (c 0)).val < 2 := by
      have := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 (c 0)); simpa using this
    rcases (by omega : (PadicInt.toZModPow 1 (c 0)).val = 0
        ∨ (PadicInt.toZModPow 1 (c 0)).val = 1) with h0 | h1
    · exact h0
    · rw [h1, pow_one, toAdd_ofAdd] at hvt
      exact absurd hvt (by decide)
  rw [nAbWord_single α h c hc0, ← dnX0,
    zpowZtwo_of_sq_eq_one (nIsProP_two_topAb_DN α h) _ (dnTorsionGen_sq hα h) (c 0),
    hval0, pow_zero]

/-! ### §6.2 Surjectivity

Also simpler: with no forced row to compensate for, the four core exponents *are* the four
target coordinates. -/

/-- The exponent vector realizing a prescribed coordinate tuple.  Note the absence of any
α-dependence, in contrast with `mSurjVec`. -/
noncomputable def nSurjVec {h : ℕ} (a : ZMod 2) (b cc d : ℤ_[2])
    (f : Fin (2 * h) → ℤ_[2]) : Fin (coreRank h) → ℤ_[2] := fun i =>
  if (i : ℕ) = 0 then ((a.val : ℤ_[2])) else
  if (i : ℕ) = 1 then b else
  if (i : ℕ) = 2 then cc else
  if (i : ℕ) = 3 then d else
  if hk : (i : ℕ) - 4 < 2 * h then f ⟨(i : ℕ) - 4, hk⟩ else 0

section SurjVec

variable {h : ℕ} (a : ZMod 2) (b cc d : ℤ_[2]) (f : Fin (2 * h) → ℤ_[2])

@[simp] theorem nSurjVec_zero : nSurjVec a b cc d f 0 = ((a.val : ℤ_[2])) := by
  rw [nSurjVec, if_pos (coreVal_zero h)]

@[simp] theorem nSurjVec_one : nSurjVec a b cc d f 1 = b := by
  rw [nSurjVec, if_neg (by rw [coreVal_one]; omega), if_pos (coreVal_one h)]

@[simp] theorem nSurjVec_two : nSurjVec a b cc d f 2 = cc := by
  rw [nSurjVec, if_neg (by rw [coreVal_two]; omega), if_neg (by rw [coreVal_two]; omega),
    if_pos (coreVal_two h)]

@[simp] theorem nSurjVec_three : nSurjVec a b cc d f 3 = d := by
  rw [nSurjVec, if_neg (by rw [coreVal_three]; omega), if_neg (by rw [coreVal_three]; omega),
    if_neg (by rw [coreVal_three]; omega), if_pos (coreVal_three h)]

@[simp] theorem nSurjVec_handle (k : Fin (2 * h)) :
    nSurjVec a b cc d f (mHandleIdx k) = f k := by
  rw [nSurjVec, if_neg (by rw [mHandleIdx_val]; omega), if_neg (by rw [mHandleIdx_val]; omega),
    if_neg (by rw [mHandleIdx_val]; omega), if_neg (by rw [mHandleIdx_val]; omega),
    dif_pos (by rw [mHandleIdx_val]; have := k.isLt; omega)]
  exact congrArg f (Fin.ext (by simp only [mHandleIdx_val]; omega))

end SurjVec

theorem nPhiHom_surjective : Function.Surjective (nPhiHom hα h) := by
  intro w
  rw [← ofAdd_toAdd w]
  obtain ⟨a, b, cc, d, f⟩ := w.toAdd
  refine ⟨nAbWord α h (nSurjVec a b cc d f), ?_⟩
  rw [nPhiHom_word, nSurjVec_zero, nSurjVec_one, nSurjVec_two, nSurjVec_three]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))))
  · show (zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) ((a.val : ℤ_[2]))).toAdd = a
    rw [zpowZtwo_ofAdd_one_zmod2, toAdd_ofAdd]
  · exact nSurjVec_handle a b cc d f k

/-! ### §6.3 `φ_N` on the marked generators

These six values are the six fields of `NFrame`.  All four core rows are standard basis
vectors: there is no forced row to reconcile, which is the `N`-side structural fact
(memo V1/§7.1(2)) showing up as the absence of an `mE_A_frame` analogue. -/

/-- `Cores.lean`'s `u_j`-index is `N.lean`'s `nHandleCoordU j`-th handle coordinate. -/
theorem nHandleIdx_coordU {h : ℕ} (j : Fin h) :
    mHandleIdx (nHandleCoordU j) = handleIdxU j :=
  Fin.ext (by rw [mHandleIdx_val, handleIdxU_val]; rfl)

/-- `Cores.lean`'s `v_j`-index is `N.lean`'s `nHandleCoordV j`-th handle coordinate. -/
theorem nHandleIdx_coordV {h : ℕ} (j : Fin h) :
    mHandleIdx (nHandleCoordV j) = handleIdxV j :=
  Fin.ext (by
    rw [mHandleIdx_val, handleIdxV_val]
    show 4 + (2 * (j : ℕ) + 1) = 5 + 2 * (j : ℕ)
    omega)

/-- `φ_N` at a marked generator: each slot reads its own marking. -/
theorem nPhiHom_gen (i : Fin (coreRank h)) :
    nPhiHom hα h (abMk (dnGen α h i))
      = ofAdd ((coreMark (ofAdd (1 : ZMod 2)) 1 1 1 i).toAdd,
          (coreMark 1 (ofAdd (1 : ℤ_[2])) 1 1 i).toAdd,
          (coreMark 1 1 (ofAdd (1 : ℤ_[2])) 1 i).toAdd,
          (coreMark 1 1 1 (ofAdd (1 : ℤ_[2])) i).toAdd,
          fun k => (mHandleMark k (ofAdd (1 : ℤ_[2])) i).toAdd) := by
  show ofAdd (_, _, _, _, _) = _
  rw [nTHom, nBHom, nCHom, nDHom, nCoordHom_gen, nCoordHom_gen, nCoordHom_gen, nCoordHom_gen]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _
    (funext fun k => by rw [nHHom, nCoordHom_gen])))))

/-- The torsion coordinate is the **marked** generator: `x̄₀ ↦ (1, 0, 0, 0, 0)`.  No forced row
has to be reconciled, unlike `mPhiHom_t`. -/
theorem nPhiHom_X0 : nPhiHom hα h (abMk (dnX0 α h)) = ofAdd (1, 0, 0, 0, 0) := by
  rw [dnX0, nPhiHom_gen]
  simp only [coreMark_zero, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (0 : Fin (coreRank h)) (by rw [coreVal_zero]; omega)]
  rfl

theorem nPhiHom_X1 : nPhiHom hα h (abMk (dnX1 α h)) = ofAdd (0, 1, 0, 0, 0) := by
  rw [dnX1, nPhiHom_gen]
  simp only [coreMark_one, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (1 : Fin (coreRank h)) (by rw [coreVal_one]; omega)]
  rfl

theorem nPhiHom_Sigma : nPhiHom hα h (abMk (dnSigma α h)) = ofAdd (0, 0, 1, 0, 0) := by
  rw [dnSigma, nPhiHom_gen]
  simp only [coreMark_two, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (2 : Fin (coreRank h)) (by rw [coreVal_two]; omega)]
  rfl

theorem nPhiHom_X2 : nPhiHom hα h (abMk (dnX2 α h)) = ofAdd (0, 0, 0, 1, 0) := by
  rw [dnX2, nPhiHom_gen]
  simp only [coreMark_three, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (3 : Fin (coreRank h)) (by rw [coreVal_three]; omega)]
  rfl

/-- `ū_j ↦` the `2j`-th handle coordinate. -/
theorem nPhiHom_U {h : ℕ} (j : Fin h) :
    nPhiHom hα h (abMk (dnGen α h (handleIdxU j)))
      = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordU j) 1) := by
  rw [← nHandleIdx_coordU j, nPhiHom_gen]
  simp only [coreMark_mHandleIdx, toAdd_one, mHandleMark_toAdd_single]

/-- `v̄_j ↦` the `(2j+1)`-st handle coordinate. -/
theorem nPhiHom_V {h : ℕ} (j : Fin h) :
    nPhiHom hα h (abMk (dnGen α h (handleIdxV j)))
      = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordV j) 1) := by
  rw [← nHandleIdx_coordV j, nPhiHom_gen]
  simp only [coreMark_mHandleIdx, toAdd_one, mHandleMark_toAdd_single]

end Phi

/-! ## §7 The deliverable, the sharp `α`-boundary, and the unlocks -/

/-- **The coordinate isomorphism** `φ_N : D_N^{ab} ≃ₜ* ℤ/2 × ℤ₂³ × ℤ₂^{2h}`, the `N` twin of
`mFrameExists_phiEquiv`. -/
noncomputable def nFrameExists_phiEquiv {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ContinuousMulEquiv (topAbelianization (DN α h : Type)) (NFrameModel h) :=
  continuousMulEquivOfBijective ⟨nPhiHom hα h, continuous_nPhiHom hα h⟩
    ⟨nPhiHom_injective hα h, nPhiHom_surjective hα h⟩

@[simp] theorem nFrameExists_phiEquiv_apply {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (z : topAbelianization (DN α h : Type)) :
    nFrameExists_phiEquiv hα h z = nPhiHom hα h z := rfl

/-- **Existence of the general-`h` `N`-frame** (ticket W51-MFRAME2 follow-up F1; the gap
`N.lean` §1's preamble leaves open).  For every `α ≥ 2` and every handle count `h`,
`NFrame α h` is inhabited.

The hypothesis is `2 ≤ α`, **not** the `1 ≤ α` of the `M` side, and it is sharp:
`nFrameExists_isEmpty_zero` and `nFrameExists_isEmpty_one` rule out the two smaller values, by
two different mechanisms.  See `nFrameExists_nonempty_iff`. -/
theorem nonempty_nFrame {α : ℕ} (hα : 2 ≤ α) (h : ℕ) : Nonempty (NFrame α h) :=
  ⟨{ e := nFrameExists_phiEquiv hα h
     map_t := nPhiHom_X0 hα h
     map_B := nPhiHom_X1 hα h
     map_C := nPhiHom_Sigma hα h
     map_D := nPhiHom_X2 hα h
     map_U := fun j => nPhiHom_U hα j
     map_V := fun j => nPhiHom_V hα j }⟩

/-- **`α = 0` is out of range**: the relation vector is `3·x̄₀` with `3 ∈ ℤ₂ˣ`, so `x̄₀ = 1` in
`D_N^{ab}` (`dnX0_eq_one_zero`), while a frame demands `x̄₀ ↦ (1,0,0,0,0) ≠ 1`.  The `N` analogue
of `mFrame_isEmpty_zero`, though the mechanism differs: on the `M` side the model equation
`−1 = 0` fails, here the torsion generator itself collapses. -/
theorem nFrameExists_isEmpty_zero (h : ℕ) : IsEmpty (NFrame 0 h) := by
  refine ⟨fun F => ?_⟩
  have h1 : (ofAdd (1, 0, 0, 0, 0) : NFrameModel h) = 1 := by
    rw [← F.map_t, dnX0_eq_one_zero, map_one]
  have h2 := congrArg (fun z : NFrameModel h => (toAdd z).1) h1
  simp only [toAdd_ofAdd, toAdd_one, Prod.fst_zero] at h2
  exact absurd h2 (by decide)

/-- **`α = 1` is out of range too**, and this has no `M`-side counterpart: the relation vector
is `4·x̄₀`, of 2-adic valuation `2`, so `x̄₀` has order `4`.  A frame would force `x̄₀² = 1`
(its image squares to `0` in `ℤ/2 ⊕ ℤ₂^{3+2h}` and `e` is injective), which
`dnX0_sq_ne_one_one` refutes.

Note what this does *not* claim: the `q`-invariant of `D_N` at `α = 1` is not computed here.
What is proved is that the rank-`(4+2h)` frame with a `ℤ/2` torsion slot cannot exist there, so
`demushkinQ_DN_nFrame` is simply unavailable at `α = 1`. -/
theorem nFrameExists_isEmpty_one (h : ℕ) : IsEmpty (NFrame 1 h) := by
  refine ⟨fun F => ?_⟩
  refine dnX0_sq_ne_one_one h (F.e.toMulEquiv.injective ?_)
  show F.e ((abMk (dnX0 1 h)) ^ 2) = F.e 1
  rw [map_pow, F.map_t, map_one, ← ofAdd_nsmul, ← ofAdd_zero]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · show (2 : ℕ) • (1 : ZMod 2) = 0
    decide
  all_goals simp

/-- **The sharp boundary**: `NFrame α h` is inhabited **iff** `α ≥ 2`, at every handle count.
The `N`-side twin of the pair `nonempty_mFrame`/`mFrame_isEmpty_zero`, with one more excluded
value.

This is the machine-checked source of `N.lean`'s standing "everything is uniform in `α ≥ 2`":
on the `N` side that hypothesis is forced by the **frame layer itself**, whereas on the `M` side
the frame layer allows `α = 1` (`MFrame.lean` §3 says so explicitly) and the `α ≥ 2` conditions
come from the shared Gram downstream.  So the two cores reach the same working range for
genuinely different reasons. -/
theorem nFrameExists_nonempty_iff (α h : ℕ) : Nonempty (NFrame α h) ↔ 2 ≤ α := by
  refine ⟨fun hne => ?_, fun hα => nonempty_nFrame hα h⟩
  by_contra hlt
  rcases (by omega : α = 0 ∨ α = 1) with rfl | rfl
  · exact (nFrameExists_isEmpty_zero h).false hne.some
  · exact (nFrameExists_isEmpty_one h).false hne.some

/-- **The rank-four corollary**: MC2's `NDecomposition α` (`Cores.lean:1786`) is inhabited for
every `α ≥ 2`, through `NFrame.toNDecomposition`.  With `mFrameExists_mDecomposition` this
closes both halves of the `Cores.lean` §5 scope note ("the two `Nonempty` existence theorems are
not in this file"). -/
theorem nFrameExists_nDecomposition {α : ℕ} (hα : 2 ≤ α) : Nonempty (NDecomposition α) :=
  (nonempty_nFrame hα 0).map NFrame.toNDecomposition

/-- **The unlock**: `demushkinQ D_N = 2` with **no frame hypothesis**, at every handle count.
`demushkinQ_DN_nFrame` carries exactly one hypothesis, the frame itself, so composing is honest
and leaves only `2 ≤ α`, which is sharp by `nFrameExists_nonempty_iff`.  The `N` twin of
`mFrameExists_demushkinQ_DM`, and the general-`h`, hypothesis-free form of `demushkinQ_DN`. -/
theorem nFrameExists_demushkinQ_DN {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    demushkinQ (DN α h : Type) = 2 :=
  (nonempty_nFrame hα h).elim demushkinQ_DN_nFrame

end MarkedCore

end Dyadic

end GQ2
