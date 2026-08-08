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

end MarkedCore

end Dyadic

end GQ2
