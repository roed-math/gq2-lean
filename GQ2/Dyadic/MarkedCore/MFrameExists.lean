/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.MarkedCore.MFrame
public import GQ2.Reconstruction

@[expose] public section

/-!
# W51-MFRAME2: existence of the general-`h` `M`-frame, `Nonempty (MFrame α h)`

**Ticket W51-MFRAME2.**  `GQ2/Dyadic/MarkedCore/MFrame.lean` builds the general-`h` `M`-frame
`MFrame α h` and everything one can read off it (the forced `Ā`-row `mE_A_frame`, the
α-boundary `mFrame_isEmpty_zero`, the deliverable `demushkinQ_DM_mFrame`), but its scope note
deliberately leaves **existence** out:

> The existence theorem `Nonempty (MFrame α h)` (the `phiEquiv` route of
> `GQ2/Roe/DRAbelianization.lean`) is *not* in scope, exactly as it is not in scope for
> `MDecomposition`/`NDecomposition` (`Cores.lean` §7 preamble) nor for `NFrame` (`N.lean` §1):
> consumers take the frame as a hypothesis.

This file closes that gap, at **every** handle count `h` and for **every** `α ≥ 1`, by running
the `phiEquiv` route on `D_M`.  The α-boundary is exactly the one `MFrame.lean` already pins
from the other side: `mFrame_isEmpty_zero` says `MFrame 0 h` is empty, and `nonempty_mFrame`
says `MFrame α h` is inhabited for every `α ≥ 1`, so together they decide inhabitation of
`MFrame α h` for all `(α, h)`.

## The route, and why the handles cost nothing

`GQ2/Roe/DRAbelianization.lean` builds `B_R = D_R^{ab} ≅ ℤ/2 × ℤ₂²` in four moves: coordinate
homs out of the presentation (`abLiftG ∘ drLiftHom`), coordinate surjectivity of the source
(`DRab_coord`, from topological generation), injectivity, surjectivity, then
`continuousMulEquivOfBijective`.  Every one of those moves is available for `D_M` at general
rank, and at general rank it is *shorter*, because `Cores.lean` §3.1 already proves the
presentation plumbing generically: `mLiftHom`/`mLiftHom_gen` (the universal property),
`dm_topGen` (topological generation), and `mRelWord_comm` (the abelian collapse
`ρ_M = 2Ā + 2^αC̄₀`).

The handle letters are free because of `handleWord_comm` (`Cores.lean` §1): the handle block
`∏_j [u_j, v_j]` dies in **any** commutative group, so `mRelWord_comm` reads
`mRelWord α m = m 0 ^ 2 * m 2 ^ (2^α)` with no `h` in it at all.  Concretely, the relator check
that every coordinate hom below has to pass mentions only the `Ā`- and `C̄₀`-values of its
marking, so the `2h` handle coordinate homs pass it *vacuously* (their markings are trivial on
the core letters).  That is the machine-checked form of `MFrame.lean`'s claim that handles are
"`2h` extra free `ℤ₂`-coordinates invisible to the relation vector": general `h` is not an
extension of the `h = 0` proof here, it is the same proof, uniform in `h`.

The single α-dependent input is the `C̄₀`-coordinate hom, whose `Ā`-value is `−2^{α−1}`: its
relator check is `2·(−2^{α−1}) + 2^α = 0`, which needs `2·2^{α−1} = 2^α`, i.e. `α ≥ 1`.  This is
the *same* arithmetic that `mRelVector_model_eq_zero` verifies inside the model, so the
hypothesis `1 ≤ α` here is not a new restriction: it is `MFrame.lean`'s α-boundary, met from
the constructive side.

## Contents

* **§1** Local instance restatements (`topAbelianization` is a compact, Hausdorff, totally
  disconnected commutative group) and `mIsProP_two_topAb_DM`.
* **§2** The marking shapes: `mHandleIdx` (the generator index of a handle coordinate) with
  `handleIdxU`/`handleIdxV` re-read through it, and `mHandleMark`.
* **§3** The coordinate homs, all through one generic builder `mCoordHom` whose relator
  obligation is exactly the abelian collapse: `mTHom` (torsion, to `ZMod 2`), `mBHom`, `mCHom`
  (the α-dependent one), `mDHom` and the family `mHHom k`.
* **§4** Coordinate surjectivity `mDMab_coord`: every element of `D_M^{ab}` is a `ℤ₂`-power
  word `∏ᵢ ḡᵢ^{cᵢ}` in the marked generators, the general-rank `DRab_coord`.
* **§5** The combined coordinate hom `mPhiHom`, its generator values, and bijectivity.
* **§6** `mFrameExists_phiEquiv` and the deliverable `nonempty_mFrame`, plus the rank-four
  corollary `mFrameExists_mDecomposition`.
* **§7** The unlock: `mFrameExists_demushkinQ_DM`, `demushkinQ (D_M) = 2` with no frame
  hypothesis.
* **§8** Axiom pins.

## Variance (MC-VAR discipline)

The proof stays entirely in the **abelianization layer**, exactly as `MFrame.lean` does: no cup
form, no Gram matrix, no bilinear pairing occurs in any statement or proof in this file, so the
`M`/`N` row-vs-column dictionary (`GQ2/Dyadic/MarkedCore/Variance.lean`, sharpest instance
`mFrameMatrix_transpose_eq_nMatOf`) is **not** invoked and no transposition arises.  The
`Finset.prod` over `Fin (coreRank h)` in §4 is a product in an abelian group, not a matrix
product, and the vectors `coreMark …` in §3 are markings of generators, not rows of a Gram.  The
dictionary re-enters only downstream, where a consumer feeds `MFrame.toMDecomposition` to
`mFrameMatrix`, and it does so through `MDecomposition` in the `M` variance, unchanged.

## Scope note (what is *not* here)

The `N`-side twin `Nonempty (NFrame α h)` is **not** in this file; see §6's
`nFrameExists_route` docstring for the priced follow-up and for the one place the two proofs
genuinely differ.

## Axiom scope (measured)

**Every declaration in this file prints at most `[propext, Classical.choice, Quot.sound]`**, the
std-3 set: the cited inputs (`MFrame.lean`, `Cores.lean` §1/§3, `SectionThree.lean`'s `abLiftG`
and `zpowZtwo` layer, `Reconstruction.lean`'s `continuousMulEquivOfBijective`) carry no census
axiom, and this file adds none.  See §8.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §1 The `topAbelianization` instances, and pro-2-ness of `D_M^{ab}`

Restated `local` from `GQ2/SectionThree.lean:112–160` exactly as
`GQ2/Roe/DRAbelianization.lean:54` and `GQ2/Dyadic/MarkedCore/Cores.lean:1775` restate them:
the originals are file-scoped in their homes, so a fourth consumer has to re-register them.
They are `local`, so nothing leaks to importers.  (**Hoist request H1**: these four instances
have now been copied verbatim four times; they belong in a shared module-system file, e.g. as a
`public` instance block in `GQ2/SectionThree.lean` or a new `GQ2/TopAbelianizationInst.lean`.)

`DRAbelianization.lean`'s warning applies: register them as direct `local instance`s, **not**
wrapped in a `def`, which breaks the group structure. -/

/-- `G^{ab}` is commutative (local restatement). -/
noncomputable local instance instCommGroupTopAbMFE {G : Type*} [Group G] [TopologicalSpace G]
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
local instance instCompactSpaceTopAbMFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

/-- `G^{ab}` is Hausdorff (local restatement). -/
local instance instT2SpaceTopAbMFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

/-- `G^{ab}` is totally disconnected (local restatement). -/
local instance instTotDiscTopAbMFE {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

/-- **`D_M^{ab}` is pro-2**, the image of the pro-2 group `D_M` (`isProP_DM`) under `abMk`.
The general-`(α, h)` clone of `isProP_two_topAb_DR` (`DRAbelianization.lean:91`); it is what
licenses `ℤ₂`-powering (`zpowZtwo`) inside `D_M^{ab}`. -/
theorem mIsProP_two_topAb_DM (α h : ℕ) : IsProP 2 (topAbelianization (DM α h : Type)) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective (isProP_DM α h)

/-! ## §2 Handle indices, and the two marking shapes

A coordinate hom is built from a **marking** of `Fin (coreRank h)`.  The four core coordinates
use `Cores.lean`'s `coreMark` (four values, trivial on every handle letter); the `2h` handle
coordinates use `mHandleMark`, trivial everywhere except at one generator.  `mHandleIdx` is the
translation between the *generator* index `Fin (coreRank h)` and the *model* handle coordinate
index `Fin (2h)` that `MFrame.lean`'s `mHandleCoordU`/`mHandleCoordV` name. -/

/-- The generator index carrying the `k`-th handle coordinate: `k ↦ 4 + k`.  Inverse to
`MFrame.lean`'s `mHandleCoordU`/`mHandleCoordV` composed with `handleIdxU`/`handleIdxV`. -/
def mHandleIdx {h : ℕ} (k : Fin (2 * h)) : Fin (coreRank h) :=
  ⟨4 + (k : ℕ), by have := k.isLt; simp only [coreRank]; omega⟩

@[simp] theorem mHandleIdx_val {h : ℕ} (k : Fin (2 * h)) :
    ((mHandleIdx k : Fin (coreRank h)) : ℕ) = 4 + (k : ℕ) := rfl

theorem mHandleIdx_injective {h : ℕ} : Function.Injective (mHandleIdx (h := h)) := by
  intro k l hkl
  have := congrArg Fin.val hkl
  simp only [mHandleIdx_val] at this
  exact Fin.ext (by omega)

/-- `Cores.lean`'s `u_j`-index is the `mHandleCoordU j`-th handle coordinate. -/
theorem mHandleIdx_coordU {h : ℕ} (j : Fin h) :
    mHandleIdx (mHandleCoordU j) = handleIdxU j :=
  Fin.ext (by simp only [mHandleIdx_val, handleIdxU]; show 4 + 2 * (j : ℕ) = 4 + 2 * (j : ℕ); rfl)

/-- `Cores.lean`'s `v_j`-index is the `mHandleCoordV j`-th handle coordinate. -/
theorem mHandleIdx_coordV {h : ℕ} (j : Fin h) :
    mHandleIdx (mHandleCoordV j) = handleIdxV j :=
  Fin.ext (by simp only [mHandleIdx_val, handleIdxV]; show 4 + (2 * (j : ℕ) + 1) = 5 + 2 * (j : ℕ)
              omega)

/-- The `k`-th **handle marking**: `x` at the generator carrying handle coordinate `k`, trivial
at every other generator (in particular at all four core letters, which is why its relator check
is vacuous). -/
def mHandleMark {G : Type*} [Group G] {h : ℕ} (k : Fin (2 * h)) (x : G) :
    Fin (coreRank h) → G :=
  fun i => if i = mHandleIdx k then x else 1

@[simp] theorem mHandleMark_self {G : Type*} [Group G] {h : ℕ} (k : Fin (2 * h)) (x : G) :
    mHandleMark k x (mHandleIdx k) = x := if_pos rfl

theorem mHandleMark_of_ne {G : Type*} [Group G] {h : ℕ} (k : Fin (2 * h)) (x : G)
    {i : Fin (coreRank h)} (hi : i ≠ mHandleIdx k) : mHandleMark k x i = 1 := if_neg hi

/-- The four core letters are never handle letters, so a handle marking is trivial on all of
them.  This is the vacuity that makes the `2h` handle coordinate homs free: their relator check
`m 0 ^ 2 * m 2 ^ (2^α) = 1` reads `1 = 1`. -/
theorem mHandleMark_core {G : Type*} [Group G] {h : ℕ} (k : Fin (2 * h)) (x : G)
    {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) : mHandleMark k x i = 1 :=
  if_neg fun hc => by
    have := congrArg Fin.val hc
    simp only [mHandleIdx_val] at this
    omega

/-! ## §3 The coordinate homs

All five families come from one builder.  The point of the builder is that its relator
obligation, after `mRelWord_comm`, mentions **only** the `Ā`- and `C̄₀`-values of the marking:
`m 0 ^ 2 * m 2 ^ (2^α) = 1`.  The handle letters do not appear, which is why the `2h` handle
coordinate homs of §3.5 exist at no cost, and the `B̄`/`D̄` homs at no cost either. -/

section CoordHoms

variable {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **The coordinate hom builder.**  A marking of a commutative pro-2 group `H` whose `Ā`- and
`C̄₀`-values satisfy the abelianized relation `2Ā + 2^αC̄₀ = 0` classifies a continuous hom
`D_M^{ab} → H`: lift through the presentation (`mLiftHom`), then descend through `abMk`
(`abLiftG`).  The `abLiftG ∘ mLiftHom` composite is the general-rank
`abLiftG ∘ drLiftHom` of `GQ2/Roe/DRAbelianization.lean:259`. -/
noncomputable def mCoordHom (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : m 0 ^ 2 * m 2 ^ (2 ^ α) = 1) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) H :=
  abLiftG (mLiftHom α h hH m (by rw [mRelWord_comm]; exact hrel))

@[simp] theorem mCoordHom_gen (α h : ℕ) (hH : IsProP 2 H) (m : Fin (coreRank h) → H)
    (hrel : m 0 ^ 2 * m 2 ^ (2 ^ α) = 1) (i : Fin (coreRank h)) :
    mCoordHom α h hH m hrel (abMk (dmGen α h i)) = m i := by
  rw [mCoordHom, abLiftG_abMk, mLiftHom_gen]

end CoordHoms

/-! ### §3.1 The torsion coordinate `t`

`Ā ↦ 1`, everything else `↦ 0`, into `ZMod 2`.  Then the composite torsion class
`t = Ā·C̄₀^{2^{α−1}}` also goes to `1`, since `C̄₀ ↦ 0`.  The relator check is `2·1 = 0` in
`ZMod 2`, which holds at *every* `α`, including `α = 0`: the α-obstruction of
`mFrame_isEmpty_zero` lives in the `C̄₀`-coordinate (§3.3), not here. -/
noncomputable def mTHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (Multiplicative (ZMod 2)) :=
  mCoordHom α h isProP_two_multZMod2 (coreMark (ofAdd (1 : ZMod 2)) 1 1 1) (by
    rw [coreMark_zero, coreMark_two, one_pow, mul_one, ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1)

/-! ### §3.2 The `B̄`-coordinate -/

/-- `B̄ ↦ 1`, everything else `↦ 0`, into `ℤ₂`.  Relator check: `0^2 · 0^{2^α} = 0`. -/
noncomputable def mBHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (Multiplicative ℤ_[2]) :=
  mCoordHom α h PropOneOne.isProP_two_multPadicInt (coreMark 1 (ofAdd (1 : ℤ_[2])) 1 1) (by
    rw [coreMark_zero, coreMark_two, one_pow, one_pow, mul_one])

/-! ### §3.3 The `C̄₀`-coordinate: the one α-dependent hom

`Ā ↦ −2^{α−1}`, `C̄₀ ↦ 1`, everything else `↦ 0`.  Its relator check is
`2·(−2^{α−1}) + 2^α·1 = 0`, i.e. `2·2^{α−1} = 2^α`, which is exactly the arithmetic
`mRelVector_model_eq_zero` performs inside the model, and exactly what fails at `α = 0`.  So
`1 ≤ α` enters the construction here and nowhere else, and it enters as the constructive twin
of `mFrame_isEmpty_zero`.  The `Ā`-value is forced by `mE_A_frame`; we are simply writing down
the row that theorem says any frame must have. -/
noncomputable def mCHom {α : ℕ} (hα : 1 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (Multiplicative ℤ_[2]) :=
  mCoordHom α h PropOneOne.isProP_two_multPadicInt
    (coreMark (ofAdd (-(2 : ℤ_[2]) ^ (α - 1))) 1 (ofAdd (1 : ℤ_[2])) 1) (by
      obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
      rw [coreMark_zero, coreMark_two, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
      congr 1
      simp only [Nat.add_sub_cancel]
      rw [nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring)

/-! ### §3.4 The `D̄`-coordinate -/

/-- `D̄ ↦ 1`, everything else `↦ 0`, into `ℤ₂`. -/
noncomputable def mDHom (α h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (Multiplicative ℤ_[2]) :=
  mCoordHom α h PropOneOne.isProP_two_multPadicInt (coreMark 1 1 1 (ofAdd (1 : ℤ_[2]))) (by
    rw [coreMark_zero, coreMark_two, one_pow, one_pow, mul_one])

/-! ### §3.5 The `2h` handle coordinates

The `k`-th handle hom sends the generator carrying handle coordinate `k` to `1` and every other
generator, **in particular all four core letters**, to `0`.  Its relator check is therefore
`0^2 · 0^{2^α} = 0`, vacuously, at every `α` and every `h`: `mHandleMark_core` is the whole
content of "handles are invisible to the relation vector". -/
noncomputable def mHHom (α : ℕ) {h : ℕ} (k : Fin (2 * h)) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (Multiplicative ℤ_[2]) :=
  mCoordHom α h PropOneOne.isProP_two_multPadicInt (mHandleMark k (ofAdd (1 : ℤ_[2]))) (by
    rw [mHandleMark_core k _ (by rw [coreVal_zero]; omega),
      mHandleMark_core k _ (by rw [coreVal_two]; omega), one_pow, one_pow, mul_one])

/-! ## §4 Coordinate surjectivity: `D_M^{ab}` is `ℤ₂`-power words in the marked generators

The general-rank `DRab_coord` (`GQ2/Roe/DRAbelianization.lean:203`).  `D_M` is topologically
generated by its `4 + 2h` marked generators (`dm_topGen`), so `D_M^{ab}` is topologically
generated by their images; the set of `ℤ₂`-power words is the *compact*, hence closed, range of
a continuous hom out of `ℤ₂^{4+2h}`, so it swallows that closure. -/

section Coord

variable (α h : ℕ)

/-- The `ℤ₂`-power word `∏ᵢ ḡᵢ^{cᵢ}` in the marked generators of `D_M^{ab}`.  A `Finset.prod` in
an abelian group, not a matrix product: see the variance note. -/
noncomputable def mAbWord (c : Fin (coreRank h) → ℤ_[2]) : topAbelianization (DM α h : Type) :=
  ∏ i, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) (c i)

/-- `mAbWord` as a monoid hom out of `ℤ₂^{4+2h}` (the general-rank `PhiR`). -/
noncomputable def mAbWordHom :
    Multiplicative (Fin (coreRank h) → ℤ_[2]) →* topAbelianization (DM α h : Type) where
  toFun c := mAbWord α h c.toAdd
  map_one' := by
    refine Finset.prod_eq_one fun i _ => ?_
    show zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) 0 = 1
    exact zpowZtwo_zero _ _
  map_mul' c d := by
    show ∏ i, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) (c.toAdd i + d.toAdd i)
      = (∏ i, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) (c.toAdd i))
        * ∏ i, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) (d.toAdd i)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => zpowZtwo_add _ _ _ _

theorem continuous_mAbWordHom : Continuous (mAbWordHom α h) := by
  show Continuous fun c : Multiplicative (Fin (coreRank h) → ℤ_[2]) =>
    ∏ i, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h i)) (c.toAdd i)
  exact continuous_finsetProd _ fun i _ =>
    (continuous_zpowZtwo _ _).comp ((continuous_apply i).comp continuous_toAdd)

/-- The `i`-th marked generator is the `ℤ₂`-power word with a single `1`. -/
theorem mAbWordHom_single (i : Fin (coreRank h)) :
    mAbWordHom α h (ofAdd (Pi.single i (1 : ℤ_[2]))) = abMk (dmGen α h i) := by
  show ∏ j, zpowZtwo (mIsProP_two_topAb_DM α h) (abMk (dmGen α h j))
    ((Pi.single i (1 : ℤ_[2]) : Fin (coreRank h) → ℤ_[2]) j) = _
  rw [Finset.prod_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, zpowZtwo_zero]) (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [Pi.single_eq_same, zpowZtwo_one_exp]

/-- **Coordinate surjectivity of `D_M^{ab}`**: every element is a `ℤ₂`-power word
`Ā^{c₀}·B̄^{c₁}·C̄₀^{c₂}·D̄^{c₃}·∏ⱼ ūⱼ^{…}v̄ⱼ^{…}` in the marked generators.  The general-rank
`DRab_coord`. -/
theorem mDMab_coord (z : topAbelianization (DM α h : Type)) :
    ∃ c : Fin (coreRank h) → ℤ_[2], z = mAbWord α h c := by
  have hgen : (Subgroup.closure (⇑abMk '' Set.range (dmGen α h))).topologicalClosure = ⊤ := by
    have := abMk_surjective.denseRange.topologicalClosure_map_subgroup
      (continuous_abMk (G := (DM α h : Type))) (dm_topGen α h)
    rwa [MonoidHom.map_closure] at this
  have hclosed : IsClosed ((mAbWordHom α h).range : Set (topAbelianization (DM α h : Type))) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_mAbWordHom α h)).isClosed
  have hsub : Subgroup.closure (⇑abMk '' Set.range (dmGen α h)) ≤ (mAbWordHom α h).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨ofAdd (Pi.single i 1), mAbWordHom_single α h i⟩
  have htop : (mAbWordHom α h).range = ⊤ :=
    eq_top_iff.mpr (hgen ▸ Subgroup.topologicalClosure_minimal _ hsub hclosed)
  have hz : z ∈ (mAbWordHom α h).range := by rw [htop]; exact Subgroup.mem_top z
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hz
  exact ⟨p.toAdd, hp.symm⟩

end Coord

/-! ## §5 Evaluating the coordinate homs on a word

Every marking used in §3 is supported on at most two generator slots, so each coordinate hom
reads a word off in at most two of its exponents.  §5.1 is the two sparse-product lemmas, §5.2
the index case split, §5.3 the five evaluation formulas. -/

/-! ### §5.1 Sparse products -/

section Sparse

variable {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] {h : ℕ}

/-- A marking supported at one slot pairs with a word through that slot only. -/
theorem mProd_single (hH : IsProP 2 H) (m : Fin (coreRank h) → H) (c : Fin (coreRank h) → ℤ_[2])
    (i₀ : Fin (coreRank h)) (hm : ∀ i, i ≠ i₀ → m i = 1) :
    ∏ i, zpowZtwo hH (m i) (c i) = zpowZtwo hH (m i₀) (c i₀) :=
  Finset.prod_eq_single i₀ (fun j _ hj => by rw [hm j hj, zpowZtwo_one_base])
    (fun hi => absurd (Finset.mem_univ i₀) hi)

/-- A marking supported at two slots pairs with a word through those two slots only. -/
theorem mProd_pair (hH : IsProP 2 H) (m : Fin (coreRank h) → H) (c : Fin (coreRank h) → ℤ_[2])
    {i₀ i₁ : Fin (coreRank h)} (hne : i₀ ≠ i₁) (hm : ∀ i, i ≠ i₀ → i ≠ i₁ → m i = 1) :
    ∏ i, zpowZtwo hH (m i) (c i)
      = zpowZtwo hH (m i₀) (c i₀) * zpowZtwo hH (m i₁) (c i₁) := by
  rw [← Finset.prod_pair (f := fun i => zpowZtwo hH (m i) (c i)) hne]
  refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  rw [hm i hi.1 hi.2, zpowZtwo_one_base]

end Sparse

/-! ### §5.2 The generator index split

Every generator index is one of the four core letters or exactly one handle letter. -/

/-- `coreMark` spelled out; the definition, for `split_ifs`. -/
theorem coreMark_apply {G : Type*} [Group G] {h : ℕ} (a b c d : G) (i : Fin (coreRank h)) :
    coreMark a b c d i = if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then b else
      if (i : ℕ) = 2 then c else if (i : ℕ) = 3 then d else 1 := rfl

theorem mCoreVal_ne_zero {h : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 0) : (i : ℕ) ≠ 0 :=
  fun hv => hi (Fin.ext (hv.trans (coreVal_zero h).symm))

theorem mCoreVal_ne_one {h : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 1) : (i : ℕ) ≠ 1 :=
  fun hv => hi (Fin.ext (hv.trans (coreVal_one h).symm))

theorem mCoreVal_ne_two {h : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 2) : (i : ℕ) ≠ 2 :=
  fun hv => hi (Fin.ext (hv.trans (coreVal_two h).symm))

theorem mCoreVal_ne_three {h : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 3) : (i : ℕ) ≠ 3 :=
  fun hv => hi (Fin.ext (hv.trans (coreVal_three h).symm))

theorem mCoreZero_ne_two {h : ℕ} : (0 : Fin (coreRank h)) ≠ 2 :=
  fun hc => by have := congrArg Fin.val hc; rw [coreVal_zero, coreVal_two] at this; omega

/-- **The generator index split**: `Fin (coreRank h)` is the four core letters plus the `2h`
handle letters, and nothing else. -/
theorem mIdx_cases {h : ℕ} (i : Fin (coreRank h)) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ ∃ k, i = mHandleIdx k := by
  by_cases h0 : (i : ℕ) = 0
  · exact Or.inl (Fin.ext (h0.trans (coreVal_zero h).symm))
  by_cases h1 : (i : ℕ) = 1
  · exact Or.inr (Or.inl (Fin.ext (h1.trans (coreVal_one h).symm)))
  by_cases h2 : (i : ℕ) = 2
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (h2.trans (coreVal_two h).symm))))
  by_cases h3 : (i : ℕ) = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (h3.trans (coreVal_three h).symm)))))
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(i : ℕ) - 4, ?_⟩, Fin.ext ?_⟩)))
  · have := i.isLt; simp only [coreRank] at this; omega
  · simp only [mHandleIdx_val]; omega

/-! ### §5.3 The five evaluation formulas -/

section Words

variable (α h : ℕ) (c : Fin (coreRank h) → ℤ_[2])

/-- A coordinate hom on a `ℤ₂`-power word: apply the marking slotwise. -/
theorem mCoordHom_word {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] (hH : IsProP 2 H)
    (m : Fin (coreRank h) → H) (hrel : m 0 ^ 2 * m 2 ^ (2 ^ α) = 1) :
    mCoordHom α h hH m hrel (mAbWord α h c) = ∏ i, zpowZtwo hH (m i) (c i) := by
  rw [mAbWord, map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [map_zpowZtwo (mIsProP_two_topAb_DM α h) hH, mCoordHom_gen]

/-- The `B̄`-coordinate of a word is its `B̄`-exponent. -/
theorem mBHom_word : mBHom α h (mAbWord α h c) = ofAdd (c 1) := by
  rw [mBHom, mCoordHom_word, mProd_single _ _ _ 1 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_one hi
    split_ifs <;> rfl), coreMark_one, zpowZtwo_ofAdd, one_mul]

/-- The `D̄`-coordinate of a word is its `D̄`-exponent. -/
theorem mDHom_word : mDHom α h (mAbWord α h c) = ofAdd (c 3) := by
  rw [mDHom, mCoordHom_word, mProd_single _ _ _ 3 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_three hi
    split_ifs <;> rfl), coreMark_three, zpowZtwo_ofAdd, one_mul]

/-- The `k`-th handle coordinate of a word is its `k`-th handle exponent. -/
theorem mHHom_word {h : ℕ} (α : ℕ) (c : Fin (coreRank h) → ℤ_[2]) (k : Fin (2 * h)) :
    mHHom α k (mAbWord α h c) = ofAdd (c (mHandleIdx k)) := by
  rw [mHHom, mCoordHom_word,
    mProd_single _ _ _ (mHandleIdx k) (fun i hi => mHandleMark_of_ne k _ hi),
    mHandleMark_self, zpowZtwo_ofAdd, one_mul]

/-- The `C̄₀`-coordinate of a word: the `Ā`-slot contributes `−2^{α−1}`, the `C̄₀`-slot `1`.
This is the coordinate that sees the forced `Ā`-row of `mE_A_frame`. -/
theorem mCHom_word {α : ℕ} (hα : 1 ≤ α) (h : ℕ) (c : Fin (coreRank h) → ℤ_[2]) :
    mCHom hα h (mAbWord α h c) = ofAdd (-(2 : ℤ_[2]) ^ (α - 1) * c 0 + c 2) := by
  rw [mCHom, mCoordHom_word, mProd_pair _ _ _ mCoreZero_ne_two (fun i hi0 hi2 => by
    rw [coreMark_apply]
    have hv0 := mCoreVal_ne_zero hi0
    have hv2 := mCoreVal_ne_two hi2
    split_ifs <;> first | rfl | omega), coreMark_zero, coreMark_two,
    zpowZtwo_ofAdd, zpowZtwo_ofAdd, ← ofAdd_add, one_mul]

/-- The torsion coordinate of a word: only the `Ā`-exponent contributes, through `ZMod 2`. -/
theorem mTHom_word : mTHom α h (mAbWord α h c)
    = zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (c 0) := by
  rw [mTHom, mCoordHom_word, mProd_single _ _ _ 0 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_zero hi
    split_ifs <;> first | rfl | omega), coreMark_zero]

end Words

end MarkedCore

end Dyadic

end GQ2
