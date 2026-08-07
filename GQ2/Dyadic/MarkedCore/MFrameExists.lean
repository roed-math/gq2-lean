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

end MarkedCore

end Dyadic

end GQ2
