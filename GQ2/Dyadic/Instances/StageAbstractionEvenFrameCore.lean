/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenModel
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFrattiniFrame
import GQ2.Dyadic.MarkedCore.Variance
import GQ2.Dyadic.FieldDataEven

/-!
# W51-EV3C1, part 1: the core-agnostic even Frattini-frame scaffolding

Ticket **EV-3c** of `docs/dyadic/ev4b-stage-abstraction.md` §4, split at dispatch into a
core-agnostic half (this file) and the `N`-row instance
(`GQ2/Dyadic/Instances/StageAbstractionEvenFrattiniFrameN.lean`).  **Everything here is
independent of which even core is being framed**: nothing mentions `nUnit`/`mUnit`,
`chiN`/`chiM`, `vN`/`vM`, or any mod-eight table.  The `M`-row clone reuses this file verbatim,
which is possible because the two even cores share one Gram
(`MarkedCore.mGram_eq_nGram`, `GQ2/Dyadic/MarkedCore/Variance.lean:107`, a `rfl`).

## The split, explicitly

| here (core-agnostic) | in the row file (`N`, and its `M` twin) |
|---|---|
| the coordinate model, its Gram, and the frame-index coordinates | the row table's mod-four/mod-eight tables |
| the Gram-extension adapter `evenFrameGram` from `MarkedCore.nGram` | the `nUnit`/`mUnit` mod-sixteen bridge values |
| the dual-**vector** map `evenDualVec` (board crux (i)) | the `im χ` row-membership discussion |
| the even Witt adaptation `evenFrameAdaptedModelEquiv` | the supply statement and its binders |
| the row-relative exact lift `evenFrameExactLift` | |
| the frame assembly `evenFrame_of_adapted` and `evenFrame_of_kappaPin` | |

## Board crux (i): no dual-basis permutation, a dual-vector map instead

`EvenForwardRouteSkeleton.lean:48–51` records that the even head `[[1,1],[1,0]]` has inverse
Gram `[[0,1],[1,1]]`, so the odd route's `sqInitialPartner : Equiv.Perm` (legitimate there,
because `⟨1⟩ ⊥ H ⊥ H^{⊥h}` pairs each coordinate basis vector with exactly one other) has no
even analogue.  §1.4 replaces it by `evenDualVec`, sending a frame index `i` to the *vector*
representing the `i`-th coordinate functional:

| frame index | letter | `evenDualVec` | a basis vector? |
|---|---|---|---|
| `0` | `x₀` | `e₁` | yes (the partner index `1`) |
| `1` | `x₁` | `e₀ + e₁` | **no**, and this is the crux |
| `2`, `3` | `σ`, `x₂` | `e₃`, `e₂` | yes (the `(2,3)` plane swaps) |
| `U j`, `V j` | handles | `e_{V j}`, `e_{U j}` | yes (the handle planes swap) |

Only the head is non-permutational, and only at index `1`.  The pay-off is §1.5: the model's
Labute vector, the vector representing the diagonal `z ↦ b z z`, is `evenDualVec 0`, and it is
`e₁`, so it sits at **frame index 1**.  That is exactly the index at which both even row tables
carry their nontrivial cyclotomic value, which is why the parity half of the bridge table
matches for free.

## What is proved and what is carried

Proved here: all of the above, sorry-free, and the assembly of a
`StageGeneric.Frame` with `Frame.IsCupAdapted` from an adapted coordinate system.

Carried as hypotheses (never as admitted goals), because they are the honest even-degree
inputs and are owned by other tickets:

* `RowExactLevelFibreLiftSupply v _ chiCycKTwo`, ticket EV-4a.  At even degree `chiCycKTwo`
  is *not* surjective, so the odd route's `SharpExactLevelFibreLiftSupply` is unavailable and
  the row-relative weakening of `StageAbstraction.lean` §2.1(b) is what the lane must use.
* `cyclotomicModFourClassKTwo ≠ 0`, the campaign's standing ramified-`i` binder.
  `FieldDataEven.kappaK_eq_zero_iff` is the stated interface for deriving it, and that file's
  own docstring records that nothing in `GQ2/Dyadic/` currently derives it from the binder.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.FieldDataEven
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The even coordinate model

`[[1,1],[1,0]] ⊥ H^{⊥(h+1)}` in explicit coordinates, laid out to match the even relator's
frame indexing: the head carries the core letters `(x₀, x₁)`, the *first* hyperbolic plane
carries the core letters `(σ, x₂)`, and the `j`-th remaining plane carries the `j`-th handle
pair.  The head is `FieldDataEven.headGram` and the planes are `LSqStokes.hypGram`, both
committed; no form is redefined here. -/

/-- The even coordinate model at `h` handles: the rank-two non-alternating head followed by
`h + 1` hyperbolic planes.  This is the target of `FieldDataEven`'s even normal form
`exists_cupForm_normalForm_even`, with the plane count already pinned. -/
abbrev evenFrameModel (h : ℕ) : Type :=
  (ZMod 2 × ZMod 2) × (Fin (h + 1) → ZMod 2 × ZMod 2)

/-- The model Gram `[[1,1],[1,0]] ⊥ H^{⊥(h+1)}`. -/
def evenFrameGramModel (h : ℕ) (z z' : evenFrameModel h) : ZMod 2 :=
  headGram z.1 z'.1 + hypGram z.2 z'.2

/-! ### §1.1 Two facts about the hyperbolic block -/

/-- The hyperbolic block is alternating. -/
theorem evenFrameHypGram_self {m : ℕ} (r : Fin m → ZMod 2 × ZMod 2) : hypGram r r = 0 := by
  simp only [hypGram]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [mul_comm (r j).2 (r j).1]
  exact CharTwo.add_self_eq_zero _

/-- The hyperbolic block vanishes on the zero vector. -/
theorem evenFrameHypGram_zero_left {m : ℕ} (r : Fin m → ZMod 2 × ZMod 2) :
    hypGram (0 : Fin m → ZMod 2 × ZMod 2) r = 0 := by
  simp [hypGram]

/-- The hyperbolic block against a single plane reads that plane's two coordinates. -/
theorem evenFrameHypGram_single {m : ℕ} (k : Fin m) (p : ZMod 2 × ZMod 2)
    (r : Fin m → ZMod 2 × ZMod 2) :
    hypGram (Pi.single k p) r = p.1 * (r k).2 + p.2 * (r k).1 := by
  classical
  simp only [hypGram]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ### §1.2 Frame-index coordinates

The plane carrying a handle index, and the coordinate of a model vector at a frame index.  The
`min` in `evenFramePlane` is only there to make the bound proof-free; on the handle indices,
which are the only ones the coordinate function feeds it, it is inert. -/

/-- The hyperbolic plane carrying the frame index `i`: plane `0` for the core letters `σ`, `x₂`
and plane `j + 1` for either letter of the `j`-th handle pair. -/
def evenFramePlane {h : ℕ} (i : Fin (MarkedCore.coreRank h)) : Fin (h + 1) :=
  ⟨min (((i : ℕ) - 4) / 2 + 1) h, by omega⟩

/-- The coordinate of a model vector at a frame index, in the layout of §1: `x₀`, `x₁` are the
two head coordinates, `σ`, `x₂` the two coordinates of plane `0`, and the `j`-th handle pair the
two coordinates of plane `j + 1`.  The shape is `MarkedCore.coreMark`'s. -/
def evenFrameCoord {h : ℕ} (i : Fin (MarkedCore.coreRank h)) (z : evenFrameModel h) : ZMod 2 :=
  if (i : ℕ) = 0 then z.1.1 else
  if (i : ℕ) = 1 then z.1.2 else
  if (i : ℕ) = 2 then (z.2 0).1 else
  if (i : ℕ) = 3 then (z.2 0).2 else
  if ((i : ℕ) - 4) % 2 = 0 then (z.2 (evenFramePlane i)).1 else (z.2 (evenFramePlane i)).2

section CoordValues

variable {h : ℕ} (z : evenFrameModel h) {i : Fin (MarkedCore.coreRank h)}

/-- The coordinate at an index of value `0`. -/
theorem evenFrameCoord_val_zero (hi : (i : ℕ) = 0) : evenFrameCoord i z = z.1.1 := by
  unfold evenFrameCoord
  rw [if_pos hi]

/-- The coordinate at an index of value `1`. -/
theorem evenFrameCoord_val_one (hi : (i : ℕ) = 1) : evenFrameCoord i z = z.1.2 := by
  unfold evenFrameCoord
  rw [if_neg (by omega), if_pos hi]

/-- The coordinate at an index of value `2`. -/
theorem evenFrameCoord_val_two (hi : (i : ℕ) = 2) : evenFrameCoord i z = (z.2 0).1 := by
  unfold evenFrameCoord
  rw [if_neg (by omega), if_neg (by omega), if_pos hi]

/-- The coordinate at an index of value `3`. -/
theorem evenFrameCoord_val_three (hi : (i : ℕ) = 3) : evenFrameCoord i z = (z.2 0).2 := by
  unfold evenFrameCoord
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hi]

/-- The plane of an index in the `j`-th handle pair is plane `j + 1`. -/
theorem evenFramePlane_val (j : Fin h) (hi : (i : ℕ) = 4 + 2 * (j : ℕ) ∨ (i : ℕ) = 5 + 2 * (j : ℕ)) :
    evenFramePlane i = j.succ := by
  have hj := j.isLt
  refine Fin.val_injective ?_
  simp only [evenFramePlane, Fin.val_succ]
  omega

/-- The coordinate at the first letter of the `j`-th handle pair. -/
theorem evenFrameCoord_val_handleU (j : Fin h) (hi : (i : ℕ) = 4 + 2 * (j : ℕ)) :
    evenFrameCoord i z = (z.2 j.succ).1 := by
  unfold evenFrameCoord
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), evenFramePlane_val j (Or.inl hi)]

/-- The coordinate at the second letter of the `j`-th handle pair. -/
theorem evenFrameCoord_val_handleV (j : Fin h) (hi : (i : ℕ) = 5 + 2 * (j : ℕ)) :
    evenFrameCoord i z = (z.2 j.succ).2 := by
  unfold evenFrameCoord
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), evenFramePlane_val j (Or.inr hi)]

/-- The `x₀` coordinate is the first head coordinate. -/
@[simp] theorem evenFrameCoord_zero :
    evenFrameCoord (0 : Fin (MarkedCore.coreRank h)) z = z.1.1 :=
  evenFrameCoord_val_zero z (MarkedCore.coreVal_zero h)

/-- The `x₁` coordinate is the second head coordinate, the index at which the model's Labute
vector lives (§1.5). -/
@[simp] theorem evenFrameCoord_one :
    evenFrameCoord (1 : Fin (MarkedCore.coreRank h)) z = z.1.2 :=
  evenFrameCoord_val_one z (MarkedCore.coreVal_one h)

/-- The `σ` coordinate is the first coordinate of plane `0`. -/
@[simp] theorem evenFrameCoord_two :
    evenFrameCoord (2 : Fin (MarkedCore.coreRank h)) z = (z.2 0).1 :=
  evenFrameCoord_val_two z (MarkedCore.coreVal_two h)

/-- The `x₂` coordinate is the second coordinate of plane `0`. -/
@[simp] theorem evenFrameCoord_three :
    evenFrameCoord (3 : Fin (MarkedCore.coreRank h)) z = (z.2 0).2 :=
  evenFrameCoord_val_three z (MarkedCore.coreVal_three h)

/-- The first letter of the `j`-th handle pair reads the first coordinate of plane `j + 1`. -/
@[simp] theorem evenFrameCoord_handleU (j : Fin h) :
    evenFrameCoord (MarkedCore.handleIdxU j) z = (z.2 j.succ).1 :=
  evenFrameCoord_val_handleU z j (MarkedCore.handleIdxU_val j)

/-- The second letter of the `j`-th handle pair reads the second coordinate of plane `j + 1`. -/
@[simp] theorem evenFrameCoord_handleV (j : Fin h) :
    evenFrameCoord (MarkedCore.handleIdxV j) z = (z.2 j.succ).2 :=
  evenFrameCoord_val_handleV z j (MarkedCore.handleIdxV_val j)

end CoordValues

/-! ### §1.3 Linearity and faithfulness of the coordinate family -/

section CoordLinear

variable {h : ℕ}

theorem evenFrameCoord_add (i : Fin (MarkedCore.coreRank h)) (z z' : evenFrameModel h) :
    evenFrameCoord i (z + z') = evenFrameCoord i z + evenFrameCoord i z' := by
  simp only [evenFrameCoord]
  split_ifs <;> rfl

theorem evenFrameCoord_zero_vec (i : Fin (MarkedCore.coreRank h)) :
    evenFrameCoord i (0 : evenFrameModel h) = 0 := by
  simp only [evenFrameCoord]
  split_ifs <;> rfl

theorem evenFrameCoord_smul (i : Fin (MarkedCore.coreRank h)) (c : ZMod 2)
    (z : evenFrameModel h) : evenFrameCoord i (c • z) = c * evenFrameCoord i z := by
  rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, evenFrameCoord_zero_vec, zero_mul]
  · rw [one_smul, one_mul]

/-- The coordinate at a frame index, as a linear functional.  This is what
`frattiniFrameEval_realizable` consumes when the dual family of generators is chosen. -/
def evenFrameCoordL (i : Fin (MarkedCore.coreRank h)) : evenFrameModel h →ₗ[ZMod 2] ZMod 2 where
  toFun := evenFrameCoord i
  map_add' := evenFrameCoord_add i
  map_smul' := evenFrameCoord_smul i

@[simp] theorem evenFrameCoordL_apply (i : Fin (MarkedCore.coreRank h))
    (z : evenFrameModel h) : evenFrameCoordL i z = evenFrameCoord i z := rfl

/-- **The frame coordinates are faithful**: a model vector all of whose frame coordinates vanish
is zero.  This is what turns Frattini generation into a duality statement. -/
theorem evenFrameCoord_eq_zero (z : evenFrameModel h)
    (hall : ∀ i, evenFrameCoord i z = 0) : z = 0 := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun k ↦ ?_)
  · exact (evenFrameCoord_zero z).symm.trans (hall 0)
  · exact (evenFrameCoord_one z).symm.trans (hall 1)
  · refine Fin.cases ?_ (fun j ↦ ?_) k
    · exact Prod.ext ((evenFrameCoord_two z).symm.trans (hall 2))
        ((evenFrameCoord_three z).symm.trans (hall 3))
    · exact Prod.ext ((evenFrameCoord_handleU z j).symm.trans (hall _))
        ((evenFrameCoord_handleV z j).symm.trans (hall _))

end CoordLinear

/-! ### §1.4 The Gram-extension adapter, and the dual-vector map (board crux (i))

`Frame.IsCupAdapted` takes the word's quadratic-initial Gram as a function of the full
`Fin (coreRank h)`-indexed matrix of character products (`StageAbstraction.lean` §2.1(a)), so the
committed rank-four `MarkedCore.nGram` has to be extended to rank `coreRank h`.  The extension is
by the `h` handle planes and by zero on every core/handle cross term: the even relator is
`(core word) * ∏ⱼ [uⱼ, vⱼ]`, so its degree-two initial form is the core Gram plus one hyperbolic
plane per handle and nothing else.

`MarkedCore.nGram` is cited, never redefined; by `MarkedCore.mGram_eq_nGram` (a `rfl`) the same
adapter serves the `M` row, which is the main reason this section is core-agnostic. -/

/-- The four core letters as frame indices. -/
def evenFrameCoreIdx {h : ℕ} : Fin 4 → Fin (MarkedCore.coreRank h) := ![0, 1, 2, 3]

/-- **The even quadratic-initial Gram at rank `coreRank h`**: the committed rank-four Gram
`MarkedCore.nGram` (`= MarkedCore.mGram`, `Variance.lean:107`) on the core block, one hyperbolic
plane per handle, zero across.  This is the `gram` parameter of `Frame.IsCupAdapted`.

**Composition seam.**  The right-hand side is written in exactly the shape of ticket EV-3d's
word-independent predicate `IsEvenGram`, itself verbatim the right-hand side of the committed
`IsCupCocycle.nRelWord_centLift_fib` / `mRelWord_centLift_fib`, so that EV-3d's realization
endpoints accept this adapter with `hg` discharged by `fun _ ↦ rfl`.  That the core block really
is the committed Gram, rather than a hand-copied matrix, is `evenFrameGram_nGram` below. -/
def evenFrameGram (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) : ZMod 2 :=
  M 0 0 + (M 0 1 + M 1 0) + (M 2 3 + M 3 2)
    + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
        + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j))

/-- The adapter, in the EV-3d seam shape, definitionally. -/
theorem evenFrameGram_expand (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenFrameGram h M = M 0 0 + (M 0 1 + M 1 0) + (M 2 3 + M 3 2)
      + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
          + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j)) := rfl

/-- **The core block is the committed even Gram.**  The rank-four block of the adapter is the
contraction against `MarkedCore.nGram`, which by `MarkedCore.mGram_eq_nGram` (a `rfl`) is also
`mGram`, so the `M` row's adapter is this one.  No Gram is redefined anywhere in this lane. -/
theorem evenFrameGram_nGram (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenFrameGram h M =
      (∑ a : Fin 4, ∑ b : Fin 4,
          MarkedCore.nGram a b * M (evenFrameCoreIdx a) (evenFrameCoreIdx b))
        + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
            + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j)) := by
  rw [evenFrameGram]
  simp only [evenFrameCoreIdx, Fin.sum_univ_four, MarkedCore.nGram, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  ring

/-- **The adapter is the model Gram.**  Contracting the extended Gram against the matrix of
coordinate products of two model vectors returns the model Gram, exactly as the odd route's
`sqRelatorQuadraticInitialGram_modelCoord` does.  This is the identity the cup-adaptation step
of §4 runs on. -/
theorem evenFrameGram_modelCoord (h : ℕ) (z z' : evenFrameModel h) :
    evenFrameGram h (fun i j ↦ evenFrameCoord i z * evenFrameCoord j z') =
      evenFrameGramModel h z z' := by
  rw [evenFrameGram_expand, evenFrameGramModel]
  simp only [evenFrameCoord_zero, evenFrameCoord_one, evenFrameCoord_two, evenFrameCoord_three,
    evenFrameCoord_handleU, evenFrameCoord_handleV, headGram, hypGram, Fin.sum_univ_succ]
  ring

/-- **The dual-vector map.**  `evenDualVec i` is the model vector representing the `i`-th
coordinate functional against the model Gram (`evenDualVec_pairing`).  At the two core letters
of the head it is *not* a coordinate basis vector: `evenDualVec 0 = e₁` is one, but
`evenDualVec 1 = e₀ + e₁` is not, and no relabelling makes it one: the even head's inverse Gram
is `[[0,1],[1,1]]`, not a permutation matrix.  This is the object the board's crux (i) asks for
in place of the odd route's `sqInitialPartner : Equiv.Perm`. -/
def evenDualVec {h : ℕ} (i : Fin (MarkedCore.coreRank h)) : evenFrameModel h :=
  if (i : ℕ) = 0 then ((0, 1), 0) else
  if (i : ℕ) = 1 then ((1, 1), 0) else
  if (i : ℕ) = 2 then (0, Pi.single 0 (0, 1)) else
  if (i : ℕ) = 3 then (0, Pi.single 0 (1, 0)) else
  if ((i : ℕ) - 4) % 2 = 0 then (0, Pi.single (evenFramePlane i) (0, 1))
  else (0, Pi.single (evenFramePlane i) (1, 0))

section Dual

variable {h : ℕ} (z : evenFrameModel h)

/-- **The defining property of the dual-vector map**: pairing against `evenDualVec i` is the
`i`-th frame coordinate.  This is the even replacement for "pair with the partner index". -/
theorem evenDualVec_pairing (i : Fin (MarkedCore.coreRank h)) :
    evenFrameGramModel h (evenDualVec i) z = evenFrameCoord i z := by
  have hd0 : ∀ q : ZMod 2 × ZMod 2, headGram ((0 : ZMod 2), (1 : ZMod 2)) q = q.1 := by decide
  have hd1 : ∀ q : ZMod 2 × ZMod 2, headGram ((1 : ZMod 2), (1 : ZMod 2)) q = q.2 := by decide
  have hzL : ∀ q : ZMod 2 × ZMod 2, headGram (0 : ZMod 2 × ZMod 2) q = 0 := by decide
  unfold evenDualVec evenFrameCoord
  split_ifs with h0 h1 h2 h3 hpar
  · show headGram ((0 : ZMod 2), (1 : ZMod 2)) z.1
      + hypGram (0 : Fin (h + 1) → ZMod 2 × ZMod 2) z.2 = z.1.1
    rw [evenFrameHypGram_zero_left, hd0, add_zero]
  · show headGram ((1 : ZMod 2), (1 : ZMod 2)) z.1
      + hypGram (0 : Fin (h + 1) → ZMod 2 × ZMod 2) z.2 = z.1.2
    rw [evenFrameHypGram_zero_left, hd1, add_zero]
  · show headGram (0 : ZMod 2 × ZMod 2) z.1
      + hypGram (Pi.single 0 ((0 : ZMod 2), (1 : ZMod 2))) z.2 = (z.2 0).1
    rw [evenFrameHypGram_single, hzL]
    simp
  · show headGram (0 : ZMod 2 × ZMod 2) z.1
      + hypGram (Pi.single 0 ((1 : ZMod 2), (0 : ZMod 2))) z.2 = (z.2 0).2
    rw [evenFrameHypGram_single, hzL]
    simp
  · show headGram (0 : ZMod 2 × ZMod 2) z.1
      + hypGram (Pi.single (evenFramePlane i) ((0 : ZMod 2), (1 : ZMod 2))) z.2 = _
    rw [evenFrameHypGram_single, hzL]
    simp
  · show headGram (0 : ZMod 2 × ZMod 2) z.1
      + hypGram (Pi.single (evenFramePlane i) ((1 : ZMod 2), (0 : ZMod 2))) z.2 = _
    rw [evenFrameHypGram_single, hzL]
    simp

/-- The dual vector at `x₀` is the second head basis vector; the partner index is `1`. -/
theorem evenDualVec_zero :
    evenDualVec (0 : Fin (MarkedCore.coreRank h)) = (((0 : ZMod 2), (1 : ZMod 2)), 0) := by
  unfold evenDualVec
  rw [if_pos (MarkedCore.coreVal_zero h)]

/-- **The crux entry**: the dual vector at `x₁` is `e₀ + e₁`, not a coordinate basis vector. -/
theorem evenDualVec_one :
    evenDualVec (1 : Fin (MarkedCore.coreRank h)) = (((1 : ZMod 2), (1 : ZMod 2)), 0) := by
  unfold evenDualVec
  rw [if_neg (by rw [MarkedCore.coreVal_one]; omega), if_pos (MarkedCore.coreVal_one h)]

end Dual

/-! ### §1.5 The model's Labute vector

The diagonal `z ↦ b z z` of the model Gram is the frame coordinate at `x₀` (the head is not
alternating and the planes are), so the vector representing it, the Labute vector, is
`evenDualVec 0 = e₁`, which lives at **frame index 1**.  That single fact is what makes the
parity half of both even bridge tables automatic. -/

/-- The model's Labute vector, `e₁`. -/
def evenFrameKappaVec (h : ℕ) : evenFrameModel h :=
  evenDualVec (0 : Fin (MarkedCore.coreRank h))

@[simp] theorem evenFrameKappaVec_eq (h : ℕ) :
    evenFrameKappaVec h = (((0 : ZMod 2), (1 : ZMod 2)), 0) := evenDualVec_zero

/-- The model Gram is not alternating: its diagonal is the `x₀` coordinate. -/
theorem evenFrameGramModel_self {h : ℕ} (z : evenFrameModel h) :
    evenFrameGramModel h z z = evenFrameCoord 0 z := by
  rw [evenFrameGramModel, evenFrameHypGram_self, headGram_self, evenFrameCoord_zero, add_zero]

/-- **The Labute identity in the model**: `evenFrameKappaVec` represents the diagonal. -/
theorem evenFrameKappaVec_labute {h : ℕ} (z : evenFrameModel h) :
    evenFrameGramModel h (evenFrameKappaVec h) z = evenFrameGramModel h z z := by
  rw [evenFrameKappaVec, evenDualVec_pairing, evenFrameGramModel_self]

/-- The Labute vector is isotropic, as the even degree demands. -/
theorem evenFrameKappaVec_self (h : ℕ) :
    evenFrameGramModel h (evenFrameKappaVec h) (evenFrameKappaVec h) = 0 := by
  rw [evenFrameGramModel_self, evenFrameKappaVec_eq, evenFrameCoord_zero]

/-- The Labute vector is nonzero. -/
theorem evenFrameKappaVec_ne_zero (h : ℕ) : evenFrameKappaVec h ≠ 0 := by
  intro hzero
  have := congrArg (evenFrameCoord (1 : Fin (MarkedCore.coreRank h))) hzero
  rw [evenFrameKappaVec_eq, evenFrameCoord_one, evenFrameCoord_zero_vec] at this
  exact one_ne_zero this

/-- **The κ row of both even bridge tables**: the model's Labute vector has frame coordinate `1`
at the letter `x₁` and `0` at every other letter. -/
theorem evenFrameCoord_kappaVec {h : ℕ} (i : Fin (MarkedCore.coreRank h)) :
    evenFrameCoord i (evenFrameKappaVec h) = if (i : ℕ) = 1 then 1 else 0 := by
  rw [evenFrameKappaVec_eq]
  refine evenIndex_cases
    (P := fun i ↦ evenFrameCoord i (((0 : ZMod 2), (1 : ZMod 2)), 0) = if (i : ℕ) = 1 then 1 else 0)
    ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [evenFrameCoord_zero, if_neg (by rw [MarkedCore.coreVal_zero]; omega)]
  · rw [evenFrameCoord_one, if_pos (MarkedCore.coreVal_one h)]
  · rw [evenFrameCoord_two, if_neg (by rw [MarkedCore.coreVal_two]; omega)]
    rfl
  · rw [evenFrameCoord_three, if_neg (by rw [MarkedCore.coreVal_three]; omega)]
    rfl
  · intro j
    rw [evenFrameCoord_handleU, if_neg (by rw [MarkedCore.handleIdxU_val]; omega)]
    rfl
  · intro j
    rw [evenFrameCoord_handleV, if_neg (by rw [MarkedCore.handleIdxV_val]; omega)]
    rfl

/-! ## §2 The even Witt adaptation

The odd route's `frattiniFrameAdaptedModelEquiv` refines the `⟨1⟩ ⊥ H^{⊥m}` normal form twice:
it puts the Labute vector in the `⟨1⟩` slot and the `ω` vector on the diagonal of the first
hyperbolic plane.  The even analogue needs only the *first* refinement, and gets it for free:
`FieldDataEven.headSplitEquiv` already sends the Labute vector to the head coordinates `(0,1)`,
which by §1.5 is the model's own Labute vector.  The `ω` vector is placed not by a second Witt
step but by the class identity of §4.2; see the discussion there.

Nothing here is even-core-specific; it is the missing even twin of
`frattiniFrameAdaptedModelEquiv`, stated for an arbitrary finite `𝔽₂` cup–Bockstein form. -/

/-- **The even adapted normal form.**  A nondegenerate `𝔽₂` cup–Bockstein form of order
`2 ^ (2h + 4)` whose Labute vector `e` is isotropic and nonzero is isometric to the even
coordinate model, *by an isometry carrying `e` to the model's Labute vector*, that is, to the
frame coordinate vector supported at the letter `x₁`.

The plane count `h + 1` is pinned by counting, exactly as in
`FieldDataEven.exists_cupFormK_normalForm_even`; the extra content over that theorem is the
placement of `e`, which is what the frame construction consumes. -/
theorem evenFrameAdaptedModelEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {b : W → W → ZMod 2} (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e : W}
    (he : ∀ w, b e w = b w w) (he0 : b e e = 0) (hne : e ≠ 0)
    {h : ℕ} (hcard : Nat.card W = 2 ^ (2 * h + 4)) :
    ∃ Φ : W ≃ₗ[ZMod 2] evenFrameModel h,
      (∀ x y, b x y = evenFrameGramModel h (Φ x) (Φ y)) ∧ Φ e = evenFrameKappaVec h := by
  obtain ⟨f, hf⟩ := exists_diag_eq_one hnd he hne
  obtain ⟨m, ψ, hψ⟩ :=
    exists_symplectic_equiv (fun x y : headPerp b hb f e ↦ b (x : W) (y : W))
      (isSymplectic_headPerp hb hnd he he0 hf)
  set φ₀ := headSplitEquiv hb he he0 hf with hφ₀
  set Φ := φ₀.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr ψ) with hΦ
  -- the plane count, by counting
  have hm : m = h + 1 := by
    have h1 : Nat.card W = 4 * 4 ^ m := by
      rw [Nat.card_congr Φ.toEquiv, Nat.card_prod]
      simp
    have h2 : (2 : ℕ) ^ (2 + 2 * m) = 2 ^ (2 * h + 4) := by
      rw [← hcard, h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hm
  -- the Labute vector lands in the head, at the second head coordinate
  have hef : b e f = 1 := head_offDiag he hf
  have hfe : b f e = 1 := by rw [hb.symm]; exact hef
  have hφe : φ₀ e = (((0 : ZMod 2), (1 : ZMod 2)), 0) := by
    refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext ?_)
    · show b e e = 0
      exact he0
    · show b f e + b e e = 1
      rw [hfe, he0, add_zero]
    · show e + (b e e) • f + (b f e + b e e) • e = (0 : W)
      simp only [he0, hfe, zero_smul, add_zero, one_smul]
      exact GQ2.Dyadic.Certificates.module_zmod2_two_torsion e
  refine ⟨Φ, fun x y ↦ ?_, ?_⟩
  · have hx : (φ₀ x).1.1 • f + (φ₀ x).1.2 • e + ((φ₀ x).2 : W) = x := φ₀.left_inv x
    have hy : (φ₀ y).1.1 • f + (φ₀ y).1.2 • e + ((φ₀ y).2 : W) = y := φ₀.left_inv y
    show b x y = headGram (φ₀ x).1 (φ₀ y).1 + hypGram (ψ (φ₀ x).2) (ψ (φ₀ y).2)
    rw [← hψ]
    calc b x y = b ((φ₀ x).1.1 • f + (φ₀ x).1.2 • e + ((φ₀ x).2 : W))
          ((φ₀ y).1.1 • f + (φ₀ y).1.2 • e + ((φ₀ y).2 : W)) := by rw [hx, hy]
      _ = headGram (φ₀ x).1 (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) :=
          headSplit_gram hb he he0 hf _ _ _ _
  · show ((φ₀ e).1, ψ (φ₀ e).2) = evenFrameKappaVec h
    rw [hφe, evenFrameKappaVec_eq, map_zero]

/-! ## §3 The row-relative exact cyclotomic lift

The odd route's `frattiniFrameExactLift` consumes `SharpExactLevelFibreLiftSupply`, which asks
for an exact lift at *every* target of `ℤ₂ˣ` and is available only when `chiCycKTwo` is
surjective, which is false at even degree.  This is the same statement against the row-relative supply
`StageGeneric.RowExactLevelFibreLiftSupply` of `StageAbstraction.lean` §2.1(b), which is all the
even lane can have and all it needs: lifting is only ever performed at a row value. -/

section EvenField

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenFrameScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenFrameContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **Exact cyclotomic-value lifting within a Frattini coset, at a row value.**  If the mod-four
and `ω` classes evaluate on `g'` to the corresponding data of the row target `v i`, the
row-relative sharp supply replaces `g'` by an element with cyclotomic value exactly `v i` in the
same Frattini coset. -/
theorem evenFrameExactLift {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
    (supply : RowExactLevelFibreLiftSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (i : Fin n) (g' : maxProPQuotient 2 (GalK K))
    (h4 : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g' =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))))
    (h8 : frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g' =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i)))) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = v i ∧
        levelMk (maxProPQuotient 2 (GalK K)) 2 x =
          levelMk (maxProPQuotient 2 (GalK K)) 2 g' := by
  have hshadow : SqCyclotomicStageTuple.sharpChiLevel (chiCycKTwo (K := K)) 2 (le_refl 2)
      (levelMk (maxProPQuotient 2 (GalK K)) 2 g') =
        Units.map (PadicInt.toZModPow 3).toMonoidHom (v i) := by
    apply unitsModEightData_injective
    rw [frattiniFrame_sharpShadow_data, h4, h8]
    unfold unitsModEightData
    rw [frattiniFrame_unitsMap_cast]
  obtain ⟨x, hx1, hx2⟩ := supply.lift 2 (le_refl 2) i
    (levelMk (maxProPQuotient 2 (GalK K)) 2 g') hshadow
  exact ⟨x, hx1, hx2.symm⟩

/-! ## §4 The frame assembly

The core-agnostic half of the odd supply's proof body, with the row table left as a parameter.
§4.1 takes an adapted coordinate system plus the two match tables and produces the frame; §4.2
supplies the match tables from a single class identity, which is the shape both even rows use. -/

/-- The pairing appearing in the even `IsCupAdapted`: the field cup form on the degree-one
classes of two mod-two characters of `G_K(2)`.  Identical to the odd route's, which is why the
`P` parameter of `Frame.IsCupAdapted` was introduced. -/
def evenFramePairing
    (c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    ZMod 2 :=
  frattiniFrameCup (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
    (SqCyclotomicFrattiniFrame.characterClass (K := K) d)

omit [T2Space (GalK K)] in
/-- **Composition seam with EV-3d**: the pairing is the field cup form spelling that ticket's
realization endpoints are stated against, definitionally. -/
theorem evenFramePairing_fieldCup
    (c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    evenFramePairing (K := K) c d =
      FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) :=
  rfl

omit [T2Space (GalK K)] in
/-- **The even-degree twin of `frattiniFrameCup_kappa_self`.**  At even degree the Labute vector
of the transported cup form is isotropic.  This is the `𝔽₂` equation whose odd-degree value is
`1`, and it is a parity corollary, not a fresh arithmetic input
(`FieldDataEven.cupFormK_kappa_self_zero`). -/
theorem evenFrameCup_kappa_self (hev : Even (Module.finrank ℚ_[2] K)) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (cyclotomicModFourClassKTwo (K := K)) = 0 := by
  unfold frattiniFrameCup
  rw [h1MaxProTwoEquivGalK_cyclotomicModFourClassKTwo, cyclotomicModFourClassK_eq_kappaK]
  exact FieldDataEven.cupFormK_kappa_self_zero K hev

/-- **The frame assembly.**  Given an adapted coordinate system on `H¹(G_K(2), 𝔽₂)` whose
mod-four and `ω` classes have the row table's mod-four parities and `ω` values as coordinates,
the dual family of the coordinates, corrected to exact cyclotomic values inside its Frattini
cosets, is a `StageGeneric.Frame` at the row table, cup-adapted at the even Gram.

Core-agnostic: the row table `v` and the two match tables are parameters, so the `M` clone
consumes this theorem unchanged. -/
theorem evenFrame_of_adapted {h : ℕ} (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)))
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h)
    (hGram : ∀ x y, frattiniFrameCup x y = evenFrameGramModel h (Φ x) (Φ y))
    (supply : RowExactLevelFibreLiftSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (hpar : ∀ i, evenFrameCoord i (Φ (cyclotomicModFourClassKTwo (K := K))) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))))
    (homega : ∀ i, evenFrameCoord i (Φ (cyclotomicModEightOmegaClassKTwo (K := K))) =
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i)))) :
    ∃ F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) := by
  classical
  haveI := hfin
  -- realize the adapted coordinate functionals by group elements
  choose gens' hgens' using fun i : Fin (MarkedCore.coreRank h) ↦
    frattiniFrameEval_realizable (K := K) hfin ((evenFrameCoordL i).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (MarkedCore.coreRank h))
      (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) = evenFrameCoord i (Φ x) := fun i x ↦ hgens' i x
  -- exact cyclotomic values in each dual Frattini coset
  have hmatch4 : ∀ i : Fin (MarkedCore.coreRank h),
      frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))) := by
    intro i
    rw [hD i]
    exact hpar i
  have hmatch8 : ∀ i : Fin (MarkedCore.coreRank h),
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i))) := by
    intro i
    rw [hD i]
    exact homega i
  choose gens hχ hlevel using fun i : Fin (MarkedCore.coreRank h) ↦
    evenFrameExactLift supply i (gens' i) (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (MarkedCore.coreRank h))
      (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) = evenFrameCoord i (Φ x) := fun i x ↦
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, hχ, ?_⟩, ?_⟩
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
      refine evenFrameCoord_eq_zero _ fun i ↦ ?_
      rw [← hD2 i]
      exact hvanish i
    have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
      have hs := congrArg Φ.symm hΦ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    apply hcne
    apply MonoidHom.ext
    intro fq
    obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 fq
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
  · -- cup adaptation, against the extended even Gram
    intro c d
    show frattiniFrameCup (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
        (SqCyclotomicFrattiniFrame.characterClass (K := K) d) =
      evenFrameGram h (fun i j ↦ Multiplicative.toAdd (c (gens i)) *
        Multiplicative.toAdd (d (gens j)))
    rw [hGram, ← evenFrameGram_modelCoord]
    congr 1
    funext i j
    rw [← hD2 i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
      ← hD2 j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
      frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]

/-! ### §4.2 The `ω`-class pin

The odd route places the `ω` vector `τ` by a second Witt refinement, putting it on the diagonal
of the first hyperbolic plane.  The even route cannot do that and does not need to: by §1.5 the
mod-four class `κ` is forced to the frame coordinate vector supported at `x₁`, and both even row
tables have their `ω` values supported at a single letter as well.  So the whole `ω` table is
determined by one scalar `c` together with the *class* identity `τ = c • κ`, and the frame
construction reduces to two purely arithmetic tables on the row values.

Whether that class identity holds is a fact about `K`, not a free choice: `c` must be the `ω`
value of the row table's nontrivial entry.  The row file states it and discusses what it costs. -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- If the `ω` class is a scalar multiple of the mod-four class, every `ω` coordinate is that
scalar times the corresponding mod-four coordinate. -/
theorem evenFrameCoord_omega_of_pin {h : ℕ}
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h) (c : ZMod 2)
    (hpin : cyclotomicModEightOmegaClassKTwo (K := K) =
      c • cyclotomicModFourClassKTwo (K := K))
    (i : Fin (MarkedCore.coreRank h)) :
    evenFrameCoord i (Φ (cyclotomicModEightOmegaClassKTwo (K := K))) =
      c * evenFrameCoord i (Φ (cyclotomicModFourClassKTwo (K := K))) := by
  rw [hpin, map_smul, evenFrameCoord_smul]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The `ω`-class pin, from a pointwise condition on cyclotomic values.**  The class identity
`τ = c • κ` is exactly the assertion that `ω` and `c · parity` agree on every cyclotomic value,
which is a checkable statement about the mod-eight image of `chiCycKTwo`, and hence about which
`α` belongs to `K`.  This is the form the row files discharge. -/
theorem evenFrameOmegaPin_of_pointwise (c : ZMod 2)
    (hpt : ∀ g : maxProPQuotient 2 (GalK K),
      Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (chiCycKTwo (K := K) g))) =
        c * Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g)))) :
    cyclotomicModEightOmegaClassKTwo (K := K) =
      c • cyclotomicModFourClassKTwo (K := K) := by
  refine eq_of_sub_eq_zero (frattiniFrameEval_eq_zero _ fun g ↦ ?_)
  have hsub : frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K) -
        c • cyclotomicModFourClassKTwo (K := K)) g =
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g -
        c * frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g := by
    simpa using map_sub (frattiniFrameEvalL (K := K) g)
      (cyclotomicModEightOmegaClassKTwo (K := K)) (c • cyclotomicModFourClassKTwo (K := K))
  rw [hsub, frattiniFrameEval_modEight, frattiniFrameEval_modFour, hpt g, sub_self]

/-- **The even frame supply, from a row table and an `ω` pin.**  This is the theorem both even
rows instantiate: it consumes only

* the even-degree binder `[K:ℚ₂] = 2h + 2`;
* the ramified-`i` binder in the form `κ ≠ 0`;
* the EV-4a row-relative exact lift supply at the row table;
* the `ω`-class pin `τ = c • κ`; and
* two arithmetic tables on the row values: the mod-four parities must be the indicator of the
  letter `x₁`, and the mod-eight `ω` values must be `c` times that indicator.

Everything else, including the placement of `κ` at `x₁`, is forced by the model. -/
theorem evenFrame_of_kappaPin {h : ℕ} (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (supply : RowExactLevelFibreLiftSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (c : ZMod 2)
    (hpin : cyclotomicModEightOmegaClassKTwo (K := K) =
      c • cyclotomicModFourClassKTwo (K := K))
    (hpar : ∀ i : Fin (MarkedCore.coreRank h),
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (v i))) = if (i : ℕ) = 1 then 1 else 0)
    (homega : ∀ i : Fin (MarkedCore.coreRank h),
      Multiplicative.toAdd (unitsModEightOmega
        (Units.map (PadicInt.toZModPow 3).toMonoidHom (v i))) =
          c * (if (i : ℕ) = 1 then 1 else 0)) :
    ∃ F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) := by
  classical
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * h + 4) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K), hdeg,
      show 2 * h + 2 + 2 = 2 * h + 4 from by omega]
  obtain ⟨Φ, hGram, hΦkappa⟩ :=
    evenFrameAdaptedModelEquiv (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (evenFrameCup_kappa_self (K := K) ⟨h + 1, by omega⟩) hkappa hcard
  have hkap : ∀ i : Fin (MarkedCore.coreRank h),
      evenFrameCoord i (Φ (cyclotomicModFourClassKTwo (K := K))) =
        if (i : ℕ) = 1 then 1 else 0 := by
    intro i
    rw [hΦkappa, evenFrameCoord_kappaVec]
  refine evenFrame_of_adapted v hfin Φ hGram supply (fun i ↦ ?_) (fun i ↦ ?_)
  · rw [hkap i, hpar i]
  · rw [evenFrameCoord_omega_of_pin Φ c hpin i, hkap i, homega i]

end EvenField

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins

Every public declaration of this file.  The linear-algebra layer (§1–§2) is std-3; the field-level
layer (§3–§4) additionally carries whatever its committed inputs carry, which is a subset of what
the odd-degree template supply `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` prints. -/

#print axioms GQ2.Dyadic.StageGeneric.evenFrameGramModel
#print axioms GQ2.Dyadic.StageGeneric.evenFrameHypGram_self
#print axioms GQ2.Dyadic.StageGeneric.evenFrameHypGram_zero_left
#print axioms GQ2.Dyadic.StageGeneric.evenFrameHypGram_single
#print axioms GQ2.Dyadic.StageGeneric.evenFramePlane
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_zero
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_one
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_two
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_three
#print axioms GQ2.Dyadic.StageGeneric.evenFramePlane_val
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_handleU
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_val_handleV
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_zero
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_one
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_two
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_three
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_handleU
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_handleV
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_add
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_zero_vec
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_smul
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoordL
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoordL_apply
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_eq_zero
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoreIdx
#print axioms GQ2.Dyadic.StageGeneric.evenFrameGram
#print axioms GQ2.Dyadic.StageGeneric.evenFrameGram_expand
#print axioms GQ2.Dyadic.StageGeneric.evenFrameGram_nGram
#print axioms GQ2.Dyadic.StageGeneric.evenFrameGram_modelCoord
#print axioms GQ2.Dyadic.StageGeneric.evenDualVec
#print axioms GQ2.Dyadic.StageGeneric.evenDualVec_pairing
#print axioms GQ2.Dyadic.StageGeneric.evenDualVec_zero
#print axioms GQ2.Dyadic.StageGeneric.evenDualVec_one
#print axioms GQ2.Dyadic.StageGeneric.evenFrameKappaVec
#print axioms GQ2.Dyadic.StageGeneric.evenFrameKappaVec_eq
#print axioms GQ2.Dyadic.StageGeneric.evenFrameGramModel_self
#print axioms GQ2.Dyadic.StageGeneric.evenFrameKappaVec_labute
#print axioms GQ2.Dyadic.StageGeneric.evenFrameKappaVec_self
#print axioms GQ2.Dyadic.StageGeneric.evenFrameKappaVec_ne_zero
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_kappaVec
#print axioms GQ2.Dyadic.StageGeneric.evenFrameAdaptedModelEquiv
#print axioms GQ2.Dyadic.StageGeneric.evenFrameExactLift
#print axioms GQ2.Dyadic.StageGeneric.evenFramePairing
#print axioms GQ2.Dyadic.StageGeneric.evenFramePairing_fieldCup
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCup_kappa_self
#print axioms GQ2.Dyadic.StageGeneric.evenFrame_of_adapted
#print axioms GQ2.Dyadic.StageGeneric.evenFrameCoord_omega_of_pin
#print axioms GQ2.Dyadic.StageGeneric.evenFrameOmegaPin_of_pointwise
#print axioms GQ2.Dyadic.StageGeneric.evenFrame_of_kappaPin
