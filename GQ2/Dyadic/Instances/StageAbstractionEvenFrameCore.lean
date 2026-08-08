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
Gram `[[0,1],[1,1]]`, so the odd route's `sqInitialPartner : Equiv.Perm` — legitimate there
because `⟨1⟩ ⊥ H ⊥ H^{⊥h}` pairs each coordinate basis vector with exactly one other — has no
even analogue.  §1.4 replaces it by `evenDualVec`, sending a frame index `i` to the *vector*
representing the `i`-th coordinate functional:

| frame index | letter | `evenDualVec` | a basis vector? |
|---|---|---|---|
| `0` | `x₀` | `e₁` | yes (the partner index `1`) |
| `1` | `x₁` | `e₀ + e₁` | **no** — this is the crux |
| `2`, `3` | `σ`, `x₂` | `e₃`, `e₂` | yes (the `(2,3)` plane swaps) |
| `U j`, `V j` | handles | `e_{V j}`, `e_{U j}` | yes (the handle planes swap) |

Only the head is non-permutational, and only at index `1`.  The pay-off is §1.5: the model's
Labute vector — the vector representing the diagonal `z ↦ b z z` — is `evenDualVec 0`, and it is
`e₁`, so it sits at **frame index 1**.  That is exactly the index at which both even row tables
carry their nontrivial cyclotomic value, which is why the parity half of the bridge table
matches for free.

## What is proved and what is carried

Proved here: all of the above, sorry-free, and the assembly of a
`StageGeneric.Frame` with `Frame.IsCupAdapted` from an adapted coordinate system.

Carried as hypotheses (never as admitted goals), because they are the honest even-degree
inputs and are owned by other tickets:

* `RowExactLevelFibreLiftSupply v _ chiCycKTwo` — ticket EV-4a.  At even degree `chiCycKTwo`
  is *not* surjective, so the odd route's `SharpExactLevelFibreLiftSupply` is unavailable and
  the row-relative weakening of `StageAbstraction.lean` §2.1(b) is what the lane must use.
* `cyclotomicModFourClassKTwo ≠ 0` — the campaign's standing ramified-`i` binder.
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

/-- The `x₁` coordinate is the second head coordinate — the index at which the model's Labute
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
plane per handle, zero across.  This is the `gram` parameter of `Frame.IsCupAdapted`. -/
def evenFrameGram (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) : ZMod 2 :=
  (∑ a : Fin 4, ∑ b : Fin 4, MarkedCore.nGram a b * M (evenFrameCoreIdx a) (evenFrameCoreIdx b))
    + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
        + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j))

/-- The adapter written out: `MarkedCore.nGram`'s five nonzero entries are `(0,0)`, `(0,1)`,
`(1,0)`, `(2,3)`, `(3,2)`. -/
theorem evenFrameGram_expand (h : ℕ)
    (M : Fin (MarkedCore.coreRank h) → Fin (MarkedCore.coreRank h) → ZMod 2) :
    evenFrameGram h M = (M 0 0 + (M 0 1 + M 1 0)) + (M 2 3 + M 3 2)
      + ∑ j : Fin h, (M (MarkedCore.handleIdxU j) (MarkedCore.handleIdxV j)
          + M (MarkedCore.handleIdxV j) (MarkedCore.handleIdxU j)) := by
  simp only [evenFrameGram, evenFrameCoreIdx, Fin.sum_univ_four, MarkedCore.nGram,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  ring

/-- **The dual-vector map.**  `evenDualVec i` is the model vector representing the `i`-th
coordinate functional against the model Gram (`evenDualVec_pairing`).  At the two core letters
of the head it is *not* a coordinate basis vector: `evenDualVec 0 = e₁` is one, but
`evenDualVec 1 = e₀ + e₁` is not, and no relabelling makes it one — the even head's inverse Gram
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

/-- The dual vector at `x₀` is the second head basis vector — the partner index is `1`. -/
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
alternating and the planes are), so the vector representing it — the Labute vector — is
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

end

end GQ2.Dyadic.StageGeneric
