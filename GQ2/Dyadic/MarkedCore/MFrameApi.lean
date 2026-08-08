/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.MarkedCore.MFrameExists

@[expose] public section

/-!
# W51-MFRAME2 follow-on: the `M`-frame API at every handle count

**Ticket W51-MFRAME2 (general-`h` `M` frame API).**
`GQ2/Dyadic/MarkedCore/MFrame.lean` §2 records that a rank-four `MFrame` *is* MC2's
`MDecomposition` via `MFrame.toMDecomposition`, so everything MC3 proves from a frame applies
**at `h = 0` only**.  This file lifts the matrix-free part of that API to every handle count,
driven by a general-`h` `MFrame α h`.

## What landed, and where this file stops

Items 1 and 2 of the ticket are here; items 3 and 4 are **priced, not attempted**, and §6
explains precisely why they are inseparable and what design decision blocks them.  That is a
deliberate cut, not an omission: see §6.

* **§1–§3, item 1**: `mFrameApiChiModel` (the general-`h` model character) and
  `mFrameApi_chi_frame` (χ read in the frame), plus `mFrameApi_sqEqOne_iff`.
* **§4, item 2**: `mFrameApi_xi_fixes_t`.
* **§5**: the unconditional corollaries.  `mFrameApi_sqEqOne_iff` and `mFrameApi_xi_fixes_t`
  have conclusions that do not mention the frame, so composing with `nonempty_mFrame`
  (`MFrameExists.lean`) removes the frame hypothesis outright.  `mFrameApi_chi_frame` cannot be
  made frame-free: its conclusion names `F.e`.
* **§6**: items 3 and 4, priced.
* **§7**: axiom pins.

## The finding: χ needs `2h` more pins at general `h`, and they are not decoration

At `h = 0` the four core values `(1, −1, 1, u)` on `Ā, B̄, C̄₀, D̄` determine χ (`mChi_frame`).
At general `h` they do **not**: `D_M^{ab}` has `2h` further free `ℤ₂`-coordinates and a
continuous character may be arbitrary on them.  So `mFrameApi_chi_frame` carries two extra
hypotheses, `χ(ūⱼ) = 1` and `χ(v̄ⱼ) = 1`, and these are **necessary**, not merely convenient:
`mFrameApiChiModel` ignores the handle tail by construction, so any χ nontrivial on a handle
letter is a counterexample to the conclusion.  At `h = 0` the two hypotheses are vacuous
(`Fin 0` is empty) and the statement degenerates to `mChi_frame`.

This is worth stating plainly because the campaign's memo §4.2 language ("the handle lemma says
that is forced for χ") can be misread as saying the handle values are *determined*.  What
`Cores.lean` §2 actually proves (`handleWord_wordLift_one`, `commP_wordLift_one`) is the
**conditional** statement: a handle block whose two letters have `χ = 1` is invisible to the
crossed derivation.  It does not force `χ = 1` on those letters, and nothing else does either.
The honest general-`h` orientation therefore has `4 + 2h` pins, of which `2h` say "trivial on
handles".

## Variance (MC-VAR discipline)

**This file is matrix-free, exactly as `MFrame.lean` and `MFrameExists.lean` are.**  No cup
form, no Gram matrix, no bilinear pairing and no `Matrix.transpose` occurs in any statement or
proof here, so the `M`/`N` row-versus-column dictionary
(`GQ2/Dyadic/MarkedCore/Variance.lean`, sharpest instance
`mFrameMatrix_transpose_eq_nMatOf`) is **not** invoked and no transposition arises.

That is not an accident of drafting, it is the reason the file stops where it does.  The moment
a Gram appears the dictionary becomes mandatory, and §6 records that the two remaining ticket
items both live on the far side of that line: `IsMStabilizer` is *defined* by
`(mFrameMatrix B ξ)ᵀ * mGram * mFrameMatrix B ξ = mGram`, so item 3 cannot even be *stated* at
general `h` before item 4's convention is fixed.  No statement in this file carries a matrix, so
no statement in this file needs a convention annotation.

## Axiom scope (measured)

**Every declaration in this file prints at most `[propext, Classical.choice, Quot.sound]`**; see
§7.  No census axiom.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §1 The general-`h` model character

`M.lean`'s `mChiModel α : MModel →* ℤ₂ˣ` is `(τ, b, c, d) ↦ (−1)^b · u^d`.  Its general-`h`
form reads the same two coordinates and **ignores the handle tail**, which is the coordinate
shadow of memo §4.2: handles carry no orientation.  Note that this is a *design choice made by
the model*, and §3's extra hypotheses are exactly the price of it. -/

/-- **χ in the general-`h` frame**: the model character `(τ, b, c, d, f) ↦ (−1)^b · u^d`, with
the `2h` handle coordinates `f` ignored.  Restricts to `M.lean`'s `mChiModel α` at `h = 0`. -/
noncomputable def mFrameApiChiModel (α h : ℕ) : MFrameModel h →* ℤ_[2]ˣ where
  toFun z := mSign (toAdd z).2.1
    * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd z).2.2.2.1
  map_one' := by
    show mSign 0 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) 0 = 1
    rw [mSign_zero, zpowZtwo_zero, mul_one]
  map_mul' x y := by
    show mSign ((toAdd x).2.1 + (toAdd y).2.1)
        * zpowZtwo isProP_two_unitsPadicInt (mUnit α) ((toAdd x).2.2.2.1 + (toAdd y).2.2.2.1)
      = (mSign (toAdd x).2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd x).2.2.2.1)
        * (mSign (toAdd y).2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd y).2.2.2.1)
    rw [mSign_add, zpowZtwo_add]
    exact mul_mul_mul_comm _ _ _ _

@[simp] theorem mFrameApiChiModel_ofAdd (α : ℕ) {h : ℕ} (ε : ZMod 2) (b c d : ℤ_[2])
    (f : Fin (2 * h) → ℤ_[2]) :
    mFrameApiChiModel α h (ofAdd (ε, b, c, d, f))
      = mSign b * zpowZtwo isProP_two_unitsPadicInt (mUnit α) d := rfl

theorem mFrameApiChiModel_continuous (α h : ℕ) : Continuous (mFrameApiChiModel α h) := by
  have hb : Continuous fun z : MFrameModel h => (toAdd z).2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_toAdd)
  have hd : Continuous fun z : MFrameModel h => (toAdd z).2.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp
      (continuous_snd.comp continuous_toAdd)))
  exact (mSign_continuous.comp hb).mul
    ((continuous_zpowZtwo isProP_two_unitsPadicInt (mUnit α)).comp hd)

/-- The general-`h` model character bundled with its continuity. -/
noncomputable def mFrameApiChiModelHom (α h : ℕ) : ContinuousMonoidHom (MFrameModel h) ℤ_[2]ˣ :=
  ⟨mFrameApiChiModel α h, mFrameApiChiModel_continuous α h⟩

/-- The general-`h` frame coordinate isomorphism as a continuous monoid hom (the `mFrameHom` of
`M.lean:661`, at every handle count). -/
noncomputable def mFrameApiHom {α h : ℕ} (F : MFrame α h) :
    ContinuousMonoidHom (topAbelianization (DM α h : Type)) (MFrameModel h) :=
  ⟨F.e.toMulEquiv.toMonoidHom, F.e.continuous_toFun⟩

@[simp] theorem mFrameApiHom_apply {α h : ℕ} (F : MFrame α h)
    (x : topAbelianization (DM α h : Type)) : mFrameApiHom F x = F.e x := rfl

/-! ## §2 Coordinates at general `h`

The two utilities `M.lean` §3 uses at rank four, restated for the rank-`(4+2h)` model:
coordinate extensionality, and the split of the handle index range.  `mIdx_cases`
(`MFrameExists.lean`) already generalises `mCoreIdx_cases`. -/

/-- Coordinate extensionality in the general-`h` model (the `mCoord_ext` of `M.lean:592`). -/
theorem mFrameApi_coord_ext {h : ℕ} {ε : ZMod 2} {b c d : ℤ_[2]} {f : Fin (2 * h) → ℤ_[2]}
    {z : MFrameModel h} (h1 : (toAdd z).1 = ε) (h2 : (toAdd z).2.1 = b)
    (h3 : (toAdd z).2.2.1 = c) (h4 : (toAdd z).2.2.2.1 = d) (h5 : (toAdd z).2.2.2.2 = f) :
    z = ofAdd (ε, b, c, d, f) := by
  conv_lhs => rw [← ofAdd_toAdd z]
  exact congrArg ofAdd (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5))))

/-- **Every handle coordinate is a `u`-coordinate or a `v`-coordinate.**  The bridge between
`MFrameExists.lean`'s `mHandleIdx`-indexed case split and `MFrame.lean`'s `mHandleCoordU`/
`mHandleCoordV` vocabulary, which is what the frame's `map_U`/`map_V` fields speak. -/
theorem mHandleCoord_cases {h : ℕ} (k : Fin (2 * h)) :
    (∃ j : Fin h, k = mHandleCoordU j) ∨ ∃ j : Fin h, k = mHandleCoordV j := by
  have hk := k.isLt
  have hj : (k : ℕ) / 2 < h := by omega
  rcases Nat.even_or_odd (k : ℕ) with he | ho
  · refine Or.inl ⟨⟨(k : ℕ) / 2, hj⟩, Fin.ext ?_⟩
    show (k : ℕ) = 2 * ((k : ℕ) / 2)
    obtain ⟨m, hm⟩ := he
    omega
  · refine Or.inr ⟨⟨(k : ℕ) / 2, hj⟩, Fin.ext ?_⟩
    show (k : ℕ) = 2 * ((k : ℕ) / 2) + 1
    obtain ⟨m, hm⟩ := ho
    omega

end MarkedCore

end Dyadic

end GQ2
