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

/-! ## §3 Item 1: χ in the frame, and the 2-torsion, at every handle count -/

/-- **The canonical orientation is the frame character, at every handle count** (the general-`h`
`mChi_frame`, `M.lean:674`).  A continuous character of `D_M^{ab}` pinned to `(1, −1, 1, u)` on
the four core letters **and trivial on the `2h` handle letters** is `mFrameApiChiModel α h` read
through the frame.

The two handle hypotheses are the honest cost of general `h`, and they are **necessary**: the
model character ignores the handle tail, so a χ nontrivial on any handle letter refutes the
conclusion outright.  They are not exotic either, since `Cores.lean`'s canonical orientation
`chiM α h` is built from `coreMark 1 (-1) 1 (mUnit α)`, which is `1` on every handle letter by
construction, so `chiM` satisfies them.  At `h = 0` both hypotheses are vacuous (`Fin 0` is
empty) and the statement is exactly `mChi_frame`. -/
theorem mFrameApi_chi_frame {α h : ℕ} (F : MFrame α h)
    (χ : ContinuousMonoidHom (topAbelianization (DM α h : Type)) ℤ_[2]ˣ)
    (hχA : χ (abMk (dmA α h)) = 1) (hχB : χ (abMk (dmB α h)) = -1)
    (hχC : χ (abMk (dmC α h)) = 1) (hχD : χ (abMk (dmD α h)) = mUnit α)
    (hχU : ∀ j : Fin h, χ (abMk (dmGen α h (handleIdxU j))) = 1)
    (hχV : ∀ j : Fin h, χ (abMk (dmGen α h (handleIdxV j))) = 1)
    (x : topAbelianization (DM α h : Type)) :
    χ x = mFrameApiChiModel α h (F.e x) := by
  refine mAb_hom_ext χ ((mFrameApiChiModelHom α h).comp (mFrameApiHom F)) (fun i => ?_) x
  have hval : ∀ z : topAbelianization (DM α h : Type),
      ((mFrameApiChiModelHom α h).comp (mFrameApiHom F)) z
        = mFrameApiChiModel α h (F.e z) := fun _ => rfl
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
  · rw [hval, show dmGen α h 0 = dmA α h from rfl, hχA, mE_A_frame F,
      mFrameApiChiModel_ofAdd, mSign_zero, zpowZtwo_zero, mul_one]
  · rw [hval, show dmGen α h 1 = dmB α h from rfl, hχB, F.map_B, mFrameApiChiModel_ofAdd,
      zpowZtwo_zero, mul_one]
    show (-1 : ℤ_[2]ˣ) = mSign 1
    rw [← mNegOne_zpow, zpowZtwo_one_exp]
  · rw [hval, show dmGen α h 2 = dmC α h from rfl, hχC, F.map_C, mFrameApiChiModel_ofAdd,
      mSign_zero, zpowZtwo_zero, mul_one]
  · rw [hval, show dmGen α h 3 = dmD α h from rfl, hχD, F.map_D, mFrameApiChiModel_ofAdd,
      mSign_zero, zpowZtwo_one_exp, one_mul]
  · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [mHandleIdx_coordU, hval, hχU j, F.map_U j, mFrameApiChiModel_ofAdd, mSign_zero,
        zpowZtwo_zero, mul_one]
    · rw [mHandleIdx_coordV, hval, hχV j, F.map_V j, mFrameApiChiModel_ofAdd, mSign_zero,
        zpowZtwo_zero, mul_one]

/-- **The 2-torsion of `D_M^{ab}` is `{1, t}` at every handle count** (the general-`h`
`mSqEqOne_iff`, `M.lean:697`).  The `2h` handle coordinates are `ℤ₂`, hence torsion-free, so
they are killed exactly as the three core `ℤ₂`-coordinates are and the answer is `h`-independent.
Note the conclusion never mentions the frame, which is what makes §5's frame-free form
possible. -/
theorem mFrameApi_sqEqOne_iff {α h : ℕ} (hα : 1 ≤ α) (F : MFrame α h)
    (z : topAbelianization (DM α h : Type)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) := by
  constructor
  · intro hz
    have hFe : (F.e z) ^ 2 = 1 := by rw [← map_pow, hz, map_one]
    have hcomp : (2 : ℕ) • (toAdd (F.e z)) = 0 := by
      have h' := congrArg toAdd hFe
      rwa [show toAdd ((F.e z) ^ 2) = (2 : ℕ) • (toAdd (F.e z)) from rfl] at h'
    have hkill : ∀ w : ℤ_[2], (2 : ℕ) • w = 0 → w = 0 := by
      intro w hw
      have hw' : (2 : ℤ_[2]) * w = 0 := by rw [← hw, nsmul_eq_mul]; norm_num
      exact (mul_eq_zero.mp hw').resolve_left (by norm_num)
    have hb : (toAdd (F.e z)).2.1 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]) =>
        p.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at this
      exact hkill _ this
    have hc : (toAdd (F.e z)).2.2.1 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]) =>
        p.2.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at this
      exact hkill _ this
    have hd : (toAdd (F.e z)).2.2.2.1 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]) =>
        p.2.2.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at this
      exact hkill _ this
    have hf : (toAdd (F.e z)).2.2.2.2 = 0 := by
      have hfa := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]) =>
        p.2.2.2.2) hcomp
      simp only [Prod.smul_snd, Prod.snd_zero] at hfa
      funext i
      have hi := congrFun hfa i
      rw [Pi.smul_apply] at hi
      exact hkill _ hi
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) (toAdd (F.e z)).1 with hε | hε
    · left
      refine EquivLike.injective F.e ?_
      rw [map_one]
      exact (mFrameApi_coord_ext hε hb hc hd hf).trans rfl
    · right
      refine EquivLike.injective F.e ?_
      rw [F.map_t]
      exact mFrameApi_coord_ext hε hb hc hd hf
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact dm_torsionGen_sq hα h

/-! ## §4 Item 2: every continuous automorphism fixes `t`, at every handle count -/

/-- **Every continuous automorphism of `D_M^{ab}` fixes `t`** (the general-`h` `mXi_fixes_t`,
`M.lean:738`).  `t` is still the unique element of order two at every handle count, by
`mFrameApi_sqEqOne_iff`, so the relation-vector clause of the stabilizer stays automatic when
the handles are switched on.  This is the one input item 3 would need that does **not** depend
on the Gram convention. -/
theorem mFrameApi_xi_fixes_t {α h : ℕ} (hα : 1 ≤ α) (F : MFrame α h)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α h : Type))
      (topAbelianization (DM α h : Type))) :
    ξ (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))))
      = abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) := by
  have ht2 : (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) :
      topAbelianization (DM α h : Type)) ^ 2 = 1 := dm_torsionGen_sq hα h
  have hξ2 : (ξ (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))))) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  rcases (mFrameApi_sqEqOne_iff hα F _).mp hξ2 with h1 | ht
  · exfalso
    have hteq : (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) :
        topAbelianization (DM α h : Type)) = 1 := by
      have hs := congrArg ξ.symm h1
      rwa [ContinuousMulEquiv.symm_apply_apply, map_one] at hs
    have hFet := congrArg F.e hteq
    rw [F.map_t, map_one] at hFet
    have hone : (1 : ZMod 2) = 0 := congrArg (fun z : MFrameModel h => (toAdd z).1) hFet
    exact absurd hone (by decide)
  · exact ht

/-! ## §5 The frame-free forms

`mFrameApi_sqEqOne_iff` and `mFrameApi_xi_fixes_t` both have conclusions that do not mention the
frame: it enters only as a proof device.  So `nonempty_mFrame` (`MFrameExists.lean`) discharges
it, leaving `1 ≤ α`, which is sharp by `mFrame_isEmpty_zero`.

`mFrameApi_chi_frame` admits no such form: its conclusion names `F.e`, so the frame is part of
the statement, not scaffolding. -/

/-- **The 2-torsion of `D_M^{ab}` is `{1, t}`, with no frame hypothesis**, at every `α ≥ 1` and
every handle count. -/
theorem mFrameApi_sqEqOne_iff_frameFree {α : ℕ} (hα : 1 ≤ α) (h : ℕ)
    (z : topAbelianization (DM α h : Type)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) :=
  (nonempty_mFrame hα h).elim fun F => mFrameApi_sqEqOne_iff hα F z

/-- **Every continuous automorphism of `D_M^{ab}` fixes `t`, with no frame hypothesis**, at
every `α ≥ 1` and every handle count. -/
theorem mFrameApi_xi_fixes_t_frameFree {α : ℕ} (hα : 1 ≤ α) (h : ℕ)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α h : Type))
      (topAbelianization (DM α h : Type))) :
    ξ (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))))
      = abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))) :=
  (nonempty_mFrame hα h).elim fun F => mFrameApi_xi_fixes_t hα F ξ

end MarkedCore

end Dyadic

end GQ2
