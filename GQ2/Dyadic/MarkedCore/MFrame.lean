/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.MarkedCore.M

@[expose] public section

/-!
# W50-MFRAME: the general-`h` `M`-frame and `demushkinQ (D_M) = 2` at every handle count

**Ticket W50-MFRAME** (owner memo `docs/dyadic/owner-items-2026-08-05.md` §6, item "`MFrame` at
general `h`").  Before this file the `M`-side `q`-invariant existed only at `h = 0`, and only
out of MC2's rank-four frame `MDecomposition α` (`GQ2/Dyadic/MarkedCore/Cores.lean:1823`,
`demushkinQ_DM` at `Cores.lean:1946`); the `N`-side already had the general-`h` layer
(`GQ2/Dyadic/MarkedCore/N.lean` §1, `demushkinQ_DN_nFrame`).  This file is the `M` twin of that
layer.

`D_M^{ab} ≅ ℤ/2·t ⊕ ℤ₂·B̄ ⊕ ℤ₂·C̄₀ ⊕ ℤ₂·D̄ ⊕ ℤ₂^{2h}`, where — and this is the only place the two
cores differ in this layer — the torsion coordinate is **not** a marked generator but the
α-dependent combination

  `t = Ā · C̄₀^{2^{α−1}}`  (memo §2.1; `dm_torsionGen_sq`, `Cores.lean:1814`),

so the `Ā`-row is *forced*: `Ā ↦ (1, 0, −2^{α−1}, 0, 0)` (`mE_A_frame`, the general-`h` `mE_A`).
The `N`-frame has no forced row (memo V1/§7.1(2)).  As on the `N` side the handle letters are
`2h` extra *free* `ℤ₂`-coordinates — handles are invisible to the relation vector (memo §4.2) —
so the torsion, and hence `q`, is untouched by `h`.

## Contents

* **§1** `MFrameModel`, `mHandleCoordU`/`mHandleCoordV`, and the frame `MFrame α h`.
* **§2** `mFrameModelZero` and `MFrame.toMDecomposition`: a rank-four `MFrame` *is* MC2's
  `MDecomposition`, so everything MC3 proves from a frame (`M.lean` §3–§4: `mChi_frame`,
  `mSqEqOne_iff`, `mXi_fixes_t`, `mStabilizer_classification`, and through
  `Variance.lean` the cup-matrix dictionary) applies to a general-`h` frame at `h = 0`.
* **§3** `mE_A_frame` — the forced `Ā`-row at every handle count — and the α-boundary from both
  sides: `mFrame_isEmpty_zero` proves `α = 0` genuinely out of range (`MFrame 0 h` is *empty*,
  the relation vector `2Ā + C̄₀` reading `−1 = 0` in `ℤ₂`), while `mRelVector_model_eq_zero`
  proves the same computation vanishes for every `α ≥ 1`.  So `α = 1` is **in** range for this
  layer; the `α ≥ 2` hypotheses downstream come from the shared Gram.
* **§4** `mTorsionEquivZMod2`, `demushkinQ_DM_mFrame` — the deliverable.

## Scope note (inherited from MC2/MC4, deliberate)

The **existence** theorem `Nonempty (MFrame α h)` (the `phiEquiv` route of
`GQ2/Roe/DRAbelianization.lean`) is *not* in scope, exactly as it is not in scope for
`MDecomposition`/`NDecomposition` (`Cores.lean` §7 preamble) nor for `NFrame` (`N.lean` §1):
consumers take the frame as a hypothesis, as `prop_3_8_classification` consumes
`BDecomposition`.  What this file removes is the *other* gap — that even **given** a frame at
`h > 0` there was no `M`-side `q`-invariant to read off it.

## Variance (MC-VAR discipline)

This layer is matrix-free: no cup form, no Gram matrix, no bilinear pairing appears in any
statement or proof, so the `M`/`N` row-vs-column dictionary
(`GQ2/Dyadic/MarkedCore/Variance.lean`, sharpest instance
`mFrameMatrix_transpose_eq_nMatOf`) is **not** invoked and no transposition is needed.  The
`N`-side template transfers with renaming only.  The dictionary re-enters the moment a consumer
feeds `MFrame.toMDecomposition` to `mFrameMatrix`, and it does so through `MDecomposition`, in
the `M` variance, unchanged.

## Axiom scope (measured)

Every declaration in this file prints `[propext, Classical.choice, Quot.sound]` — no census
axiom.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §1 The general-`h` `M`-frame -/

/-- The coordinate model of the rank-`(4+2h)` `M`-frame: `ℤ/2 × ℤ₂³ × ℤ₂^{2h}`.  Identical in
shape to `NFrameModel` (`N.lean`); the two differ only in which element of `D^{ab}` sits in the
torsion slot. -/
abbrev MFrameModel (h : ℕ) : Type :=
  Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]))

/-- The handle coordinate index of the `j`-th handle's first letter `u_j`. -/
def mHandleCoordU {h : ℕ} (j : Fin h) : Fin (2 * h) :=
  ⟨2 * (j : ℕ), by omega⟩

/-- The handle coordinate index of the `j`-th handle's second letter `v_j`. -/
def mHandleCoordV {h : ℕ} (j : Fin h) : Fin (2 * h) :=
  ⟨2 * (j : ℕ) + 1, by omega⟩

/-- **The general-`h` `M`-frame** (memo §2.1/§4.2; the `M` twin of `NFrame`): a continuous
coordinate isomorphism `D_M^{ab} ≅ ℤ/2 ⊕ ℤ₂^{3+2h}` whose torsion coordinate is the
**α-dependent** class `t = Ā·C̄₀^{2^{α−1}}` — 2-torsion by `dm_torsionGen_sq` — the three
remaining core letters `B̄, C̄₀, D̄` occupy the `ℤ₂³`-block, and the `2h` handle letters the free
tail.  Unlike `NFrame`, the `Ā`-row is then *forced* (`mE_A_frame`), and it is the only
α-dependent row. -/
structure MFrame (α h : ℕ) where
  /-- The coordinate isomorphism. -/
  e : ContinuousMulEquiv (topAbelianization (DM α h : Type)) (MFrameModel h)
  /-- The torsion coordinate — the *composite* class `t = Ā·C̄₀^{2^{α−1}} ↦ (1, 0, 0, 0, 0)`. -/
  map_t : e (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1)))) = ofAdd (1, 0, 0, 0, 0)
  /-- `B̄ ↦ (0, 1, 0, 0, 0)`. -/
  map_B : e (abMk (dmB α h)) = ofAdd (0, 1, 0, 0, 0)
  /-- `C̄₀ ↦ (0, 0, 1, 0, 0)`. -/
  map_C : e (abMk (dmC α h)) = ofAdd (0, 0, 1, 0, 0)
  /-- `D̄ ↦ (0, 0, 0, 1, 0)`. -/
  map_D : e (abMk (dmD α h)) = ofAdd (0, 0, 0, 1, 0)
  /-- `ū_j ↦` the `2j`-th handle coordinate. -/
  map_U : ∀ j : Fin h, e (abMk (dmGen α h (handleIdxU j)))
    = ofAdd (0, 0, 0, 0, Pi.single (mHandleCoordU j) 1)
  /-- `v̄_j ↦` the `(2j+1)`-st handle coordinate. -/
  map_V : ∀ j : Fin h, e (abMk (dmGen α h (handleIdxV j)))
    = ofAdd (0, 0, 0, 0, Pi.single (mHandleCoordV j) 1)

/-! ## §2 The `h = 0` bridge to MC2's `MDecomposition` -/

/-- The rank-four model is the `h = 0` frame model with the empty handle tail dropped. -/
noncomputable def mFrameModelZero : ContinuousMulEquiv (MFrameModel 0) MModel where
  toFun p := ofAdd (p.toAdd.1, p.toAdd.2.1, p.toAdd.2.2.1, p.toAdd.2.2.2.1)
  invFun q := ofAdd (q.toAdd.1, q.toAdd.2.1, q.toAdd.2.2.1, q.toAdd.2.2.2, 0)
  left_inv p := by
    refine Multiplicative.toAdd.injective ?_
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
    exact funext fun i => absurd i.2 (by omega)
  right_inv q := rfl
  map_mul' p q := rfl
  continuous_toFun := by
    refine continuous_ofAdd.comp ?_
    exact ((continuous_fst.comp continuous_toAdd).prodMk
      (((continuous_fst.comp continuous_snd).comp continuous_toAdd).prodMk
        (((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp
            continuous_toAdd).prodMk
          ((continuous_fst.comp (continuous_snd.comp
            (continuous_snd.comp continuous_snd))).comp continuous_toAdd))))
  continuous_invFun := by
    refine continuous_ofAdd.comp ?_
    exact ((continuous_fst.comp continuous_toAdd).prodMk
      (((continuous_fst.comp continuous_snd).comp continuous_toAdd).prodMk
        (((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp
            continuous_toAdd).prodMk
          (((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp
              continuous_toAdd).prodMk
            continuous_const))))

/-- **The `h = 0` bridge**: a rank-four `MFrame` *is* MC2's `MDecomposition`
(`GQ2/Dyadic/MarkedCore/Cores.lean:1823`), so the whole MC3 frame layer — `mChi_frame`,
`mSqEqOne_iff`, `mXi_fixes_t`, `mStabilizer_classification`, and the `Variance.lean` cup
dictionary — applies to any group carrying the general-`h` frame at `h = 0`.  The `N`-side twin
is `NFrame.toNDecomposition`. -/
noncomputable def MFrame.toMDecomposition {α : ℕ} (F : MFrame α 0) : MDecomposition α where
  e := F.e.trans mFrameModelZero
  map_t := by
    show mFrameModelZero (F.e (abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))))) = _
    rw [F.map_t]; rfl
  map_B := by
    show mFrameModelZero (F.e (abMk (dmB α 0))) = _
    rw [F.map_B]; rfl
  map_C := by
    show mFrameModelZero (F.e (abMk (dmC α 0))) = _
    rw [F.map_C]; rfl
  map_D := by
    show mFrameModelZero (F.e (abMk (dmD α 0))) = _
    rw [F.map_D]; rfl

/-! ## §3 The forced `Ā`-row, and the `α = 0` obstruction -/

/-- **The forced `Ā`-row of the general-`h` `M`-frame** (memo §2.1, §4.1):
`Ā ↦ (1, 0, −2^{α−1}, 0, 0)`.  This single row carries *all* of the frame's α-dependence — the
general-`h` `mE_A` (`Cores.lean:1855`), and the structural feature the `N`-frame lacks. -/
theorem mE_A_frame {α h : ℕ} (F : MFrame α h) :
    F.e (abMk (dmA α h)) = ofAdd (1, 0, -(2 : ℤ_[2]) ^ (α - 1), 0, 0) := by
  have ht := F.map_t
  simp only [map_mul, map_pow, F.map_C] at ht
  rw [eq_mul_inv_of_mul_eq ht, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  congr 1
  simp only [Prod.smul_mk, Prod.neg_mk, Prod.mk_add_mk, smul_zero, nsmul_eq_mul, mul_one,
    neg_zero, add_zero]
  refine Prod.ext rfl (Prod.ext (by push_cast; ring) (Prod.ext ?_ (Prod.ext (by push_cast; ring)
    (by simp))))
  push_cast
  ring

/-- **`α = 0` is out of range, provably**: there is no `M`-frame at `α = 0`, at any handle
count.  With `2^{0−1} = 2^0 = 1` the torsion class would be `t = Ā·C̄₀`, so the forced row is
`Ā ↦ (1, 0, −1, 0, 0)`, and the abelianized relation `2Ā + 2^0C̄₀ = 0` (`dm_abRel`) reads
`−1 = 0` in `ℤ₂`.  Contrast `NFrame`, which is α-free and consistent at every `α`: what breaks
at `α = 0` is the *`M`-side* torsion generator, not the model.  (`α = 1` is *not* excluded here
— `MFrame 1 h` is consistent; it is the shared-Gram arguments downstream that need `α ≥ 2`.) -/
theorem mFrame_isEmpty_zero (h : ℕ) : IsEmpty (MFrame 0 h) := by
  refine ⟨fun F => ?_⟩
  have hrel := congrArg F.e (dm_abRel 0 h)
  rw [map_mul, map_pow, map_pow, mE_A_frame F, F.map_C, map_one] at hrel
  have hcoord := congrArg (fun z : MFrameModel h => (toAdd z).2.2.1) hrel
  simp only [← ofAdd_nsmul, ← ofAdd_add, toAdd_ofAdd, Prod.smul_mk, Prod.mk_add_mk,
    toAdd_one] at hcoord
  norm_num at hcoord

/-- **The other side of the boundary: `α ≥ 1` is unobstructed.**  The same model computation
that refutes `α = 0` above — the forced `Ā`-row `(1, 0, −2^{α−1}, 0, 0)` fed to the relation
vector `2Ā + 2^αC̄₀` — comes out *zero* as soon as `α ≥ 1`, because then `2·2^{α−1} = 2^α`.
So `α = 0` is the only value this layer rules out; in particular `α = 1` is **in** range here,
and the `α ≥ 2` hypotheses carried by MC3's stabilizer results and by the even-degree consumers
come from the shared Gram, not from the frame. -/
theorem mRelVector_model_eq_zero {α : ℕ} (hα : 1 ≤ α) (h : ℕ) :
    (ofAdd (1, 0, -(2 : ℤ_[2]) ^ (α - 1), 0, 0) : MFrameModel h) ^ 2
      * (ofAdd (0, 0, 1, 0, 0) : MFrameModel h) ^ (2 ^ α) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
  congr 1
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, Nat.add_sub_cancel]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl)))
  · show (2 : ℕ) • (1 : ZMod 2) = 0
    rw [two_nsmul]
    decide
  · show (2 : ℕ) • (-(2 : ℤ_[2]) ^ k) + (2 ^ (k + 1)) • (1 : ℤ_[2]) = 0
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-! ## §4 Torsion of the model, and the `q`-invariant

The `ℤ₂`-block is torsion-free, so the finite-order subgroup of the model is the `ℤ/2` factor at
every handle count — verbatim the `N`-side argument (`N.lean` §1), and the rank-`(4+2h)`
extension of `Cores.lean`'s `torsionEquivZMod2Four`. -/

section FrameTorsion

private lemma mPadicInt_nsmul_eq_zero {n : ℕ} (hn : 0 < n) {b : ℤ_[2]} (h : n • b = 0) :
    b = 0 := by
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr hn.ne')
  · exact h1

/-- A finite-order element of the general-`h` model has zero `ℤ₂`-components (core and
handle). -/
private lemma mFinOrder_model {h : ℕ} {a : ZMod 2} {b c d : ℤ_[2]} {f : Fin (2 * h) → ℤ_[2]}
    (hfin : IsOfFinOrder (ofAdd (a, b, c, d, f) : MFrameModel h)) :
    b = 0 ∧ c = 0 ∧ d = 0 ∧ f = 0 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hfin
  obtain ⟨n, hn, hpow⟩ := hfin
  rw [← ofAdd_nsmul, ← ofAdd_zero] at hpow
  have hz := Multiplicative.ofAdd.injective hpow
  have hb : n • b = 0 := congrArg (fun p => p.2.1) hz
  have hc : n • c = 0 := congrArg (fun p => p.2.2.1) hz
  have hd : n • d = 0 := congrArg (fun p => p.2.2.2.1) hz
  have hf : n • f = 0 := congrArg (fun p => p.2.2.2.2) hz
  refine ⟨mPadicInt_nsmul_eq_zero hn hb, mPadicInt_nsmul_eq_zero hn hc,
    mPadicInt_nsmul_eq_zero hn hd, funext fun i => ?_⟩
  have hfi : n • f i = 0 := by
    have hfi' := congrFun hf i
    rwa [Pi.smul_apply] at hfi'
  exact mPadicInt_nsmul_eq_zero hn hfi

/-- **Torsion of the general-`h` `M`-model**: the finite-order subtype of `ℤ/2 × ℤ₂^{3+2h}` is
`ℤ/2` — `Cores.lean`'s `torsionEquivZMod2Four` at every handle count. -/
noncomputable def mTorsionEquivZMod2 (h : ℕ) :
    {z : MFrameModel h // IsOfFinOrder z} ≃ ZMod 2 where
  toFun z := z.1.toAdd.1
  invFun a := ⟨ofAdd (a, 0, 0, 0, 0), by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2, by norm_num, ?_⟩
    rw [← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · show (2 : ℕ) • a = 0
      rw [two_nsmul]
      exact (by decide : ∀ b : ZMod 2, b + b = 0) a
    all_goals simp⟩
  left_inv := by
    rintro ⟨z, hz⟩
    apply Subtype.ext
    have hz' : IsOfFinOrder (ofAdd
        (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
          : MFrameModel h) := by
      rw [show (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
        = z.toAdd from rfl, ofAdd_toAdd]
      exact hz
    obtain ⟨hb, hc, hd, hf⟩ := mFinOrder_model hz'
    show (ofAdd (z.toAdd.1, (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2])) : MFrameModel h) = z
    conv_rhs => rw [← ofAdd_toAdd z]
    exact congrArg ofAdd
      (Prod.ext rfl (Prod.ext hb.symm (Prod.ext hc.symm (Prod.ext hd.symm hf.symm))))
  right_inv a := rfl

/-- The `q`-invariant of a group carrying a general-`h` `M`-frame model is `2`. -/
private theorem mDemushkinQ_of_frame {h : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (e : ContinuousMulEquiv (topAbelianization G) (MFrameModel h)) : demushkinQ G = 2 := by
  rw [demushkinQ]
  have eq : {x : topAbelianization G // IsOfFinOrder x}
      ≃ {z : MFrameModel h // IsOfFinOrder z} :=
    Equiv.subtypeEquiv e.toMulEquiv.toEquiv (fun x => by
      show IsOfFinOrder x ↔ IsOfFinOrder (e.toMulEquiv x)
      rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
      exact ⟨fun ⟨n, hn, hp⟩ => ⟨n, hn, by rw [← map_pow, hp, map_one]⟩,
        fun ⟨n, hn, hp⟩ => ⟨n, hn, e.toMulEquiv.injective (by rw [map_pow, map_one]; exact hp)⟩⟩)
  rw [Nat.card_congr eq, Nat.card_congr (mTorsionEquivZMod2 h), Nat.card_zmod]

/-- **`demushkinQ D_M = 2` at every handle count** (memo §2.1/§4.2; owner memo item 6a): the
handles are invisible to the relation vector, so the torsion of `D_M^{ab}` — and hence the
`q`-invariant of the `M`-family — is `2` uniformly in `(α, h)`.  The general-`h` extension of
MC2's `demushkinQ_DM`, and the `M` twin of `demushkinQ_DN_nFrame`. -/
theorem demushkinQ_DM_mFrame {α h : ℕ} (F : MFrame α h) : demushkinQ (DM α h : Type) = 2 :=
  mDemushkinQ_of_frame F.e

end FrameTorsion

end MarkedCore

end Dyadic

end GQ2
