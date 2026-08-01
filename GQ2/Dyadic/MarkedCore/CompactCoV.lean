/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.Certificate

@[expose] public section

/-!
# MC-CoV — the compact-`M` marked change of variables (errata item 3)

**Ticket MC-CoV** of the dyadic campaign (lane MC).  This file *derives* the substitution that
MC1 §7.2 flagged as missing from the vendored sources, and converts MC5's threaded pivot datum
`IsUnit (ν'(C̄₀))` into a theorem consequence of a strictly weaker, arithmetically automatic
hypothesis.

## The gap, restated

Packet Prop. 8.1 fixes the two surviving `M` rows as **compact** (`r = 0`) and **procyclic**
(`r ≥ 1`, `η` odd), but only the procyclic substitution is displayed, and it degenerates at
`r = 0` (`ε·2^{r−1} = ε/2 ∉ ℤ₂`).  MC1 §7.2 and owner Q4 record this; the owner has since ruled
that the campaign derives the compact row itself.

## The answer, in one line

**The compact row's `Ā`-value is not an `r`-exponent at all — it is forced by the abelianized
relation `2Ā + 2^αC̄₀ = 0`, giving the `α`-exponent `ν(Ā) = −2^{α−1}·ν(C̄₀)`.**  This is
`nu_dmA_eq` below, stated for an **arbitrary transported** `ν'` (MC2's `nuM`/`nuM_torsionGen`
is the special case at the standard marking).  The procyclic recipe degenerates at `r = 0`
because it inverts `2^{r−1}`; the compact recipe never inverts anything — see §5.

## What is actually true about the pivot (the load-bearing finding)

Writing the frame coordinates as `(t, B̄, C̄₀, D̄)`, every `ℤ₂`-valued marking kills the torsion
coordinate, and the `Ā`-row is forced; so a marking is exactly a triple
`(ν'(B̄), ν'(C̄₀), ν'(D̄)) ∈ ℤ₂³` (`mNu_frame`).  Against that:

* **The pivot datum is a `St_M`-invariant, not something a substitution can create**
  (`isUnit_nu_stab_iff`).  MC3's classification forces the `C̄₀`-row of *every* χ-preserving cup
  isometry to be `(0, 2c₁, γ, 0)` with `γ ∈ ℤ₂ˣ`; hence `ν'(ξ(C̄₀)) = 2c₁·ν'(B̄) + γ·ν'(C̄₀)`
  and its unit-ness equals that of `ν'(C̄₀)`.  **No change of variables can rescue a
  non-unit pivot at `h = 0`.**
* **But the datum is equivalent to a χ-kernel statement** (`isUnit_nu_dmC_iff_chiKer`):
  `IsUnit (ν'(C̄₀)) ↔ ∃ x, χ_M(x) = 1 ∧ IsUnit (ν'(x))`.  The right-hand side is `f`-free,
  intrinsic to the marked pair, and on the `K`-side automatic (the cyclotomic tower
  `K(μ_{2^∞})/K` is totally ramified, so some Frobenius lift is χ-trivial).

That equivalence is the discharge: it replaces MC5's binder by a hypothesis the packet supplies
in one arithmetic line, with **no loss of strength** (the two are equivalent, not merely
comparable).

## Layout

* **§1** the forced `Ā`-row at an arbitrary marking (`nu_dmA_eq`), uniform in `(α, h)`;
* **§2** the ν-frame model and `mNu_frame` — a marking *is* its triple `(n_b, n_c, n_d)`;
* **§3** the χ-kernel criterion and the discharge (`isUnit_nu_dmC_iff_chiKer`);
* **§4** `St_M`-invariance of the pivot datum and the substitution itself (`mCoVParam`);
* **§5** the comparison with the displayed procyclic substitution;
* **§6** the MC5-facing reductions with the binder replaced;
* **§7** instance pins at `√2` (`α = 3`) and `√5` (`α = 2`).

## Deviations / choices (flagged for the source document)

1. **`h = 0` for the frame-level results.**  MC3's frame API (`MDecomposition`, `MStabParam`,
   `mStabilizer_classification`) is rank-four only, and the campaign's two compact-`M` fields
   are quadratic (`n = [K:ℚ₂] + 2 = 4`), so `h = 0` is the load-bearing case.  §1 is uniform in
   `h`; §3/§4 are `h = 0`.  See the report for the `h ≥ 1` shape.
2. **The hypothesis, not the conclusion, is what changes.**  `IsUnit (ν'(C̄₀))` is *provably*
   not derivable from nothing (a marking with `ν'(C̄₀) ∈ 2ℤ₂` and `ν'(D̄) ∈ ℤ₂ˣ` exists —
   `mNu_frame` shows the triple is free), so the binder is *replaced*, not deleted.  The
   replacement is equivalent, so nothing is lost.
-/

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

open Multiplicative

/-! ## §1 The forced `Ā`-row at an arbitrary transported marking

MC2's `nuM_torsionGen` checks `ν(t) = 0` for the *standard* marking.  The same equation holds
for **every** marking, because it is the ν-image of the group relator: `mRelWord` collapses
abelianly to `Ā²·C̄₀^{2^α}` (`mRelWord_comm`), and `ℤ₂` is abelian and torsion-free.  This is
the compact row's substitution rule, and it is uniform in `h`. -/

section ForcedRow

variable {α h : ℕ}

/-- **The abelianized relation, read at an arbitrary marking**: `2·ν'(Ā) + 2^α·ν'(C̄₀) = 0`.
The ν-image of the relator `P_M`, whose abelian collapse is `Ā²·C̄₀^{2^α}`. -/
theorem nu_mRel (α h : ℕ)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    2 * toAdd (nu' (dmA α h)) + 2 ^ α * toAdd (nu' (dmC α h)) = 0 := by
  have hrel : nu' (mRelWord α (dmGen α h)) = 1 := by rw [dm_relation, map_one]
  rw [map_mRelWord, mRelWord_comm] at hrel
  have h0 : (dmGen α h 0) = dmA α h := rfl
  have h2 : (dmGen α h 2) = dmC α h := rfl
  rw [h0, h2] at hrel
  have := congrArg toAdd hrel
  rw [toAdd_mul] at this
  simpa only [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_pow] using this

/-- **The compact-`M` substitution rule for the `Ā`-row** (the content MC1 §7.2 reports
missing): at every transported marking, `ν'(Ā) = −2^{α−1}·ν'(C̄₀)`.  The exponent is `α − 1`,
the *frame* parameter — **not** the procyclic row's `r − 1`.  MC2's `nuM_torsionGen` is this at
the standard marking `ν'(C̄₀) = 1`. -/
theorem nu_dmA_eq (α h : ℕ) (hα : 1 ≤ α)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (dmA α h)) = -(2 : ℤ_[2]) ^ (α - 1) * toAdd (nu' (dmC α h)) := by
  have hrel := nu_mRel α h nu'
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
  rw [Nat.add_sub_cancel] at *
  have hsplit : (2 : ℤ_[2]) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hsplit] at hrel
  have h2 : (2 : ℤ_[2]) * (toAdd (nu' (dmA (k + 1) h))
      + 2 ^ k * toAdd (nu' (dmC (k + 1) h))) = 0 := by rw [mul_add, ← hrel]; ring
  have hne : (2 : ℤ_[2]) ≠ 0 := by norm_num
  have := (mul_eq_zero.mp h2).resolve_left hne
  linear_combination this

/-- **`Ā` is never a pivot** when `α ≥ 2`: its ν-value is `2^{α−1}` times something, hence even.
This is why the `M`-core has no second frame pivot to pair `C̄₀` with — the structural contrast
with the `N`-core, whose packet clause pins the *pair* `(ν'(σ̄), ν'(x̄₂))`. -/
theorem not_isUnit_nu_dmA (α h : ℕ) (hα : 2 ≤ α)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    ¬ IsUnit (toAdd (nu' (dmA α h))) := by
  intro hu
  have hpar := mParityZ_of_isUnit hu
  rw [nu_dmA_eq α h (by omega) nu'] at hpar
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
  have heven : -(2 : ℤ_[2]) ^ (k + 2 - 1) * toAdd (nu' (dmC (k + 2) h))
      = 2 * (-(2 : ℤ_[2]) ^ k * toAdd (nu' (dmC (k + 2) h))) := by
    rw [show k + 2 - 1 = k + 1 from rfl, pow_succ]
    ring
  rw [heven, mParityZ_two_mul] at hpar
  exact absurd hpar (by decide)

end ForcedRow

/-! ## §2 The ν-frame: a marking *is* a triple

`ν'` kills the torsion coordinate (nothing of order 2 survives in `ℤ₂`) and its `Ā`-row is
forced by §1, so on the rank-four frame a marking is exactly `(n_b, n_c, n_d) = (ν'(B̄),
ν'(C̄₀), ν'(D̄))`.  `mNu_frame` is the ν-analogue of MC3's `mChi_frame`. -/

section NuFrame

/-- **The ν-model on the frame**: the `ℤ₂`-linear form `(τ, b, c, d) ↦ n_b·b + n_c·c + n_d·d`.
The torsion coordinate `τ` is killed — `ℤ₂` is torsion-free. -/
noncomputable def mNuModel (nb nc nd : ℤ_[2]) : MModel →* Multiplicative ℤ_[2] where
  toFun z := ofAdd (nb * (toAdd z).2.1 + nc * (toAdd z).2.2.1 + nd * (toAdd z).2.2.2)
  map_one' := by
    show ofAdd (nb * 0 + nc * 0 + nd * 0) = 1
    rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero]
    rfl
  map_mul' x y := by
    show ofAdd (nb * ((toAdd x).2.1 + (toAdd y).2.1)
        + nc * ((toAdd x).2.2.1 + (toAdd y).2.2.1)
        + nd * ((toAdd x).2.2.2 + (toAdd y).2.2.2)) = _
    rw [← ofAdd_add]
    congr 1
    ring

@[simp] theorem mNuModel_ofAdd (nb nc nd : ℤ_[2]) (ε : ZMod 2) (b c d : ℤ_[2]) :
    mNuModel nb nc nd (ofAdd (ε, b, c, d)) = ofAdd (nb * b + nc * c + nd * d) := rfl

theorem mNuModel_continuous (nb nc nd : ℤ_[2]) : Continuous (mNuModel nb nc nd) := by
  have hb : Continuous fun z : MModel => (toAdd z).2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_toAdd)
  have hc : Continuous fun z : MModel => (toAdd z).2.2.1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
  have hd : Continuous fun z : MModel => (toAdd z).2.2.2 :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
  exact continuous_ofAdd.comp
    ((((continuous_const.mul hb).add (continuous_const.mul hc)).add (continuous_const.mul hd)))

/-- The ν-model bundled with its continuity. -/
noncomputable def mNuModelHom (nb nc nd : ℤ_[2]) : ContinuousMonoidHom MModel
    (Multiplicative ℤ_[2]) := ⟨mNuModel nb nc nd, mNuModel_continuous nb nc nd⟩

/-- **Every marking is its triple** (the ν-analogue of MC3's `mChi_frame`): a continuous
`ℤ₂`-valued character of `D_M` at rank four is the linear form `(n_b, n_c, n_d)` read through
the frame, with `n_? = ν'(?)`.  The `Ā`-row is *not* a fourth parameter — §1 forces it. -/
theorem mNu_frame {α : ℕ} (hα : 1 ≤ α) (B : MDecomposition α)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (x : (DM α 0 : Type)) :
    nu' x = mNuModel (toAdd (nu' (dmB α 0))) (toAdd (nu' (dmC α 0)))
      (toAdd (nu' (dmD α 0))) (B.e (abMk x)) := by
  set nb := toAdd (nu' (dmB α 0)) with hnb
  set nc := toAdd (nu' (dmC α 0)) with hnc
  set nd := toAdd (nu' (dmD α 0)) with hnd
  have hext : nu' = (mNuModelHom nb nc nd).comp ((mFrameHom B).comp (mAbMkHom α 0)) := by
    refine dm_hom_ext _ _ fun i => ?_
    have hval : ∀ z : (DM α 0 : Type),
        ((mNuModelHom nb nc nd).comp ((mFrameHom B).comp (mAbMkHom α 0))) z
          = mNuModel nb nc nd (B.e (abMk z)) := fun _ => rfl
    rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
    · rw [hval, show dmGen α 0 0 = dmA α 0 from rfl, mE_A B, mNuModel_ofAdd]
      rw [show nu' (dmA α 0) = ofAdd (toAdd (nu' (dmA α 0))) from rfl,
        nu_dmA_eq α 0 hα nu', ← hnc]
      congr 1
      ring
    · rw [hval, show dmGen α 0 1 = dmB α 0 from rfl, B.map_B, mNuModel_ofAdd]
      rw [show nu' (dmB α 0) = ofAdd nb from rfl]
      congr 1
      ring
    · rw [hval, show dmGen α 0 2 = dmC α 0 from rfl, B.map_C, mNuModel_ofAdd]
      rw [show nu' (dmC α 0) = ofAdd nc from rfl]
      congr 1
      ring
    · rw [hval, show dmGen α 0 3 = dmD α 0 from rfl, B.map_D, mNuModel_ofAdd]
      rw [show nu' (dmD α 0) = ofAdd nd from rfl]
      congr 1
      ring
  exact DFunLike.congr_fun hext x

/-- **`χ_M` in the frame, at the group level**: MC3's `mChi_frame` for the *canonical*
orientation, without a descended `χ` — the composite of `mChiModel` with the frame and `abMk`
agrees with `chiM` on the marked generators, hence everywhere. -/
theorem mChi_frame_group {α : ℕ} (B : MDecomposition α) (x : (DM α 0 : Type)) :
    chiM α 0 x = mChiModel α (B.e (abMk x)) := by
  have hext : chiM α 0 = (mChiModelHom α).comp ((mFrameHom B).comp (mAbMkHom α 0)) := by
    refine dm_hom_ext _ _ fun i => ?_
    have hval : ∀ z : (DM α 0 : Type),
        ((mChiModelHom α).comp ((mFrameHom B).comp (mAbMkHom α 0))) z
          = mChiModel α (B.e (abMk z)) := fun _ => rfl
    rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
    · rw [hval, show dmGen α 0 0 = dmA α 0 from rfl, chiM_dmA, mE_A B, mChiModel_ofAdd,
        mSign_zero, zpowZtwo_zero, mul_one]
    · rw [hval, show dmGen α 0 1 = dmB α 0 from rfl, chiM_dmB, B.map_B, mChiModel_ofAdd,
        zpowZtwo_zero, mul_one]
      show (-1 : ℤ_[2]ˣ) = mSign 1
      rw [← mNegOne_zpow, zpowZtwo_one_exp]
    · rw [hval, show dmGen α 0 2 = dmC α 0 from rfl, chiM_dmC, B.map_C, mChiModel_ofAdd,
        mSign_zero, zpowZtwo_zero, mul_one]
    · rw [hval, show dmGen α 0 3 = dmD α 0 from rfl, chiM_dmD, B.map_D, mChiModel_ofAdd,
        mSign_zero, zpowZtwo_one_exp, one_mul]
  exact DFunLike.congr_fun hext x

end NuFrame

/-! ## §3 The χ-kernel criterion — the discharge

The `M`-core has **no second frame pivot**: `Ā` is forced even (§1), and χ-triviality forces the
`B̄`-coordinate even and the `D̄`-coordinate zero (`mChi_row_extract`, where `α ≥ 2` is exactly
what separates `−1` from the `u`-powers).  So a χ-trivial element's ν-value lies in
`(2·ν'(B̄), ν'(C̄₀))` — and is a unit precisely when `ν'(C̄₀)` is.

This makes the pivot datum **equivalent** to the intrinsic, `f`-free statement "`ν'` is
unimodular somewhere on `ker χ_M`". -/

section Discharge

/-- **The compact-`M` marked-data clause**: `ν'` is unimodular somewhere on `ker χ_M`.  This is
the `M`-analogue of the packet's `N`-side pair clause `IsUnit ν'(σ̄) ∨ IsUnit ν'(x̄₂)`, and,
unlike `IsUnit (ν'(C̄₀))`, it does not name a generator — it is invariant under every
χ-preserving change of variables and under every choice of the abstract isomorphism `f`.

On the `K`-side it is the statement that some Frobenius lift acts trivially on `μ_{2^∞}`, which
holds because `K(μ_{2^∞})/K` is totally ramified. -/
def MChiKerUnimodular (α h : ℕ)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ x : (DM α h : Type), chiM α h x = 1 ∧ IsUnit (toAdd (nu' x))

/-- The easy direction, uniform in `h`: the pivot itself is χ-trivial (`chiM_dmC`). -/
theorem mChiKerUnimodular_of_isUnit {α h : ℕ}
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) : MChiKerUnimodular α h nu' :=
  ⟨dmC α h, chiM_dmC α h, hc⟩

/-- **The discharge** (the compact-`M` change of variables, criterion form): at rank four, a
marking that is unimodular anywhere on `ker χ_M` is unimodular **at the pivot**.

Mechanism: write `x` in frame coordinates `(ε, b, c, d)`.  `χ_M(x) = 1` forces `d = 0` and
`b` even (`mChi_row_extract`, `α ≥ 2`); the torsion coordinate is killed by `ν'`; so
`ν'(x) = b·ν'(B̄) + c·ν'(C̄₀)` with `b` even, and a unit value forces `ν'(C̄₀)` odd. -/
theorem isUnit_nu_dmC_of_chiKer {α : ℕ} (hα : 2 ≤ α) (B : MDecomposition α)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hker : MChiKerUnimodular α 0 nu') : IsUnit (toAdd (nu' (dmC α 0))) := by
  obtain ⟨x, hchi, hunit⟩ := hker
  have hα1 : 1 ≤ α := by omega
  -- the χ-row of `x`: `b` even, `d = 0`
  have hchif : mChiModel α (B.e (abMk x)) = 1 := by rw [← mChi_frame_group B x, hchi]
  have hrow : mParityZ (toAdd (B.e (abMk x))).2.1 = 0 ∧ (toAdd (B.e (abMk x))).2.2.2 = 0 := by
    refine mChi_row_extract hα ?_
    rw [show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, zpowZtwo_zero, mul_one]
    exact hchif
  obtain ⟨hb, hd⟩ := hrow
  obtain ⟨b', hb'⟩ := (mParityZ_eq_zero_iff _).mp hb
  -- the ν-row of `x`
  have hnu := mNu_frame hα1 B nu' x
  have hval : toAdd (nu' x) = toAdd (nu' (dmB α 0)) * (toAdd (B.e (abMk x))).2.1
      + toAdd (nu' (dmC α 0)) * (toAdd (B.e (abMk x))).2.2.1
      + toAdd (nu' (dmD α 0)) * (toAdd (B.e (abMk x))).2.2.2 := by
    rw [hnu]; rfl
  rw [hb', hd, mul_zero, add_zero] at hval
  -- parity bookkeeping
  have hpar := mParityZ_of_isUnit hunit
  rw [hval, show toAdd (nu' (dmB α 0)) * (2 * b')
      = 2 * (toAdd (nu' (dmB α 0)) * b') by ring] at hpar
  rw [mParityZ_add, mParityZ_two_mul, zero_add, mParityZ_mul] at hpar
  refine mIsUnit_of_parity_one ?_
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) (mParityZ (toAdd (nu' (dmC α 0)))) with h0 | h1
  · rw [h0, zero_mul] at hpar; exact absurd hpar (by decide)
  · exact h1

/-- **The compact-`M` change of variables, as an equivalence.**  At rank four the threaded
pivot datum and the intrinsic χ-kernel clause are the *same* hypothesis. -/
theorem isUnit_nu_dmC_iff_chiKer {α : ℕ} (hα : 2 ≤ α) (B : MDecomposition α)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2])) :
    IsUnit (toAdd (nu' (dmC α 0))) ↔ MChiKerUnimodular α 0 nu' :=
  ⟨mChiKerUnimodular_of_isUnit nu', isUnit_nu_dmC_of_chiKer hα B nu'⟩

end Discharge

end MarkedCore

end Dyadic

end GQ2
