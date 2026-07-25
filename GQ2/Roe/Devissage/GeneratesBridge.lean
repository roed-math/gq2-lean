/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage.LESMaster
public import GQ2.Devissage.GeneratesBridge

@[expose] public section

/-!
# §5.11 dévissage on the `r_R` spine: the Generates bridge and Lemma 5.11

Mechanical R-spine clone of `GQ2/Devissage/GeneratesBridge.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`); proofs ported verbatim.  Spine renames `Z1w → Z1wR`, `H1w →
H1wR`, `H2w → H2wR`, `d1Fun → d1FunR`, `d1 → d1R`, `mixedB → mixedB_R`, `WildRel → WildRelR`,
`IsSelfDual(W) → IsSelfDual(W)_R`, with R-suffixed public names.  `H0w_eq_fixedPts` (relator-free)
is reused from `GQ2.Devissage.GeneratesBridge`; the self-duality predicate `IsSelfDual_R` is R25's
(`GQ2.Roe.TrivialSelfDual`, the campaign convention — recon §1.5).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## The `Generates` bridge: `H⁰w = fixedPts` and `IsSelfDual_R ↔ IsSelfDualW_R`

For a *generating* marking, `ker d⁰` is exactly the `C`-fixed points, so the word-internal
package coincides with `IsSelfDual_R`.  This is the precise gap between `lemma_5_11_R` as stated
(no generation hypothesis) and the dévissage `selfdualW_two_of_three_R`: the two-out-of-three
for the `fixedPts`-form follows wherever `t.Generates` is available. -/

section GeneratesBridge

variable {M : Type*} [AddCommGroup M] [DistribMulAction C M]

/-- For a generating marking, the two self-duality packages coincide. -/
theorem isSelfDual_iff_W_R {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [Finite C] (t : Marking C) (hgen : t.Generates) :
    IsSelfDual_R t A ↔ IsSelfDualW_R t A := by
  have hcard : Nat.card (fixedPts C (ElemDual A)) = Nat.card (H0w (A := ElemDual A) t) :=
    Nat.card_congr (Equiv.setCongr (H0w_eq_fixedPts t hgen)).symm
  unfold IsSelfDual_R IsSelfDualW_R
  rw [hcard]

end GeneratesBridge

/-! ## Lemma 5.11, `fixedPts`-form

The theorem `GQ2.FoxH.lemma_5_11_R` includes the hypothesis `hgen : t.Generates`.
Generation identifies
`ker d⁰` with the `C`-fixed points (`H0w_eq_fixedPts`), bridging the word-internal dévissage
`selfdualW_two_of_three_R` to the `fixedPts`-phrased `IsSelfDual_R`; the paper's setting
(admissible markings) always provides it.  It lives here rather than in `FoxHeisenberg.lean`
because the proof needs this file's machinery and the import runs the other way. -/

/-- **Lemma 5.11 (exact cone dévissage)**, stated as its consequence: along a short exact
sequence of finite elementary `𝔽₂[C]`-modules over a *generating* marking, self-duality
satisfies two-out-of-three.  Proved via the word-internal dévissage `selfdualW_two_of_three_R`
and the `Generates` bridge `isSelfDual_iff_W_R`. -/
theorem lemma_5_11_R [Finite C] {A A' A'' : Type*}
    [AddCommGroup A] [DistribMulAction C A]
    [AddCommGroup A'] [DistribMulAction C A']
    [AddCommGroup A''] [DistribMulAction C A''] [Finite A'] [Finite A] [Finite A'']
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) (hgen : t.Generates)
    (hA₂ : ∀ a : A, a + a = 0)
    (f : A' →+ A) (g : A →+ A'')
    (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a)
    (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : f.range = g.ker) :
    (IsSelfDual_R t A' ∧ IsSelfDual_R t A'' → IsSelfDual_R t A) ∧
    (IsSelfDual_R t A' ∧ IsSelfDual_R t A → IsSelfDual_R t A'') ∧
    (IsSelfDual_R t A ∧ IsSelfDual_R t A'' → IsSelfDual_R t A') := by
  have h' := isSelfDual_iff_W_R (A := A') t hgen
  have h := isSelfDual_iff_W_R (A := A) t hgen
  have h'' := isSelfDual_iff_W_R (A := A'') t hgen
  have hW := selfdualW_two_of_three_R f g hf hg hinj hsurj hexact hA₂ t ht hw
  exact ⟨fun hp => h.mpr (hW.1 ⟨h'.mp hp.1, h''.mp hp.2⟩),
    fun hp => h''.mpr (hW.2.1 ⟨h'.mp hp.1, h.mp hp.2⟩),
    fun hp => h'.mpr (hW.2.2 ⟨h.mp hp.1, h''.mp hp.2⟩)⟩

end GQ2.FoxH
