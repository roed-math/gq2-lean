/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Devissage.LESMaster

@[expose] public section

/-!
# §5.11 dévissage: the Generates bridge and Lemma 5.11

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## The `Generates` bridge: `H⁰w = fixedPts` and `IsSelfDual ↔ IsSelfDualW`

For a *generating* marking, `ker d⁰` is exactly the `C`-fixed points, so the word-internal
package coincides with `IsSelfDual`.  This is the precise gap between `lemma_5_11` as stated
(no generation hypothesis) and the dévissage `selfdualW_two_of_three`: the two-out-of-three
for the `fixedPts`-form follows wherever `t.Generates` is available. -/

section GeneratesBridge

variable {M : Type*} [AddCommGroup M] [DistribMulAction C M]

/-- For a generating marking, the word-complex `H⁰w` is the set of `C`-fixed points. -/
theorem H0w_eq_fixedPts (t : Marking C) (hgen : t.Generates) :
    (H0w (A := M) t : Set M) = fixedPts C M := by
  ext v
  constructor
  · intro hv
    have hv' : d0 t v = 0 := AddMonoidHom.mem_ker.mp hv
    -- The stabilizer of `v` is a subgroup containing the four marked elements.
    let S : Subgroup C :=
      { carrier := {c | c • v = v}
        one_mem' := one_smul C v
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [mul_smul, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [← ha, inv_smul_smul, ha] }
    have hmarked : {t.σ, t.τ, t.x₀, t.x₁} ⊆ (S : Set C) := by
      rintro c (rfl | rfl | rfl | rfl)
      · exact sub_eq_zero.mp (congrFun hv' 0)
      · exact sub_eq_zero.mp (congrFun hv' 1)
      · exact sub_eq_zero.mp (congrFun hv' 2)
      · exact sub_eq_zero.mp (congrFun hv' 3)
    have hle : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤ S :=
      (Subgroup.closure_le S).mpr hmarked
    intro c
    exact hle (by rw [hgen]; trivial)
  · intro hv
    apply AddMonoidHom.mem_ker.mpr
    funext i
    fin_cases i <;> simp [d0, hv _]

/-- For a generating marking, the two self-duality packages coincide. -/
theorem isSelfDual_iff_W {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [Finite C] (t : Marking C) (hgen : t.Generates) :
    IsSelfDual t A ↔ IsSelfDualW t A := by
  have hcard : Nat.card (fixedPts C (ElemDual A)) = Nat.card (H0w (A := ElemDual A) t) :=
    Nat.card_congr (Equiv.setCongr (H0w_eq_fixedPts t hgen)).symm
  unfold IsSelfDual IsSelfDualW
  rw [hcard]

end GeneratesBridge

/-! ## Lemma 5.11, `fixedPts`-form

The theorem `GQ2.FoxH.lemma_5_11` includes the hypothesis `hgen : t.Generates`.  Generation identifies
`ker d⁰` with the `C`-fixed points (`H0w_eq_fixedPts`), bridging the word-internal dévissage
`selfdualW_two_of_three` to the `fixedPts`-phrased `IsSelfDual`; the paper's setting
(admissible markings) always provides it.  It lives here rather than in `FoxHeisenberg.lean`
because the proof needs this file's machinery and the import runs the other way. -/

/-- **Lemma 5.11 (exact cone dévissage)**, stated as its consequence: along a short exact
sequence of finite elementary `𝔽₂[C]`-modules over a *generating* marking, self-duality
satisfies two-out-of-three.  Proved via the word-internal dévissage `selfdualW_two_of_three`
and the `Generates` bridge `isSelfDual_iff_W`. -/
theorem lemma_5_11 [Finite C] {A A' A'' : Type*}
    [AddCommGroup A] [DistribMulAction C A]
    [AddCommGroup A'] [DistribMulAction C A']
    [AddCommGroup A''] [DistribMulAction C A''] [Finite A'] [Finite A] [Finite A'']
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hA₂ : ∀ a : A, a + a = 0)
    (f : A' →+ A) (g : A →+ A'')
    (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a)
    (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : f.range = g.ker) :
    (IsSelfDual t A' ∧ IsSelfDual t A'' → IsSelfDual t A) ∧
    (IsSelfDual t A' ∧ IsSelfDual t A → IsSelfDual t A'') ∧
    (IsSelfDual t A ∧ IsSelfDual t A'' → IsSelfDual t A') := by
  have h' := isSelfDual_iff_W (A := A') t hgen
  have h := isSelfDual_iff_W (A := A) t hgen
  have h'' := isSelfDual_iff_W (A := A'') t hgen
  have hW := selfdualW_two_of_three f g hf hg hinj hsurj hexact hA₂ t ht hw
  exact ⟨fun hp => h.mpr (hW.1 ⟨h'.mp hp.1, h''.mp hp.2⟩),
    fun hp => h''.mpr (hW.2.1 ⟨h'.mp hp.1, h.mp hp.2⟩),
    fun hp => h'.mpr (hW.2.2 ⟨h.mp hp.1, h''.mp hp.2⟩)⟩


end GQ2.FoxH
