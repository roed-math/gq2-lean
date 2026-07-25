/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage.LESExact
public import GQ2.Devissage.LESMaster

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# §5.11 dévissage on the `r_R` spine: the dualized SES, δ-squares, and the master two-of-three

Mechanical R-spine clone of `GQ2/Devissage/LESMaster.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`); proofs ported verbatim.  Spine renames `Z1w → Z1wR`, `H1w →
H1wR`, `H2w → H2wR`, `d1Fun → d1FunR`, `d1 → d1R`, `mixedB → mixedB_R`, `WildRel → WildRelR`,
`IsSelfDual(W) → IsSelfDual(W)_R`, with R-suffixed public names.  The generic `four_lemma_inj`,
`dual_exact_pair`, `dual_ses_exact`, `dualMap*` and `H0w_exact_mid`/`H0wMap` are reused from
`GQ2.Devissage.*`; the δ-square cores forward to `prop_5_8_*_R`/`lemma_5_6_R`
(`GQ2.Roe.Devissage.TracedRows`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

section LES

variable {A' A A'' : Type*}
  [AddCommGroup A'] [DistribMulAction C A'] [Finite A']
  [AddCommGroup A] [DistribMulAction C A] [Finite A]
  [AddCommGroup A''] [DistribMulAction C A''] [Finite A''] [Finite C]
  (f : A' →+ A) (g : A →+ A'')
  (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a) (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
  (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : f.range = g.ker)

/-! ### The dualized SES and the δ-squares

Dualizing the SES gives `0 → A''^∨ --g^∨--> A^∨ --f^∨--> A'^∨ → 0`; the LES machinery
instantiates on it verbatim.  The δ-squares — the genuinely new commutativity content of the
ladder — reduce to two `snake`-vs-`snake` core computations, each a chain of Prop 5.8 and
Lemma 5.6 through the chosen lifts. -/

include hf hg hinj hsurj hexact in
/-- `δ⁰` of the dualized SES: `H⁰w(A'^∨) →+ H¹w(A''^∨)`. -/
noncomputable def delta0D_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) : H0w (A := ElemDual A') t →+ H1wR (A := ElemDual A'') t :=
  delta0_R (dualMap g) (dualMap f) (dualMap_equivariant g hg) (dualMap_equivariant f hf)
    (dualMap_injective g hsurj) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t ht hw

include hf hg hinj hsurj hexact in
/-- `δ¹` of the dualized SES: `H¹w(A'^∨) →+ H²w(A''^∨)`. -/
noncomputable def delta1D_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) : H1wR (A := ElemDual A') t →+ H2wR (A := ElemDual A'') t :=
  delta1_R (dualMap g) (dualMap f) (dualMap_equivariant g hg) (dualMap_equivariant f hf)
    (dualMap_injective g hsurj) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t ht hw

omit [Finite A'] in
include hf hg hinj hsurj hexact in
/-- **δ-square core 1**: evaluating `λ ∈ H⁰w(A'^∨)` on the `δ¹`-snake of `c''` equals pairing
`c''` against the dual `δ⁰`-snake word of `λ`.  (Lift `λ` to `Λ` along `f^∨`; both sides equal
`B(lift c'', d⁰Λ)` by Prop 5.8 right resp. Lemma 5.6.) -/
theorem delta_square_core1_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (c'' : Z1wR (A := A'') t) (lam : H0w (A := ElemDual A') t) :
    lam.1 ((snakeZ_R f g hg hsurj hexact t c'').1 + (snakeZ_R f g hg hsurj hexact t c'').2)
      = mixedB_R t c''.1
          (snake0Z'_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
            (dualMap_surjective hA₂ f hinj)
            (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam) := by
  set Λ : ElemDual A := (dualMap_surjective hA₂ f hinj lam.1).choose with hΛdef
  have hΛ : dualMap f Λ = lam.1 := (dualMap_surjective hA₂ f hinj lam.1).choose_spec
  set w : Fin 4 → ElemDual A'' := snake0Z'_R (dualMap g) (dualMap f)
    (dualMap_equivariant f hf) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam with hwdef
  have hws : (fun i => dualMap g (w i)) = d0 t Λ :=
    snake0Z'_spec_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
      (dualMap_surjective hA₂ f hinj)
      (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam
  have hz := snakeZ_spec_R f g hg hsurj hexact t c''
  have hz1 : f (snakeZ_R f g hg hsurj hexact t c'').1
      = (d1FunR t (snakeLift_R g hsurj c''.1)).1 := congrArg Prod.fst hz
  have hz2 : f (snakeZ_R f g hg hsurj hexact t c'').2
      = (d1FunR t (snakeLift_R g hsurj c''.1)).2 := congrArg Prod.snd hz
  calc lam.1 ((snakeZ_R f g hg hsurj hexact t c'').1 + (snakeZ_R f g hg hsurj hexact t c'').2)
      = Λ (f ((snakeZ_R f g hg hsurj hexact t c'').1 + (snakeZ_R f g hg hsurj hexact t c'').2)) :=
        by rw [← hΛ]; rfl
    _ = Λ ((d1FunR t (snakeLift_R g hsurj c''.1)).1 + (d1FunR t (snakeLift_R g hsurj c''.1)).2) :=
        by rw [map_add, hz1, hz2]
    _ = mixedB_R t (snakeLift_R g hsurj c''.1) (d0 t Λ) :=
        (prop_5_8_right_R t ht hw (snakeLift_R g hsurj c''.1) Λ).symm
    _ = mixedB_R t (snakeLift_R g hsurj c''.1) (fun i => dualMap g (w i)) := by rw [hws]
    _ = mixedB_R t (fun i => g (snakeLift_R g hsurj c''.1 i)) w :=
        (lemma_5_6_R g hg t (snakeLift_R g hsurj c''.1) w).symm
    _ = mixedB_R t c''.1 w := by
        rw [show (fun i => g (snakeLift_R g hsurj c''.1 i)) = c''.1 from
          funext (snakeLift_spec_R g hsurj c''.1)]

include hf hg hinj hsurj hexact in
/-- **δ-square core 2**: pairing the primal `δ⁰`-snake word of `a''` against a dual cocycle `y'`
equals evaluating the dual `δ¹`-snake of `y'` on `a''`.  (Mirror of core 1: Prop 5.8 left +
Lemma 5.6 through the lifts.) -/
theorem delta_square_core2_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (a'' : H0w (A := A'') t) (y' : Z1wR (A := ElemDual A') t) :
    mixedB_R t (snake0Z'_R f g hg hsurj hexact t a'') y'.1
      = (snakeZ_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').1 a''.1
        + (snakeZ_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
            (dualMap_surjective hA₂ f hinj)
            (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').2
          a''.1 := by
  set Y : Fin 4 → ElemDual A :=
    snakeLift_R (dualMap f) (dualMap_surjective hA₂ f hinj) y'.1 with hYdef
  have hY : ∀ i, dualMap f (Y i) = y'.1 i :=
    snakeLift_spec_R (dualMap f) (dualMap_surjective hA₂ f hinj) y'.1
  set q := snakeZ_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
    (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y' with hqdef
  have hq := snakeZ_spec_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
    (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y'
  have hq1 : dualMap g q.1 = (d1FunR (A := ElemDual A) t Y).1 := congrArg Prod.fst hq
  have hq2 : dualMap g q.2 = (d1FunR (A := ElemDual A) t Y).2 := congrArg Prod.snd hq
  have hws : (fun i => f (snake0Z'_R f g hg hsurj hexact t a'' i))
      = d0 t (hsurj a''.1).choose := snake0Z'_spec_R f g hg hsurj hexact t a''
  calc mixedB_R t (snake0Z'_R f g hg hsurj hexact t a'') y'.1
      = mixedB_R t (snake0Z'_R f g hg hsurj hexact t a'') (fun i => dualMap f (Y i)) := by
        rw [show (fun i => dualMap f (Y i)) = y'.1 from funext hY]
    _ = mixedB_R t (fun i => f (snake0Z'_R f g hg hsurj hexact t a'' i)) Y :=
        (lemma_5_6_R f hf t (snake0Z'_R f g hg hsurj hexact t a'') Y).symm
    _ = mixedB_R t (d0 t (hsurj a''.1).choose) Y := by rw [hws]
    _ = ((d1FunR (A := ElemDual A) t Y).1 + (d1FunR (A := ElemDual A) t Y).2)
          ((hsurj a''.1).choose) := prop_5_8_left_R t ht hw ((hsurj a''.1).choose) Y
    _ = (d1FunR (A := ElemDual A) t Y).1 ((hsurj a''.1).choose)
          + (d1FunR (A := ElemDual A) t Y).2 ((hsurj a''.1).choose) := rfl
    _ = (dualMap g q.1) ((hsurj a''.1).choose) + (dualMap g q.2) ((hsurj a''.1).choose) := by
        rw [hq1, hq2]
    _ = q.1 (g ((hsurj a''.1).choose)) + q.2 (g ((hsurj a''.1).choose)) := rfl
    _ = q.1 a''.1 + q.2 a''.1 := by rw [(hsurj a''.1).choose_spec]

include hf hg hinj hsurj hexact in
/-- **δ-square (1,2)**: `χ²_{A'} ∘ δ¹ = (δ⁰ of the dual SES)^∨ ∘ χ¹_{A''}`. -/
theorem square_delta1_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (h'' : H1wR (A := A'') t) :
    chi2_R (A := A') t ht hw (delta1_R f g hf hg hinj hsurj hexact t ht hw h'')
      = dualMap (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (chi1_R (A := A'') t ht hw h'') := by
  obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h''
  apply ElemDual.ext
  intro lam
  show lam.1 ((snakeZ_R f g hg hsurj hexact t c'').1 + (snakeZ_R f g hg hsurj hexact t c'').2)
    = mixedB_R t c''.1
        (snake0Z'_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam)
  exact delta_square_core1_R f g hf hg hinj hsurj hexact hA₂ t ht hw c'' lam

include hf hg hinj hsurj hexact in
/-- **δ-square (0,1)**: `χ¹_{A'} ∘ δ⁰ = (δ¹ of the dual SES)^∨ ∘ χ⁰_{A''}`. -/
theorem square_delta0_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (a'' : H0w (A := A'') t) :
    chi1_R (A := A') t ht hw (delta0_R f g hf hg hinj hsurj hexact t ht hw a'')
      = dualMap (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (chi0_R (A := A'') t ht hw a'') := by
  apply ElemDual.ext
  intro z'
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective z'
  show mixedB_R t (snake0Z'_R f g hg hsurj hexact t a'') y'.1 = _
  exact delta_square_core2_R f g hf hg hinj hsurj hexact hA₂ t ht hw a'' y'

include hf hg hinj hsurj hexact in
/-- **δ-square (0,1), transposed**: `χ¹ᵀ_{A''} ∘ δ⁰_dual = (δ¹)^∨ ∘ χ⁰ᵀ_{A'}`. -/
theorem square_delta0D_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (lam : H0w (A := ElemDual A') t) :
    chi1T_R (A := A'') t ht hw (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw lam)
      = dualMap (delta1_R f g hf hg hinj hsurj hexact t ht hw)
          (chi0T_R (A := A') t ht hw lam) := by
  apply ElemDual.ext
  intro h''
  obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h''
  show mixedB_R t c''.1
      (snake0Z'_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
        (dualMap_surjective hA₂ f hinj)
        (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam)
    = lam.1 ((snakeZ_R f g hg hsurj hexact t c'').1 + (snakeZ_R f g hg hsurj hexact t c'').2)
  exact (delta_square_core1_R f g hf hg hinj hsurj hexact hA₂ t ht hw c'' lam).symm

include hf hg hinj hsurj hexact in
/-- **δ-square (1,2), transposed**: `χ²ᵀ_{A''} ∘ δ¹_dual = (δ⁰)^∨ ∘ χ¹ᵀ_{A'}`. -/
theorem square_delta1D_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) (z' : H1wR (A := ElemDual A') t) :
    chi2T_R (A := A'') t ht hw (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw z')
      = dualMap (delta0_R f g hf hg hinj hsurj hexact t ht hw)
          (chi1T_R (A := A') t ht hw z') := by
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective z'
  apply ElemDual.ext
  intro a''
  show (snakeZ_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
        (dualMap_surjective hA₂ f hinj)
        (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').1 a''.1
      + (snakeZ_R (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').2 a''.1
    = mixedB_R t (snake0Z'_R f g hg hsurj hexact t a'') y'.1
  exact (delta_square_core2_R f g hf hg hinj hsurj hexact hA₂ t ht hw a'' y').symm

include hf hg hinj hsurj hexact in
/-- **Direction (mid)** of `selfdualW_two_of_three_R`: if the sub `A'` and the quotient `A''` are
self-dual, so is the middle `A`.  Three `four_lemma_inj` windows across the duality ladder. -/
private theorem selfdualW_two_of_three_mid_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C)
    (ht : t.TameRel) (hw : t.WildRelR) (hsd' : IsSelfDualW_R t A') (hsd'' : IsSelfDualW_R t A'') :
    IsSelfDualW_R t A := by
  -- Torsion on the outer modules and the duals.
  have hA'₂ : ∀ a' : A', a' + a' = 0 := two_torsion_of_injective f hinj hA₂
  have hA''₂ : ∀ a'' : A'', a'' + a'' = 0 := two_torsion_of_surjective g hsurj hA₂
  have hD''₂ : ∀ lam : ElemDual A'', lam + lam = 0 := ElemDual.add_self_eq_zero
  -- Finiteness of the subquotients.
  have : Finite (H1wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  -- The dualized SES and its equivariances (proof-irrelevant aliases).
  have hgse : ∀ (c : C) (lam : ElemDual A''), dualMap g (c • lam) = c • dualMap g lam :=
    dualMap_equivariant g hg
  have hfse : ∀ (c : C) (lam : ElemDual A), dualMap f (c • lam) = c • dualMap f lam :=
    dualMap_equivariant f hf
  have hginj := dualMap_injective g hsurj
  have hfsurj := dualMap_surjective hA₂ f hinj
  have hdualex := dual_ses_exact hA''₂ f g hexact
  -- Top-row pointwise exactness adapters.
  have tE4 : ∀ h : H1wR (A := A') t, H1wMap_R t f hf h = 0
      ↔ h ∈ (delta0_R f g hf hg hinj hsurj hexact t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE5 : ∀ h : H1wR (A := A) t, H1wMap_R t g hg h = 0 ↔ h ∈ (H1wMap_R t f hf).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE7 : ∀ y : H2wR (A := A') t, H2wMap_R t f hf y = 0
      ↔ y ∈ (delta1_R f g hf hg hinj hsurj hexact t ht hw).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans
      (H2w_exact_left_R f g hf hg hinj hsurj hexact t ht hw y)
  have tE8 : ∀ y : H2wR (A := A) t, H2wMap_R t g hg y = 0 ↔ y ∈ (H2wMap_R t f hf).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans (H2w_exact_mid_R f g hf hg hsurj hexact t y)
  have tD4 : ∀ h : H1wR (A := ElemDual A'') t, H1wMap_R t (dualMap g) hgse h = 0
      ↔ h ∈ (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  have tD5 : ∀ h : H1wR (A := ElemDual A) t, H1wMap_R t (dualMap f) hfse h = 0
      ↔ h ∈ (H1wMap_R t (dualMap g) hgse).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  -- Subgroup-form exactness (for dualizing bottom rows).
  have ex1_H1right : (H1wMap_R t g hg).range
      = (delta1_R f g hf hg hinj hsurj hexact t ht hw).ker :=
    AddSubgroup.ext fun h => (H1w_exact_right_R f g hf hg hinj hsurj hexact t ht hw h).symm
  have ex2_H0right : (H0wMap t (dualMap f) hfse).range
      = (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).ker :=
    AddSubgroup.ext fun a =>
      (H0w_exact_right_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw a).symm
  have ex2_H1right : (H1wMap_R t (dualMap f) hfse).range
      = (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_right_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  obtain ⟨hb2', hb2T', hb0', hb0T', hb1', hb1T'⟩ := chi_bij_of_selfdualW_R t ht hw hA'₂ hsd'
  obtain ⟨hb2'', hb2T'', hb0'', hb0T'', hb1'', hb1T''⟩ :=
    chi_bij_of_selfdualW_R t ht hw hA''₂ hsd''
  rw [isSelfDualW_iff_R t ht hw hA₂]
  refine ⟨⟨?_, chi2_surjective_R t ht hw hA₂⟩, ?_, ?_⟩
  · -- `χ²_A` injective: window `[H¹(A''), H²(A'), H²(A), H²(A'')]`.
    exact four_lemma_inj
      (delta1_R f g hf hg hinj hsurj hexact t ht hw) (H2wMap_R t f hf) (H2wMap_R t g hg)
      (dualMap (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw))
      (dualMap (H0wMap t (dualMap f) hfse)) (dualMap (H0wMap t (dualMap g) hgse))
      (chi1_R (A := A'') t ht hw) (chi2_R (A := A') t ht hw) (chi2_R (A := A) t ht hw)
      (chi2_R (A := A'') t ht hw)
      (square_delta1_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi2_square_R f hf t ht hw) (chi2_square_R g hg t ht hw)
      tE7 tE8
      (fun y hy => (dual_exact_pair (H1w_two_torsion_R t hD''₂)
        (H0wMap t (dualMap f) hfse)
        (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw) ex2_H0right y).mp hy)
      hb1''.surjective hb2'.injective hb2''.injective
  · -- `χ¹_A` injective: window `[H⁰(A''), H¹(A'), H¹(A), H¹(A'')]`.
    exact four_lemma_inj
      (delta0_R f g hf hg hinj hsurj hexact t ht hw) (H1wMap_R t f hf) (H1wMap_R t g hg)
      (dualMap (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw))
      (dualMap (H1wMap_R t (dualMap f) hfse)) (dualMap (H1wMap_R t (dualMap g) hgse))
      (chi0_R (A := A'') t ht hw) (chi1_R (A := A') t ht hw) (chi1_R (A := A) t ht hw)
      (chi1_R (A := A'') t ht hw)
      (square_delta0_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi1_square_R f hf t ht hw) (chi1_square_R g hg t ht hw)
      tE4 tE5
      (fun y hy => (dual_exact_pair (H2w_two_torsion_R t hD''₂)
        (H1wMap_R t (dualMap f) hfse)
        (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw) ex2_H1right y).mp hy)
      hb0''.surjective hb1'.injective hb1''.injective
  · -- `χ¹ᵀ_A` injective: transpose window `[H⁰(A'^∨), H¹(A''^∨), H¹(A^∨), H¹(A'^∨)]`.
    exact four_lemma_inj
      (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw) (H1wMap_R t (dualMap g) hgse)
      (H1wMap_R t (dualMap f) hfse)
      (dualMap (delta1_R f g hf hg hinj hsurj hexact t ht hw))
      (dualMap (H1wMap_R t g hg)) (dualMap (H1wMap_R t f hf))
      (chi0T_R (A := A') t ht hw) (chi1T_R (A := A'') t ht hw) (chi1T_R (A := A) t ht hw)
      (chi1T_R (A := A') t ht hw)
      (square_delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi1T_square_R g hg t ht hw) (chi1T_square_R f hf t ht hw)
      tD4 tD5
      (fun y hy => (dual_exact_pair (H2w_two_torsion_R t hA'₂)
        (H1wMap_R t g hg) (delta1_R f g hf hg hinj hsurj hexact t ht hw) ex1_H1right y).mp hy)
      hb0T'.surjective hb1T''.injective hb1T'.injective

include hf hg hinj hsurj hexact in
/-- **Direction (quot)** of `selfdualW_two_of_three_R`: if the sub `A'` and the middle `A` are
self-dual, so is the quotient `A''`.  Three `four_lemma_inj` windows across the duality ladder. -/
private theorem selfdualW_two_of_three_quot_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C)
    (ht : t.TameRel) (hw : t.WildRelR) (hsd' : IsSelfDualW_R t A') (hsdA : IsSelfDualW_R t A) :
    IsSelfDualW_R t A'' := by
  -- Torsion on the outer modules and the duals.
  have hA'₂ : ∀ a' : A', a' + a' = 0 := two_torsion_of_injective f hinj hA₂
  have hA''₂ : ∀ a'' : A'', a'' + a'' = 0 := two_torsion_of_surjective g hsurj hA₂
  have hD'₂ : ∀ lam : ElemDual A', lam + lam = 0 := ElemDual.add_self_eq_zero
  -- Finiteness of the subquotients.
  have : Finite (H1wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  -- The dualized SES and its equivariances (proof-irrelevant aliases).
  have hgse : ∀ (c : C) (lam : ElemDual A''), dualMap g (c • lam) = c • dualMap g lam :=
    dualMap_equivariant g hg
  have hfse : ∀ (c : C) (lam : ElemDual A), dualMap f (c • lam) = c • dualMap f lam :=
    dualMap_equivariant f hf
  have hginj := dualMap_injective g hsurj
  have hfsurj := dualMap_surjective hA₂ f hinj
  have hdualex := dual_ses_exact hA''₂ f g hexact
  -- Top-row pointwise exactness adapters.
  have tE5 : ∀ h : H1wR (A := A) t, H1wMap_R t g hg h = 0 ↔ h ∈ (H1wMap_R t f hf).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE6 : ∀ h : H1wR (A := A'') t, delta1_R f g hf hg hinj hsurj hexact t ht hw h = 0
      ↔ h ∈ (H1wMap_R t g hg).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_right_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE8 : ∀ y : H2wR (A := A) t, H2wMap_R t g hg y = 0 ↔ y ∈ (H2wMap_R t f hf).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans (H2w_exact_mid_R f g hf hg hsurj hexact t y)
  have tD3 : ∀ lam : H0w (A := ElemDual A') t,
      delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw lam = 0
        ↔ lam ∈ (H0wMap t (dualMap f) hfse).range :=
    fun lam => AddMonoidHom.mem_ker.symm.trans
      (H0w_exact_right_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw lam)
  have tD4 : ∀ h : H1wR (A := ElemDual A'') t, H1wMap_R t (dualMap g) hgse h = 0
      ↔ h ∈ (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  -- Subgroup-form exactness (for dualizing bottom rows).
  have ex1_H2left : (delta1_R f g hf hg hinj hsurj hexact t ht hw).range
      = (H2wMap_R t f hf).ker :=
    AddSubgroup.ext fun y => (H2w_exact_left_R f g hf hg hinj hsurj hexact t ht hw y).symm
  have ex2_H0mid : (H0wMap t (dualMap g) hgse).range = (H0wMap t (dualMap f) hfse).ker :=
    AddSubgroup.ext fun a =>
      (H0w_exact_mid (dualMap g) (dualMap f) hgse hfse hginj hdualex t a).symm
  have ex2_H1mid : (H1wMap_R t (dualMap g) hgse).range = (H1wMap_R t (dualMap f) hfse).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_mid_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  obtain ⟨hb2', hb2T', hb0', hb0T', hb1', hb1T'⟩ := chi_bij_of_selfdualW_R t ht hw hA'₂ hsd'
  obtain ⟨hb2A, hb2TA, hb0A, hb0TA, hb1A, hb1TA⟩ := chi_bij_of_selfdualW_R t ht hw hA₂ hsdA
  rw [isSelfDualW_iff_R t ht hw hA''₂]
  refine ⟨⟨?_, chi2_surjective_R t ht hw hA''₂⟩, ?_, ?_⟩
  · -- `χ²_{A''}` injective: end window `[H²(A'), H²(A), H²(A''), 0]`.
    exact four_lemma_inj
      (H2wMap_R t f hf) (H2wMap_R t g hg) (0 : H2wR (A := A'') t →+ PUnit.{1})
      (dualMap (H0wMap t (dualMap f) hfse)) (dualMap (H0wMap t (dualMap g) hgse))
      (0 : ElemDual (H0w (A := ElemDual A'') t) →+ PUnit.{1})
      (chi2_R (A := A') t ht hw) (chi2_R (A := A) t ht hw) (chi2_R (A := A'') t ht hw)
      (AddMonoidHom.id PUnit.{1})
      (chi2_square_R f hf t ht hw) (chi2_square_R g hg t ht hw)
      (fun x => Subsingleton.elim _ _)
      tE8
      (fun x => iff_of_true (Subsingleton.elim _ _)
        (AddMonoidHom.mem_range.mpr (H2wMap_g_surjective_R g hg hsurj t x)))
      (fun y hy => (dual_exact_pair (H0w_two_torsion t hD'₂)
        (H0wMap t (dualMap g) hgse) (H0wMap t (dualMap f) hfse) ex2_H0mid y).mp hy)
      hb2'.surjective hb2A.injective (fun a b _ => Subsingleton.elim a b)
  · -- `χ¹_{A''}` injective: window `[H¹(A'), H¹(A), H¹(A''), H²(A')]`.
    exact four_lemma_inj
      (H1wMap_R t f hf) (H1wMap_R t g hg) (delta1_R f g hf hg hinj hsurj hexact t ht hw)
      (dualMap (H1wMap_R t (dualMap f) hfse)) (dualMap (H1wMap_R t (dualMap g) hgse))
      (dualMap (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw))
      (chi1_R (A := A') t ht hw) (chi1_R (A := A) t ht hw) (chi1_R (A := A'') t ht hw)
      (chi2_R (A := A') t ht hw)
      (chi1_square_R f hf t ht hw) (chi1_square_R g hg t ht hw)
      (square_delta1_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      tE5 tE6
      (fun y hy => (dual_exact_pair (H1w_two_torsion_R t hD'₂)
        (H1wMap_R t (dualMap g) hgse) (H1wMap_R t (dualMap f) hfse) ex2_H1mid y).mp hy)
      hb1'.surjective hb1A.injective hb2'.injective
  · -- `χ¹ᵀ_{A''}` injective: transpose window `[H⁰(A^∨), H⁰(A'^∨), H¹(A''^∨), H¹(A^∨)]`.
    exact four_lemma_inj
      (H0wMap t (dualMap f) hfse) (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (H1wMap_R t (dualMap g) hgse)
      (dualMap (H2wMap_R t f hf)) (dualMap (delta1_R f g hf hg hinj hsurj hexact t ht hw))
      (dualMap (H1wMap_R t g hg))
      (chi0T_R (A := A) t ht hw) (chi0T_R (A := A') t ht hw) (chi1T_R (A := A'') t ht hw)
      (chi1T_R (A := A) t ht hw)
      (chi0T_square_R f hf t ht hw)
      (square_delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi1T_square_R g hg t ht hw)
      tD3 tD4
      (fun y hy => (dual_exact_pair (H2w_two_torsion_R t hA₂)
        (delta1_R f g hf hg hinj hsurj hexact t ht hw) (H2wMap_R t f hf) ex1_H2left y).mp hy)
      hb0TA.surjective (chi0T_injective_R t ht hw) hb1TA.injective

include hf hg hinj hsurj hexact in
/-- **Direction (sub)** of `selfdualW_two_of_three_R`: if the middle `A` and the quotient `A''` are
self-dual, so is the sub `A'`.  Three `four_lemma_inj` windows across the duality ladder. -/
private theorem selfdualW_two_of_three_sub_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C)
    (ht : t.TameRel) (hw : t.WildRelR) (hsdA : IsSelfDualW_R t A) (hsd'' : IsSelfDualW_R t A'') :
    IsSelfDualW_R t A' := by
  -- Torsion on the outer modules and the duals.
  have hA'₂ : ∀ a' : A', a' + a' = 0 := two_torsion_of_injective f hinj hA₂
  have hA''₂ : ∀ a'' : A'', a'' + a'' = 0 := two_torsion_of_surjective g hsurj hA₂
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := ElemDual.add_self_eq_zero
  -- Finiteness of the subquotients.
  have : Finite (H1wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  -- The dualized SES and its equivariances (proof-irrelevant aliases).
  have hgse : ∀ (c : C) (lam : ElemDual A''), dualMap g (c • lam) = c • dualMap g lam :=
    dualMap_equivariant g hg
  have hfse : ∀ (c : C) (lam : ElemDual A), dualMap f (c • lam) = c • dualMap f lam :=
    dualMap_equivariant f hf
  have hginj := dualMap_injective g hsurj
  have hfsurj := dualMap_surjective hA₂ f hinj
  have hdualex := dual_ses_exact hA''₂ f g hexact
  -- Top-row pointwise exactness adapters.
  have tE3 : ∀ a'' : H0w (A := A'') t,
      delta0_R f g hf hg hinj hsurj hexact t ht hw a'' = 0 ↔ a'' ∈ (H0wMap t g hg).range :=
    fun a'' => AddMonoidHom.mem_ker.symm.trans
      (H0w_exact_right_R f g hf hg hinj hsurj hexact t ht hw a'')
  have tE4 : ∀ h : H1wR (A := A') t, H1wMap_R t f hf h = 0
      ↔ h ∈ (delta0_R f g hf hg hinj hsurj hexact t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE6 : ∀ h : H1wR (A := A'') t, delta1_R f g hf hg hinj hsurj hexact t ht hw h = 0
      ↔ h ∈ (H1wMap_R t g hg).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_right_R f g hf hg hinj hsurj hexact t ht hw h)
  have tE7 : ∀ y : H2wR (A := A') t, H2wMap_R t f hf y = 0
      ↔ y ∈ (delta1_R f g hf hg hinj hsurj hexact t ht hw).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans
      (H2w_exact_left_R f g hf hg hinj hsurj hexact t ht hw y)
  have tD5 : ∀ h : H1wR (A := ElemDual A) t, H1wMap_R t (dualMap f) hfse h = 0
      ↔ h ∈ (H1wMap_R t (dualMap g) hgse).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  have tD6 : ∀ h : H1wR (A := ElemDual A') t,
      delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw h = 0
        ↔ h ∈ (H1wMap_R t (dualMap f) hfse).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_right_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  -- Subgroup-form exactness (for dualizing bottom rows).
  have ex1_H1mid : (H1wMap_R t f hf).range = (H1wMap_R t g hg).ker :=
    AddSubgroup.ext fun h => (H1w_exact_mid_R f g hf hg hinj hsurj hexact t ht hw h).symm
  have ex2_H1left : (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).range
      = (H1wMap_R t (dualMap g) hgse).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_left_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  have ex2_H2left : (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw).range
      = (H2wMap_R t (dualMap g) hgse).ker :=
    AddSubgroup.ext fun y =>
      (H2w_exact_left_R (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw y).symm
  obtain ⟨hb2A, hb2TA, hb0A, hb0TA, hb1A, hb1TA⟩ := chi_bij_of_selfdualW_R t ht hw hA₂ hsdA
  obtain ⟨hb2'', hb2T'', hb0'', hb0T'', hb1'', hb1T''⟩ :=
    chi_bij_of_selfdualW_R t ht hw hA''₂ hsd''
  rw [isSelfDualW_iff_R t ht hw hA'₂]
  refine ⟨⟨?_, chi2_surjective_R t ht hw hA'₂⟩, ?_, ?_⟩
  · -- `χ²_{A'}` injective: window `[H¹(A), H¹(A''), H²(A'), H²(A)]`.
    exact four_lemma_inj
      (H1wMap_R t g hg) (delta1_R f g hf hg hinj hsurj hexact t ht hw) (H2wMap_R t f hf)
      (dualMap (H1wMap_R t (dualMap g) hgse))
      (dualMap (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw))
      (dualMap (H0wMap t (dualMap f) hfse))
      (chi1_R (A := A) t ht hw) (chi1_R (A := A'') t ht hw) (chi2_R (A := A') t ht hw)
      (chi2_R (A := A) t ht hw)
      (chi1_square_R g hg t ht hw)
      (square_delta1_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi2_square_R f hf t ht hw)
      tE6 tE7
      (fun y hy => (dual_exact_pair (H1w_two_torsion_R t hD₂)
        (delta0D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (H1wMap_R t (dualMap g) hgse) ex2_H1left y).mp hy)
      hb1A.surjective hb1''.injective hb2A.injective
  · -- `χ¹_{A'}` injective: window `[H⁰(A), H⁰(A''), H¹(A'), H¹(A)]`.
    exact four_lemma_inj
      (H0wMap t g hg) (delta0_R f g hf hg hinj hsurj hexact t ht hw) (H1wMap_R t f hf)
      (dualMap (H2wMap_R t (dualMap g) hgse))
      (dualMap (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw))
      (dualMap (H1wMap_R t (dualMap f) hfse))
      (chi0_R (A := A) t ht hw) (chi0_R (A := A'') t ht hw) (chi1_R (A := A') t ht hw)
      (chi1_R (A := A) t ht hw)
      (chi0_square_R g hg t ht hw)
      (square_delta0_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (chi1_square_R f hf t ht hw)
      tE3 tE4
      (fun y hy => (dual_exact_pair (H2w_two_torsion_R t hD₂)
        (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (H2wMap_R t (dualMap g) hgse) ex2_H2left y).mp hy)
      hb0A.surjective (chi0_injective_R t ht hw hA''₂) hb1A.injective
  · -- `χ¹ᵀ_{A'}` injective: transpose window `[H¹(A''^∨), H¹(A^∨), H¹(A'^∨), H²(A''^∨)]`.
    exact four_lemma_inj
      (H1wMap_R t (dualMap g) hgse) (H1wMap_R t (dualMap f) hfse)
      (delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      (dualMap (H1wMap_R t g hg)) (dualMap (H1wMap_R t f hf))
      (dualMap (delta0_R f g hf hg hinj hsurj hexact t ht hw))
      (chi1T_R (A := A'') t ht hw) (chi1T_R (A := A) t ht hw) (chi1T_R (A := A') t ht hw)
      (chi2T_R (A := A'') t ht hw)
      (chi1T_square_R g hg t ht hw) (chi1T_square_R f hf t ht hw)
      (square_delta1D_R f g hf hg hinj hsurj hexact hA₂ t ht hw)
      tD5 tD6
      (fun y hy => (dual_exact_pair (H1w_two_torsion_R t hA''₂)
        (H1wMap_R t f hf) (H1wMap_R t g hg) ex1_H1mid y).mp hy)
      hb1T''.surjective hb1TA.injective hb2T''.injective

include hf hg hinj hsurj hexact in
/-- **Lemma 5.11, word-internal form (exact-cone dévissage)**: two-out-of-three for
`IsSelfDualW_R` along the module SES.  Proof: translate each `IsSelfDualW_R` into
`χ`-bijectivities (`isSelfDualW_iff_R`, `chi_bij_of_selfdualW_R`), then chase the duality ladder —
nine four-lemma windows across the two LESs (word complex of the SES, and of its dualization)
tied by the `lemma_5_6_R`-squares, the evaluation squares and the δ-squares. -/
theorem selfdualW_two_of_three_R (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRelR) :
    (IsSelfDualW_R t A' ∧ IsSelfDualW_R t A'' → IsSelfDualW_R t A) ∧
    (IsSelfDualW_R t A' ∧ IsSelfDualW_R t A → IsSelfDualW_R t A'') ∧
    (IsSelfDualW_R t A ∧ IsSelfDualW_R t A'' → IsSelfDualW_R t A') := by
  refine ⟨fun ⟨hsd', hsd''⟩ =>
      selfdualW_two_of_three_mid_R f g hf hg hinj hsurj hexact hA₂ t ht hw hsd' hsd'',
    fun ⟨hsd', hsdA⟩ =>
      selfdualW_two_of_three_quot_R f g hf hg hinj hsurj hexact hA₂ t ht hw hsd' hsdA,
    fun ⟨hsdA, hsd''⟩ =>
      selfdualW_two_of_three_sub_R f g hf hg hinj hsurj hexact hA₂ t ht hw hsdA hsd''⟩

end LES

end GQ2.FoxH
