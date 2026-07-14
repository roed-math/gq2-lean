import GQ2.Devissage.LESExact

/-!
# §5.11 dévissage: the dualized SES, δ-squares, and the master two-of-three

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
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
noncomputable def delta0D (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) : H0w (A := ElemDual A') t →+ H1w (A := ElemDual A'') t :=
  delta0 (dualMap g) (dualMap f) (dualMap_equivariant g hg) (dualMap_equivariant f hf)
    (dualMap_injective g hsurj) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t ht hw

include hf hg hinj hsurj hexact in
/-- `δ¹` of the dualized SES: `H¹w(A'^∨) →+ H²w(A''^∨)`. -/
noncomputable def delta1D (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) : H1w (A := ElemDual A') t →+ H2w (A := ElemDual A'') t :=
  delta1 (dualMap g) (dualMap f) (dualMap_equivariant g hg) (dualMap_equivariant f hf)
    (dualMap_injective g hsurj) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t ht hw

omit [Finite A'] in
include hf hg hinj hsurj hexact in
/-- **δ-square core 1**: evaluating `λ ∈ H⁰w(A'^∨)` on the `δ¹`-snake of `c''` equals pairing
`c''` against the dual `δ⁰`-snake word of `λ`.  (Lift `λ` to `Λ` along `f^∨`; both sides equal
`B(lift c'', d⁰Λ)` by Prop 5.8 right resp. Lemma 5.6.) -/
theorem delta_square_core1 (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (c'' : Z1w (A := A'') t) (lam : H0w (A := ElemDual A') t) :
    lam.1 ((snakeZ f g hg hsurj hexact t c'').1 + (snakeZ f g hg hsurj hexact t c'').2)
      = mixedB t c''.1
          (snake0Z' (dualMap g) (dualMap f) (dualMap_equivariant f hf)
            (dualMap_surjective hA₂ f hinj)
            (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam) := by
  set Λ : ElemDual A := (dualMap_surjective hA₂ f hinj lam.1).choose with hΛdef
  have hΛ : dualMap f Λ = lam.1 := (dualMap_surjective hA₂ f hinj lam.1).choose_spec
  set w : Fin 4 → ElemDual A'' := snake0Z' (dualMap g) (dualMap f)
    (dualMap_equivariant f hf) (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam with hwdef
  have hws : (fun i => dualMap g (w i)) = d0 t Λ :=
    snake0Z'_spec (dualMap g) (dualMap f) (dualMap_equivariant f hf)
      (dualMap_surjective hA₂ f hinj)
      (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam
  have hz := snakeZ_spec f g hg hsurj hexact t c''
  have hz1 : f (snakeZ f g hg hsurj hexact t c'').1
      = (d1Fun t (snakeLift g hsurj c''.1)).1 := congrArg Prod.fst hz
  have hz2 : f (snakeZ f g hg hsurj hexact t c'').2
      = (d1Fun t (snakeLift g hsurj c''.1)).2 := congrArg Prod.snd hz
  calc lam.1 ((snakeZ f g hg hsurj hexact t c'').1 + (snakeZ f g hg hsurj hexact t c'').2)
      = Λ (f ((snakeZ f g hg hsurj hexact t c'').1 + (snakeZ f g hg hsurj hexact t c'').2)) := by
        rw [← hΛ]; rfl
    _ = Λ ((d1Fun t (snakeLift g hsurj c''.1)).1 + (d1Fun t (snakeLift g hsurj c''.1)).2) := by
        rw [map_add, hz1, hz2]
    _ = mixedB t (snakeLift g hsurj c''.1) (d0 t Λ) :=
        (prop_5_8_right t ht hw (snakeLift g hsurj c''.1) Λ).symm
    _ = mixedB t (snakeLift g hsurj c''.1) (fun i => dualMap g (w i)) := by rw [hws]
    _ = mixedB t (fun i => g (snakeLift g hsurj c''.1 i)) w :=
        (lemma_5_6 g hg t (snakeLift g hsurj c''.1) w).symm
    _ = mixedB t c''.1 w := by
        rw [show (fun i => g (snakeLift g hsurj c''.1 i)) = c''.1 from
          funext (snakeLift_spec g hsurj c''.1)]

include hf hg hinj hsurj hexact in
/-- **δ-square core 2**: pairing the primal `δ⁰`-snake word of `a''` against a dual cocycle `y'`
equals evaluating the dual `δ¹`-snake of `y'` on `a''`.  (Mirror of core 1: Prop 5.8 left +
Lemma 5.6 through the lifts.) -/
theorem delta_square_core2 (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (a'' : H0w (A := A'') t) (y' : Z1w (A := ElemDual A') t) :
    mixedB t (snake0Z' f g hg hsurj hexact t a'') y'.1
      = (snakeZ (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').1 a''.1
        + (snakeZ (dualMap g) (dualMap f) (dualMap_equivariant f hf)
            (dualMap_surjective hA₂ f hinj)
            (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').2
          a''.1 := by
  set Y : Fin 4 → ElemDual A :=
    snakeLift (dualMap f) (dualMap_surjective hA₂ f hinj) y'.1 with hYdef
  have hY : ∀ i, dualMap f (Y i) = y'.1 i :=
    snakeLift_spec (dualMap f) (dualMap_surjective hA₂ f hinj) y'.1
  set q := snakeZ (dualMap g) (dualMap f) (dualMap_equivariant f hf)
    (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y' with hqdef
  have hq := snakeZ_spec (dualMap g) (dualMap f) (dualMap_equivariant f hf)
    (dualMap_surjective hA₂ f hinj)
    (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y'
  have hq1 : dualMap g q.1 = (d1Fun (A := ElemDual A) t Y).1 := congrArg Prod.fst hq
  have hq2 : dualMap g q.2 = (d1Fun (A := ElemDual A) t Y).2 := congrArg Prod.snd hq
  have hws : (fun i => f (snake0Z' f g hg hsurj hexact t a'' i))
      = d0 t (hsurj a''.1).choose := snake0Z'_spec f g hg hsurj hexact t a''
  calc mixedB t (snake0Z' f g hg hsurj hexact t a'') y'.1
      = mixedB t (snake0Z' f g hg hsurj hexact t a'') (fun i => dualMap f (Y i)) := by
        rw [show (fun i => dualMap f (Y i)) = y'.1 from funext hY]
    _ = mixedB t (fun i => f (snake0Z' f g hg hsurj hexact t a'' i)) Y :=
        (lemma_5_6 f hf t (snake0Z' f g hg hsurj hexact t a'') Y).symm
    _ = mixedB t (d0 t (hsurj a''.1).choose) Y := by rw [hws]
    _ = ((d1Fun (A := ElemDual A) t Y).1 + (d1Fun (A := ElemDual A) t Y).2)
          ((hsurj a''.1).choose) := prop_5_8_left t ht hw ((hsurj a''.1).choose) Y
    _ = (d1Fun (A := ElemDual A) t Y).1 ((hsurj a''.1).choose)
          + (d1Fun (A := ElemDual A) t Y).2 ((hsurj a''.1).choose) := rfl
    _ = (dualMap g q.1) ((hsurj a''.1).choose) + (dualMap g q.2) ((hsurj a''.1).choose) := by
        rw [hq1, hq2]
    _ = q.1 (g ((hsurj a''.1).choose)) + q.2 (g ((hsurj a''.1).choose)) := rfl
    _ = q.1 a''.1 + q.2 a''.1 := by rw [(hsurj a''.1).choose_spec]

include hf hg hinj hsurj hexact in
/-- **δ-square (1,2)**: `χ²_{A'} ∘ δ¹ = (δ⁰ of the dual SES)^∨ ∘ χ¹_{A''}`. -/
theorem square_delta1 (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (h'' : H1w (A := A'') t) :
    chi2 (A := A') t ht hw (delta1 f g hf hg hinj hsurj hexact t ht hw h'')
      = dualMap (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (chi1 (A := A'') t ht hw h'') := by
  obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h''
  apply ElemDual.ext
  intro lam
  show lam.1 ((snakeZ f g hg hsurj hexact t c'').1 + (snakeZ f g hg hsurj hexact t c'').2)
    = mixedB t c''.1
        (snake0Z' (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam)
  exact delta_square_core1 f g hf hg hinj hsurj hexact hA₂ t ht hw c'' lam

include hf hg hinj hsurj hexact in
/-- **δ-square (0,1)**: `χ¹_{A'} ∘ δ⁰ = (δ¹ of the dual SES)^∨ ∘ χ⁰_{A''}`. -/
theorem square_delta0 (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (a'' : H0w (A := A'') t) :
    chi1 (A := A') t ht hw (delta0 f g hf hg hinj hsurj hexact t ht hw a'')
      = dualMap (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (chi0 (A := A'') t ht hw a'') := by
  apply ElemDual.ext
  intro z'
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective z'
  show mixedB t (snake0Z' f g hg hsurj hexact t a'') y'.1 = _
  exact delta_square_core2 f g hf hg hinj hsurj hexact hA₂ t ht hw a'' y'

include hf hg hinj hsurj hexact in
/-- **δ-square (0,1), transposed**: `χ¹ᵀ_{A''} ∘ δ⁰_dual = (δ¹)^∨ ∘ χ⁰ᵀ_{A'}`. -/
theorem square_delta0D (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (lam : H0w (A := ElemDual A') t) :
    chi1T (A := A'') t ht hw (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw lam)
      = dualMap (delta1 f g hf hg hinj hsurj hexact t ht hw)
          (chi0T (A := A') t ht hw lam) := by
  apply ElemDual.ext
  intro h''
  obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h''
  show mixedB t c''.1
      (snake0Z' (dualMap g) (dualMap f) (dualMap_equivariant f hf)
        (dualMap_surjective hA₂ f hinj)
        (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t lam)
    = lam.1 ((snakeZ f g hg hsurj hexact t c'').1 + (snakeZ f g hg hsurj hexact t c'').2)
  exact (delta_square_core1 f g hf hg hinj hsurj hexact hA₂ t ht hw c'' lam).symm

include hf hg hinj hsurj hexact in
/-- **δ-square (1,2), transposed**: `χ²ᵀ_{A''} ∘ δ¹_dual = (δ⁰)^∨ ∘ χ¹ᵀ_{A'}`. -/
theorem square_delta1D (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) (z' : H1w (A := ElemDual A') t) :
    chi2T (A := A'') t ht hw (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw z')
      = dualMap (delta0 f g hf hg hinj hsurj hexact t ht hw)
          (chi1T (A := A') t ht hw z') := by
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective z'
  apply ElemDual.ext
  intro a''
  show (snakeZ (dualMap g) (dualMap f) (dualMap_equivariant f hf)
        (dualMap_surjective hA₂ f hinj)
        (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').1 a''.1
      + (snakeZ (dualMap g) (dualMap f) (dualMap_equivariant f hf)
          (dualMap_surjective hA₂ f hinj)
          (dual_ses_exact (two_torsion_of_surjective g hsurj hA₂) f g hexact) t y').2 a''.1
    = mixedB t (snake0Z' f g hg hsurj hexact t a'') y'.1
  exact (delta_square_core2 f g hf hg hinj hsurj hexact hA₂ t ht hw a'' y').symm

include hf hg hinj hsurj hexact in
/-- **Lemma 5.11, word-internal form (exact-cone dévissage)**: two-out-of-three for
`IsSelfDualW` along the module SES.  Proof: translate each `IsSelfDualW` into
`χ`-bijectivities (`isSelfDualW_iff`, `chi_bij_of_selfdualW`), then chase the duality ladder —
nine four-lemma windows across the two LESs (word complex of the SES, and of its dualization)
tied by the `lemma_5_6`-squares, the evaluation squares and the δ-squares. -/
theorem selfdualW_two_of_three (hA₂ : ∀ a : A, a + a = 0) (t : Marking C) (ht : t.TameRel)
    (hw : t.WildRel) :
    (IsSelfDualW t A' ∧ IsSelfDualW t A'' → IsSelfDualW t A) ∧
    (IsSelfDualW t A' ∧ IsSelfDualW t A → IsSelfDualW t A'') ∧
    (IsSelfDualW t A ∧ IsSelfDualW t A'' → IsSelfDualW t A') := by
  -- Torsion on the outer modules and the duals.
  have hA'₂ : ∀ a' : A', a' + a' = 0 := two_torsion_of_injective f hinj hA₂
  have hA''₂ : ∀ a'' : A'', a'' + a'' = 0 := two_torsion_of_surjective g hsurj hA₂
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := ElemDual.add_self_eq_zero
  have hD'₂ : ∀ lam : ElemDual A', lam + lam = 0 := ElemDual.add_self_eq_zero
  have hD''₂ : ∀ lam : ElemDual A'', lam + lam = 0 := ElemDual.add_self_eq_zero
  -- Finiteness of the subquotients.
  have : Finite (H1w (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  -- The dualized SES and its equivariances (proof-irrelevant aliases).
  have hgse : ∀ (c : C) (lam : ElemDual A''), dualMap g (c • lam) = c • dualMap g lam :=
    dualMap_equivariant g hg
  have hfse : ∀ (c : C) (lam : ElemDual A), dualMap f (c • lam) = c • dualMap f lam :=
    dualMap_equivariant f hf
  have hginj := dualMap_injective g hsurj
  have hfsurj := dualMap_surjective hA₂ f hinj
  have hdualex := dual_ses_exact hA''₂ f g hexact
  -- Top-row pointwise exactness adapters, LES-1.
  have tE3 : ∀ a'' : H0w (A := A'') t,
      delta0 f g hf hg hinj hsurj hexact t ht hw a'' = 0 ↔ a'' ∈ (H0wMap t g hg).range :=
    fun a'' => AddMonoidHom.mem_ker.symm.trans
      (H0w_exact_right f g hf hg hinj hsurj hexact t ht hw a'')
  have tE4 : ∀ h : H1w (A := A') t, H1wMap t f hf h = 0
      ↔ h ∈ (delta0 f g hf hg hinj hsurj hexact t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left f g hf hg hinj hsurj hexact t ht hw h)
  have tE5 : ∀ h : H1w (A := A) t, H1wMap t g hg h = 0 ↔ h ∈ (H1wMap t f hf).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid f g hf hg hinj hsurj hexact t ht hw h)
  have tE6 : ∀ h : H1w (A := A'') t, delta1 f g hf hg hinj hsurj hexact t ht hw h = 0
      ↔ h ∈ (H1wMap t g hg).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_right f g hf hg hinj hsurj hexact t ht hw h)
  have tE7 : ∀ y : H2w (A := A') t, H2wMap t f hf y = 0
      ↔ y ∈ (delta1 f g hf hg hinj hsurj hexact t ht hw).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans
      (H2w_exact_left f g hf hg hinj hsurj hexact t ht hw y)
  have tE8 : ∀ y : H2w (A := A) t, H2wMap t g hg y = 0 ↔ y ∈ (H2wMap t f hf).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans (H2w_exact_mid f g hf hg hsurj hexact t y)
  -- Top-row pointwise exactness adapters, LES-2 (ascribed in `delta0D/delta1D` spelling).
  have tD3 : ∀ lam : H0w (A := ElemDual A') t,
      delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw lam = 0
        ↔ lam ∈ (H0wMap t (dualMap f) hfse).range :=
    fun lam => AddMonoidHom.mem_ker.symm.trans
      (H0w_exact_right (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw lam)
  have tD4 : ∀ h : H1w (A := ElemDual A'') t, H1wMap t (dualMap g) hgse h = 0
      ↔ h ∈ (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_left (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  have tD5 : ∀ h : H1w (A := ElemDual A) t, H1wMap t (dualMap f) hfse h = 0
      ↔ h ∈ (H1wMap t (dualMap g) hgse).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_mid (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  have tD6 : ∀ h : H1w (A := ElemDual A') t,
      delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw h = 0
        ↔ h ∈ (H1wMap t (dualMap f) hfse).range :=
    fun h => AddMonoidHom.mem_ker.symm.trans
      (H1w_exact_right (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h)
  have tD7 : ∀ y : H2w (A := ElemDual A'') t, H2wMap t (dualMap g) hgse y = 0
      ↔ y ∈ (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw).range :=
    fun y => AddMonoidHom.mem_ker.symm.trans
      (H2w_exact_left (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw y)
  -- Subgroup-form exactness (for dualizing bottom rows).
  have ex1_H1mid : (H1wMap t f hf).range = (H1wMap t g hg).ker :=
    AddSubgroup.ext fun h => (H1w_exact_mid f g hf hg hinj hsurj hexact t ht hw h).symm
  have ex1_H1right : (H1wMap t g hg).range
      = (delta1 f g hf hg hinj hsurj hexact t ht hw).ker :=
    AddSubgroup.ext fun h => (H1w_exact_right f g hf hg hinj hsurj hexact t ht hw h).symm
  have ex1_H2left : (delta1 f g hf hg hinj hsurj hexact t ht hw).range
      = (H2wMap t f hf).ker :=
    AddSubgroup.ext fun y => (H2w_exact_left f g hf hg hinj hsurj hexact t ht hw y).symm
  have ex2_H0mid : (H0wMap t (dualMap g) hgse).range = (H0wMap t (dualMap f) hfse).ker :=
    AddSubgroup.ext fun a =>
      (H0w_exact_mid (dualMap g) (dualMap f) hgse hfse hginj hdualex t a).symm
  have ex2_H0right : (H0wMap t (dualMap f) hfse).range
      = (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw).ker :=
    AddSubgroup.ext fun a =>
      (H0w_exact_right (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw a).symm
  have ex2_H1left : (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw).range
      = (H1wMap t (dualMap g) hgse).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_left (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  have ex2_H1mid : (H1wMap t (dualMap g) hgse).range = (H1wMap t (dualMap f) hfse).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_mid (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  have ex2_H1right : (H1wMap t (dualMap f) hfse).range
      = (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw).ker :=
    AddSubgroup.ext fun h =>
      (H1w_exact_right (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw h).symm
  have ex2_H2left : (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw).range
      = (H2wMap t (dualMap g) hgse).ker :=
    AddSubgroup.ext fun y =>
      (H2w_exact_left (dualMap g) (dualMap f) hgse hfse hginj hfsurj hdualex t ht hw y).symm
  refine ⟨?_, ?_, ?_⟩
  · -- **Direction 1**: `A'`, `A''` self-dual ⟹ `A` self-dual.
    rintro ⟨hsd', hsd''⟩
    obtain ⟨hb2', hb2T', hb0', hb0T', hb1', hb1T'⟩ := chi_bij_of_selfdualW t ht hw hA'₂ hsd'
    obtain ⟨hb2'', hb2T'', hb0'', hb0T'', hb1'', hb1T''⟩ :=
      chi_bij_of_selfdualW t ht hw hA''₂ hsd''
    rw [isSelfDualW_iff t ht hw hA₂]
    refine ⟨⟨?_, chi2_surjective t ht hw hA₂⟩, ?_, ?_⟩
    · -- `χ²_A` injective: window `[H¹(A''), H²(A'), H²(A), H²(A'')]`.
      exact four_lemma_inj
        (delta1 f g hf hg hinj hsurj hexact t ht hw) (H2wMap t f hf) (H2wMap t g hg)
        (dualMap (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw))
        (dualMap (H0wMap t (dualMap f) hfse)) (dualMap (H0wMap t (dualMap g) hgse))
        (chi1 (A := A'') t ht hw) (chi2 (A := A') t ht hw) (chi2 (A := A) t ht hw)
        (chi2 (A := A'') t ht hw)
        (square_delta1 f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi2_square f hf t ht hw) (chi2_square g hg t ht hw)
        tE7 tE8
        (fun y hy => (dual_exact_pair (H1w_two_torsion t hD''₂)
          (H0wMap t (dualMap f) hfse)
          (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw) ex2_H0right y).mp hy)
        hb1''.surjective hb2'.injective hb2''.injective
    · -- `χ¹_A` injective: window `[H⁰(A''), H¹(A'), H¹(A), H¹(A'')]`.
      exact four_lemma_inj
        (delta0 f g hf hg hinj hsurj hexact t ht hw) (H1wMap t f hf) (H1wMap t g hg)
        (dualMap (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw))
        (dualMap (H1wMap t (dualMap f) hfse)) (dualMap (H1wMap t (dualMap g) hgse))
        (chi0 (A := A'') t ht hw) (chi1 (A := A') t ht hw) (chi1 (A := A) t ht hw)
        (chi1 (A := A'') t ht hw)
        (square_delta0 f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi1_square f hf t ht hw) (chi1_square g hg t ht hw)
        tE4 tE5
        (fun y hy => (dual_exact_pair (H2w_two_torsion t hD''₂)
          (H1wMap t (dualMap f) hfse)
          (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw) ex2_H1right y).mp hy)
        hb0''.surjective hb1'.injective hb1''.injective
    · -- `χ¹ᵀ_A` injective: transpose window `[H⁰(A'^∨), H¹(A''^∨), H¹(A^∨), H¹(A'^∨)]`.
      exact four_lemma_inj
        (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw) (H1wMap t (dualMap g) hgse)
        (H1wMap t (dualMap f) hfse)
        (dualMap (delta1 f g hf hg hinj hsurj hexact t ht hw))
        (dualMap (H1wMap t g hg)) (dualMap (H1wMap t f hf))
        (chi0T (A := A') t ht hw) (chi1T (A := A'') t ht hw) (chi1T (A := A) t ht hw)
        (chi1T (A := A') t ht hw)
        (square_delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi1T_square g hg t ht hw) (chi1T_square f hf t ht hw)
        tD4 tD5
        (fun y hy => (dual_exact_pair (H2w_two_torsion t hA'₂)
          (H1wMap t g hg) (delta1 f g hf hg hinj hsurj hexact t ht hw) ex1_H1right y).mp hy)
        hb0T'.surjective hb1T''.injective hb1T'.injective
  · -- **Direction 2**: `A'`, `A` self-dual ⟹ `A''` self-dual.
    rintro ⟨hsd', hsdA⟩
    obtain ⟨hb2', hb2T', hb0', hb0T', hb1', hb1T'⟩ := chi_bij_of_selfdualW t ht hw hA'₂ hsd'
    obtain ⟨hb2A, hb2TA, hb0A, hb0TA, hb1A, hb1TA⟩ := chi_bij_of_selfdualW t ht hw hA₂ hsdA
    rw [isSelfDualW_iff t ht hw hA''₂]
    refine ⟨⟨?_, chi2_surjective t ht hw hA''₂⟩, ?_, ?_⟩
    · -- `χ²_{A''}` injective: end window `[H²(A'), H²(A), H²(A''), 0]`.
      exact four_lemma_inj
        (H2wMap t f hf) (H2wMap t g hg) (0 : H2w (A := A'') t →+ PUnit.{1})
        (dualMap (H0wMap t (dualMap f) hfse)) (dualMap (H0wMap t (dualMap g) hgse))
        (0 : ElemDual (H0w (A := ElemDual A'') t) →+ PUnit.{1})
        (chi2 (A := A') t ht hw) (chi2 (A := A) t ht hw) (chi2 (A := A'') t ht hw)
        (AddMonoidHom.id PUnit.{1})
        (chi2_square f hf t ht hw) (chi2_square g hg t ht hw)
        (fun x => Subsingleton.elim _ _)
        tE8
        (fun x => iff_of_true (Subsingleton.elim _ _)
          (AddMonoidHom.mem_range.mpr (H2wMap_g_surjective g hg hsurj t x)))
        (fun y hy => (dual_exact_pair (H0w_two_torsion t hD'₂)
          (H0wMap t (dualMap g) hgse) (H0wMap t (dualMap f) hfse) ex2_H0mid y).mp hy)
        hb2'.surjective hb2A.injective (fun a b _ => Subsingleton.elim a b)
    · -- `χ¹_{A''}` injective: window `[H¹(A'), H¹(A), H¹(A''), H²(A')]`.
      exact four_lemma_inj
        (H1wMap t f hf) (H1wMap t g hg) (delta1 f g hf hg hinj hsurj hexact t ht hw)
        (dualMap (H1wMap t (dualMap f) hfse)) (dualMap (H1wMap t (dualMap g) hgse))
        (dualMap (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw))
        (chi1 (A := A') t ht hw) (chi1 (A := A) t ht hw) (chi1 (A := A'') t ht hw)
        (chi2 (A := A') t ht hw)
        (chi1_square f hf t ht hw) (chi1_square g hg t ht hw)
        (square_delta1 f g hf hg hinj hsurj hexact hA₂ t ht hw)
        tE5 tE6
        (fun y hy => (dual_exact_pair (H1w_two_torsion t hD'₂)
          (H1wMap t (dualMap g) hgse) (H1wMap t (dualMap f) hfse) ex2_H1mid y).mp hy)
        hb1'.surjective hb1A.injective hb2'.injective
    · -- `χ¹ᵀ_{A''}` injective: transpose window `[H⁰(A^∨), H⁰(A'^∨), H¹(A''^∨), H¹(A^∨)]`.
      exact four_lemma_inj
        (H0wMap t (dualMap f) hfse) (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (H1wMap t (dualMap g) hgse)
        (dualMap (H2wMap t f hf)) (dualMap (delta1 f g hf hg hinj hsurj hexact t ht hw))
        (dualMap (H1wMap t g hg))
        (chi0T (A := A) t ht hw) (chi0T (A := A') t ht hw) (chi1T (A := A'') t ht hw)
        (chi1T (A := A) t ht hw)
        (chi0T_square f hf t ht hw)
        (square_delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi1T_square g hg t ht hw)
        tD3 tD4
        (fun y hy => (dual_exact_pair (H2w_two_torsion t hA₂)
          (delta1 f g hf hg hinj hsurj hexact t ht hw) (H2wMap t f hf) ex1_H2left y).mp hy)
        hb0TA.surjective (chi0T_injective t ht hw) hb1TA.injective
  · -- **Direction 3**: `A`, `A''` self-dual ⟹ `A'` self-dual.
    rintro ⟨hsdA, hsd''⟩
    obtain ⟨hb2A, hb2TA, hb0A, hb0TA, hb1A, hb1TA⟩ := chi_bij_of_selfdualW t ht hw hA₂ hsdA
    obtain ⟨hb2'', hb2T'', hb0'', hb0T'', hb1'', hb1T''⟩ :=
      chi_bij_of_selfdualW t ht hw hA''₂ hsd''
    rw [isSelfDualW_iff t ht hw hA'₂]
    refine ⟨⟨?_, chi2_surjective t ht hw hA'₂⟩, ?_, ?_⟩
    · -- `χ²_{A'}` injective: window `[H¹(A), H¹(A''), H²(A'), H²(A)]`.
      exact four_lemma_inj
        (H1wMap t g hg) (delta1 f g hf hg hinj hsurj hexact t ht hw) (H2wMap t f hf)
        (dualMap (H1wMap t (dualMap g) hgse))
        (dualMap (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw))
        (dualMap (H0wMap t (dualMap f) hfse))
        (chi1 (A := A) t ht hw) (chi1 (A := A'') t ht hw) (chi2 (A := A') t ht hw)
        (chi2 (A := A) t ht hw)
        (chi1_square g hg t ht hw)
        (square_delta1 f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi2_square f hf t ht hw)
        tE6 tE7
        (fun y hy => (dual_exact_pair (H1w_two_torsion t hD₂)
          (delta0D f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (H1wMap t (dualMap g) hgse) ex2_H1left y).mp hy)
        hb1A.surjective hb1''.injective hb2A.injective
    · -- `χ¹_{A'}` injective: window `[H⁰(A), H⁰(A''), H¹(A'), H¹(A)]`.
      exact four_lemma_inj
        (H0wMap t g hg) (delta0 f g hf hg hinj hsurj hexact t ht hw) (H1wMap t f hf)
        (dualMap (H2wMap t (dualMap g) hgse))
        (dualMap (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw))
        (dualMap (H1wMap t (dualMap f) hfse))
        (chi0 (A := A) t ht hw) (chi0 (A := A'') t ht hw) (chi1 (A := A') t ht hw)
        (chi1 (A := A) t ht hw)
        (chi0_square g hg t ht hw)
        (square_delta0 f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (chi1_square f hf t ht hw)
        tE3 tE4
        (fun y hy => (dual_exact_pair (H2w_two_torsion t hD₂)
          (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw)
          (H2wMap t (dualMap g) hgse) ex2_H2left y).mp hy)
        hb0A.surjective (chi0_injective t ht hw hA''₂) hb1A.injective
    · -- `χ¹ᵀ_{A'}` injective: transpose window `[H¹(A''^∨), H¹(A^∨), H¹(A'^∨), H²(A''^∨)]`.
      exact four_lemma_inj
        (H1wMap t (dualMap g) hgse) (H1wMap t (dualMap f) hfse)
        (delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw)
        (dualMap (H1wMap t g hg)) (dualMap (H1wMap t f hf))
        (dualMap (delta0 f g hf hg hinj hsurj hexact t ht hw))
        (chi1T (A := A'') t ht hw) (chi1T (A := A) t ht hw) (chi1T (A := A') t ht hw)
        (chi2T (A := A'') t ht hw)
        (chi1T_square g hg t ht hw) (chi1T_square f hf t ht hw)
        (square_delta1D f g hf hg hinj hsurj hexact hA₂ t ht hw)
        tD5 tD6
        (fun y hy => (dual_exact_pair (H1w_two_torsion t hA''₂)
          (H1wMap t f hf) (H1wMap t g hg) ex1_H1mid y).mp hy)
        hb1T''.surjective hb1TA.injective hb2T''.injective

end LES

end GQ2.FoxH
