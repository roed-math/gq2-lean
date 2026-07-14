import GQ2.Devissage.EvalPairings

/-!
# §5.11 dévissage: the degree-1 pairings χ¹

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## The duality ladder, degree 1: the `mixedB` pairings `χ¹`, `χ¹`-transposed

The degree-(1,1) rung: `mixedB` descends to `H¹w(A) × H¹w(A^∨)` (both coboundary directions die
by Prop 5.8), giving `chi1 : H¹w(A) →+ (H¹w(A^∨))^∨` and its transpose.  `IsSelfDual`'s pairing
clause is *exactly* the injectivity of both (the descended pairing is forced to be `chi1`). -/

section Chi1

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- The inner functional: a fixed `Z¹w(A)`-cocycle `x` pairs against `H¹w(A^∨)`-classes via
`mixedB` (dual coboundary offsets die by Prop 5.8 right, since `d¹x = 0`). -/
noncomputable def chi1Aux (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (x : Z1w (A := A) t) : ElemDual (H1w (A := ElemDual A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := fun y => mixedB t x.1 y.1
       map_zero' := mixedB_zero_right t x.1
       map_add' := fun y z => mixedB_add_right t x.1 y.1 z.1 } :
      Z1w (A := ElemDual A) t →+ ZMod 2) <| by
    intro y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    obtain ⟨lam, hlam⟩ := AddMonoidHom.mem_range.mp hy
    show mixedB t x.1 y.1 = 0
    have hlam' : d0 (A := ElemDual A) t lam = y.1 := hlam
    rw [← hlam']
    have h1 := prop_5_8_right t ht hw x.1 lam
    rw [show d1Fun t x.1 = 0 from AddMonoidHom.mem_ker.mp x.2] at h1
    rw [h1]
    show lam ((0 : A × A).1 + (0 : A × A).2) = 0
    simp

/-- **`χ¹` (degree-(1,1) `mixedB` pairing)**: `H¹w(A) →+ (H¹w(A^∨))^∨`. -/
noncomputable def chi1 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H1w (A := A) t →+ ElemDual (H1w (A := ElemDual A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := chi1Aux t ht hw
       map_zero' := by
        apply ElemDual.ext
        intro h
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h
        show mixedB t (0 : Z1w (A := A) t).1 y.1 = 0
        exact mixedB_zero_left t y.1
       map_add' := fun x z => by
        apply ElemDual.ext
        intro h
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h
        show mixedB t ((x + z : Z1w (A := A) t) : Fin 4 → A) y.1 = _
        exact mixedB_add_left t x.1 z.1 y.1 } :
      Z1w (A := A) t →+ ElemDual (H1w (A := ElemDual A) t)) <| by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
    apply ElemDual.ext
    intro h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h
    show mixedB t x.1 y.1 = 0
    have ha' : d0 (A := A) t a = x.1 := ha
    rw [← ha']
    have h1 := prop_5_8_left t ht hw a y.1
    rw [show d1Fun (A := ElemDual A) t y.1 = 0 from AddMonoidHom.mem_ker.mp y.2] at h1
    rw [h1]
    show ((0 : ElemDual A × ElemDual A).1 + (0 : ElemDual A × ElemDual A).2) a = 0
    simp


/-- The transposed inner functional: a fixed dual cocycle `y` pairs against `H¹w(A)`-classes
(primal coboundary offsets die by Prop 5.8 left, since `d¹y = 0`). -/
noncomputable def chi1TAux (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (y : Z1w (A := ElemDual A) t) : ElemDual (H1w (A := A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := fun x => mixedB t x.1 y.1
       map_zero' := mixedB_zero_left t y.1
       map_add' := fun x z => mixedB_add_left t x.1 z.1 y.1 } :
      Z1w (A := A) t →+ ZMod 2) <| by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
    show mixedB t x.1 y.1 = 0
    have ha' : d0 (A := A) t a = x.1 := ha
    rw [← ha']
    have h1 := prop_5_8_left t ht hw a y.1
    rw [show d1Fun (A := ElemDual A) t y.1 = 0 from AddMonoidHom.mem_ker.mp y.2] at h1
    rw [h1]
    show ((0 : ElemDual A × ElemDual A).1 + (0 : ElemDual A × ElemDual A).2) a = 0
    simp

/-- **`χ¹` transposed**: `H¹w(A^∨) →+ (H¹w(A))^∨`. -/
noncomputable def chi1T (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H1w (A := ElemDual A) t →+ ElemDual (H1w (A := A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := chi1TAux t ht hw
       map_zero' := by
        apply ElemDual.ext
        intro h
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
        show mixedB t x.1 (0 : Z1w (A := ElemDual A) t).1 = 0
        exact mixedB_zero_right t x.1
       map_add' := fun y z => by
        apply ElemDual.ext
        intro h
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
        show mixedB t x.1 ((y + z : Z1w (A := ElemDual A) t) : Fin 4 → ElemDual A) = _
        exact mixedB_add_right t x.1 y.1 z.1 } :
      Z1w (A := ElemDual A) t →+ ElemDual (H1w (A := A) t)) <| by
    intro y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    obtain ⟨lam, hlam⟩ := AddMonoidHom.mem_range.mp hy
    apply ElemDual.ext
    intro h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
    show mixedB t x.1 y.1 = 0
    have hlam' : d0 (A := ElemDual A) t lam = y.1 := hlam
    rw [← hlam']
    have h1 := prop_5_8_right t ht hw x.1 lam
    rw [show d1Fun t x.1 = 0 from AddMonoidHom.mem_ker.mp x.2] at h1
    rw [h1]
    show lam ((0 : A × A).1 + (0 : A × A).2) = 0
    simp


/-- The two orientations pair the same classes: `χ¹ᵀ(h', h) = χ¹(h, h')`. -/
theorem chi1T_flip (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (h : H1w (A := A) t) (h' : H1w (A := ElemDual A) t) :
    chi1T t ht hw h' h = chi1 t ht hw h h' := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h'
  rfl

/-- **The `IsSelfDual` pairing clause, characterized**: a descended two-sided-nondegenerate
pairing exists iff `χ¹` and `χ¹ᵀ` are both injective.  (The descent condition forces
`P = χ¹`-evaluation.) -/
theorem pairing_clause_iff (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    (∃ P : H1w (A := A) t → H1w (A := ElemDual A) t → ZMod 2,
      (∀ (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t),
          P (h1wMk t x) (h1wMk t y) = mixedB t x.val y.val) ∧
      (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
      (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)) ↔
    (Function.Injective (chi1 (A := A) t ht hw) ∧
      Function.Injective (chi1T (A := A) t ht hw)) := by
  constructor
  · rintro ⟨P, hdesc, hl, hr⟩
    have hPeq : ∀ h h', P h h' = chi1 t ht hw h h' := by
      intro h h'
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective h'
      exact hdesc x y
    constructor
    · intro h1 h2 h12
      by_contra hne
      obtain ⟨h', hP⟩ := hl _ (sub_ne_zero_of_ne hne)
      apply hP
      rw [hPeq, map_sub]
      show chi1 t ht hw h1 h' - chi1 t ht hw h2 h' = 0
      rw [h12, sub_self]
    · intro h1' h2' h12
      by_contra hne
      obtain ⟨h, hP⟩ := hr _ (sub_ne_zero_of_ne hne)
      apply hP
      rw [hPeq, map_sub]
      show chi1 t ht hw h h1' - chi1 t ht hw h h2' = 0
      rw [← chi1T_flip t ht hw h h1', ← chi1T_flip t ht hw h h2', h12, sub_self]
  · rintro ⟨hinj, hinjT⟩
    refine ⟨fun h h' => chi1 t ht hw h h', fun x y => rfl, ?_, ?_⟩
    · intro h hne
      by_contra! hno
      apply hne
      apply hinj
      rw [map_zero]
      exact ElemDual.ext hno
    · intro h' hne
      by_contra! hno
      apply hne
      apply hinjT
      rw [map_zero]
      apply ElemDual.ext
      intro h
      rw [chi1T_flip]
      exact hno h

/-- Both-injectivity upgrades to both-bijectivity (finite cards through `#X^∨ = #X`), and gives
the `H¹w`-card equality. -/
theorem chi1_bij_of_inj (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0)
    (hinj : Function.Injective (chi1 (A := A) t ht hw))
    (hinjT : Function.Injective (chi1T (A := A) t ht hw)) :
    Function.Bijective (chi1 (A := A) t ht hw) ∧
      Function.Bijective (chi1T (A := A) t ht hw) ∧
      Nat.card (H1w (A := A) t) = Nat.card (H1w (A := ElemDual A) t) := by
  have : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have he : Nat.card (ElemDual (H1w (A := ElemDual A) t))
      = Nat.card (H1w (A := ElemDual A) t) :=
    card_elemDual (A := H1w (A := ElemDual A) t)
      (H1w_two_torsion t ElemDual.add_self_eq_zero)
  have heT : Nat.card (ElemDual (H1w (A := A) t)) = Nat.card (H1w (A := A) t) :=
    card_elemDual (A := H1w (A := A) t) (H1w_two_torsion t hA₂)
  have hc1 : Nat.card (H1w (A := A) t) ≤ Nat.card (ElemDual (H1w (A := ElemDual A) t)) :=
    Nat.card_le_card_of_injective _ hinj
  have hc2 : Nat.card (H1w (A := ElemDual A) t) ≤ Nat.card (ElemDual (H1w (A := A) t)) :=
    Nat.card_le_card_of_injective _ hinjT
  have hcard : Nat.card (H1w (A := A) t) = Nat.card (H1w (A := ElemDual A) t) :=
    le_antisymm (hc1.trans he.le) (hc2.trans heT.le)
  refine ⟨?_, ?_, hcard⟩
  · rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinj, hcard.trans he.symm⟩
  · rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinjT, hcard.symm.trans heT.symm⟩

/-! ### The Lemma 5.6 squares: `χ¹` commutes with coefficient maps

For an equivariant `φ : A →+ B`, the degree-1 ladder square commutes — in both orientations it
unfolds on classes to exactly `lemma_5_6`. -/

variable {B : Type*} [AddCommGroup B] [DistribMulAction C B] [Finite B]

/-- The `χ¹` square over a coefficient map: `χ¹_B ∘ H¹wMap φ = (H¹wMap φ^∨)^∨ ∘ χ¹_A`. -/
theorem chi1_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H1w (A := A) t) :
    chi1 (A := B) t ht hw (H1wMap t φ hφ h)
      = dualMap (H1wMap t (dualMap φ) (dualMap_equivariant φ hφ))
          (chi1 (A := A) t ht hw h) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  apply ElemDual.ext
  intro z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  show mixedB t (fun i => φ (x.1 i)) y.1
    = mixedB t x.1 (fun i => ((y.1 i : B →+ ZMod 2).comp φ : ElemDual A))
  exact lemma_5_6 φ hφ t x.1 y.1

/-- The transposed `χ¹` square: `χ¹ᵀ_A ∘ H¹wMap φ^∨ = (H¹wMap φ)^∨ ∘ χ¹ᵀ_B`. -/
theorem chi1T_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (z : H1w (A := ElemDual B) t) :
    chi1T (A := A) t ht hw (H1wMap t (dualMap φ) (dualMap_equivariant φ hφ) z)
      = dualMap (H1wMap t φ hφ) (chi1T (A := B) t ht hw z) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  apply ElemDual.ext
  intro h
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  show mixedB t x.1 (fun i => ((y.1 i : B →+ ZMod 2).comp φ : ElemDual A))
    = mixedB t (fun i => φ (x.1 i)) y.1
  exact (lemma_5_6 φ hφ t x.1 y.1).symm

end Chi1

end GQ2.FoxH
