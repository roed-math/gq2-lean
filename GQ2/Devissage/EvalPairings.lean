/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Devissage.ElemDualPack

@[expose] public section

/-!
# §5.11 dévissage: the evaluation pairings χ⁰, χ²

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## The duality ladder: the evaluation pairings `χ⁰`, `χ²` (and transposes)

The chain map from the word complex of `A` to the reversed dual of the word complex of
`A^∨ = ElemDual A`, in the two degrees where it is an *evaluation* pairing (degree 1 — the
`mixedB` pairing — comes separately).  Well-definedness against `im d¹`/`ker d⁰` is exactly
Prop 5.8 (left/right).  Four maps: `chi0`/`chi2` (primal `A` against dual classes) and their
transposes `chi0T`/`chi2T` (primal `A^∨` against `A`-classes).  Two are *always* injective
(separation) and two are *always* surjective (extension/biduality) — no self-duality input. -/

section EvalPairings

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

omit [Finite A] [Finite C] in
/-- 2-torsion of the word-complex `H⁰w` (a subgroup of `A`). -/
theorem H0w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (a : H0w (A := A) t) :
    a + a = 0 :=
  Subtype.ext (hA₂ a.1)

/-- 2-torsion of the word-complex `H¹w` (a subquotient of `A⁴`). -/
theorem H1w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (h : H1w (A := A) t) :
    h + h = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  show (QuotientAddGroup.mk (x + x) : H1w (A := A) t) = 0
  rw [show x + x = 0 from Subtype.ext (funext fun i => hA₂ _)]
  exact QuotientAddGroup.mk_zero _

/-- 2-torsion of the word-complex `H²w` (a quotient of `A²`). -/
theorem H2w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (h : H2w (A := A) t) :
    h + h = 0 := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
  show (QuotientAddGroup.mk (p + p) : H2w (A := A) t) = 0
  rw [show p + p = 0 from Prod.ext (hA₂ p.1) (hA₂ p.2)]
  exact QuotientAddGroup.mk_zero _

/-- `mixedB t x 0 = 0` (from right-additivity, in the 2-torsion target). -/
theorem mixedB_zero_right (t : Marking C) (x : Fin 4 → A) : mixedB t x 0 = 0 := by
  simpa using mixedB_add_right t x 0 0

/-- `mixedB t 0 y = 0` (from left-additivity, in the 2-torsion target). -/
theorem mixedB_zero_left (t : Marking C) (y : Fin 4 → ElemDual A) : mixedB t 0 y = 0 := by
  simpa using mixedB_add_left t 0 0 y

/-- **`χ⁰` (degree-(0,2) evaluation)**: `H⁰w(A) →+ (H²w(A^∨))^∨`, `a ↦ ([λ,μ] ↦ λ(a) + μ(a))`.
Well-defined on `H²w(A^∨)`-classes by Prop 5.8 (left): on `(λ,μ) = d¹y` the value is
`B(d⁰a, y) = B(0, y) = 0`. -/
noncomputable def chi0 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H0w (A := A) t →+ ElemDual (H2w (A := ElemDual A) t) where
  toFun a := QuotientAddGroup.lift _
    ({ toFun := fun q => q.1 a.1 + q.2 a.1
       map_zero' := by show (0 : ZMod 2) + 0 = 0; rw [add_zero]
       map_add' := fun q r => by
        show (q.1 + r.1) a.1 + (q.2 + r.2) a.1 = _
        rw [ElemDual.add_apply, ElemDual.add_apply, add_add_add_comm] } :
      (ElemDual A × ElemDual A) →+ ZMod 2) <| by
    intro z hz
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hz
    show (d1Fun (A := ElemDual A) t y).1 a.1 + (d1Fun (A := ElemDual A) t y).2 a.1 = 0
    have h1 := prop_5_8_left t ht hw a.1 y
    rw [AddMonoidHom.mem_ker.mp a.2, mixedB_zero_left] at h1
    rw [← ElemDual.add_apply]
    exact h1.symm
  map_zero' := by
    ext h
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective h
    show q.1 (0 : H0w (A := A) t).1 + q.2 (0 : H0w (A := A) t).1 = 0
    rw [show ((0 : H0w (A := A) t) : A) = 0 from rfl, map_zero, map_zero, add_zero]
  map_add' a b := by
    ext h
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective h
    show q.1 ((a + b : H0w (A := A) t) : A) + q.2 ((a + b : H0w (A := A) t) : A) = _
    rw [show ((a + b : H0w (A := A) t) : A) = a.1 + b.1 from rfl, map_add, map_add,
      add_add_add_comm]
    rfl


/-- **`χ²` (degree-(2,0) evaluation)**: `H²w(A) →+ (H⁰w(A^∨))^∨`, `[(u,v)] ↦ (λ ↦ λ(u+v))`.
Well-defined on `H²w(A)`-classes by Prop 5.8 (right). -/
noncomputable def chi2 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H2w (A := A) t →+ ElemDual (H0w (A := ElemDual A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := fun p =>
        ({ toFun := fun lam => lam.1 (p.1 + p.2)
           map_zero' := rfl
           map_add' := fun lam mu => rfl } : ElemDual (H0w (A := ElemDual A) t))
       map_zero' := by
        apply ElemDual.ext
        intro lam
        show lam.1 (0 + 0) = 0
        rw [add_zero, map_zero]
       map_add' := fun p q => by
        apply ElemDual.ext
        intro lam
        show lam.1 ((p.1 + q.1) + (p.2 + q.2)) = lam.1 (p.1 + p.2) + lam.1 (q.1 + q.2)
        rw [add_add_add_comm, map_add] } :
      (A × A) →+ ElemDual (H0w (A := ElemDual A) t)) <| by
    intro z hz
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hz
    apply ElemDual.ext
    intro lam
    show lam.1 ((d1Fun t x).1 + (d1Fun t x).2) = 0
    have h1 := prop_5_8_right t ht hw x lam.1
    rw [AddMonoidHom.mem_ker.mp lam.2, mixedB_zero_right] at h1
    exact h1.symm


/-- **`χ⁰` transposed**: `H⁰w(A^∨) →+ (H²w(A))^∨`, `λ ↦ ([(u,v)] ↦ λ(u+v))`.  Well-defined by
Prop 5.8 (right), like `chi2` with the roles of the arguments exchanged. -/
noncomputable def chi0T (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H0w (A := ElemDual A) t →+ ElemDual (H2w (A := A) t) where
  toFun lam := QuotientAddGroup.lift _
    ({ toFun := fun p => lam.1 (p.1 + p.2)
       map_zero' := by show lam.1 (0 + 0) = 0; rw [add_zero, map_zero]
       map_add' := fun p q => by
        show lam.1 ((p.1 + q.1) + (p.2 + q.2)) = _
        rw [add_add_add_comm, map_add] } : (A × A) →+ ZMod 2) <| by
    intro z hz
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hz
    show lam.1 ((d1Fun t x).1 + (d1Fun t x).2) = 0
    have h1 := prop_5_8_right t ht hw x lam.1
    rw [AddMonoidHom.mem_ker.mp lam.2, mixedB_zero_right] at h1
    exact h1.symm
  map_zero' := by
    ext h
    obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
    show (0 : H0w (A := ElemDual A) t).1 (p.1 + p.2) = 0
    rw [show ((0 : H0w (A := ElemDual A) t) : ElemDual A) = 0 from rfl]
    rfl
  map_add' lam mu := by
    ext h
    obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
    show ((lam + mu : H0w (A := ElemDual A) t) : ElemDual A) (p.1 + p.2) = _
    rw [show ((lam + mu : H0w (A := ElemDual A) t) : ElemDual A) = lam.1 + mu.1 from rfl,
      ElemDual.add_apply]
    rfl


/-- **`χ²` transposed**: `H²w(A^∨) →+ (H⁰w(A))^∨`, `[(λ,μ)] ↦ (a ↦ λ(a) + μ(a))`.  Well-defined
by Prop 5.8 (left), like `chi0` with the roles exchanged. -/
noncomputable def chi2T (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H2w (A := ElemDual A) t →+ ElemDual (H0w (A := A) t) :=
  QuotientAddGroup.lift _
    ({ toFun := fun q =>
        ({ toFun := fun a => q.1 a.1 + q.2 a.1
           map_zero' := by
            show q.1 (0 : H0w (A := A) t).1 + q.2 (0 : H0w (A := A) t).1 = 0
            rw [show ((0 : H0w (A := A) t) : A) = 0 from rfl, map_zero, map_zero, add_zero]
           map_add' := fun a b => by
            show q.1 ((a + b : H0w (A := A) t) : A) + q.2 ((a + b : H0w (A := A) t) : A) = _
            rw [show ((a + b : H0w (A := A) t) : A) = a.1 + b.1 from rfl, map_add, map_add,
              add_add_add_comm] } : ElemDual (H0w (A := A) t))
       map_zero' := by
        apply ElemDual.ext
        intro a
        show (0 : ElemDual A) a.1 + (0 : ElemDual A) a.1 = 0
        rw [ElemDual.zero_apply, add_zero]
       map_add' := fun q r => by
        apply ElemDual.ext
        intro a
        show (q.1 + r.1) a.1 + (q.2 + r.2) a.1 = _
        rw [ElemDual.add_apply, ElemDual.add_apply, add_add_add_comm]
        rfl } :
      (ElemDual A × ElemDual A) →+ ElemDual (H0w (A := A) t)) <| by
    intro z hz
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hz
    apply ElemDual.ext
    intro a
    show (d1Fun (A := ElemDual A) t y).1 a.1 + (d1Fun (A := ElemDual A) t y).2 a.1 = 0
    have h1 := prop_5_8_left t ht hw a.1 y
    rw [AddMonoidHom.mem_ker.mp a.2, mixedB_zero_left] at h1
    rw [← ElemDual.add_apply]
    exact h1.symm


/-- `χ⁰` is **always** injective (the dual separates points; no self-duality input). -/
theorem chi0_injective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) : Function.Injective (chi0 (A := A) t ht hw) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ (sub_ne_zero_of_ne hne)
  have h1 := DFunLike.congr_fun hab (QuotientAddGroup.mk ((lam, 0) : ElemDual A × ElemDual A))
  have h2 : lam a.1 = lam b.1 := by
    have h3 : lam a.1 + (0 : ElemDual A) a.1 = lam b.1 + (0 : ElemDual A) b.1 := h1
    simpa using h3
  exact hlam (by rw [map_sub, h2, sub_self])

/-- `χ⁰` transposed is **always** injective (evaluation at `[(u,0)]` recovers `λ(u)`). -/
theorem chi0T_injective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    Function.Injective (chi0T (A := A) t ht hw) := by
  intro lam mu h
  apply Subtype.ext
  apply ElemDual.ext
  intro u
  have h2 : lam.1 (u + 0) = mu.1 (u + 0) :=
    DFunLike.congr_fun h (QuotientAddGroup.mk ((u, 0) : A × A))
  simpa using h2

/-- `χ²` is **always** surjective (extension along `H⁰w(A^∨) ≤ A^∨` + biduality). -/
theorem chi2_surjective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) : Function.Surjective (chi2 (A := A) t ht hw) := by
  intro psi
  -- Extend `psi` along the subgroup inclusion to a functional on all of `A^∨`…
  obtain ⟨Psi, hPsi⟩ := elemDual_extend ElemDual.add_self_eq_zero
    (H0w (A := ElemDual A) t).subtype (AddSubgroup.subtype_injective _)
    (psi : ElemDual ((H0w (A := ElemDual A) t : AddSubgroup (ElemDual A))))
  -- …and realize it as evaluation at some `w : A` (biduality).
  obtain ⟨w, hw'⟩ := (dualEval_bijective hA₂).2 Psi
  refine ⟨QuotientAddGroup.mk ((w, 0) : A × A), ?_⟩
  apply ElemDual.ext
  intro lam
  show lam.1 (w + 0) = psi lam
  rw [add_zero, ← hPsi lam, ← hw']
  exact (dualEval_apply _ _).symm

/-- `χ²` transposed is **always** surjective (extension along `H⁰w(A) ≤ A`). -/
theorem chi2T_surjective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) : Function.Surjective (chi2T (A := A) t ht hw) := by
  intro psi
  obtain ⟨nu, hnu⟩ := elemDual_extend hA₂ (H0w (A := A) t).subtype
    (AddSubgroup.subtype_injective _)
    (psi : ElemDual ((H0w (A := A) t : AddSubgroup A)))
  refine ⟨QuotientAddGroup.mk ((nu, 0) : ElemDual A × ElemDual A), ?_⟩
  apply ElemDual.ext
  intro a
  show nu a.1 + (0 : ElemDual A) a.1 = psi a
  simpa using hnu a

/-! ### The evaluation squares: `χ⁰`/`χ²` commute with coefficient maps

Four squares, general in an equivariant `φ : A →+ B`; each unfolds on classes to `map_add`
or to a literal `rfl`. -/

section EvalSquares

variable {B : Type*} [AddCommGroup B] [DistribMulAction C B] [Finite B]

/-- The `χ²` square: `χ²_B ∘ H²wMap φ = (H⁰wMap φ^∨)^∨ ∘ χ²_A`. -/
theorem chi2_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H2w (A := A) t) :
    chi2 (A := B) t ht hw (H2wMap t φ hφ h)
      = dualMap (H0wMap t (dualMap φ) (dualMap_equivariant φ hφ))
          (chi2 (A := A) t ht hw h) := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective h
  apply ElemDual.ext
  intro lam
  show lam.1 (φ z.1 + φ z.2) = lam.1 (φ (z.1 + z.2))
  rw [map_add φ z.1 z.2]

/-- The `χ⁰` square: `χ⁰_B ∘ H⁰wMap φ = (H²wMap φ^∨)^∨ ∘ χ⁰_A`. -/
theorem chi0_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (a : H0w (A := A) t) :
    chi0 (A := B) t ht hw (H0wMap t φ hφ a)
      = dualMap (H2wMap t (dualMap φ) (dualMap_equivariant φ hφ))
          (chi0 (A := A) t ht hw a) := by
  apply ElemDual.ext
  intro h
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective h
  rfl


/-- The transposed `χ⁰` square: `χ⁰ᵀ_A ∘ H⁰wMap φ^∨ = (H²wMap φ)^∨ ∘ χ⁰ᵀ_B`. -/
theorem chi0T_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (lam : H0w (A := ElemDual B) t) :
    chi0T (A := A) t ht hw (H0wMap t (dualMap φ) (dualMap_equivariant φ hφ) lam)
      = dualMap (H2wMap t φ hφ) (chi0T (A := B) t ht hw lam) := by
  apply ElemDual.ext
  intro h
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective h
  show lam.1 (φ (z.1 + z.2)) = lam.1 (φ z.1 + φ z.2)
  rw [map_add φ z.1 z.2]

end EvalSquares

end EvalPairings

end GQ2.FoxH
