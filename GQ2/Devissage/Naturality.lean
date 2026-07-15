/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.FoxHeisenberg
public import GQ2.MixedBilinear
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# §5.11 dévissage: naturality, functoriality, rank-nullity

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## Naturality of the word complex under coefficient maps

The maps `d⁰`, `d¹` commute with a `C`-equivariant additive map `φ : A →+ B` (applied degreewise),
so `φ` induces a chain map `C(A) → C(B)`.  These are the arrows of the SES of complexes. -/

section Naturality

variable {A B : Type*} [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B]

/-- **`d⁰` is natural**: `d⁰_B(φ v) = φ ∘ d⁰_A(v)` for a `C`-equivariant `φ`. -/
theorem d0_natural (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (v : A) :
    d0 t (φ v) = fun i => φ (d0 t v i) := by
  funext i
  fin_cases i <;> simp [d0, hφ]

/-- **`d¹` is natural**: `d¹_B(φ ∘ x) = (φ, φ) ∘ d¹_A(x)` for a `C`-equivariant `φ` — the finite
Fox rule pushed through the coefficient map (`WordLift.map φ` + `Marking.map_{tame,wild}Value`). -/
theorem d1_natural [Finite A] [Finite B] [Finite C] (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (x : Fin 4 → A) :
    d1Fun t (fun i => φ (x i)) = (φ (d1Fun t x).1, φ (d1Fun t x).2) := by
  set Φ := WordLift.map (C := C) φ hφ
  have hL : (liftMarking t x).map Φ = liftMarking t (fun i => φ (x i)) := rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (fun i => φ (x i))).tameValue.u = φ ((liftMarking t x).tameValue.u)
    rw [← hL, Marking.map_tameValue, WordLift.map_u]
  · show (liftMarking t (fun i => φ (x i))).wildValue.u = φ ((liftMarking t x).wildValue.u)
    rw [← hL, Marking.map_wildValue, WordLift.map_u]

end Naturality

/-! ## Functoriality of the cohomology

A `C`-equivariant `φ : A →+ B` induces maps `Z¹w`, `H²w`, `H¹w` — the arrows the module SES turns
into the LES. -/

section Functoriality

variable {A B : Type*} [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B] [Finite A] [Finite B] [Finite C]

/-- `d¹`-kernel is preserved: `x ∈ Z¹w(A) ⟹ φ ∘ x ∈ Z¹w(B)`. -/
theorem d1_ker_map (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) {x : Fin 4 → A} (hx : d1 t x = 0) :
    d1 t (fun i => φ (x i)) = 0 := by
  show d1Fun t (fun i => φ (x i)) = 0
  simp [d1_natural t φ hφ x, show d1Fun t x = 0 from hx]

/-- The induced map `Z¹w(A) →+ Z¹w(B)`. -/
noncomputable def Z1wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : Z1w (A := A) t →+ Z1w (A := B) t where
  toFun x := ⟨fun i => φ (x.1 i),
    AddMonoidHom.mem_ker.mpr (d1_ker_map t φ hφ (AddMonoidHom.mem_ker.mp x.2))⟩
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- The induced map `H²w(A) →+ H²w(B)`, descended from `(φ, φ) : A × A →+ B × B` through the
`im d¹`-quotient (well-defined by `d1_natural`). -/
noncomputable def H2wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H2w (A := A) t →+ H2w (A := B) t :=
  QuotientAddGroup.map ((d1 (A := A) t).range) ((d1 (A := B) t).range) (φ.prodMap φ) <| by
    rintro z hz
    obtain ⟨x, rfl⟩ := hz
    rw [AddSubgroup.mem_comap]
    exact ⟨fun i => φ (x i), d1_natural t φ hφ x⟩

/-- The induced map `H⁰w(A) →+ H⁰w(B)`: `φ` restricted to the `d⁰`-kernels (`d⁰`-naturality sends
`ker d⁰_A` into `ker d⁰_B`). -/
def H0wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H0w (A := A) t →+ H0w (A := B) t where
  toFun a := ⟨φ a.1, by
    rw [H0w, AddMonoidHom.mem_ker, d0_natural t φ hφ a.1,
      show d0 t a.1 = 0 from AddMonoidHom.mem_ker.mp a.2]
    funext i; simp⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp

/-- The induced map `H¹w(A) →+ H¹w(B)`, descended from `Z1wMap` through the `B¹w`-quotient
(coboundaries map to coboundaries by `d⁰`-naturality). -/
noncomputable def H1wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H1w (A := A) t →+ H1w (A := B) t :=
  QuotientAddGroup.map _ _ (Z1wMap t φ hφ) <| by
    rintro z hz
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hz
    exact AddMonoidHom.mem_range.mpr ⟨φ a, by
      show d0 t (φ a) = fun i => φ (z.1 i)
      simp only [d0_natural t φ hφ a, ha]⟩

end Functoriality

/-! ## Rank-nullity on `d¹`: the two card clauses of `IsSelfDual` are equivalent

`d¹ : A⁴ → A²` gives `#A⁴ = #Z¹w · #(im d¹)` (rank-nullity) and `#A² = #H²w · #(im d¹)`
(`H²w = A²/im d¹`).  Eliminating `#(im d¹)` yields `#Z¹w = #A² · #H²w` for **every** `A`, so the
two `IsSelfDual` card clauses (`#H²w = #fixedPts` and `#Z¹w = #A²·#fixedPts`) are equivalent —
one need only track `#H²w`.  (Flagged in the module header as the key simplification.) -/

section RankNullity

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- **Rank-nullity for the word complex**: `#Z¹w(A) = #A² · #H²w(A)`, for every finite `A`. -/
theorem card_Z1w_eq_sq_mul_card_H2w (t : Marking C) :
    Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 * Nat.card (H2w (A := A) t) := by
  have hrange_pos : 0 < Nat.card ((d1 (A := A) t).range) := Nat.card_pos
  -- (i) `#A⁴ = #Z¹w · #(im d¹)` via `(A⁴/ker d¹) ≃ im d¹` and Lagrange.
  have hi : Nat.card (Z1w (A := A) t) * Nat.card ((d1 (A := A) t).range) = Nat.card A ^ 4 := by
    have e1 : Nat.card ((Fin 4 → A) ⧸ (d1 (A := A) t).ker)
        = Nat.card ((d1 (A := A) t).range) :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (d1 (A := A) t)).toEquiv
    have e2 : Nat.card (Fin 4 → A)
        = Nat.card ((Fin 4 → A) ⧸ (d1 (A := A) t).ker) * Nat.card ((d1 (A := A) t).ker) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    rw [show Nat.card (Z1w (A := A) t) = Nat.card ((d1 (A := A) t).ker) from rfl, mul_comm, ← e1,
      ← e2, Nat.card_fun]
    simp
  -- (ii) `#A² = #H²w · #(im d¹)` (Lagrange on the quotient `H²w = A²/im d¹`).
  have hii : Nat.card (H2w (A := A) t) * Nat.card ((d1 (A := A) t).range) = Nat.card A ^ 2 := by
    rw [show Nat.card (H2w (A := A) t)
        = Nat.card ((A × A) ⧸ (d1 (A := A) t).range) from rfl,
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup, Nat.card_prod, sq]
  -- Eliminate `#(im d¹)`.
  apply Nat.eq_of_mul_eq_mul_right hrange_pos
  rw [hi, mul_assoc, hii]
  ring

/-- `B¹w ≤ Z¹w` (the chain condition, subgroup form of `d1Fun_comp_d0`). -/
theorem B1w_le_Z1w (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    B1w (A := A) t ≤ Z1w (A := A) t := by
  rintro x ⟨v, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (d1Fun_comp_d0 t ht hw v)

/-- **Euler characteristic of the word complex**: `#H¹w = #A · #H⁰w · #H²w`.  (Lagrange on the
`B¹w`-quotient, first isomorphism on `d⁰`, and rank-nullity on `d¹`.) -/
theorem card_H1w_eq (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    Nat.card (H1w (A := A) t)
      = Nat.card A * Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t) := by
  -- (a) `#Z¹w = #H¹w · #B¹w`.
  have ha : Nat.card (Z1w (A := A) t)
      = Nat.card (H1w (A := A) t) * Nat.card (B1w (A := A) t) := by
    have e1 : Nat.card ((B1w (A := A) t).addSubgroupOf (Z1w (A := A) t))
        = Nat.card (B1w (A := A) t) :=
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1w_le_Z1w t ht hw)).toEquiv
    rw [← e1]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  -- (c) `#A = #B¹w · #H⁰w` (first isomorphism on `d⁰`).
  have hc : Nat.card A = Nat.card (B1w (A := A) t) * Nat.card (H0w (A := A) t) := by
    have e1 : Nat.card (A ⧸ (d0 (A := A) t).ker) = Nat.card (B1w (A := A) t) :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (d0 (A := A) t)).toEquiv
    rw [← e1, show H0w (A := A) t = (d0 (A := A) t).ker from rfl]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  -- Combine with `#Z¹w = #A² · #H²w` and cancel `#A > 0`.
  have hpos : 0 < Nat.card A := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (H1w (A := A) t) * Nat.card A
      = Nat.card (H1w (A := A) t) * (Nat.card (B1w (A := A) t) * Nat.card (H0w (A := A) t)) := by
        rw [← hc]
    _ = Nat.card (Z1w (A := A) t) * Nat.card (H0w (A := A) t) := by rw [ha]; ring
    _ = Nat.card A ^ 2 * Nat.card (H2w (A := A) t) * Nat.card (H0w (A := A) t) := by
        rw [card_Z1w_eq_sq_mul_card_H2w]
    _ = Nat.card A * Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t) * Nat.card A := by
        ring

end RankNullity

end GQ2.FoxH
