import GQ2.FoxHeisenberg
import GQ2.MixedBilinear
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# §5.11 dévissage: two-out-of-three for `IsSelfDual` along a module SES  (ticket P-13e)

`lemma_5_11` (`GQ2/FoxHeisenberg.lean`) is the two-out-of-three property of the `IsSelfDual`
package along a short exact sequence `0 → A' → A → A'' → 0` of finite elementary `𝔽₂[C]`-modules.
The proof device is the **long exact cohomology sequence** of the word complex
`C(A) : A --d⁰--> A⁴ --d¹--> A²` (displays (30)/(49)/(50)): the degreewise functors `A ↦ A`,
`A ↦ Fin 4 → A`, `A ↦ A × A` are **exact** (identity / finite products), and `d⁰`, `d¹` are
**natural** in the coefficient module (this file's `d0_natural`/`d1_natural`), so the module SES
induces a short exact sequence of complexes, whence a nine-term LES

  `0 → H⁰(A') → H⁰(A) → H⁰(A'') → H¹(A') → H¹(A) → H¹(A'') → H²(A') → H²(A) → H²(A'') → 0`.

A key simplification: **rank-nullity on `d¹`** gives `dim Z¹w = 2·dim A + dim H²w` for *every* `A`
(`Z1w = ker d¹`, `H2w = coker d¹`), so the two card clauses of `IsSelfDual` are **equivalent** —
the card part reduces to the single clause `#H²w(A) = #fixedPts(ElemDual A)`.

## STATUS: the dévissage is PROVED (std-3, no sorries)

**`selfdualW_two_of_three`** is the master theorem: two-out-of-three for **`IsSelfDualW`**, the
*word-internal* form of the package with `#H⁰w(A^∨)` in place of `#fixedPts C (A^∨)`.  The proof
runs two nine-term LESs (the word complex of the SES, and of its **dualization** — exact by the
elementary-dual pack) tied into a duality ladder by six `χ`-maps whose squares all commute
(`lemma_5_6`, the evaluation squares, and the two δ-square cores), and closes with nine
four-lemma windows.  Free inputs: `χ⁰`/`χ⁰ᵀ` are *always* injective (separation), `χ²`/`χ²ᵀ`
*always* surjective (extension/biduality), and the Euler-characteristic swap
`#H⁰w(A) = #H²w(A^∨)` converts the given card clauses into full bijectivity.

## The `fixedPts` gap and the `lemma_5_11` relocation (EXECUTED)

`ker d⁰` is the fixed set of the **four marked elements**, whereas `IsSelfDual` uses
`fixedPts C` — all of `C`.  These agree exactly for a *generating* marking:
`H0w_eq_fixedPts (hgen : t.Generates)`, whence `isSelfDual_iff_W`.  Accordingly `lemma_5_11`
now carries `hgen : t.Generates` and lives **at the bottom of this file** (the proof needs this
file's machinery; imports run `FoxHeisenberg → Devissage`), proved by splicing
`selfdualW_two_of_three` through `isSelfDual_iff_W`.  Its consumer `prop_5_15`
(`FoxHeisenberg.lean`, P-13f) gained the same hypothesis — admissible markings supply it.
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
  set Φ := WordLift.map (C := C) φ hφ with hΦ
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
  have : d1Fun t (fun i => φ (x i)) = (φ (d1Fun t x).1, φ (d1Fun t x).2) := d1_natural t φ hφ x
  have hx' : d1Fun t x = 0 := hx
  show d1Fun t (fun i => φ (x i)) = 0
  rw [this, hx']
  simp

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
    obtain ⟨a, ha⟩ := (AddMonoidHom.mem_range).mp hz
    exact (AddMonoidHom.mem_range).mpr ⟨φ a, by
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

/-! ## The elementary-dual pack

`ElemDual`-infrastructure for the dual side of the dévissage: contravariant functoriality, the
extension lemma (`ZMod 2` is injective for finite elementary 2-groups), separation, the dimension
count, biduality, and exactness of dualization.  `Module (ZMod 2)`-structures appear only
*locally* inside proofs (`AddCommGroup.zmodModule`), per the repo's no-`Module`-instances
convention. -/

section ElemDualPack

/-- Contravariant functoriality of the `𝔽₂`-dual: precomposition `λ ↦ λ ∘ φ`. -/
def dualMap {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) :
    ElemDual B →+ ElemDual A where
  toFun lam := ((lam : B →+ ZMod 2).comp φ : ElemDual A)
  map_zero' := AddMonoidHom.zero_comp φ
  map_add' lam mu := AddMonoidHom.add_comp lam mu φ

@[simp] theorem dualMap_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B)
    (lam : ElemDual B) (a : A) : dualMap φ lam a = lam (φ a) := rfl

/-- `dualMap` is equivariant for the contragredient actions. -/
theorem dualMap_equivariant {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction C A] [DistribMulAction C B] (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (c : C) (lam : ElemDual B) :
    dualMap φ (c • lam) = c • dualMap φ lam := by
  ext a
  simp only [dualMap_apply, ElemDual.smul_apply, hφ]

/-- `ElemDual A` is elementary (2-torsion). -/
theorem elemDual_two_torsion {A : Type*} [AddCommGroup A] (lam : ElemDual A) : lam + lam = 0 :=
  ElemDual.ext fun a => by
    show lam a + lam a = 0
    exact CharTwo.add_self_eq_zero _

/-- **Extension lemma**: every `𝔽₂`-functional extends along an injection into a finite
elementary 2-group (`ZMod 2` is self-injective on this category; proof by complementing the
image subspace). -/
theorem elemDual_extend {A' A : Type*} [AddCommGroup A'] [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) (f : A' →+ A) (hinj : Function.Injective f)
    (lam' : ElemDual A') : ∃ lam : ElemDual A, ∀ a', lam (f a') = lam' a' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  haveI : Module (ZMod 2) A' := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]
    apply hinj
    rw [map_add, map_zero]
    exact hA₂ (f v))
  set F := AddMonoidHom.toZModLinearMap 2 f with hFdef
  have hFapp : ∀ a', F a' = f a' := fun a' =>
    congrFun (AddMonoidHom.coe_toZModLinearMap 2 f) a'
  have hFinj : Function.Injective F := by
    rw [show ⇑F = ⇑f from AddMonoidHom.coe_toZModLinearMap 2 f]
    exact hinj
  set L := AddMonoidHom.toZModLinearMap 2 (lam' : A' →+ ZMod 2) with hLdef
  -- A linear left inverse `G` of `F` (basis complement); then `L ∘ G` extends.
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.mpr hFinj)
  refine ⟨((L.comp G).toAddMonoidHom : ElemDual A), fun a' => ?_⟩
  show L (G (f a')) = lam' a'
  have h1 : G (f a') = a' := by
    rw [← hFapp a']
    exact LinearMap.congr_fun hG a'
  rw [h1]
  exact congrFun (AddMonoidHom.coe_toZModLinearMap 2 _) a'

/-- The `𝔽₂`-dual separates points on a finite elementary 2-group. -/
theorem elemDual_separates {A : Type*} [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {a : A} (ha : a ≠ 0) : ∃ lam : ElemDual A, lam a ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  by_contra h
  push_neg at h
  refine ha ?_
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2) a]
  intro φ
  exact h (φ.toAddMonoidHom : ElemDual A)

/-- The dimension count `#(ElemDual A) = #A` for finite elementary `A`. -/
theorem card_elemDual {A : Type*} [AddCommGroup A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (ElemDual A) = Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  haveI : FiniteDimensional (ZMod 2) A := Module.Finite.of_finite
  have e1 : ElemDual A ≃ Module.Dual (ZMod 2) A :=
    { toFun := AddMonoidHom.toZModLinearMap 2
      invFun := LinearMap.toAddMonoidHom
      left_inv := fun lam => rfl
      right_inv := fun φ => rfl }
  obtain ⟨e2⟩ :=
    (Basis.linearEquiv_dual_iff_finiteDimensional (K := ZMod 2) (V := A)).mpr inferInstance
  calc Nat.card (ElemDual A) = Nat.card (Module.Dual (ZMod 2) A) := Nat.card_congr e1
    _ = Nat.card A := (Nat.card_congr e2.toEquiv).symm

/-- **Biduality**: evaluation `A →+ ElemDual (ElemDual A)` is bijective for finite elementary
`A`. -/
theorem dualEval_bijective {A : Type*} [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : Function.Bijective (dualEval A) := by
  haveI : Finite (ElemDual A →+ ZMod 2) := inferInstanceAs (Finite (ElemDual (ElemDual A)))
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · intro x y hxy
    have h1 : ∀ lam : ElemDual A, lam x = lam y := fun lam => by
      have h2 := DFunLike.congr_fun hxy lam
      rwa [dualEval_apply, dualEval_apply] at h2
    by_contra hne
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ (sub_ne_zero_of_ne hne)
    exact hlam (by rw [map_sub, h1 lam, sub_self])
  · show Nat.card A = Nat.card (ElemDual (ElemDual A))
    rw [card_elemDual (fun lam => elemDual_two_torsion lam), card_elemDual hA₂]

/-- Dualizing a surjection gives an injection. -/
theorem dualMap_injective {Y Z : Type*} [AddCommGroup Y] [AddCommGroup Z] (v : Y →+ Z)
    (hsurj : Function.Surjective v) : Function.Injective (dualMap (A := Y) v) := by
  intro mu nu h
  ext z
  obtain ⟨y, rfl⟩ := hsurj z
  exact DFunLike.congr_fun h y

/-- Dualizing an injection into a finite elementary 2-group gives a surjection (the extension
lemma, bundled). -/
theorem dualMap_surjective {A' A : Type*} [AddCommGroup A'] [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) (f : A' →+ A) (hinj : Function.Injective f) :
    Function.Surjective (dualMap f) := by
  intro lam'
  obtain ⟨lam, hlam⟩ := elemDual_extend hA₂ f hinj lam'
  exact ⟨lam, ElemDual.ext hlam⟩

/-- 2-torsion passes to subobjects along an injection. -/
theorem two_torsion_of_injective {A' A : Type*} [AddCommGroup A'] [AddCommGroup A]
    (f : A' →+ A) (hinj : Function.Injective f) (hA₂ : ∀ a : A, a + a = 0) (a' : A') :
    a' + a' = 0 := by
  apply hinj
  rw [map_add, map_zero]
  exact hA₂ (f a')

/-- 2-torsion passes to quotients along a surjection. -/
theorem two_torsion_of_surjective {A A'' : Type*} [AddCommGroup A] [AddCommGroup A'']
    (g : A →+ A'') (hsurj : Function.Surjective g) (hA₂ : ∀ a : A, a + a = 0) (a'' : A'') :
    a'' + a'' = 0 := by
  obtain ⟨a, rfl⟩ := hsurj a''
  rw [← map_add, hA₂, map_zero]

/-- **Dual exactness**: dualizing an exact pair is exact (finite elementary target; the factored
functional extends via `kerLift`). -/
theorem dual_exact_pair {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Finite Z] (hZ₂ : ∀ z : Z, z + z = 0) (u : X →+ Y) (v : Y →+ Z)
    (hexact : u.range = v.ker) (lam : ElemDual Y) :
    dualMap u lam = 0 ↔ lam ∈ (dualMap v).range := by
  constructor
  · intro h0
    have hker : ∀ y ∈ v.ker, lam y = 0 := by
      intro y hy
      obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp (by rw [hexact]; exact hy)
      exact DFunLike.congr_fun h0 x
    obtain ⟨mu, hmu⟩ := elemDual_extend hZ₂ (QuotientAddGroup.kerLift v)
      (QuotientAddGroup.kerLift_injective v)
      ((QuotientAddGroup.lift v.ker lam hker : (Y ⧸ v.ker) →+ ZMod 2) :
        ElemDual (Y ⧸ v.ker))
    refine AddMonoidHom.mem_range.mpr ⟨mu, ?_⟩
    ext y
    have h1 := hmu (QuotientAddGroup.mk y)
    rw [QuotientAddGroup.kerLift_mk] at h1
    exact h1
  · rintro ⟨mu, rfl⟩
    ext x
    show mu (v (u x)) = 0
    rw [show v (u x) = 0 from AddMonoidHom.mem_ker.mp
      (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩), map_zero]

/-- **The dualized SES is exact in the middle**, subgroup form: `range g^∨ = ker f^∨`. -/
theorem dual_ses_exact {A' A A'' : Type*} [AddCommGroup A'] [AddCommGroup A] [AddCommGroup A'']
    [Finite A''] (hA''₂ : ∀ a'' : A'', a'' + a'' = 0) (f : A' →+ A) (g : A →+ A'')
    (hexact : f.range = g.ker) : (dualMap g).range = (dualMap f).ker := by
  ext lam
  rw [AddMonoidHom.mem_ker]
  exact (dual_exact_pair hA''₂ f g hexact lam).symm

end ElemDualPack

/-! ## The duality ladder: the evaluation pairings `χ⁰`, `χ²` (and transposes)

The chain map from the word complex of `A` to the reversed dual of the word complex of
`A^∨ = ElemDual A`, in the two degrees where it is an *evaluation* pairing (degree 1 — the
`mixedB` pairing — comes separately).  Well-definedness against `im d¹`/`ker d⁰` is exactly
Prop 5.8 (left/right).  Four maps: `chi0`/`chi2` (primal `A` against dual classes) and their
transposes `chi0T`/`chi2T` (primal `A^∨` against `A`-classes).  Two are *always* injective
(separation) and two are *always* surjective (extension/biduality) — no self-duality input. -/

section EvalPairings

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- 2-torsion of the word-complex `H⁰w` (a subgroup of `A`). -/
theorem H0w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (a : H0w (A := A) t) :
    a + a = 0 :=
  Subtype.ext (hA₂ a.1)

/-- 2-torsion of the word-complex `H¹w` (a subquotient of `A⁴`). -/
theorem H1w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (h : H1w (A := A) t) :
    h + h = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  have hxx : (x + x : Z1w (A := A) t) = 0 := by
    apply Subtype.ext
    funext i
    show x.1 i + x.1 i = 0
    exact hA₂ _
  show (QuotientAddGroup.mk (x + x) : H1w (A := A) t) = 0
  rw [hxx]
  exact QuotientAddGroup.mk_zero _

/-- 2-torsion of the word-complex `H²w` (a quotient of `A²`). -/
theorem H2w_two_torsion (t : Marking C) (hA₂ : ∀ a : A, a + a = 0) (h : H2w (A := A) t) :
    h + h = 0 := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective h
  have hpp : (p + p : A × A) = 0 := Prod.ext (hA₂ p.1) (hA₂ p.2)
  show (QuotientAddGroup.mk (p + p) : H2w (A := A) t) = 0
  rw [hpp]
  exact QuotientAddGroup.mk_zero _

/-- `mixedB t x 0 = 0` (from right-additivity, in the 2-torsion target). -/
theorem mixedB_zero_right (t : Marking C) (x : Fin 4 → A) : mixedB t x 0 = 0 := by
  have h := mixedB_add_right t x 0 0
  rw [add_zero] at h
  have h2 : mixedB t x 0 + 0 = mixedB t x 0 + mixedB t x 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- `mixedB t 0 y = 0` (from left-additivity, in the 2-torsion target). -/
theorem mixedB_zero_left (t : Marking C) (y : Fin 4 → ElemDual A) : mixedB t 0 y = 0 := by
  have h := mixedB_add_left t 0 0 y
  rw [add_zero] at h
  have h2 : mixedB t 0 y + 0 = mixedB t 0 y + mixedB t 0 y := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

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

@[simp] theorem chi0_apply_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a : H0w (A := A) t) (q : ElemDual A × ElemDual A) :
    chi0 t ht hw a (QuotientAddGroup.mk q) = q.1 a.1 + q.2 a.1 := rfl

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

@[simp] theorem chi2_apply_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (p : A × A) (lam : H0w (A := ElemDual A) t) :
    chi2 t ht hw (QuotientAddGroup.mk p) lam = lam.1 (p.1 + p.2) := rfl

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

@[simp] theorem chi0T_apply_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (lam : H0w (A := ElemDual A) t) (p : A × A) :
    chi0T t ht hw lam (QuotientAddGroup.mk p) = lam.1 (p.1 + p.2) := rfl

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

@[simp] theorem chi2T_apply_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (q : ElemDual A × ElemDual A) (a : H0w (A := A) t) :
    chi2T t ht hw (QuotientAddGroup.mk q) a = q.1 a.1 + q.2 a.1 := rfl

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
  have h1 := DFunLike.congr_fun h (QuotientAddGroup.mk ((u, 0) : A × A))
  have h2 : lam.1 (u + 0) = mu.1 (u + 0) := h1
  simpa using h2

/-- `χ²` is **always** surjective (extension along `H⁰w(A^∨) ≤ A^∨` + biduality). -/
theorem chi2_surjective (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) : Function.Surjective (chi2 (A := A) t ht hw) := by
  intro psi
  -- Extend `psi` along the subgroup inclusion to a functional on all of `A^∨`…
  obtain ⟨Psi, hPsi⟩ := elemDual_extend (fun lam => elemDual_two_torsion lam)
    (H0w (A := ElemDual A) t).subtype (AddSubgroup.subtype_injective _)
    (psi : ElemDual ((H0w (A := ElemDual A) t : AddSubgroup (ElemDual A))))
  -- …and realize it as evaluation at some `w : A` (biduality).
  obtain ⟨w, hw'⟩ := (dualEval_bijective hA₂).2 Psi
  refine ⟨QuotientAddGroup.mk ((w, 0) : A × A), ?_⟩
  apply ElemDual.ext
  intro lam
  show lam.1 (w + 0) = psi lam
  rw [add_zero]
  have h1 : Psi lam.1 = psi lam := hPsi lam
  have h2 : Psi lam.1 = lam.1 w := by rw [← hw']; exact dualEval_apply _ _
  rw [← h2, h1]

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
  rw [ElemDual.zero_apply, add_zero]
  exact hnu a

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

/-- The transposed `χ²` square: `χ²ᵀ_A ∘ H²wMap φ^∨ = (H⁰wMap φ)^∨ ∘ χ²ᵀ_B`. -/
theorem chi2T_square (φ : A →+ B) (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a)
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H2w (A := ElemDual B) t) :
    chi2T (A := A) t ht hw (H2wMap t (dualMap φ) (dualMap_equivariant φ hφ) h)
      = dualMap (H0wMap t φ hφ) (chi2T (A := B) t ht hw h) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective h
  apply ElemDual.ext
  intro a'
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

@[simp] theorem chi1_apply_mk_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t) :
    chi1 t ht hw (QuotientAddGroup.mk x) (QuotientAddGroup.mk y) = mixedB t x.1 y.1 := rfl

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

@[simp] theorem chi1T_apply_mk_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (y : Z1w (A := ElemDual A) t) (x : Z1w (A := A) t) :
    chi1T t ht hw (QuotientAddGroup.mk y) (QuotientAddGroup.mk x) = mixedB t x.1 y.1 := rfl

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
      by_contra hno
      push_neg at hno
      apply hne
      apply hinj
      rw [map_zero]
      exact ElemDual.ext hno
    · intro h' hne
      by_contra hno
      push_neg at hno
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
  haveI : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have he : Nat.card (ElemDual (H1w (A := ElemDual A) t))
      = Nat.card (H1w (A := ElemDual A) t) :=
    card_elemDual (A := H1w (A := ElemDual A) t)
      (H1w_two_torsion t (fun lam : ElemDual A => elemDual_two_torsion lam))
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

/-! ## Word-internal self-duality

The marking-internal form of the `IsSelfDual` package: `#H⁰w(A^∨)` in place of
`#fixedPts C (A^∨)`.  For a *generating* marking (`t.Generates`) the two agree — `ker d⁰` is then
exactly the `C`-fixed points; `lemma_5_11`'s dévissage propagates the internal form, and the
`fixedPts`-form follows wherever generation is available. -/

section SelfDualW

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- **Word-internal self-duality** (the `IsSelfDual` package with the invariants of the dual
replaced by the word-complex `H⁰w` of the dual). -/
def IsSelfDualW (t : Marking C) (A : Type*) [AddCommGroup A] [DistribMulAction C A]
    [Finite A] : Prop :=
  (Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t)) ∧
  (Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 * Nat.card (H0w (A := ElemDual A) t)) ∧
  ∃ P : H1w (A := A) t → H1w (A := ElemDual A) t → ZMod 2,
    (∀ (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t),
        P (h1wMk t x) (h1wMk t y) = mixedB t x.val y.val) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
    (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

/-- `IsSelfDualW` in `χ`-language: `χ²` bijective and `χ¹`, `χ¹ᵀ` injective.  (The second card
clause is rank-nullity; the pairing clause is `pairing_clause_iff`.) -/
theorem isSelfDualW_iff (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDualW t A ↔
      (Function.Bijective (chi2 (A := A) t ht hw) ∧
        Function.Injective (chi1 (A := A) t ht hw) ∧
        Function.Injective (chi1T (A := A) t ht hw)) := by
  haveI : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hED : Nat.card (ElemDual (H0w (A := ElemDual A) t))
      = Nat.card (H0w (A := ElemDual A) t) :=
    card_elemDual (A := H0w (A := ElemDual A) t)
      (H0w_two_torsion t (fun lam : ElemDual A => elemDual_two_torsion lam))
  constructor
  · rintro ⟨hc1, -, hpair⟩
    refine ⟨?_, (pairing_clause_iff t ht hw).mp hpair⟩
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨chi2_surjective t ht hw hA₂, hc1.trans hED.symm⟩
  · rintro ⟨hbij, hinj, hinjT⟩
    have hc1 : Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t) :=
      (Nat.card_eq_of_bijective _ hbij).trans hED
    exact ⟨hc1, by rw [card_Z1w_eq_sq_mul_card_H2w, hc1],
      (pairing_clause_iff t ht hw).mpr ⟨hinj, hinjT⟩⟩

/-- From a `IsSelfDualW`-package, **all six** `χ`-maps are bijective (the free halves plus the
Euler-characteristic swap `#H⁰w(A) = #H²w(A^∨)`). -/
theorem chi_bij_of_selfdualW (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) (hsd : IsSelfDualW t A) :
    Function.Bijective (chi2 (A := A) t ht hw) ∧
      Function.Bijective (chi2T (A := A) t ht hw) ∧
      Function.Bijective (chi0 (A := A) t ht hw) ∧
      Function.Bijective (chi0T (A := A) t ht hw) ∧
      Function.Bijective (chi1 (A := A) t ht hw) ∧
      Function.Bijective (chi1T (A := A) t ht hw) := by
  haveI : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := fun lam => elemDual_two_torsion lam
  obtain ⟨hbij2, hinj1, hinj1T⟩ := (isSelfDualW_iff t ht hw hA₂).mp hsd
  obtain ⟨hbij1, hbij1T, h11⟩ := chi1_bij_of_inj t ht hw hA₂ hinj1 hinj1T
  -- The card package.
  have hc1 : Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t) := hsd.1
  have hAD : Nat.card (ElemDual A) = Nat.card A := card_elemDual hA₂
  -- Euler swap: `#H⁰w(A) = #H²w(A^∨)`.
  have hswap : Nat.card (H0w (A := A) t) = Nat.card (H2w (A := ElemDual A) t) := by
    have e1 := card_H1w_eq (A := A) t ht hw
    have e2 := card_H1w_eq (A := ElemDual A) t ht hw
    have hprod : Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t))
        = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
            * Nat.card (H2w (A := ElemDual A) t)) := by
      calc Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t))
          = Nat.card (H1w (A := A) t) := by rw [e1]; ring
        _ = Nat.card (H1w (A := ElemDual A) t) := h11
        _ = Nat.card (ElemDual A) * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2w (A := ElemDual A) t)) := by rw [e2]; ring
        _ = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2w (A := ElemDual A) t)) := by rw [hAD]
    have hcancel := Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod
    rw [hc1, mul_comm] at hcancel
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel
  -- The four evaluation bijectivities.
  refine ⟨hbij2, ?_, ?_, ?_, hbij1, hbij1T⟩
  · -- `χ²ᵀ : H²w(A^∨) → (H⁰w(A))^∨`: always surjective; cards by the swap.
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨chi2T_surjective t ht hw hA₂, ?_⟩
    rw [hswap.symm, (card_elemDual (A := H0w (A := A) t) (H0w_two_torsion t hA₂)).symm]
  · -- `χ⁰ : H⁰w(A) → (H²w(A^∨))^∨`: always injective; cards by the swap.
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0_injective t ht hw hA₂, ?_⟩
    rw [hswap, (card_elemDual (A := H2w (A := ElemDual A) t)
      (H2w_two_torsion t hD₂)).symm]
  · -- `χ⁰ᵀ : H⁰w(A^∨) → (H²w(A))^∨`: always injective; cards by clause (i).
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0T_injective t ht hw, ?_⟩
    rw [← hc1, (card_elemDual (A := H2w (A := A) t) (H2w_two_torsion t hA₂)).symm]

end SelfDualW

/-! ## The four lemma (injectivity form)

The standard diagram chase, hand-rolled for `AddMonoidHom`s with pointwise exactness data — the
engine that turns the ladder squares into the conditional halves of the `χ`-bijectivities. -/

section FourLemma

variable {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
  [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄]
  [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄]

/-- **Four lemma, injectivity**: in a commuting ladder with exact rows, if `m₁` is surjective and
`m₂`, `m₄` are injective, then `m₃` is injective.  (Exactness is taken pointwise; only the
`ker ⊆ im` direction is needed on the bottom row.) -/
theorem four_lemma_inj (a₁ : A₁ →+ A₂) (a₂ : A₂ →+ A₃) (a₃ : A₃ →+ A₄)
    (b₁ : B₁ →+ B₂) (b₂ : B₂ →+ B₃) (b₃ : B₃ →+ B₄)
    (m₁ : A₁ →+ B₁) (m₂ : A₂ →+ B₂) (m₃ : A₃ →+ B₃) (m₄ : A₄ →+ B₄)
    (sq₁ : ∀ x, m₂ (a₁ x) = b₁ (m₁ x))
    (sq₂ : ∀ x, m₃ (a₂ x) = b₂ (m₂ x))
    (sq₃ : ∀ x, m₄ (a₃ x) = b₃ (m₃ x))
    (htop₂ : ∀ x : A₂, a₂ x = 0 ↔ x ∈ a₁.range)
    (htop₃ : ∀ x : A₃, a₃ x = 0 ↔ x ∈ a₂.range)
    (hbot₂ : ∀ y : B₂, b₂ y = 0 → y ∈ b₁.range)
    (hm₁ : Function.Surjective m₁) (hm₂ : Function.Injective m₂)
    (hm₄ : Function.Injective m₄) :
    Function.Injective m₃ := by
  rw [injective_iff_map_eq_zero]
  intro x₃ hx₃
  -- `m₄ (a₃ x₃) = b₃ (m₃ x₃) = 0` and `m₄` injective, so `a₃ x₃ = 0`, so `x₃ = a₂ x₂`.
  have ha₃ : a₃ x₃ = 0 := by
    have h := sq₃ x₃
    rw [hx₃, map_zero] at h
    exact (injective_iff_map_eq_zero m₄).mp hm₄ _ h
  obtain ⟨x₂, rfl⟩ := AddMonoidHom.mem_range.mp ((htop₃ _).mp ha₃)
  -- `b₂ (m₂ x₂) = m₃ (a₂ x₂) = 0`, so `m₂ x₂ = b₁ (m₁ x₁) = m₂ (a₁ x₁)`, so `x₂ = a₁ x₁`.
  have h1 : b₂ (m₂ x₂) = 0 := by rw [← sq₂]; exact hx₃
  obtain ⟨y₁, hy₁⟩ := AddMonoidHom.mem_range.mp (hbot₂ _ h1)
  obtain ⟨x₁, rfl⟩ := hm₁ y₁
  have h2 : x₂ = a₁ x₁ := hm₂ (by rw [sq₁, hy₁])
  -- Hence `x₃ = a₂ (a₁ x₁) = 0` by top exactness at `A₂`.
  rw [h2]
  exact (htop₂ _).mpr (AddMonoidHom.mem_range.mpr ⟨x₁, rfl⟩)

end FourLemma

/-! ## The long exact sequence

A module SES `0 → A' --f--> A --g--> A'' → 0` (with `C`-equivariant `f`, `g`) induces a short
exact sequence of word complexes; the degreewise functors `(·)⁴` and `(·)²` are exact.  From this
we build the connecting maps and the nine-term LES. -/

section LES

variable {A' A A'' : Type*}
  [AddCommGroup A'] [DistribMulAction C A'] [Finite A']
  [AddCommGroup A] [DistribMulAction C A] [Finite A]
  [AddCommGroup A''] [DistribMulAction C A''] [Finite A''] [Finite C]
  (f : A' →+ A) (g : A →+ A'')
  (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a) (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
  (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : f.range = g.ker)

include hsurj in
/-- Degree-1 (`(·)⁴`) surjectivity: `g` applied componentwise is surjective. -/
theorem pi_g_surjective : Function.Surjective (fun (x : Fin 4 → A) (i : Fin 4) => g (x i)) := by
  intro y; choose x hx using fun i => hsurj (y i); exact ⟨x, funext hx⟩

include hexact in
/-- Degree-1 exactness: `ker(g∘·) = range(f∘·)` on `Fin 4 → A`. -/
theorem pi_exact (y : Fin 4 → A) :
    (fun i => g (y i)) = 0 ↔ ∃ x : Fin 4 → A', (fun i => f (x i)) = y := by
  constructor
  · intro hy
    have hmem : ∀ i, y i ∈ f.range := by
      intro i
      rw [hexact, AddMonoidHom.mem_ker]
      exact congrFun hy i
    choose x hx using fun i => (AddMonoidHom.mem_range).mp (hmem i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext i
    show g (f (x i)) = 0
    have : f (x i) ∈ g.ker := by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨x i, rfl⟩
    exact AddMonoidHom.mem_ker.mp this

include hsurj in
/-- Degree-2 (`(·)²`) surjectivity: `g × g` is surjective. -/
theorem prod_g_surjective : Function.Surjective (g.prodMap g) := by
  rintro ⟨u, v⟩
  obtain ⟨a, ha⟩ := hsurj u
  obtain ⟨b, hb⟩ := hsurj v
  exact ⟨(a, b), by simp [AddMonoidHom.coe_prodMap, ha, hb]⟩

include hexact in
/-- Degree-2 exactness: `ker(g × g) = range(f × f)` on `A × A`. -/
theorem prod_exact (p : A × A) :
    (g.prodMap g) p = 0 ↔ ∃ q : A' × A', (f.prodMap f) q = p := by
  have hmem : ∀ x : A, x ∈ f.range ↔ g x = 0 := fun x => by
    rw [hexact, AddMonoidHom.mem_ker]
  rw [show (g.prodMap g) p = (g p.1, g p.2) from by rw [AddMonoidHom.coe_prodMap]; rfl,
    Prod.mk_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := (hmem p.1).mpr h1
    obtain ⟨b, hb⟩ := (hmem p.2).mpr h2
    exact ⟨(a, b), by rw [AddMonoidHom.coe_prodMap]; exact Prod.ext ha hb⟩
  · rintro ⟨q, hq⟩
    rw [AddMonoidHom.coe_prodMap] at hq
    exact ⟨(hmem p.1).mp ⟨q.1, congrArg Prod.fst hq⟩,
      (hmem p.2).mp ⟨q.2, congrArg Prod.snd hq⟩⟩

/-! ### The connecting map `δ¹ : H¹w(A'') → H²w(A')` (snake) -/

include hsurj in
/-- A chosen lift of a degree-1 `A''`-cochain to `A⁴` (via `g` surjective). -/
noncomputable def snakeLift (c'' : Fin 4 → A'') : Fin 4 → A := fun i => (hsurj (c'' i)).choose

include hsurj in
@[simp] theorem snakeLift_spec (c'' : Fin 4 → A'') (i : Fin 4) : g (snakeLift g hsurj c'' i) = c'' i :=
  (hsurj (c'' i)).choose_spec

include hg hsurj in
/-- For a cocycle `c'' ∈ Z¹w(A'')`, `d¹` of its lift lands in `ker(g × g)`. -/
theorem snake_d1_mem (t : Marking C) (c'' : Z1w (A := A'') t) :
    (g.prodMap g) (d1 t (snakeLift g hsurj c''.1)) = 0 := by
  have h1 : d1 t (fun i => g (snakeLift g hsurj c''.1 i))
      = (g.prodMap g) (d1 t (snakeLift g hsurj c''.1)) := by
    rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg (snakeLift g hsurj c''.1)
  rw [← h1, show (fun i => g (snakeLift g hsurj c''.1 i)) = c''.1 from
    funext (snakeLift_spec g hsurj c''.1)]
  exact AddMonoidHom.mem_ker.mp c''.2

include hg hsurj hexact in
/-- The `A'²`-element the snake extracts: `(f × f)(snakeZ) = d¹(lift c'')`. -/
noncomputable def snakeZ (t : Marking C) (c'' : Z1w (A := A'') t) : A' × A' :=
  ((prod_exact f g hexact (d1 t (snakeLift g hsurj c''.1))).mp
    (snake_d1_mem g hg hsurj t c'')).choose

include hg hsurj hexact in
theorem snakeZ_spec (t : Marking C) (c'' : Z1w (A := A'') t) :
    (f.prodMap f) (snakeZ f g hg hsurj hexact t c'') = d1 t (snakeLift g hsurj c''.1) :=
  ((prod_exact f g hexact (d1 t (snakeLift g hsurj c''.1))).mp
    (snake_d1_mem g hg hsurj t c'')).choose_spec

include hf hg hinj hsurj hexact in
/-- **Well-definedness of the snake**: for *any* lift `c` of `c''` and *any* `z` with
`(f×f)(z) = d¹(c)`, the class `[z] ∈ H²w(A')` equals `[snakeZ c'']` — so `δ¹` will not depend on
the chosen lift, hence descends to a hom on `H¹w(A'')`. -/
theorem snakeZ_welldef (t : Marking C) (c'' : Z1w (A := A'') t)
    (c : Fin 4 → A) (z : A' × A') (hc : (fun i => g (c i)) = c''.1)
    (hz : (f.prodMap f) z = d1 t c) :
    (QuotientAddGroup.mk z : H2w (A := A') t)
      = QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  -- `c − snakeLift` maps to `0` under `g`, so it is `f` of some `w : A'⁴`.
  have hker : (fun i => g ((c - snakeLift g hsurj c''.1) i)) = 0 := by
    funext i
    simp only [Pi.sub_apply, map_sub, snakeLift_spec, congrFun hc i, sub_self, Pi.zero_apply]
  obtain ⟨w, hw⟩ := (pi_exact f g hexact (c - snakeLift g hsurj c''.1)).mp hker
  -- `(f×f)(z − snakeZ) = d¹(c) − d¹(snakeLift) = d¹(f∘w) = (f×f)(d¹ w)`, so `z − snakeZ = d¹ w`.
  have hd1w : (f.prodMap f) (d1 t w) = d1 t (c - snakeLift g hsurj c''.1) := by
    rw [show (c - snakeLift g hsurj c''.1) = (fun i => f (w i)) from hw.symm]
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w).symm
  have hzz : (f.prodMap f) (z - snakeZ f g hg hsurj hexact t c'') = (f.prodMap f) (d1 t w) := by
    rw [map_sub, hz, snakeZ_spec, hd1w, map_sub]
  have : z - snakeZ f g hg hsurj hexact t c'' = d1 t w := hfinj hzz
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  exact ⟨w, this.symm⟩

include hf hg hinj hsurj hexact in
/-- The connecting map on cocycles, `Z¹w(A'') →+ H²w(A')`, `c'' ↦ [snakeZ c'']` (a hom by
`snakeZ_welldef`, using additive lifts). -/
noncomputable def delta1raw (t : Marking C) : Z1w (A := A'') t →+ H2w (A := A') t where
  toFun c'' := QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'')
  map_zero' :=
    ((snakeZ_welldef f g hf hg hinj hsurj hexact t 0 0 0
      (by funext i; simp) (by simp only [map_zero])).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' c''₁ c''₂ := by
    refine ((snakeZ_welldef f g hf hg hinj hsurj hexact t (c''₁ + c''₂)
      (snakeLift g hsurj c''₁.1 + snakeLift g hsurj c''₂.1)
      (snakeZ f g hg hsurj hexact t c''₁ + snakeZ f g hg hsurj hexact t c''₂) ?_ ?_).symm).trans
      (QuotientAddGroup.mk_add _ _ _)
    · funext i; simp only [Pi.add_apply, map_add, snakeLift_spec]; rfl
    · rw [map_add, snakeZ_spec, snakeZ_spec, ← map_add]

include hf hg hinj hsurj hexact in
/-- **The snake connecting map** `δ¹ : H¹w(A'') → H²w(A')`.  Descends `delta1raw` through the
`B¹w`-quotient: a coboundary `c'' = d⁰(a'')` lifts to `d⁰(â)`, whose `d¹` is `0`, so its class
is `0`. -/
noncomputable def delta1 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H1w (A := A'') t →+ H2w (A := A') t :=
  QuotientAddGroup.lift _ (delta1raw f g hf hg hinj hsurj hexact t) <| by
    rintro c'' hc''
    rw [AddSubgroup.mem_addSubgroupOf] at hc''
    obtain ⟨a'', ha''⟩ := hc''
    obtain ⟨a, ha⟩ := hsurj a''
    show QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') = 0
    refine ((snakeZ_welldef f g hf hg hinj hsurj hexact t c'' (d0 t a) 0 ?_ ?_).symm).trans
      (QuotientAddGroup.mk_zero _)
    · rw [← d0_natural t g hg a, ha]; exact ha''
    · rw [map_zero]; exact (d1Fun_comp_d0 t ht hw a).symm

/-! ### The connecting map `δ⁰ : H⁰w(A'') → H¹w(A')` (snake)

The mirror of `δ¹` one degree down.  Lift `a'' ∈ H⁰w(A'')` to `a ∈ A`; then `d⁰a ∈ ker(g∘·)`
(as `g∘d⁰a = d⁰(g a) = d⁰a'' = 0`), so `d⁰a = f∘w` for a unique `w : A'⁴`, which is a cocycle
(`f∘d¹w = d¹(f∘w) = d¹d⁰a = 0`, `f` injective).  `δ⁰(a'') := [w] ∈ H¹w(A')`; the class is
independent of the lift `a` (a different lift shifts `w` by a coboundary).  The domain `H⁰w` is an
honest subgroup (no quotient), so — unlike `δ¹` — no descent is needed, only lift-independence. -/

include hg hsurj in
/-- For `a'' ∈ H⁰w(A'')`, `d⁰` of the chosen lift lands in `ker(g∘·)` (degree 1). -/
theorem snake0_d0_mem (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => g (d0 t (hsurj a''.1).choose i)) = 0 := by
  rw [← d0_natural t g hg, (hsurj a''.1).choose_spec]
  exact AddMonoidHom.mem_ker.mp a''.2

include hg hsurj hexact in
/-- The `A'⁴`-cochain the degree-0 snake extracts: `f∘(snake0Z') = d⁰(lift a'')`. -/
noncomputable def snake0Z' (t : Marking C) (a'' : H0w (A := A'') t) : Fin 4 → A' :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp (snake0_d0_mem g hg hsurj t a'')).choose

include hg hsurj hexact in
theorem snake0Z'_spec (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => f (snake0Z' f g hg hsurj hexact t a'' i)) = d0 t (hsurj a''.1).choose :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp (snake0_d0_mem g hg hsurj t a'')).choose_spec

include hf hg hinj hsurj hexact in
/-- `snake0Z' ∈ Z¹w(A')`: its `d¹` vanishes (pull `d¹∘d⁰ = 0` back through the injection `f`). -/
theorem snake0Z'_mem (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) : d1 t (snake0Z' f g hg hsurj hexact t a'') = 0 := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  apply hfinj
  rw [map_zero]
  have hnat : (f.prodMap f) (d1 t (snake0Z' f g hg hsurj hexact t a''))
      = d1 t (fun i => f (snake0Z' f g hg hsurj hexact t a'' i)) := by
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf _).symm
  rw [hnat, snake0Z'_spec]
  exact d1Fun_comp_d0 t ht hw _

include hf hg hinj hsurj hexact in
/-- Lift-independence of `δ⁰`: *any* lift `a` of `a''` with cocycle `w` (`f∘w = d⁰a`) gives the
same class `[w] = δ⁰(a'')`.  A second lift differs by `f a'`, shifting `w` by `d⁰a'`. -/
theorem delta0_welldef (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) (a : A) (w : Fin 4 → A') (hwmem : d1 t w = 0)
    (ha : g a = a''.1) (hfw : (fun i => f (w i)) = d0 t a) :
    (QuotientAddGroup.mk ⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ : H1w (A := A') t)
      = QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
          AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ := by
  set w₀ := snake0Z' f g hg hsurj hexact t a'' with hw₀
  -- `a − lift` is in `ker g = range f`.
  have hga : g (a - (hsurj a''.1).choose) = 0 := by
    rw [map_sub, ha, (hsurj a''.1).choose_spec, sub_self]
  obtain ⟨a', ha'⟩ := (AddMonoidHom.mem_range).mp (by rw [hexact]; exact AddMonoidHom.mem_ker.mpr hga)
  -- `f∘(w − w₀) = d⁰a − d⁰(lift) = d⁰(a − lift) = d⁰(f a') = f∘(d⁰a')`, so `w − w₀ = d⁰a'`.
  have hww₀ : (w - w₀ : Fin 4 → A') = d0 t a' := by
    funext i
    apply hinj
    have ex := congrFun (snake0Z'_spec f g hg hsurj hexact t a'') i
    rw [Pi.sub_apply, map_sub, congrFun hfw i, ex, ← congrFun (d0_natural t f hf a') i, ha',
      map_sub, Pi.sub_apply]
  -- Hence the difference of the two cocycles is a coboundary, so the classes agree.
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  refine (AddMonoidHom.mem_range).mpr ⟨a', ?_⟩
  have hcoe : (↑(⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ - ⟨w₀,
      AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ :
      Z1w (A := A') t) : Fin 4 → A') = w - w₀ := rfl
  rw [hcoe]; exact hww₀.symm

include hf hg hinj hsurj hexact in
/-- **The degree-0 connecting map** `δ⁰ : H⁰w(A'') →+ H¹w(A')`. -/
noncomputable def delta0 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H0w (A := A'') t →+ H1w (A := A') t where
  toFun a'' := QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
    AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩
  map_zero' :=
    ((delta0_welldef f g hf hg hinj hsurj hexact t ht hw 0 0 0 (by simp) (by simp)
      (by funext i; simp)).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' x y := by
    refine Eq.trans ?_ (QuotientAddGroup.mk_add _ _ _)
    exact (delta0_welldef f g hf hg hinj hsurj hexact t ht hw (x + y)
      ((hsurj x.1).choose + (hsurj y.1).choose)
      (snake0Z' f g hg hsurj hexact t x + snake0Z' f g hg hsurj hexact t y)
      (by rw [map_add, snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw x,
            snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw y, add_zero])
      (by rw [map_add, (hsurj x.1).choose_spec, (hsurj y.1).choose_spec]; rfl)
      (by funext i
          rw [Pi.add_apply, map_add,
            congrFun (snake0Z'_spec f g hg hsurj hexact t x) i,
            congrFun (snake0Z'_spec f g hg hsurj hexact t y) i, ← Pi.add_apply, ← map_add])).symm

/-! ### Exactness of the nine-term LES

Each spot is stated as `y ∈ ker(out) ↔ y ∈ range(in)` (equivalently at the ends, injectivity /
surjectivity), the usual snake-lemma bookkeeping. -/

include hsurj in
/-- Exactness at the right end: `H²wMap g` is surjective. -/
theorem H2wMap_g_surjective (t : Marking C) : Function.Surjective (H2wMap t g hg) := by
  intro y
  obtain ⟨p'', rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨p, hp⟩ := prod_g_surjective g hsurj p''
  exact ⟨QuotientAddGroup.mk p, by
    rw [show H2wMap t g hg (QuotientAddGroup.mk p)
      = QuotientAddGroup.mk (g.prodMap g p) from rfl, hp]⟩

include hg hsurj hexact in
/-- Exactness at `H²w(A)`: `ker(H²wMap g) = range(H²wMap f)`. -/
theorem H2w_exact_mid (t : Marking C) (y : H2w (A := A) t) :
    y ∈ (H2wMap t g hg).ker ↔ y ∈ (H2wMap t f hf).range := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective y
  constructor
  · intro hy
    have hmem : (g.prodMap g) p ∈ (d1 (A := A'') t).range :=
      (QuotientAddGroup.eq_zero_iff _).mp (AddMonoidHom.mem_ker.mp hy)
    obtain ⟨x'', hx''⟩ := AddMonoidHom.mem_range.mp hmem   -- d¹ x'' = g×g p
    obtain ⟨x, hx⟩ := pi_g_surjective g hsurj x''          -- g∘x = x''
    have H : d1 t (fun i => g (x i)) = (g.prodMap g) (d1 t x) := by
      rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg x
    have hd1 : (g.prodMap g) (d1 t x) = d1 t x'' := by rw [← H]; exact congrArg (d1 t) hx
    have hker : (g.prodMap g) (p - d1 t x) = 0 := by rw [map_sub, hd1, hx'', sub_self]
    obtain ⟨q, hq⟩ := (prod_exact f g hexact (p - d1 t x)).mp hker  -- f×f q = p − d¹ x
    refine ⟨QuotientAddGroup.mk q, ?_⟩
    show (QuotientAddGroup.mk (f.prodMap f q) : H2w (A := A) t) = QuotientAddGroup.mk p
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff, hq,
      show (p - d1 t x) - p = -(d1 t x) from by abel]
    exact (AddSubgroup.neg_mem_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  · rintro ⟨z, hz⟩
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hgf : (g.prodMap g) (f.prodMap f q) = 0 := by
      rw [AddMonoidHom.coe_prodMap, AddMonoidHom.coe_prodMap]
      have hz0 : ∀ a', g (f a') = 0 := fun a' =>
        AddMonoidHom.mem_ker.mp (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨a', rfl⟩)
      show (g (f q.1), g (f q.2)) = 0
      rw [hz0, hz0]; rfl
    rw [AddMonoidHom.mem_ker, ← hz]
    show (QuotientAddGroup.mk (g.prodMap g (f.prodMap f q)) : H2w (A := A'') t) = 0
    rw [hgf]; exact QuotientAddGroup.mk_zero _

include hinj in
/-- Exactness at the left end: `H⁰wMap f` is injective. -/
theorem H0wMap_f_injective (t : Marking C) : Function.Injective (H0wMap t f hf) := by
  intro a b hab
  exact Subtype.ext (hinj (congrArg Subtype.val hab))

include hf hinj hexact in
/-- Exactness at `H⁰w(A)`: `ker(H⁰wMap g) = range(H⁰wMap f)`. -/
theorem H0w_exact_mid (t : Marking C) (a : H0w (A := A) t) :
    a ∈ (H0wMap t g hg).ker ↔ a ∈ (H0wMap t f hf).range := by
  constructor
  · intro ha
    have h1 : g a.1 = 0 := congrArg Subtype.val (AddMonoidHom.mem_ker.mp ha)
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.mp
      (by rw [hexact]; exact AddMonoidHom.mem_ker.mpr h1)
    have hd0 : d0 t a' = 0 := by
      funext i
      show d0 t a' i = 0
      apply hinj
      have h2 : d0 t (f a') i = f (d0 t a' i) := congrFun (d0_natural t f hf a') i
      have h3 : d0 t a.1 i = 0 := congrFun (AddMonoidHom.mem_ker.mp a.2) i
      rw [map_zero, ← h2, ha']
      exact h3
    exact ⟨⟨a', AddMonoidHom.mem_ker.mpr hd0⟩, Subtype.ext ha'⟩
  · rintro ⟨a', rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    apply Subtype.ext
    show g (f a'.1) = 0
    exact AddMonoidHom.mem_ker.mp
      (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨a'.1, rfl⟩)

include hf hg hinj hsurj hexact in
/-- Exactness at `H⁰w(A'')`: `ker δ⁰ = range(H⁰wMap g)`. -/
theorem H0w_exact_right (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) :
    a'' ∈ (delta0 f g hf hg hinj hsurj hexact t ht hw).ker ↔ a'' ∈ (H0wMap t g hg).range := by
  constructor
  · intro h0
    have h0' : (QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
        AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ :
        H1w (A := A') t) = 0 := AddMonoidHom.mem_ker.mp h0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0'
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.mp h0'
    have ha'' : d0 t a' = snake0Z' f g hg hsurj hexact t a'' := ha'
    refine ⟨⟨(hsurj a''.1).choose - f a', AddMonoidHom.mem_ker.mpr ?_⟩, Subtype.ext ?_⟩
    · funext i
      show d0 t ((hsurj a''.1).choose - f a') i = 0
      have h2 : d0 t (f a') i = f (d0 t a' i) := congrFun (d0_natural t f hf a') i
      have h4 : f (snake0Z' f g hg hsurj hexact t a'' i)
          = d0 t (hsurj a''.1).choose i := congrFun (snake0Z'_spec f g hg hsurj hexact t a'') i
      have h5 : d0 t a' i = snake0Z' f g hg hsurj hexact t a'' i := congrFun ha'' i
      rw [map_sub, Pi.sub_apply, h2, h5, h4, sub_self]
    · show g ((hsurj a''.1).choose - f a') = a''.1
      rw [map_sub, (hsurj a''.1).choose_spec,
        show g (f a') = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨a', rfl⟩), sub_zero]
  · rintro ⟨a, rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    have hwd := delta0_welldef f g hf hg hinj hsurj hexact t ht hw (H0wMap t g hg a) a.1 0
      (map_zero _) rfl
      (by funext i
          simp only [Pi.zero_apply, map_zero]
          exact (congrFun (AddMonoidHom.mem_ker.mp a.2) i).symm)
    show (QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t (H0wMap t g hg a),
      AddMonoidHom.mem_ker.mpr
        (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw (H0wMap t g hg a))⟩ :
      H1w (A := A') t) = 0
    exact hwd.symm.trans (QuotientAddGroup.mk_zero _)

include hf hg hinj hsurj hexact in
/-- Exactness at `H¹w(A')`: `ker(H¹wMap f) = range δ⁰`. -/
theorem H1w_exact_left (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H1w (A := A') t) :
    h ∈ (H1wMap t f hf).ker ↔ h ∈ (delta0 f g hf hg hinj hsurj hexact t ht hw).range := by
  constructor
  · intro hker
    obtain ⟨w', rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (Z1wMap t f hf w') : H1w (A := A) t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp h1
    have ha' : d0 t a = fun i => f (w'.1 i) := ha
    -- `g a` is an `H⁰w(A'')`-element hitting `[w']` under `δ⁰`.
    have hga : d0 t (g a) = 0 := by
      funext i
      show d0 t (g a) i = 0
      have h2 : d0 t (g a) i = g (d0 t a i) := congrFun (d0_natural t g hg a) i
      have h3 : d0 t a i = f (w'.1 i) := congrFun ha' i
      rw [h2, h3]
      exact AddMonoidHom.mem_ker.mp
        (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨w'.1 i, rfl⟩)
    exact ⟨⟨g a, AddMonoidHom.mem_ker.mpr hga⟩,
      (delta0_welldef f g hf hg hinj hsurj hexact t ht hw ⟨g a, AddMonoidHom.mem_ker.mpr hga⟩
        a w'.1 (AddMonoidHom.mem_ker.mp w'.2) rfl ha'.symm).symm⟩
  · rintro ⟨a'', rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (Z1wMap t f hf ⟨snake0Z' f g hg hsurj hexact t a'',
      AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩) :
      H1w (A := A) t) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨(hsurj a''.1).choose,
      (snake0Z'_spec f g hg hsurj hexact t a'').symm⟩

include hf hg hinj hsurj hexact in
/-- Exactness at `H¹w(A)`: `ker(H¹wMap g) = range(H¹wMap f)`. -/
theorem H1w_exact_mid (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H1w (A := A) t) :
    h ∈ (H1wMap t g hg).ker ↔ h ∈ (H1wMap t f hf).range := by
  constructor
  · intro hker
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (Z1wMap t g hg x) : H1w (A := A'') t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨a'', ha''⟩ := AddMonoidHom.mem_range.mp h1
    have ha : d0 t a'' = fun i => g (x.1 i) := ha''
    obtain ⟨a, rfl⟩ := hsurj a''
    -- `x − d⁰a` maps to `0` under `g`, hence is `f∘w'` for a cocycle `w'`.
    have hxa : (fun i => g ((x.1 - d0 t a) i)) = 0 := by
      funext i
      show g ((x.1 - d0 t a) i) = 0
      have h2 : d0 t (g a) i = g (d0 t a i) := congrFun (d0_natural t g hg a) i
      have h3 : d0 t (g a) i = g (x.1 i) := congrFun ha i
      rw [Pi.sub_apply, map_sub, ← h3, h2, sub_self]
    obtain ⟨w', hw'⟩ := (pi_exact f g hexact (x.1 - d0 t a)).mp hxa
    have hw'z : d1 t w' = 0 := by
      have hfinj : Function.Injective (f.prodMap f) := by
        rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
      apply hfinj
      have hnat : (f.prodMap f) (d1 t w') = d1 t (fun i => f (w' i)) := by
        rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w').symm
      rw [map_zero, hnat, hw', map_sub, AddMonoidHom.mem_ker.mp x.2,
        show d1 t (d0 t a) = 0 from d1Fun_comp_d0 t ht hw a, sub_zero]
    refine ⟨QuotientAddGroup.mk ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩, ?_⟩
    show (QuotientAddGroup.mk (Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩) :
      H1w (A := A) t) = QuotientAddGroup.mk x
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.mpr ⟨-a, ?_⟩
    show d0 t (-a)
      = ((Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩ - x : Z1w (A := A) t) :
        Fin 4 → A)
    have hval : ((Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩ - x :
        Z1w (A := A) t) : Fin 4 → A) = (fun i => f (w' i)) - x.1 := rfl
    rw [hval, hw', map_neg]
    abel
  · rintro ⟨z, rfl⟩
    obtain ⟨w', rfl⟩ := QuotientAddGroup.mk_surjective z
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (Z1wMap t g hg (Z1wMap t f hf w')) : H1w (A := A'') t) = 0
    have hzero : Z1wMap t g hg (Z1wMap t f hf w') = 0 := by
      apply Subtype.ext
      funext i
      show g (f (w'.1 i)) = 0
      exact AddMonoidHom.mem_ker.mp
        (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨w'.1 i, rfl⟩)
    rw [hzero]
    exact QuotientAddGroup.mk_zero _

include hf hg hinj hsurj hexact in
/-- Exactness at `H¹w(A'')`: `ker δ¹ = range(H¹wMap g)`. -/
theorem H1w_exact_right (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (h : H1w (A := A'') t) :
    h ∈ (delta1 f g hf hg hinj hsurj hexact t ht hw).ker ↔ h ∈ (H1wMap t g hg).range := by
  constructor
  · intro hker
    obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') : H2w (A := A') t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    obtain ⟨w', hw'⟩ := AddMonoidHom.mem_range.mp ((QuotientAddGroup.eq_zero_iff _).mp h1)
    -- `x := (lift c'') − f∘w'` is a `Z¹w(A)`-cocycle mapping onto `c''`.
    have hd1x : d1 t (snakeLift g hsurj c''.1 - fun i => f (w' i)) = 0 := by
      have hnat : (f.prodMap f) (d1 t w') = d1 t (fun i => f (w' i)) := by
        rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w').symm
      rw [map_sub, ← snakeZ_spec f g hg hsurj hexact t c'', ← hnat, hw', sub_self]
    refine ⟨QuotientAddGroup.mk ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
      AddMonoidHom.mem_ker.mpr hd1x⟩, ?_⟩
    show (QuotientAddGroup.mk (Z1wMap t g hg ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
      AddMonoidHom.mem_ker.mpr hd1x⟩) : H1w (A := A'') t) = QuotientAddGroup.mk c''
    have hval : Z1wMap t g hg ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
        AddMonoidHom.mem_ker.mpr hd1x⟩ = c'' := by
      apply Subtype.ext
      funext i
      show g ((snakeLift g hsurj c''.1 - fun i => f (w' i)) i) = c''.1 i
      rw [Pi.sub_apply, map_sub, snakeLift_spec g hsurj c''.1 i,
        show g (f (w' i)) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨w' i, rfl⟩), sub_zero]
    rw [hval]
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t (Z1wMap t g hg x)) :
      H2w (A := A') t) = 0
    refine ((snakeZ_welldef f g hf hg hinj hsurj hexact t (Z1wMap t g hg x) x.1 0 rfl ?_).symm).trans
      (QuotientAddGroup.mk_zero _)
    rw [map_zero]
    exact (AddMonoidHom.mem_ker.mp x.2).symm

include hf hg hinj hsurj hexact in
/-- Exactness at `H²w(A')`: `ker(H²wMap f) = range δ¹`. -/
theorem H2w_exact_left (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (y : H2w (A := A') t) :
    y ∈ (H2wMap t f hf).ker ↔ y ∈ (delta1 f g hf hg hinj hsurj hexact t ht hw).range := by
  constructor
  · intro hker
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h1 : (f.prodMap f) z ∈ (d1 (A := A) t).range :=
      (QuotientAddGroup.eq_zero_iff _).mp (AddMonoidHom.mem_ker.mp hker)
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp h1
    have hc'' : d1 t (fun i => g (x i)) = 0 := by
      have hnat : d1 t (fun i => g (x i)) = (g.prodMap g) (d1 t x) := by
        rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg x
      rw [hnat, hx, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_prodMap]
      show (g (f z.1), g (f z.2)) = 0
      rw [show g (f z.1) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨z.1, rfl⟩),
        show g (f z.2) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨z.2, rfl⟩)]
      rfl
    refine ⟨QuotientAddGroup.mk ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩, ?_⟩
    show (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t
      ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩) : H2w (A := A') t)
      = QuotientAddGroup.mk z
    exact (snakeZ_welldef f g hf hg hinj hsurj hexact t
      ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩ x z rfl hx.symm).symm
  · rintro ⟨hcls, rfl⟩
    obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective hcls
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk ((f.prodMap f) (snakeZ f g hg hsurj hexact t c'')) :
      H2w (A := A) t) = 0
    rw [snakeZ_spec f g hg hsurj hexact t c'']
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)

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
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := fun lam => elemDual_two_torsion lam
  have hD'₂ : ∀ lam : ElemDual A', lam + lam = 0 := fun lam => elemDual_two_torsion lam
  have hD''₂ : ∀ lam : ElemDual A'', lam + lam = 0 := fun lam => elemDual_two_torsion lam
  -- Finiteness of the subquotients.
  haveI : Finite (H1w (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H1w (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := A') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := A'') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := ElemDual A') t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  haveI : Finite (H2w (A := ElemDual A'') t) := inferInstanceAs (Finite (_ ⧸ _))
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
      have h0 : t.σ • v - v = 0 := congrFun hv' 0
      have h1 : t.τ • v - v = 0 := congrFun hv' 1
      have h2 : t.x₀ • v - v = 0 := congrFun hv' 2
      have h3 : t.x₁ • v - v = 0 := congrFun hv' 3
      rintro c (rfl | rfl | rfl | rfl)
      · exact sub_eq_zero.mp h0
      · exact sub_eq_zero.mp h1
      · exact sub_eq_zero.mp h2
      · exact sub_eq_zero.mp h3
    have hle : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤ S :=
      (Subgroup.closure_le S).mpr hmarked
    intro c
    exact hle (by rw [hgen]; trivial)
  · intro hv
    apply AddMonoidHom.mem_ker.mpr
    funext i
    fin_cases i
    · show t.σ • v - v = 0
      rw [hv t.σ, sub_self]
    · show t.τ • v - v = 0
      rw [hv t.τ, sub_self]
    · show t.x₀ • v - v = 0
      rw [hv t.x₀, sub_self]
    · show t.x₁ • v - v = 0
      rw [hv t.x₁, sub_self]

/-- For a generating marking, the two self-duality packages coincide. -/
theorem isSelfDual_iff_W {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [Finite C] (t : Marking C) (hgen : t.Generates) :
    IsSelfDual t A ↔ IsSelfDualW t A := by
  have hcard : Nat.card (fixedPts C (ElemDual A)) = Nat.card (H0w (A := ElemDual A) t) :=
    Nat.card_congr (Equiv.setCongr (H0w_eq_fixedPts t hgen)).symm
  unfold IsSelfDual IsSelfDualW
  rw [hcard]

end GeneratesBridge

/-! ## Lemma 5.11, `fixedPts`-form (the P-12 statement, relocated and proved)

The statement formerly sorried in `GQ2/FoxHeisenberg.lean` — same fully qualified name
`GQ2.FoxH.lemma_5_11` — with one hypothesis added: `hgen : t.Generates`.  Generation identifies
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
