/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Devissage.Naturality

@[expose] public section

/-!
# §5.11 dévissage: the elementary-dual pack

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

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

/-- **Extension lemma**: every `𝔽₂`-functional extends along an injection into a finite
elementary 2-group (`ZMod 2` is self-injective on this category; proof by complementing the
image subspace). -/
theorem elemDual_extend {A' A : Type*} [AddCommGroup A'] [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) (f : A' →+ A) (hinj : Function.Injective f)
    (lam' : ElemDual A') : ∃ lam : ElemDual A, ∀ a', lam (f a') = lam' a' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  have : Module (ZMod 2) A' := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]
    apply hinj
    rw [map_add, map_zero]
    exact hA₂ (f v))
  set F := AddMonoidHom.toZModLinearMap 2 f with hFdef
  have hFapp : ∀ a', F a' = f a' := fun a' =>
    congrFun (AddMonoidHom.coe_toZModLinearMap 2 f) a'
  have hFinj : Function.Injective F := (AddMonoidHom.coe_toZModLinearMap 2 f).symm ▸ hinj
  set L := AddMonoidHom.toZModLinearMap 2 (lam' : A' →+ ZMod 2) with hLdef
  -- A linear left inverse `G` of `F` (basis complement); then `L ∘ G` extends.
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.mpr hFinj)
  refine ⟨((L.comp G).toAddMonoidHom : ElemDual A), fun a' => ?_⟩
  show L (G (f a')) = lam' a'
  have h1 : G (f a') = a' := by rw [← hFapp a']; exact LinearMap.congr_fun hG a'
  rw [h1]
  exact congrFun (AddMonoidHom.coe_toZModLinearMap 2 _) a'

/-- The `𝔽₂`-dual separates points on a finite elementary 2-group. -/
theorem elemDual_separates {A : Type*} [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {a : A} (ha : a ≠ 0) : ∃ lam : ElemDual A, lam a ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  by_contra! h
  exact ha ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) a).mp fun φ => h φ.toAddMonoidHom)

/-- The dimension count `#(ElemDual A) = #A` for finite elementary `A`. -/
theorem card_elemDual {A : Type*} [AddCommGroup A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (ElemDual A) = Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  have : FiniteDimensional (ZMod 2) A := Module.Finite.of_finite
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
  have : Finite (ElemDual A →+ ZMod 2) := inferInstanceAs (Finite (ElemDual (ElemDual A)))
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · intro x y hxy
    have h1 : ∀ lam : ElemDual A, lam x = lam y := fun lam => by
      simpa using DFunLike.congr_fun hxy lam
    by_contra hne
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ (sub_ne_zero_of_ne hne)
    exact hlam (by rw [map_sub, h1 lam, sub_self])
  · show Nat.card A = Nat.card (ElemDual (ElemDual A))
    rw [card_elemDual ElemDual.add_self_eq_zero, card_elemDual hA₂]

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
    a' + a' = 0 :=
  hinj (by rw [map_add, map_zero]; exact hA₂ (f a'))

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
    rwa [QuotientAddGroup.kerLift_mk] at h1
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

end GQ2.FoxH
