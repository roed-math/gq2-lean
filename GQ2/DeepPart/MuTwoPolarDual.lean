/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepPart.QuadraticFp2

@[expose] public section

/-!
# Euler-characteristic collapse, the `μ₂` bricks, and polar self-duality

The opening `GQ2.DeepPart` layer: the Euler-characteristic collapse `#H¹ = #M` (B7 with trivial
`H⁰`, `H²`) together with the `H⁰`-vanishing and fixed-point-transport lemmas; the `μ₂ ≅ ℤ/2`
bricks with trivial Galois action; and the polar self-duality `V ≃+ Hom(V, μ₂)` yielding `#H² = 1`
(§6.3 step 2, Ax B6 via the Tate-duality parameter `D`).

This file is part of the `GQ2.DeepPart` split (the deep-part proof); see `GQ2/DeepPart.lean` for the overview.
-/

open scoped Classical

namespace GQ2.DeepPart

open GQ2 GQ2.ContCoh GQ2.Foundations

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M]

/-- **Euler-characteristic collapse**: for a finite `2`-power-order `G_ℚ₂`-module with trivial
`H⁰` and `H²`, the local Euler characteristic (B7) reads `#H¹ = #M`. -/
theorem card_H1_eq_card_of_H0_H2_trivial (hH0 : Nat.card (H0 AbsGalQ2 M) = 1)
    (hH2 : Nat.card (H2 AbsGalQ2 M) = 1) {k : ℕ} (hk : Nat.card M = 2 ^ k) :
    Nat.card (H1 AbsGalQ2 M) = Nat.card M := by
  rw [card_H1_of_card_eq_two_pow M hk, hH0, hH2, one_mul, one_mul]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] [Finite M] in
/-- `H⁰(G_ℚ₂, M) = 0` (as `Nat.card = 1`) iff `M` has no nonzero `G_ℚ₂`-fixed vector. -/
theorem card_H0_eq_one_iff :
    Nat.card (H0 AbsGalQ2 M) = 1 ↔ ∀ m : M, (∀ g : AbsGalQ2, g • m = m) → m = 0 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, _⟩ m hm
    exact Subtype.ext_iff.mp (Subsingleton.elim (⟨m, hm⟩ : H0 AbsGalQ2 M) ⟨0, smul_zero⟩)
  · intro h
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨0, smul_zero⟩⟩
    rw [h a.1 a.2, h b.1 b.2]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] [Finite M] in
/-- **`H⁰`-vanishing** (§6.3 step 2, `V^{G_ℚ₂} = 0`): if the `G_ℚ₂`-action on `M` factors
through a *surjective* `ρ : G_ℚ₂ →* C`, the `C`-module `M` is simple, and some element of `C`
moves some vector, then `#H⁰ = 1`.  (`V^{im ρ} = V^C` is `C`-stable — even pointwise fixed —
so simplicity forces it to `⊥` or `⊤`, and `⊤` contradicts the moving element.) -/
theorem card_H0_eq_one_of_surjective {C : Type*} [Group C] [DistribMulAction C M]
    (ρ : AbsGalQ2 →* C) (hρsurj : Function.Surjective ρ)
    (hρ : ∀ (g : AbsGalQ2) (m : M), g • m = ρ g • m)
    (hsimple : ∀ W : AddSubgroup M, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ m : M, h₀ • m ≠ m) :
    Nat.card (H0 AbsGalQ2 M) = 1 := by
  rw [card_H0_eq_one_iff]
  intro m hm
  set W : AddSubgroup M :=
    { carrier := {x : M | ∀ h : C, h • x = x}
      zero_mem' := fun h => smul_zero h
      add_mem' := fun ha hb h => by rw [smul_add, ha h, hb h]
      neg_mem' := fun ha h => by rw [smul_neg, ha h] } with hWdef
  have hWmem : ∀ x : M, x ∈ W ↔ ∀ h : C, h • x = x := fun x => Iff.rfl
  have hstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    have hw' := (hWmem w).mp hw
    rw [hw' h]
    exact hw
  rcases hsimple W hstable with hbot | htop
  · have hmW : m ∈ W := by
      rw [hWmem]
      intro h
      obtain ⟨g, rfl⟩ := hρsurj h
      rw [← hρ g m]
      exact hm g
    rw [hbot, AddSubgroup.mem_bot] at hmW
    exact hmW
  · exfalso
    obtain ⟨m₀, hm₀⟩ := hmoves
    have hin : m₀ ∈ W := htop ▸ AddSubgroup.mem_top m₀
    exact hm₀ ((hWmem m₀).mp hin h₀)

/-- **Fixed-point transport**: an equivariant additive iso induces a cardinality equality of
`H⁰`s (it restricts to a bijection of the fixed-point subgroups). -/
theorem card_H0_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction AbsGalQ2 A] [DistribMulAction AbsGalQ2 B]
    (e : A ≃+ B) (he : ∀ (g : AbsGalQ2) (a : A), e (g • a) = g • e a) :
    Nat.card (H0 AbsGalQ2 B) = Nat.card (H0 AbsGalQ2 A) := by
  have hesymm : ∀ (g : AbsGalQ2) (b : B), e.symm (g • b) = g • e.symm b := by
    intro g b
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine Nat.card_congr ⟨fun y => ⟨e.symm y.1, fun g => ?_⟩,
    fun x => ⟨e x.1, fun g => ?_⟩, fun y => ?_, fun x => ?_⟩
  · rw [← hesymm g y.1, y.2 g]
  · rw [← he g x.1, x.2 g]
  · exact Subtype.ext (e.apply_symm_apply y.1)
  · exact Subtype.ext (e.symm_apply_apply x.1)

/-! ## The `μ₂` bricks: `μ₂ ≅ ℤ/2` with trivial Galois action

`MuN 2 = Additive (rootsOfUnity 2 ℚ̄₂) = {1, −1}` additively: classified by the value of the
underlying root, Galois-fixed because an additive automorphism of a two-element group is the
identity. -/

section MuTwo

/-- `−1` as the nonzero element of the additive `μ₂`. -/
noncomputable def muTwoGen : MuN 2 :=
  Additive.ofMul ⟨(-1 : (AlgebraicClosure ℚ_[2])ˣ), (mem_rootsOfUnity 2 _).mpr neg_one_sq⟩

theorem muTwoGen_ne_zero : muTwoGen ≠ 0 := by
  intro h
  have h1 : ((((Additive.toMul muTwoGen : rootsOfUnity 2 (AlgebraicClosure ℚ_[2])) :
      (AlgebraicClosure ℚ_[2])ˣ)) : AlgebraicClosure ℚ_[2]) = 1 := by
    rw [h]
    rfl
  have hneg : (-1 : AlgebraicClosure ℚ_[2]) = 1 := h1
  have h2 : (2 : AlgebraicClosure ℚ_[2]) = 0 := by linear_combination - hneg
  exact two_ne_zero h2

/-- Classification: `μ₂` has exactly the elements `0` and `muTwoGen`. -/
theorem muTwo_eq_zero_or_gen (x : MuN 2) : x = 0 ∨ x = muTwoGen := by
  set u : rootsOfUnity 2 (AlgebraicClosure ℚ_[2]) := Additive.toMul x with hu
  have hval : ((u : (AlgebraicClosure ℚ_[2])ˣ) : AlgebraicClosure ℚ_[2])
      * ((u : (AlgebraicClosure ℚ_[2])ˣ) : AlgebraicClosure ℚ_[2]) = 1 := by
    have hpow := (mem_rootsOfUnity 2 (u : (AlgebraicClosure ℚ_[2])ˣ)).mp u.2
    have hval' := congrArg Units.val hpow
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at hval'
  rcases mul_self_eq_one_iff.mp hval with h1 | hneg
  · left
    have hu1 : u = 1 := Subtype.ext (Units.ext h1)
    rw [← ofMul_toMul x, ← hu, hu1]
    rfl
  · right
    have hu1 : u = ⟨(-1 : (AlgebraicClosure ℚ_[2])ˣ), (mem_rootsOfUnity 2 _).mpr neg_one_sq⟩ :=
      Subtype.ext (Units.ext (by rw [Units.val_neg, Units.val_one]; exact hneg))
    rw [← ofMul_toMul x, ← hu, hu1]
    rfl

/-- The hom `ℤ/2 →+ μ₂`, `1 ↦ −1`. -/
noncomputable def zmodTwoToMuTwo : ZMod 2 →+ MuN 2 :=
  ZMod.lift 2 ⟨zmultiplesHom (MuN 2) muTwoGen, by
    show ((2 : ℕ) : ℤ) • muTwoGen = 0
    rw [natCast_zsmul]
    exact nsmul_muN_eq_zero 2 muTwoGen⟩

theorem zmodTwoToMuTwo_one : zmodTwoToMuTwo 1 = muTwoGen := by
  show ZMod.lift 2 _ ((1 : ℤ) : ZMod 2) = muTwoGen
  rw [ZMod.lift_coe]
  exact one_zsmul muTwoGen

/-- `ℤ/2 ≃+ μ₂` (additive), `1 ↦ −1`. -/
noncomputable def zmodTwoEquivMuTwo : ZMod 2 ≃+ MuN 2 := by
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine AddEquiv.ofBijective zmodTwoToMuTwo ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    rcases hcases a with rfl | rfl
    · rfl
    · rw [zmodTwoToMuTwo_one] at ha
      exact absurd ha muTwoGen_ne_zero
  · intro y
    rcases muTwo_eq_zero_or_gen y with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, zmodTwoToMuTwo_one⟩

/-- **The Galois action on `μ₂` is trivial** — an additive automorphism of the two-element
group is the identity. -/
theorem muTwo_smul_trivial (g : AbsGalQ2) (x : MuN 2) : g • x = x := by
  rcases muTwo_eq_zero_or_gen x with rfl | rfl
  · exact smul_zero g
  · rcases muTwo_eq_zero_or_gen (g • muTwoGen) with h | h
    · exact absurd ((smul_eq_zero_iff_eq g).mp h) muTwoGen_ne_zero
    · exact h

end MuTwo

/-! ## The polar self-duality `V ≃+ Hom(V, μ₂)` and `#H² = 1`  (§6.3 step 2, Ax B6 via `D`)

A nonsingular Galois-invariant `𝔽₂` quadratic form identifies `V` with its `μ₂`-dual
equivariantly, so `#H⁰(M′) = #H⁰(V)`; Tate duality's `(0,2)` clause at `M := V` then reads
`#H²(V) = #Hom(H²(V), ℤ/2) = #H⁰(M′) = #H⁰(V)` — no dual-simplicity argument needed. -/

section PolarDual

open GQ2.QuadraticFp2

variable (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [Finite V]

omit [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul AbsGalQ2 V] [Finite V] in
/-- A Galois-invariant form has Galois-invariant polar form. -/
theorem polar_smul_smul (q : V → ZMod 2) (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (g : AbsGalQ2) (a b : V) : polar q (g • a) (g • b) = polar q a b := by
  unfold GQ2.QuadraticFp2.polar
  rw [← smul_add, hqG, hqG, hqG]

omit [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul AbsGalQ2 V] in
/-- **Polar self-duality**: a nonsingular Galois-invariant quadratic form on a finite exp-2
module induces an equivariant additive iso `V ≃+ Hom(V, μ₂)`. -/
theorem exists_polarSelfDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    ∃ e : V ≃+ MuDual 2 V, ∀ (g : AbsGalQ2) (v : V), e (g • v) = g • e v := by
  classical
  set ε := zmodTwoEquivMuTwo with hε
  -- the underlying hom `v ↦ ε ∘ B(·, v)`
  set Ψ : V →+ MuDual 2 V :=
    { toFun := fun v => (ε.toAddMonoidHom.comp (polarHom q hq v) : MuDual 2 V)
      map_zero' := by
        refine DFunLike.ext _ _ fun m => ?_
        show ε (polar q m 0) = (0 : MuDual 2 V) m
        rw [MuDual.zero_apply]
        have hpz : polar q m 0 = 0 := by
          unfold GQ2.QuadraticFp2.polar
          rw [add_zero, hq.map_zero, add_zero]
          exact CharTwo.add_self_eq_zero _
        rw [hpz, map_zero]
      map_add' := fun v w => by
        refine DFunLike.ext _ _ fun m => ?_
        show ε (polar q m (v + w)) = ε (polar q m v) + ε (polar q m w)
        rw [hq.polar_add_right, map_add] } with hΨ
  have hΨapply : ∀ (v m : V), Ψ v m = ε (polar q m v) := fun v m => rfl
  -- injectivity from nonsingularity
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨w, hw⟩ := hns v hne
    have h0 : ε (polar q w v) = 0 := by
      have := DFunLike.congr_fun hv w
      rwa [MuDual.zero_apply] at this
    have hp0 : polar q w v = 0 := ε.injective (by rw [h0, map_zero])
    exact hw (polar_comm q w v ▸ hp0)
  -- cardinality: `#Hom(V, μ₂) = #Hom(V, ℤ/2) = #V`
  have hcards : Nat.card (MuDual 2 V) = Nat.card V := by
    have h1 : Nat.card (MuDual 2 V) = Nat.card (V →+ ZMod 2) := by
      refine Nat.card_congr ⟨fun f => ε.symm.toAddMonoidHom.comp (f : V →+ MuN 2),
        fun f => (ε.toAddMonoidHom.comp f : MuDual 2 V), fun f => ?_, fun f => ?_⟩
      · refine DFunLike.ext _ _ fun m => ?_
        show ε (ε.symm ((f : V →+ MuN 2) m)) = f m
        rw [ε.apply_symm_apply]
      · ext m
        show ε.symm (ε (f m)) = f m
        rw [ε.symm_apply_apply]
    rw [h1, card_addHom_zmod2 V h2]
  -- bijectivity
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (MuDual 2 V) := Fintype.ofFinite _
  have hbij : Function.Bijective Ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcards]
  -- equivariance
  refine ⟨AddEquiv.ofBijective Ψ hbij, fun g v => ?_⟩
  show Ψ (g • v) = g • Ψ v
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, muTwo_smul_trivial, hΨapply, hΨapply]
  congr 1
  have hps := polar_smul_smul V q hqG g (g⁻¹ • m) v
  rw [smul_inv_smul] at hps
  exact hps

omit [ContinuousSMul AbsGalQ2 V] [Finite V] in
/-- `H²` of an exponent-2 module has exponent 2 (pointwise, by quotient induction). -/
theorem h2_add_self (h2 : ∀ v : V, v + v = 0) (x : H2 AbsGalQ2 V) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext p
      exact h2 _
    show H2mk AbsGalQ2 V z + H2mk AbsGalQ2 V z = 0
    rw [← map_add, hz, map_zero]

/-- **`#H² = 1` from `#H⁰ = 1`** (Tate duality B6 via the parameter `D`, `(0,2)` clause at
`M := V`, through the polar self-duality and exp-2 Pontryagin duality). -/
theorem card_H2_eq_one_of_card_H0_eq_one (D : TateDuality 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (hfin : Finite (H2 AbsGalQ2 V))
    (hH0 : Nat.card (H0 AbsGalQ2 V) = 1) :
    Nat.card (H2 AbsGalQ2 V) = 1 := by
  have htor : ∀ x : V, (2 : ℕ) • x = 0 := fun x => (two_nsmul x).trans (h2 x)
  obtain ⟨e, he⟩ := exists_polarSelfDual V q hq hns h2 hqG
  have hd : Nat.card (H0 AbsGalQ2 (MuDual 2 V)) = Nat.card (H0 AbsGalQ2 V) :=
    card_H0_congr e he
  have hdual := D.card_H0_dual V htor
  haveI := hfin
  have hhom := card_addHom_zmod2 (H2 AbsGalQ2 V) (h2_add_self V h2)
  calc Nat.card (H2 AbsGalQ2 V)
      = Nat.card (H2 AbsGalQ2 V →+ ZMod 2) := hhom.symm
    _ = Nat.card (H0 AbsGalQ2 (MuDual 2 V)) := hdual.symm
    _ = Nat.card (H0 AbsGalQ2 V) := hd
    _ = 1 := hH0

/-- A finite exponent-2 group has 2-power order. -/
theorem card_eq_two_pow_of_exp_two {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) : ∃ k : ℕ, Nat.card A = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (n := 2) fun x => (two_nsmul x).trans (h2 x)
  letI : Fintype A := Fintype.ofFinite A
  refine ⟨Module.finrank (ZMod 2) A, ?_⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := A), ZMod.card]

/-- **`#H¹ = #V` in the §6.3 setting** (steps 1–2 of `lemma_6_17_dim` / Prop 6.18 assembled):
simple `C`-module, surjective classifying map, an element moving a vector, a nonsingular
invariant form.  Ax: **B6** (via `D`), **B7** (`finite_H2` + the Euler collapse). -/
theorem card_H1_eq_card_of_simple (D : TateDuality 2) {C : Type*} [Group C]
    [DistribMulAction C V]
    (ρ : AbsGalQ2 →* C) (hρsurj : Function.Surjective ρ)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ v : V, h₀ • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (h2 : ∀ v : V, v + v = 0) :
    Nat.card (H1 AbsGalQ2 V) = Nat.card V := by
  have hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v := fun g v => by
    rw [hρ]; exact hinv _ v
  have hH0 : Nat.card (H0 AbsGalQ2 V) = 1 :=
    card_H0_eq_one_of_surjective ρ hρsurj hρ hsimple h₀ hmoves
  have hH2 : Nat.card (H2 AbsGalQ2 V) = 1 :=
    card_H2_eq_one_of_card_H0_eq_one V D q hq hns h2 hqG (finite_H2 V) hH0
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_exp_two h2
  exact card_H1_eq_card_of_H0_H2_trivial hH0 hH2 hk

end PolarDual
end GQ2.DeepPart
