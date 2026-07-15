/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.EulerCharacteristic
public import GQ2.GaussCount
public import GQ2.RepIndependence
public import GQ2.TateDuality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Gauss sum over a Lagrangian (the ramified Prop 6.18 combinatorial core)

The zero-count of a nonsingular `𝔽₂` quadratic form `q` on `#V = 2^{2m}` is `2^{2m−1} ± 2^{m−1}`
by its Arf invariant (`GQ2/GaussCount.lean`, `zeroCount_of_arf_{zero,one}`).  Lemma 6.17 supplies
`Q⁰_loc` with a **half-dimensional totally singular subspace** `X₊` (deep units, `#X₊² = #H¹`,
`Q⁰_loc|X₊ = 0`).  The keystone below turns that into `arf = 0` (positive Gauss sign): a totally
singular, self-perpendicular `X` forces `g(q) = #X > 0`.  This is pure `𝔽₂` combinatorics — no
cohomology — proved by the two-way evaluation of `∑_v ∑_{x∈X} (−1)^{q(v+x)}`.

This file is part of the `GQ2.DeepPart` split (the deep-part proof); see `GQ2/DeepPart.lean` for the overview.
-/

open scoped Classical

namespace GQ2.QuadraticFp2

private theorem zmod2_ne_zero_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
private theorem zmod2_eq_add_add : ∀ a b : ZMod 2, a = b + (a + b) := by decide

variable {V : Type*} [AddCommGroup V]

/-- **Gauss sum over a Lagrangian**: if `X ≤ V` is totally singular (`q|X = 0`) and
self-perpendicular (every `v` pairing trivially with all of `X` already lies in `X`), then the
Gauss sum is `g(q) = #X`.  The combinatorial heart of the ramified Prop 6.18: a half-dimensional
totally singular subspace forces the positive Gauss sign. -/
theorem gaussSum_eq_card_of_lagrangian [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (X : AddSubgroup V) (hsing : ∀ x ∈ X, q x = 0)
    (hperp : ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X) :
    gaussSum q = Nat.card ↥X := by
  classical
  haveI : Fintype ↥X := Fintype.ofFinite _
  -- X ⊆ X⊥ : totally singular ⟹ polar vanishes on X × X
  have hXperp : ∀ v : V, v ∈ X → ∀ x : ↥X, polar q v ↑x = 0 := by
    intro v hv x
    have hmem : v + ↑x ∈ X := X.add_mem hv x.2
    unfold polar
    rw [hsing _ hmem, hsing v hv, hsing ↑x x.2]; ring
  set S : ℤ := ∑ v : V, ∑ x : ↥X, sign (q (v + ↑x)) with hSdef
  -- (A) translate v ↦ v + x for each fixed x  ⟹  S = #X · g
  have hA : S = (Fintype.card ↥X : ℤ) * gaussSum q := by
    rw [hSdef, Finset.sum_comm]
    have hgx : ∀ x : ↥X, (∑ v : V, sign (q (v + ↑x))) = gaussSum q :=
      fun x => Equiv.sum_comp (Equiv.addRight (↑x : V)) (fun v => sign (q v))
    rw [Finset.sum_congr rfl (fun x _ => hgx x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- inner character sum: ∑_{x∈X} (−1)^{B(v,x)} = #X or 0 by (non)degeneracy at v
  have hinner : ∀ v : V, (∑ x : ↥X, sign (polar q v ↑x))
      = if (∀ x : ↥X, polar q v ↑x = 0) then (Fintype.card ↥X : ℤ) else 0 := by
    intro v
    split_ifs with hv
    · rw [Finset.sum_congr rfl (fun x _ => by rw [hv x, sign_zero]), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    · push Not at hv
      obtain ⟨x₀, hx₀⟩ := hv
      exact charSum_eq_zero
        (AddMonoidHom.mk' (fun x : ↥X => polar q v ↑x)
          (fun x x' => by push_cast; exact hq.polar_add_right v ↑x ↑x'))
        ⟨x₀, zmod2_ne_zero_one _ hx₀⟩
  -- (B) expand q(v+x) = q v + B(v,x) (using q x = 0), sign multiplicative
  have hB : S = (Fintype.card ↥X : ℤ) * (Fintype.card ↥X : ℤ) := by
    have hexp : S = ∑ v : V, sign (q v) * (∑ x : ↥X, sign (polar q v ↑x)) := by
      rw [hSdef]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have key : q (v + ↑x) = q v + polar q v ↑x := by
        have hpx : polar q v ↑x = q (v + ↑x) + q v := by
          unfold polar; rw [hsing ↑x x.2, add_zero]
        rw [hpx]; exact zmod2_eq_add_add _ _
      rw [key, sign_add, mul_comm]
    have hterm : ∀ v : V, sign (q v) * (if (∀ x : ↥X, polar q v ↑x = 0) then
        (Fintype.card ↥X : ℤ) else 0) = if v ∈ X then (Fintype.card ↥X : ℤ) else 0 := by
      intro v
      by_cases hvX : v ∈ X
      · rw [if_pos hvX, if_pos (hXperp v hvX), hsing v hvX, sign_zero, one_mul]
      · rw [if_neg hvX, if_neg (fun hP => hvX (hperp v hP)), mul_zero]
    have hsum : (∑ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0))
        = (Fintype.card ↥X : ℤ) * (Fintype.card ↥X : ℤ) := by
      have h1 : ∀ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0)
          = (Fintype.card ↥X : ℤ) * (if v ∈ X then (1 : ℤ) else 0) := by
        intro v; by_cases hv : v ∈ X <;> simp [hv]
      rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.mul_sum, Finset.sum_boole]
      congr 1
      exact_mod_cast (Fintype.card_subtype (fun v => v ∈ X)).symm
    rw [hexp]
    have hstep : (∑ v : V, sign (q v) * (∑ x : ↥X, sign (polar q v ↑x)))
        = ∑ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0) :=
      Finset.sum_congr rfl (fun v _ => by rw [hinner v]; exact hterm v)
    rw [hstep]; exact hsum
  -- cancel #X > 0
  have hcpos : 0 < Fintype.card ↥X := Fintype.card_pos_iff.mpr ⟨⟨0, X.zero_mem⟩⟩
  have hcne : (Fintype.card ↥X : ℤ) ≠ 0 := mod_cast hcpos.ne'
  rw [Nat.card_eq_fintype_card]
  exact mul_left_cancel₀ hcne (hA.symm.trans hB)

/-- **A Lagrangian forces Arf 0** (positive Gauss sign).  Given a totally singular,
self-perpendicular `X ≤ V` (a "Lagrangian" for the nonsingular `q`), `arf q = 0`.  This is the
combinatorial step behind the ramified case of Prop 6.18 (eq. (115)). -/
theorem arf_zero_of_lagrangian [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (X : AddSubgroup V) (hsing : ∀ x ∈ X, q x = 0)
    (hperp : ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X) :
    arf q = 0 := by
  rw [arf_eq_zero_iff_gaussSum_pos, gaussSum_eq_card_of_lagrangian q hq X hsing hperp]
  haveI : Nonempty ↥X := ⟨⟨0, X.zero_mem⟩⟩
  exact_mod_cast Nat.card_pos

/-- **Self-perpendicularity of a half-dimensional totally singular subspace** (`𝔽₂` duality).
For a nonsingular `q` on an exponent-2 group with `q|X = 0` and `#X² = #V`, the perp `X⊥` equals
`X`: anything pairing trivially with all of `X` already lies in `X`.  Proof: the descended polar
functional injects `X⊥ ↪ (V/X)^∨` (injective by nonsingularity), so `#X⊥ ≤ #(V/X) = #V/#X = #X`;
with `X ⊆ X⊥` (total singularity) this forces `X⊥ = X`.  (No character-extension needed.) -/
theorem selfperp_of_card_sq [Finite V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (X : AddSubgroup V)
    (hsing : ∀ x ∈ X, q x = 0) (hcard : Nat.card ↥X ^ 2 = Nat.card V) :
    ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype ↥X := Fintype.ofFinite _
  haveI : Fintype {v : V // ∀ x : ↥X, polar q v ↑x = 0} := Fintype.ofFinite _
  haveI : Finite (V ⧸ X →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  -- exponent 2 passes to the quotient
  have h2q : ∀ y : V ⧸ X, y + y = 0 := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add, h2]; rfl
  -- total singularity ⟹ X ⊆ X⊥
  have hXsub : ∀ x : ↥X, ∀ y : ↥X, polar q (↑x) ↑y = 0 := by
    intro x y
    unfold polar
    rw [hsing _ (X.add_mem x.2 y.2), hsing _ x.2, hsing _ y.2]; ring
  -- X⊥ injects into (V/X)^∨ via the descended polar functional
  have hle : Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} ≤ Nat.card (V ⧸ X →+ ZMod 2) := by
    refine Nat.card_le_card_of_injective (fun v : {v : V // ∀ x : ↥X, polar q v ↑x = 0} =>
      QuotientAddGroup.lift X (polarHom q hq v.1) (fun x hx => by
        rw [AddMonoidHom.mem_ker, polarHom_apply, polar_comm]; exact v.2 ⟨x, hx⟩)) ?_
    rintro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
    have hpe : ∀ u : V, polar q u v₁ = polar q u v₂ := by
      intro u
      have h := DFunLike.congr_fun heq (QuotientAddGroup.mk u)
      simpa [QuotientAddGroup.lift_mk, polarHom_apply] using h
    have hrad : ∀ u : V, polar q (v₁ + v₂) u = 0 := by
      intro u
      rw [polar_comm, hq.polar_add_right, hpe u]
      exact CharTwo.add_self_eq_zero _
    have hsum0 : v₁ + v₂ = 0 := by
      by_contra hne
      obtain ⟨w, hw⟩ := hns _ hne
      exact hw (hrad w)
    have : v₁ = v₂ := by
      have h := congrArg (· + v₂) hsum0
      rwa [add_assoc, h2, add_zero, zero_add] at h
    exact Subtype.ext this
  -- #(V/X) = #X from Lagrange + #X² = #V
  have hlag : Nat.card V = Nat.card (V ⧸ X) * Nat.card ↥X :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hquotX : Nat.card (V ⧸ X) = Nat.card ↥X := by
    have heq : Nat.card (V ⧸ X) * Nat.card ↥X = Nat.card ↥X * Nat.card ↥X := by
      rw [← hlag, ← hcard, sq]
    exact Nat.eq_of_mul_eq_mul_right hXpos heq
  -- so #X⊥ ≤ #X
  have hle' : Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} ≤ Nat.card ↥X := by
    rw [card_addHom_zmod2 (V ⧸ X) h2q, hquotX] at hle; exact hle
  -- inclusion X ↪ X⊥ is injective, so #X ≤ #X⊥
  have hincl_inj : Function.Injective (fun x : ↥X =>
      (⟨↑x, hXsub x⟩ : {v : V // ∀ x : ↥X, polar q v ↑x = 0})) := by
    intro a b hab
    exact Subtype.ext (by simpa using hab)
  have hge : Nat.card ↥X ≤ Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} :=
    Nat.card_le_card_of_injective _ hincl_inj
  -- equal cards ⟹ the inclusion is surjective
  have hbij : Function.Bijective (fun x : ↥X => (⟨↑x, hXsub x⟩ :
      {v : V // ∀ x : ↥X, polar q v ↑x = 0})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hincl_inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm hge hle'
  intro v hv
  obtain ⟨x, hx⟩ := hbij.surjective ⟨v, hv⟩
  have hxv : (↑x : V) = v := congrArg Subtype.val hx
  exact hxv ▸ x.2

/-- **A half-dimensional totally singular subspace forces Arf 0** (the ramified Prop 6.18 input).
Combines `selfperp_of_card_sq` (self-⊥ from `#X² = #V`) with `arf_zero_of_lagrangian`. -/
theorem arf_zero_of_card_sq [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (X : AddSubgroup V)
    (hsing : ∀ x ∈ X, q x = 0) (hcard : Nat.card ↥X ^ 2 = Nat.card V) :
    arf q = 0 :=
  arf_zero_of_lagrangian q hq X hsing (selfperp_of_card_sq q hq h2 hns X hsing hcard)


/-- The polar form, bundled biadditively (first slot outer). -/
def polarBihom (q : V → ZMod 2) (hq : IsQuadraticFp2 q) : V →+ V →+ ZMod 2 :=
  AddMonoidHom.mk'
    (fun v => AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w'))
    (fun v v' => by
      ext w
      exact hq.polar_add_left v v' w)

@[simp] theorem polarBihom_apply (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (v w : V) :
    polarBihom q hq v w = polar q v w := rfl

/-- **Restriction of `𝔽₂`-functionals to a subgroup is surjective** (pure counting: the
kernel of restriction is `Hom(A/X, 𝔽₂)`, so the image has the size of `Hom(X, 𝔽₂)`). -/
theorem addHom_restrict_surjective {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) (X : AddSubgroup A) :
    Function.Surjective (fun f : A →+ ZMod 2 => f.comp X.subtype) := by
  classical
  haveI : Finite (A →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (↥X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : ↥X → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (A ⧸ X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A ⧸ X → ZMod 2)) DFunLike.coe_injective
  set res : (A →+ ZMod 2) →+ (↥X →+ ZMod 2) :=
    AddMonoidHom.mk' (fun f => f.comp X.subtype) (fun f g => rfl) with hres
  -- the kernel of restriction is `Hom(A/X, 𝔽₂)`
  have hkerEquiv : ↥res.ker ≃ (A ⧸ X →+ ZMod 2) := by
    refine ⟨fun f => QuotientAddGroup.lift X f.1 (fun x hx => ?_),
      fun g => ⟨g.comp (QuotientAddGroup.mk' X), ?_⟩, fun f => ?_, fun g => ?_⟩
    · rw [AddMonoidHom.mem_ker]
      exact DFunLike.congr_fun f.2 (⟨x, hx⟩ : ↥X)
    · have hg : ∀ x ∈ X, g.comp (QuotientAddGroup.mk' X) x = 0 := by
        intro x hx
        show g (QuotientAddGroup.mk' X x) = 0
        rw [show QuotientAddGroup.mk' X x = 0 from (QuotientAddGroup.eq_zero_iff x).mpr hx,
          map_zero]
      rw [AddMonoidHom.mem_ker]
      ext y
      exact hg ↑y y.2
    · apply Subtype.ext
      ext a
      rfl
    · ext yq
      rfl
  -- exponent 2 passes to the quotient
  have h2Q : ∀ y : A ⧸ X, y + y = 0 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add, h2]; rfl
  have h2X : ∀ x : ↥X, x + x = 0 := fun x => Subtype.ext (h2 _)
  -- counting: `#im res = #Hom(X)`
  have hlag : Nat.card (A ⧸ X) * Nat.card ↥X = Nat.card A :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X).symm
  have hkercard : Nat.card ↥res.ker = Nat.card (A ⧸ X) := by
    rw [Nat.card_congr hkerEquiv, card_addHom_zmod2 (A ⧸ X) h2Q]
  have hrn : Nat.card ↥res.range * Nat.card ↥res.ker = Nat.card (A →+ ZMod 2) := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange res).toEquiv]
    exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup res.ker).symm
  have hrange : Nat.card ↥res.range = Nat.card (↥X →+ ZMod 2) := by
    have e1 : Nat.card ↥res.range * Nat.card (A ⧸ X) = Nat.card A := by
      rw [← hkercard, hrn]
      exact card_addHom_zmod2 A h2
    have e2 : Nat.card ↥X * Nat.card (A ⧸ X) = Nat.card A := (mul_comm _ _).trans hlag
    have hQpos : 0 < Nat.card (A ⧸ X) := Nat.card_pos
    rw [card_addHom_zmod2 ↥X h2X]
    exact Nat.eq_of_mul_eq_mul_right hQpos (e1.trans e2.symm)
  -- full range ⟹ surjective
  have htop : res.range = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [hrange]
  intro g
  exact (htop ▸ AddSubgroup.mem_top g : g ∈ res.range)

/-- **Perp membership from a Lagrangian count**: for a biadditive nondegenerate `𝔽₂`-pairing
and a subgroup `X` with `#X² = #A` on which the pairing vanishes, anything pairing trivially
with all of `X` lies in `X` (the perp has the size of `X` by counting, and contains it). -/
theorem mem_of_pairing_eq_zero {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) (P : A →+ A →+ ZMod 2)
    (hnd : ∀ z : A, z ≠ 0 → ∃ w : A, P z w ≠ 0)
    (X : AddSubgroup A) (hX : ∀ x ∈ X, ∀ x' ∈ X, P x x' = 0)
    (hcard : Nat.card ↥X * Nat.card ↥X = Nat.card A)
    {c : A} (hall : ∀ y ∈ X, P c y = 0) : c ∈ X := by
  classical
  haveI : Finite (A →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (↥X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : ↥X → ZMod 2)) DFunLike.coe_injective
  -- the pairing map `A → Hom(A, 𝔽₂)` is bijective (nondegenerate + counting)
  have hPinj : Function.Injective (fun z : A => (P z : A →+ ZMod 2)) := by
    intro z₁ z₂ hz
    have hz' : P z₁ = P z₂ := hz
    by_contra hne
    obtain ⟨w, hw⟩ := hnd _ (sub_ne_zero.mpr hne)
    apply hw
    rw [map_sub, hz', sub_self]
    rfl
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (A →+ ZMod 2) := Fintype.ofFinite _
  have hPbij : Function.Bijective (fun z : A => (P z : A →+ ZMod 2)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hPinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_addHom_zmod2 A h2]
  -- `Θ : A →+ Hom(X, 𝔽₂)`, surjective as a composition
  set Θ : A →+ (↥X →+ ZMod 2) :=
    AddMonoidHom.mk' (fun z => (P z).comp X.subtype) (fun a b => by rw [map_add]; rfl) with hΘ
  have hΘsurj : Function.Surjective Θ := by
    intro g
    obtain ⟨f, hf⟩ := addHom_restrict_surjective h2 X g
    obtain ⟨z, hz⟩ := hPbij.2 f
    have hz' : P z = f := hz
    exact ⟨z, by show (P z).comp X.subtype = g; rw [hz']; exact hf⟩
  -- `ker Θ = X` by counting
  have hXle : X ≤ Θ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    ext y
    exact hX x hx ↑y y.2
  have hkercard : Nat.card ↥Θ.ker = Nat.card ↥X := by
    have hrn : Nat.card ↥Θ.range * Nat.card ↥Θ.ker = Nat.card A := by
      rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Θ).toEquiv]
      exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Θ.ker).symm
    have hrangetop : Θ.range = ⊤ := AddMonoidHom.range_eq_top.mpr hΘsurj
    have h2X : ∀ x : ↥X, x + x = 0 := fun x => Subtype.ext (h2 _)
    have hrangecard : Nat.card ↥Θ.range = Nat.card ↥X := by
      have htopc : Nat.card ↥(⊤ : AddSubgroup (↥X →+ ZMod 2)) = Nat.card (↥X →+ ZMod 2) :=
        Nat.card_congr AddSubgroup.topEquiv.toEquiv
      rw [hrangetop, htopc, card_addHom_zmod2 ↥X h2X]
    rw [hrangecard] at hrn
    have hXpos : 0 < Nat.card ↥X := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hXpos ?_
    rw [hrn, ← hcard]
  have hkereq : (Θ.ker : Set A) = (X : Set A) := by
    symm
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hXle hx) ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq hkercard
  have hcmem : c ∈ Θ.ker := by
    rw [AddMonoidHom.mem_ker]
    ext y
    exact hall ↑y y.2
  exact (hkereq ▸ hcmem : c ∈ (X : Set A))

/-- The equivariant-lift correction kills `0`: `m_c(0) = 0` (from (59) at `v = w = 0`). -/
theorem _root_.GQ2.IsEquivariantFactorSet.m_zero {C : Type*} [Group C] [DistribMulAction C V]
    {q : V → ZMod 2} {dat : GQ2.FactorSet C V} (hdat : GQ2.IsEquivariantFactorSet q dat)
    (c : C) : dat.m c 0 = 0 := by
  have h := hdat.m_quad c 0 0
  rw [add_zero, smul_zero, hdat.f_zero_left, add_zero] at h
  linear_combination h - CharTwo.add_self_eq_zero (dat.m c 0)

end GQ2.QuadraticFp2
