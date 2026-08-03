/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Stokes

@[expose] public section

/-!
# Dyadic campaign, ticket WW3b: universal coefficients and the perfect pairing on `H¹`

WW3 (`GQ2/Dyadic/Word/Stokes.lean`) proves that the Stokes ladder
`η_A : C•(A) → Hom(C•(A^∨), 𝔽₂)[−2]` is a quasi-isomorphism for every finite elementary
`𝔽₂[C]`-module (`stokesDuality_of_simple`), in the quotient-free six-clause form
`StokesQuasiIso`.  Its report flagged one follow-up gap: nothing yet turns that statement into
the one the word certificate wants, namely that the traced Stokes pairing is a **perfect
pairing on `H¹`**.  This leaf closes the gap.  `Stokes.lean` is not touched.

## Contents

1. **Cohomology of a three-term complex** `K₀ --d₀--> K₁ --d₁--> K₂` (`StokesH1`, `StokesH2`;
   `H⁰` is just `ker d₀`), in the frozen chain's `addSubgroupOf`-quotient spelling
   (`GQ2.FoxH.H1w`).

2. **The universal-coefficient step**, `H^k(Hom(K•, 𝔽₂)) ≅ Hom(H^{2−k}(K•), 𝔽₂)` for
   `k = 0, 1, 2` (`stokesUC0/1/2` and their `_bijective` theorems).  Over `𝔽₂` there is no
   `Ext` term and no dimension count is used: degree `0` is formal, and degrees `1` and `2`
   are two applications each of the frozen **elementary-dual pack**
   (`GQ2/Devissage/ElemDualPack.lean`) — `dual_exact_pair` for injectivity ("a functional
   killing the cocycles factors through the differential") and `elemDual_extend` for
   surjectivity ("`ZMod 2` is injective on finite elementary 2-groups").  No new duality
   theory is imported.

3. **The extraction**: the six relative clauses of `StokesQuasiIso` become bijections of the
   cohomology objects in each degree (`stokesQuasiIso_card_H0/H1/H2`).  Composed with (2) this
   is exactly the promised conversion of WW3's quasi-isomorphism target into
   `Hom(H¹(A^∨), 𝔽₂)` (`wordH1_target_uc`).

4. **The `IsSelfDual`-style package on the word complex** (`GQ2.FoxH.IsSelfDual`'s shape, at
   the degree-generic marking):
   * two-sided nondegeneracy of the traced Stokes pairing — WW3 supplies the left half as
     `StokesDuality.pairing_vanish_left`; the right half is `StokesDuality.pairing_vanish_right`
     here, proved by separating a non-coboundary from `im d⁰` and feeding the separating
     functional to the `h1_surj` clause;
   * the descended pairing `stokesChi1 : H¹(A) →+ (H¹(A^∨))^∨`, injective and in fact
     **bijective** (`stokesChi1_bijective`), together with the separation statement
     `stokesChi1_separating` — the `∃ P`-clause of `IsSelfDual` in the degree-generic form;
   * the **card clauses** `#H¹(A) = #H¹(A^∨)` (`card_wordH1`), `#H⁰(A) = #H²(A^∨)`
     (`card_wordH0`) and `#H²(A) = #H⁰(A^∨)` (`card_wordH2`).

`StokesDualityCertificate` (SD1 §6 field shapes) is deliberately **not** declared here; the
theorems above are what it will cite.

## Design notes

* The generic layer is stated for an arbitrary three-term complex of abelian groups, so it
  serves every branch family at every degree, exactly as WW3's cone engine does.  Finiteness
  and `2`-torsion enter only as explicit hypotheses at the two places where the elementary-dual
  pack needs them.
* `pairing_vanish_right` does **not** need the universal-coefficient theorem: separation on
  `K₁ ⧸ im d⁰` (`stokesDual_separating`) is enough, and it is the cheaper route.  The UC
  theorem is what the *card* clauses need.
* Nothing here uses a dimension equality (packet Lem. 5.1's warning); the card clauses are
  consequences of bijections, never inputs to them.

## Axiom prints (recorded at commit time)

Every headline prints **exactly the standard three** (`propext`, `Classical.choice`,
`Quot.sound`) — verified via `#print axioms` for `stokesUC0_bijective`, `stokesUC1_bijective`,
`stokesUC2_bijective`, `stokesQuasiIso_card_H0`, `stokesQuasiIso_card_H1`,
`stokesQuasiIso_card_H2`, `stokesDual_separating`, `StokesDuality.pairing_vanish_right`,
`wordH1_target_uc`, `stokesChi1_injective`, `stokesChi1_separating`, `stokesChi1_bijective`,
`card_wordH0`, `card_wordH1`, `card_wordH2`.  No sorries, no new axioms, no `decide`.

Module-style: the single import is module-style.
-/

namespace GQ2.Dyadic

open GQ2.FoxH

/-! ## Cohomology of a three-term complex

`K₀ --d₀--> K₁ --d₁--> K₂`.  `H⁰ = ker d₀` needs no name; `H¹` and `H²` are the
`addSubgroupOf`-quotient and the cokernel, spelled as in the frozen `GQ2.FoxH.H1w`/`H2w` (the
quotients are total — the chain inclusion `im d₀ ≤ ker d₁` is needed only by lemmas). -/

section ThreeTerm

variable {K₀ K₁ K₂ : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]

/-- **`H¹` of a three-term complex**: `ker d₁ ⧸ im d₀`.  Reducible, so the quotient's
`AddCommGroup`/`Finite` instances and mathlib's quotient rewrites apply without a `show`. -/
abbrev StokesH1 (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) : Type _ :=
  ↥d₁.ker ⧸ d₀.range.addSubgroupOf d₁.ker

/-- The class of a `1`-cocycle in `H¹`. -/
def stokesH1Mk (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (x : ↥d₁.ker) : StokesH1 d₀ d₁ :=
  QuotientAddGroup.mk x

theorem stokesH1Mk_surjective (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) :
    Function.Surjective (stokesH1Mk d₀ d₁) :=
  QuotientAddGroup.mk_surjective

@[simp] theorem stokesH1Mk_eq_zero_iff (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (x : ↥d₁.ker) :
    stokesH1Mk d₀ d₁ x = 0 ↔ ∃ v, d₀ v = x.1 := by
  rw [stokesH1Mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact AddMonoidHom.mem_range

/-- `H¹` is elementary when `K₁` is. -/
theorem stokesH1_two_torsion (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (hK₁ : ∀ a : K₁, a + a = 0)
    (h : StokesH1 d₀ d₁) : h + h = 0 := by
  obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ h
  show stokesH1Mk d₀ d₁ (x + x) = 0
  rw [show x + x = 0 from Subtype.ext (hK₁ x.1)]
  exact QuotientAddGroup.mk_zero _

/-- **`H²` of a three-term complex**: the cokernel `K₂ ⧸ im d₁` (reducible, as for `H¹`). -/
abbrev StokesH2 (d₁ : K₁ →+ K₂) : Type _ := K₂ ⧸ d₁.range

/-- `H²` is elementary when `K₂` is. -/
theorem stokesH2_two_torsion (d₁ : K₁ →+ K₂) (hK₂ : ∀ a : K₂, a + a = 0) (h : StokesH2 d₁) :
    h + h = 0 := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective h
  show (QuotientAddGroup.mk (b + b) : StokesH2 d₁) = 0
  rw [hK₂ b]
  exact QuotientAddGroup.mk_zero _

end ThreeTerm

/-! ## The universal-coefficient step

For a three-term complex of finite elementary `𝔽₂`-modules, `Hom(−, 𝔽₂)` is exact, so

  `H^k(Hom(K•, 𝔽₂)) ≅ Hom(H^{2−k}(K•), 𝔽₂)`,  `k = 0, 1, 2`

with no `Ext`-term and no dimension count.  The dual complex is
`K₂^∨ --d₁^∨--> K₁^∨ --d₀^∨--> K₀^∨`, so the three statements read

* `k = 0`: `ker d₁^∨ ≅ (K₂ ⧸ im d₁)^∨`  — formal (functionals on a cokernel);
* `k = 1`: `StokesH1 d₁^∨ d₀^∨ ≅ (StokesH1 d₀ d₁)^∨`;
* `k = 2`: `StokesH2 d₀^∨ ≅ (ker d₀)^∨`.

Degrees `1` and `2` each use `dual_exact_pair` (injectivity) and `elemDual_extend`
(surjectivity) from the frozen elementary-dual pack. -/

section UniversalCoefficients

variable {K₀ K₁ K₂ : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]

/-- **Universal coefficients, degree `0`**: a `0`-cocycle of the dual complex — a functional on
`K₂` killing `im d₁` — descends to `H²(K•) = K₂ ⧸ im d₁`. -/
noncomputable def stokesUC0 (d₁ : K₁ →+ K₂) :
    ↥(dualMap d₁).ker →+ ElemDual (StokesH2 d₁) :=
  AddMonoidHom.mk'
    (fun mu => (QuotientAddGroup.lift d₁.range ((mu : ElemDual K₂) : K₂ →+ ZMod 2) (by
        intro b hb
        obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hb
        show (mu : ElemDual K₂) b = 0
        rw [← hx]
        exact DFunLike.congr_fun (AddMonoidHom.mem_ker.mp mu.2) x) : ElemDual (StokesH2 d₁)))
    (fun mu nu => by
      apply ElemDual.ext
      intro h
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective h
      rfl)

/-- `H⁰(Hom(K•, 𝔽₂)) ≅ Hom(H²(K•), 𝔽₂)`.  Purely formal: no finiteness, no `2`-torsion. -/
theorem stokesUC0_bijective (d₁ : K₁ →+ K₂) : Function.Bijective (stokesUC0 d₁) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro mu hmu
    refine Subtype.ext (ElemDual.ext fun b => ?_)
    exact DFunLike.congr_fun hmu (QuotientAddGroup.mk b)
  · intro L
    refine ⟨⟨(((L : StokesH2 d₁ →+ ZMod 2).comp
        (QuotientAddGroup.mk' d₁.range) : K₂ →+ ZMod 2) : ElemDual K₂), ?_⟩, ?_⟩
    · refine AddMonoidHom.mem_ker.mpr (ElemDual.ext fun x => ?_)
      show L (QuotientAddGroup.mk (d₁ x)) = 0
      rw [show (QuotientAddGroup.mk (d₁ x) : StokesH2 d₁) = 0 from
        (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩), map_zero]
    · refine ElemDual.ext fun h => ?_
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective h
      rfl

/-- The functional on `H¹(K•)` induced by a `1`-cocycle `λ` of the dual complex: restrict `λ`
to `ker d₁` (it kills `im d₀` because `λ ∘ d₀ = 0`). -/
noncomputable def stokesUC1Aux (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (lam : ↥(dualMap d₀).ker) :
    ElemDual (StokesH1 d₀ d₁) :=
  QuotientAddGroup.lift _
    ((((lam : ElemDual K₁) : K₁ →+ ZMod 2).comp d₁.ker.subtype : ↥d₁.ker →+ ZMod 2)) (by
      intro z hz
      rw [AddSubgroup.mem_addSubgroupOf] at hz
      obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp hz
      show (lam : ElemDual K₁) z.1 = 0
      rw [← hv]
      exact DFunLike.congr_fun (AddMonoidHom.mem_ker.mp lam.2) v)

/-- **Universal coefficients, degree `1`**: `H¹(Hom(K•, 𝔽₂)) → Hom(H¹(K•), 𝔽₂)`, restriction of
a dual `1`-cocycle to the `1`-cocycles. -/
noncomputable def stokesUC1 (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) :
    StokesH1 (dualMap d₁) (dualMap d₀) →+ ElemDual (StokesH1 d₀ d₁) :=
  QuotientAddGroup.lift _
    (AddMonoidHom.mk' (stokesUC1Aux d₀ d₁) (fun lam mu => by
      refine ElemDual.ext fun h => ?_
      obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ h
      rfl)) (by
      intro lam hlam
      rw [AddSubgroup.mem_addSubgroupOf] at hlam
      obtain ⟨mu, hmu⟩ := AddMonoidHom.mem_range.mp hlam
      refine ElemDual.ext fun h => ?_
      obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ h
      show (lam : ElemDual K₁) x.1 = 0
      rw [← hmu]
      show mu (d₁ x.1) = 0
      rw [AddMonoidHom.mem_ker.mp x.2, map_zero])

/-- **`H¹(Hom(K•, 𝔽₂)) ≅ Hom(H¹(K•), 𝔽₂)`** — the finite-elementary universal-coefficient step
in the middle degree, the clause WW3's report flagged as missing.  Injectivity is
`dual_exact_pair` (a functional vanishing on `ker d₁` factors through `d₁`); surjectivity is
`elemDual_extend` (extend a functional off `ker d₁`, and the extension automatically kills
`im d₀` because `d₀` lands in `ker d₁`). -/
theorem stokesUC1_bijective [Finite K₁] [Finite K₂] (hK₁ : ∀ a : K₁, a + a = 0)
    (hK₂ : ∀ a : K₂, a + a = 0) (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (hd : ∀ v, d₁ (d₀ v) = 0) :
    Function.Bijective (stokesUC1 d₀ d₁) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro L hL
    obtain ⟨lam, rfl⟩ := QuotientAddGroup.mk_surjective L
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine (dual_exact_pair hK₂ d₁.ker.subtype d₁ (AddSubgroup.range_subtype _)
      (lam : ElemDual K₁)).mp (ElemDual.ext fun x => ?_)
    exact DFunLike.congr_fun hL (stokesH1Mk d₀ d₁ x)
  · intro L
    obtain ⟨lam, hlam⟩ := elemDual_extend hK₁ d₁.ker.subtype (AddSubgroup.subtype_injective _)
      (((L : StokesH1 d₀ d₁ →+ ZMod 2).comp
        (QuotientAddGroup.mk' _) : ↥d₁.ker →+ ZMod 2) : ElemDual ↥d₁.ker)
    have hlam0 : dualMap d₀ lam = 0 := ElemDual.ext fun v => by
      refine (hlam ⟨d₀ v, AddMonoidHom.mem_ker.mpr (hd v)⟩).trans ?_
      show L (stokesH1Mk d₀ d₁ ⟨d₀ v, AddMonoidHom.mem_ker.mpr (hd v)⟩) = 0
      rw [show stokesH1Mk d₀ d₁ ⟨d₀ v, AddMonoidHom.mem_ker.mpr (hd v)⟩ = 0 from
        (stokesH1Mk_eq_zero_iff _ _ _).mpr ⟨v, rfl⟩, map_zero]
    refine ⟨QuotientAddGroup.mk ⟨lam, AddMonoidHom.mem_ker.mpr hlam0⟩, ElemDual.ext fun h => ?_⟩
    obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ h
    exact hlam x

/-- **Universal coefficients, degree `2`**: `H²(Hom(K•, 𝔽₂)) → Hom(H⁰(K•), 𝔽₂)`, restriction of
a functional on `K₀` to `ker d₀` (well defined: `μ ∘ d₀` kills `ker d₀`). -/
noncomputable def stokesUC2 (d₀ : K₀ →+ K₁) :
    StokesH2 (dualMap d₀) →+ ElemDual ↥d₀.ker :=
  QuotientAddGroup.lift _ (dualMap d₀.ker.subtype) (by
    intro lam hlam
    obtain ⟨mu, hmu⟩ := AddMonoidHom.mem_range.mp hlam
    refine ElemDual.ext fun x => ?_
    show lam x.1 = 0
    rw [← hmu]
    show mu (d₀ x.1) = 0
    rw [AddMonoidHom.mem_ker.mp x.2, map_zero])

/-- `H²(Hom(K•, 𝔽₂)) ≅ Hom(H⁰(K•), 𝔽₂)` — same two pack lemmas, one degree up. -/
theorem stokesUC2_bijective [Finite K₀] [Finite K₁] (hK₀ : ∀ a : K₀, a + a = 0)
    (hK₁ : ∀ a : K₁, a + a = 0) (d₀ : K₀ →+ K₁) : Function.Bijective (stokesUC2 d₀) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro L hL
    obtain ⟨lam, rfl⟩ := QuotientAddGroup.mk_surjective L
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    refine (dual_exact_pair hK₁ d₀.ker.subtype d₀ (AddSubgroup.range_subtype _) lam).mp ?_
    exact hL
  · intro L
    obtain ⟨lam, hlam⟩ := elemDual_extend hK₀ d₀.ker.subtype (AddSubgroup.subtype_injective _) L
    exact ⟨QuotientAddGroup.mk lam, ElemDual.ext hlam⟩

end UniversalCoefficients

/-! ## From the six relative clauses to cohomology bijections

`StokesQuasiIso` is phrased on representatives (WW3's design choice: consumers get witnesses,
not quotient elements).  Here the six clauses are read back as bijectivity of `H⁰(φ)`, `H¹(φ)`,
`H²(φ)`, which is what a cardinality statement needs.  Only the two ladder squares are used;
no exactness of the complexes is required. -/

section QuasiIsoCohomology

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
  {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
  {φ₀ : X₀ →+ Y₀} {φ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}

/-- `H⁰(φ)`: the restriction of `φ₀` to the `0`-cocycles. -/
def stokesH0Map (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) : ↥dX₀.ker →+ ↥dY₀.ker :=
  (φ₀.comp dX₀.ker.subtype).codRestrict dY₀.ker fun x => by
    refine AddMonoidHom.mem_ker.mpr ?_
    show dY₀ (φ₀ x.1) = 0
    rw [hφ₀, AddMonoidHom.mem_ker.mp x.2, map_zero]

/-- `H¹(φ)`: the map induced on `ker d₁ ⧸ im d₀`. -/
def stokesH1Map (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    StokesH1 dX₀ dX₁ →+ StokesH1 dY₀ dY₁ :=
  QuotientAddGroup.map _ _
    ((φ₁.comp dX₁.ker.subtype).codRestrict dY₁.ker fun x => by
      refine AddMonoidHom.mem_ker.mpr ?_
      show dY₁ (φ₁ x.1) = 0
      rw [hφ₁, AddMonoidHom.mem_ker.mp x.2, map_zero])
    (by
      intro x hx
      rw [AddSubgroup.mem_addSubgroupOf] at hx
      obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp hx
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      refine AddMonoidHom.mem_range.mpr ⟨φ₀ v, ?_⟩
      show dY₀ (φ₀ v) = φ₁ x.1
      rw [hφ₀, hv])

/-- `H²(φ)`: the map induced on the cokernels. -/
def stokesH2Map (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) : StokesH2 dX₁ →+ StokesH2 dY₁ :=
  QuotientAddGroup.map _ _ φ₂ (by
    intro z hz
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hz
    refine AddSubgroup.mem_comap.mpr (AddMonoidHom.mem_range.mpr ⟨φ₁ x, ?_⟩)
    rw [hφ₁, hx])

/-- A ladder whose induced maps on `H⁰`, `H¹`, and `H²` are bijective satisfies the six
relative clauses of `StokesQuasiIso`.  This is the source-comparison handoff: a future
continuous-cohomology comparison may prove the three bijectivity hypotheses without unfolding
the representative-level Stokes clauses. -/
theorem stokesQuasiIso_of_bijective_cohomology_maps
    (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v))
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x))
    (h0 : Function.Bijective (stokesH0Map hφ₀))
    (h1 : Function.Bijective (stokesH1Map hφ₀ hφ₁))
    (h2 : Function.Bijective (stokesH2Map hφ₁)) :
    StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ := by
  constructor
  · intro x hx hφx
    let x' : ↥dX₀.ker := ⟨x, AddMonoidHom.mem_ker.mpr hx⟩
    have hz : stokesH0Map hφ₀ x' = 0 := Subtype.ext hφx
    have hx' : x' = 0 := by
      apply h0.1
      simpa using hz
    exact congrArg Subtype.val hx'
  · intro y hy
    obtain ⟨x, hx⟩ := h0.2 ⟨y, AddMonoidHom.mem_ker.mpr hy⟩
    exact ⟨x.1, AddMonoidHom.mem_ker.mp x.2, congrArg Subtype.val hx⟩
  · intro x hx hbound
    let x' : ↥dX₁.ker := ⟨x, AddMonoidHom.mem_ker.mpr hx⟩
    have hz : stokesH1Map hφ₀ hφ₁ (stokesH1Mk dX₀ dX₁ x') = 0 := by
      rw [stokesH1Mk, stokesH1Map, QuotientAddGroup.map_mk,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact AddMonoidHom.mem_range.mpr hbound
    have hz' : stokesH1Mk dX₀ dX₁ x' = 0 := by
      apply h1.1
      simpa using hz
    exact (stokesH1Mk_eq_zero_iff dX₀ dX₁ x').mp hz'
  · intro y hy
    let y' : ↥dY₁.ker := ⟨y, AddMonoidHom.mem_ker.mpr hy⟩
    obtain ⟨z, hz⟩ := h1.2 (stokesH1Mk dY₀ dY₁ y')
    obtain ⟨x, rfl⟩ := stokesH1Mk_surjective dX₀ dX₁ z
    rw [stokesH1Mk, stokesH1Map, QuotientAddGroup.map_mk] at hz
    unfold stokesH1Mk at hz
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨y₀, hy₀⟩ := AddMonoidHom.mem_range.mp hz
    change dY₀ y₀ = φ₁ x.1 - y at hy₀
    exact ⟨x.1, -y₀, AddMonoidHom.mem_ker.mp x.2, by rw [map_neg, hy₀]; abel⟩
  · intro x hbound
    have hz : stokesH2Map hφ₁ (QuotientAddGroup.mk x : StokesH2 dX₁) = 0 := by
      rw [stokesH2Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff]
      exact AddMonoidHom.mem_range.mpr hbound
    have hz' : (QuotientAddGroup.mk x : StokesH2 dX₁) = 0 := by
      apply h2.1
      simpa using hz
    rw [QuotientAddGroup.eq_zero_iff] at hz'
    exact AddMonoidHom.mem_range.mp hz'
  · intro y
    obtain ⟨z, hz⟩ := h2.2 (QuotientAddGroup.mk y : StokesH2 dY₁)
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [stokesH2Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_iff_sub_mem] at hz
    obtain ⟨y₁, hy₁⟩ := AddMonoidHom.mem_range.mp hz
    exact ⟨x, -y₁, by rw [map_neg, hy₁]; abel⟩

variable (h : StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂)

include h

/-- The six relative clauses give bijectivity of the induced `H⁰` map. -/
theorem StokesQuasiIso.bijective_stokesH0Map
    (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) :
    Function.Bijective (stokesH0Map hφ₀) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (h.h0_inj x.1 (AddMonoidHom.mem_ker.mp x.2)
      (congrArg Subtype.val hx))
  · intro y
    obtain ⟨v, hv0, hvy⟩ := h.h0_surj y.1 (AddMonoidHom.mem_ker.mp y.2)
    exact ⟨⟨v, AddMonoidHom.mem_ker.mpr hv0⟩, Subtype.ext hvy⟩

/-- The six relative clauses give bijectivity of the induced `H¹` map. -/
theorem StokesQuasiIso.bijective_stokesH1Map
    (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v))
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    Function.Bijective (stokesH1Map hφ₀ hφ₁) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [stokesH1Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨y₀, hy₀⟩ := AddMonoidHom.mem_range.mp hz
    obtain ⟨v, hv⟩ := h.h1_inj x.1 (AddMonoidHom.mem_ker.mp x.2) ⟨y₀, hy₀⟩
    exact AddMonoidHom.mem_range.mpr ⟨v, hv⟩
  · intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨x₁, y₀, hx₁, hsum⟩ := h.h1_surj y.1 (AddMonoidHom.mem_ker.mp y.2)
    refine ⟨QuotientAddGroup.mk ⟨x₁, AddMonoidHom.mem_ker.mpr hx₁⟩, ?_⟩
    rw [stokesH1Map, QuotientAddGroup.map_mk]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.mpr ⟨-y₀, ?_⟩
    show dY₀ (-y₀) = φ₁ x₁ - y.1
    rw [map_neg, ← hsum]
    abel

/-- The six relative clauses give bijectivity of the induced `H²` map. -/
theorem StokesQuasiIso.bijective_stokesH2Map
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    Function.Bijective (stokesH2Map hφ₁) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x₂, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [stokesH2Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hz
    obtain ⟨x₁, hx₁⟩ := h.h2_inj x₂ (AddMonoidHom.mem_range.mp hz)
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨x₁, hx₁⟩)
  · intro z
    obtain ⟨y₂, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨x₂, y₁, hsum⟩ := h.h2_surj y₂
    refine ⟨QuotientAddGroup.mk x₂, ?_⟩
    rw [stokesH2Map, QuotientAddGroup.map_mk]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr (AddMonoidHom.mem_range.mpr ⟨-y₁, ?_⟩)
    rw [map_neg, ← hsum]
    abel

/-- **The `H⁰` clause**: `#H⁰(X•) = #H⁰(Y•)`, from `h0_inj`/`h0_surj`. -/
theorem stokesQuasiIso_card_H0 (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) :
    Nat.card ↥dX₀.ker = Nat.card ↥dY₀.ker := by
  refine Nat.card_eq_of_bijective (stokesH0Map hφ₀) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (h.h0_inj x.1 (AddMonoidHom.mem_ker.mp x.2) (congrArg Subtype.val hx))
  · intro y
    obtain ⟨v, hv0, hvy⟩ := h.h0_surj y.1 (AddMonoidHom.mem_ker.mp y.2)
    exact ⟨⟨v, AddMonoidHom.mem_ker.mpr hv0⟩, Subtype.ext hvy⟩

/-- **The `H¹` clause**: `#H¹(X•) = #H¹(Y•)`, from `h1_inj`/`h1_surj`. -/
theorem stokesQuasiIso_card_H1 (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v))
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    Nat.card (StokesH1 dX₀ dX₁) = Nat.card (StokesH1 dY₀ dY₁) := by
  refine Nat.card_eq_of_bijective (stokesH1Map hφ₀ hφ₁) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [stokesH1Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨y₀, hy₀⟩ := AddMonoidHom.mem_range.mp hz
    obtain ⟨v, hv⟩ := h.h1_inj x.1 (AddMonoidHom.mem_ker.mp x.2) ⟨y₀, hy₀⟩
    exact AddMonoidHom.mem_range.mpr ⟨v, hv⟩
  · intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨x₁, y₀, hx₁, hsum⟩ := h.h1_surj y.1 (AddMonoidHom.mem_ker.mp y.2)
    refine ⟨QuotientAddGroup.mk ⟨x₁, AddMonoidHom.mem_ker.mpr hx₁⟩, ?_⟩
    rw [stokesH1Map, QuotientAddGroup.map_mk]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.mpr ⟨-y₀, ?_⟩
    show dY₀ (-y₀) = φ₁ x₁ - y.1
    rw [map_neg, ← hsum]
    abel

/-- **The `H²` clause**: `#H²(X•) = #H²(Y•)`, from `h2_inj`/`h2_surj`. -/
theorem stokesQuasiIso_card_H2 (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    Nat.card (StokesH2 dX₁) = Nat.card (StokesH2 dY₁) := by
  refine Nat.card_eq_of_bijective (stokesH2Map hφ₁) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x₂, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [stokesH2Map, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hz
    obtain ⟨x₁, hx₁⟩ := h.h2_inj x₂ (AddMonoidHom.mem_range.mp hz)
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨x₁, hx₁⟩)
  · intro z
    obtain ⟨y₂, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨x₂, y₁, hsum⟩ := h.h2_surj y₂
    refine ⟨QuotientAddGroup.mk x₂, ?_⟩
    rw [stokesH2Map, QuotientAddGroup.map_mk]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr (AddMonoidHom.mem_range.mpr ⟨-y₁, ?_⟩)
    rw [map_neg, ← hsum]
    abel

end QuasiIsoCohomology

/-! ## Separation off the coboundaries

The one input `pairing_vanish_right` needs beyond WW3's clauses: a `1`-cochain that is not a
coboundary is detected by a functional killing all coboundaries.  `𝔽₂`-separation on
`K₁ ⧸ im d₀` (`elemDual_separates`), nothing more — in particular no finiteness. -/

section Separation

variable {K₀ K₁ : Type*} [AddCommGroup K₀] [AddCommGroup K₁]

/-- **Separation off `im d⁰`**: if `y` is not a coboundary, some `𝔽₂`-functional kills every
coboundary but not `y`. -/
theorem stokesDual_separating (hK₁ : ∀ a : K₁, a + a = 0) (d₀ : K₀ →+ K₁) {y : K₁}
    (hy : ∀ v, d₀ v ≠ y) : ∃ lam : ElemDual K₁, dualMap d₀ lam = 0 ∧ lam y ≠ 0 := by
  have hQ₂ : ∀ q : K₁ ⧸ d₀.range, q + q = 0 := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    show (QuotientAddGroup.mk (b + b) : K₁ ⧸ d₀.range) = 0
    rw [hK₁ b]
    exact QuotientAddGroup.mk_zero _
  have hne : (QuotientAddGroup.mk y : K₁ ⧸ d₀.range) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp ((QuotientAddGroup.eq_zero_iff y).mp h0)
    exact hy v hv
  obtain ⟨mu, hmu⟩ := elemDual_separates hQ₂ hne
  refine ⟨((mu : (K₁ ⧸ d₀.range) →+ ZMod 2).comp
    (QuotientAddGroup.mk' d₀.range) : K₁ →+ ZMod 2), ElemDual.ext fun v => ?_, hmu⟩
  show mu (QuotientAddGroup.mk (d₀ v)) = 0
  rw [show (QuotientAddGroup.mk (d₀ v) : K₁ ⧸ d₀.range) = 0 from
    (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨v, rfl⟩), map_zero]

end Separation

/-! ## The word complex: the perfect pairing on `H¹`

Everything above, instantiated at WW3's word complex `A → (ι → A) → (ρ → A)` and its Stokes
ladder `η = (heisEta0, heisEta1, heisEta2)`.  The ladder squares are WW3's `stokes_square₀` and
`stokes_square₁`; the quasi-isomorphism itself is WW3's `StokesDuality` (proved for every
finite elementary module by `stokesDuality_of_simple`). -/

section WordDuality

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- `H¹` of the word complex over the coefficient module `M`. -/
noncomputable abbrev WordH1 (c : ι → C) (w : ρ → FreeGroup ι) (M : Type*) [AddCommGroup M]
    [DistribMulAction C M] : Type _ :=
  StokesH1 (heisD0 (A := M) c) (heisD1 c w)

/-- `H²` of the word complex over the coefficient module `M`. -/
noncomputable abbrev WordH2 (c : ι → C) (w : ρ → FreeGroup ι) (M : Type*) [AddCommGroup M]
    [DistribMulAction C M] : Type _ :=
  StokesH2 (heisD1 (A := M) c w)

/-- The source-facing form of Stokes duality: the three maps induced by the Stokes ladder on
word cohomology are bijective.  Unlike `StokesDuality`, this predicate does not mention any of
the six representative-level lifting clauses, so continuous-cohomology comparison theorems can
target it directly. -/
def StokesCohomologyBijections [DecidableEq ι] (c : ι → C) (w : ρ → FreeGroup ι)
    (A : Type*) [AddCommGroup A] [DistribMulAction C A]
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) : Prop :=
  Function.Bijective (stokesH0Map (stokes_square₀ (A := A) c w hr hend)) ∧
  Function.Bijective (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
    (stokes_square₁ (A := A) c w hr hend)) ∧
  Function.Bijective (stokesH2Map (stokes_square₁ (A := A) c w hr hend))

/-! ### Transport between source and word cohomology

The continuous-cohomology route does not prove the word maps directly.  It identifies their
sources and targets with continuous cohomology, where Tate cup products are perfect, and proves
that the resulting squares commute.  The following tiny interface records exactly one such
square.  In the intended use, the three source maps are the `(0,2)`, `(1,1)`, and `(2,0)` cup
maps; the left equivalences are the `H⁰`/`H¹` comparison maps and the still-missing general
`H²` comparison, while the right equivalences additionally use `stokesUC0/1/2` and the
comparisons for the dual module.  The same square also transports in reverse: once the word
map is proved bijective independently, `CohomologyComparisonSquare.source_bijective` proves
the corresponding continuous source map bijective. -/

/-- A word-cohomology map is conjugate, through two equivalences, to a source-cohomology map. -/
structure CohomologyComparisonSquare {X Y X' Y' : Type*} (wordMap : X → Y)
    (sourceMap : X' → Y') where
  left : X ≃ X'
  right : Y ≃ Y'
  commutes : ∀ x, right (wordMap x) = sourceMap (left x)

/-- Bijectivity transports across a cohomology comparison square. -/
theorem CohomologyComparisonSquare.bijective {X Y X' Y' : Type*} {wordMap : X → Y}
    {sourceMap : X' → Y'} (h : CohomologyComparisonSquare wordMap sourceMap)
    (hsource : Function.Bijective sourceMap) : Function.Bijective wordMap := by
  constructor
  · intro x y hxy
    apply h.left.injective
    apply hsource.1
    rw [← h.commutes, ← h.commutes, hxy]
  · intro y
    obtain ⟨x', hx'⟩ := hsource.2 (h.right y)
    refine ⟨h.left.symm x', h.right.injective ?_⟩
    rw [h.commutes, Equiv.apply_symm_apply, hx']

/-- Bijectivity also transports in the reverse direction across a cohomology comparison
square.  This is the direction needed when word-level Stokes duality is proved first and is
then used to establish perfectness of the corresponding continuous cup product. -/
theorem CohomologyComparisonSquare.source_bijective {X Y X' Y' : Type*} {wordMap : X → Y}
    {sourceMap : X' → Y'} (h : CohomologyComparisonSquare wordMap sourceMap)
    (hword : Function.Bijective wordMap) : Function.Bijective sourceMap := by
  constructor
  · intro x' y' hxy
    obtain ⟨x, rfl⟩ := h.left.surjective x'
    obtain ⟨y, rfl⟩ := h.left.surjective y'
    apply congrArg h.left
    apply hword.1
    apply h.right.injective
    rw [h.commutes, h.commutes, hxy]
  · intro y'
    obtain ⟨y, rfl⟩ := h.right.surjective y'
    obtain ⟨x, hx⟩ := hword.2 y
    refine ⟨h.left x, ?_⟩
    rw [← h.commutes, hx]

/-- The exact source-comparison reduction for Stokes cohomology.  It deliberately asks for
three commuting comparison squares separately: this prevents a proof from hiding the absent
general-coefficient `H²` comparison inside a monolithic `StokesDuality` hypothesis. -/
theorem stokesCohomologyBijections_of_source_comparison [DecidableEq ι]
    (c : ι → C) (w : ρ → FreeGroup ι) (A : Type*) [AddCommGroup A]
    [DistribMulAction C A] (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w)
    {S₀ T₀ S₁ T₁ S₂ T₂ : Type*}
    (source₀ : S₀ → T₀) (source₁ : S₁ → T₁) (source₂ : S₂ → T₂)
    (hsource₀ : Function.Bijective source₀)
    (hsource₁ : Function.Bijective source₁)
    (hsource₂ : Function.Bijective source₂)
    (hcompare₀ : CohomologyComparisonSquare
      (stokesH0Map (stokes_square₀ (A := A) c w hr hend)) source₀)
    (hcompare₁ : CohomologyComparisonSquare
      (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
        (stokes_square₁ (A := A) c w hr hend)) source₁)
    (hcompare₂ : CohomologyComparisonSquare
      (stokesH2Map (stokes_square₁ (A := A) c w hr hend)) source₂) :
    StokesCohomologyBijections c w A hr hend :=
  ⟨hcompare₀.bijective hsource₀, hcompare₁.bijective hsource₁,
    hcompare₂.bijective hsource₂⟩

/-- `StokesCohomologyBijections` is exactly the cohomological form of `StokesDuality`, once
relator death and the endpoint condition supply the two ladder squares. -/
theorem stokesDuality_iff_cohomologyBijections [DecidableEq ι]
    (c : ι → C) (w : ρ → FreeGroup ι) (A : Type*) [AddCommGroup A]
    [DistribMulAction C A] (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    StokesDuality c w A ↔ StokesCohomologyBijections c w A hr hend := by
  constructor
  · intro hd
    exact ⟨hd.bijective_stokesH0Map (stokes_square₀ c w hr hend),
      hd.bijective_stokesH1Map (stokes_square₀ c w hr hend) (stokes_square₁ c w hr hend),
      hd.bijective_stokesH2Map (stokes_square₁ c w hr hend)⟩
  · rintro ⟨h0, h1, h2⟩
    exact stokesQuasiIso_of_bijective_cohomology_maps
      (stokes_square₀ c w hr hend) (stokes_square₁ c w hr hend) h0 h1 h2

omit [Fintype ι] [Fintype ρ] in
/-- `(ι → A^∨)` and `(ρ → A^∨)` are elementary — the `2`-torsion side condition of the
universal-coefficient theorems, at the dual word complex. -/
theorem wordDual_two_torsion {κ : Type*} (v : κ → ElemDual A) : v + v = 0 :=
  funext fun k => ElemDual.add_self_eq_zero (v k)

/-- **WW3's quasi-isomorphism target, identified**: the middle cohomology of the target complex
`Hom(C•(A^∨), 𝔽₂)[−2]` *is* `Hom(H¹(A^∨), 𝔽₂)`.  This is the conversion the
`StokesDualityCertificate` clause needs; combined with `card_wordH1` it says the traced Stokes
pairing exhibits `H¹(A)` as the `𝔽₂`-dual of `H¹(A^∨)`. -/
theorem wordH1_target_uc [Finite A] (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) :
    Function.Bijective
      (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w)) :=
  stokesUC1_bijective wordDual_two_torsion wordDual_two_torsion _ _
    (heisD1_comp_heisD0 c w hr)

omit [Fintype ι] in
/-- **The right-side extraction** (the companion of WW3's `pairing_vanish_left`): under Stokes
duality, a dual `1`-cocycle whose traced pairing vanishes against **every** `1`-cocycle of the
primal complex is a dual coboundary.  Proof: were it not, `stokesDual_separating` produces a
functional `λ` on `(ι → A^∨)` killing `im d⁰` with `λ(y) ≠ 0`; the `h1_surj` clause writes
`λ = η¹(x) + (d¹)^∨(ξ)` with `x` a `1`-cocycle, and evaluating at `y` gives
`λ(y) = η¹(x)(y) + ξ(d¹y) = 0` — a contradiction. -/
theorem StokesDuality.pairing_vanish_right {c : ι → C} {w : ρ → FreeGroup ι} [Finite A]
    (hd : StokesDuality c w A) (y : ι → ElemDual A)
    (hy : heisD1 (A := ElemDual A) c w y = 0)
    (hvan : ∀ x : ι → A, heisD1 c w x = 0 → heisEta1 c w x y = 0) :
    ∃ lam, heisD0 (A := ElemDual A) c lam = y := by
  by_contra hno
  push Not at hno
  obtain ⟨lam, hlam0, hlamy⟩ :=
    stokesDual_separating wordDual_two_torsion (heisD0 (A := ElemDual A) c) hno
  obtain ⟨x, xi, hx, hsum⟩ := hd.h1_surj lam hlam0
  refine hlamy ?_
  rw [← hsum]
  show heisEta1 c w x y + xi (heisD1 (A := ElemDual A) c w y) = 0
  rw [hvan x hx, hy, map_zero, add_zero]

variable [DecidableEq ι]

/-- The inner functional of the descended pairing: a `1`-cocycle `x` pairs against
`H¹(A^∨)`-classes via `η¹` (dual coboundary offsets die by the second ladder square, since
`d¹x = 0`). -/
noncomputable def stokesChi1Aux (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (x : ↥(heisD1 (A := A) c w).ker) : ElemDual (WordH1 c w (ElemDual A)) :=
  QuotientAddGroup.lift _
    ((((heisEta1 c w x.1 : ElemDual (ι → ElemDual A)) : (ι → ElemDual A) →+ ZMod 2).comp
      (heisD1 (A := ElemDual A) c w).ker.subtype : ↥(heisD1 (A := ElemDual A) c w).ker →+
        ZMod 2)) (by
      intro y hy
      rw [AddSubgroup.mem_addSubgroupOf] at hy
      obtain ⟨lam, hlam⟩ := AddMonoidHom.mem_range.mp hy
      show heisEta1 c w x.1 y.1 = 0
      rw [← hlam, ← heisEta2_comp_d1 c w hr hend x.1 lam, AddMonoidHom.mem_ker.mp x.2]
      simp)

/-- **The descended traced Stokes pairing** `χ¹ : H¹(A) →+ (H¹(A^∨))^∨` — the degree-generic
form of the frozen `GQ2.FoxH.chi1`.  Both coboundary directions die by the two ladder squares
(`heisEta1_comp_d0`, `heisEta2_comp_d1`) under the endpoint condition. -/
noncomputable def stokesChi1 (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    WordH1 c w A →+ ElemDual (WordH1 c w (ElemDual A)) :=
  QuotientAddGroup.lift _
    (AddMonoidHom.mk' (stokesChi1Aux (A := A) c w hr hend) (fun x x' => by
      refine ElemDual.ext fun h => ?_
      obtain ⟨y, rfl⟩ := stokesH1Mk_surjective _ _ h
      show heisEta1 c w (x.1 + x'.1) y.1 = heisEta1 c w x.1 y.1 + heisEta1 c w x'.1 y.1
      rw [map_add]
      rfl)) (by
      intro x hx
      rw [AddSubgroup.mem_addSubgroupOf] at hx
      obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
      refine ElemDual.ext fun h => ?_
      obtain ⟨y, rfl⟩ := stokesH1Mk_surjective _ _ h
      show heisEta1 c w x.1 y.1 = 0
      rw [← ha, heisEta1_comp_d0 c w hr hend a y.1, AddMonoidHom.mem_ker.mp y.2]
      simp)

@[simp] theorem stokesChi1_apply (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (x : ↥(heisD1 (A := A) c w).ker) (y : ↥(heisD1 (A := ElemDual A) c w).ker) :
    stokesChi1 c w hr hend (stokesH1Mk _ _ x) (stokesH1Mk _ _ y) = heisEta1 c w x.1 y.1 :=
  rfl

/-- **Nondegeneracy, left half**: `χ¹` is injective — WW3's `pairing_vanish_left`, descended. -/
theorem stokesChi1_injective [Finite A] {c : ι → C} {w : ρ → FreeGroup ι}
    (hd : StokesDuality c w A) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    Function.Injective (stokesChi1 (A := A) c w hr hend) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨x, rfl⟩ := stokesH1Mk_surjective _ _ h
  refine (stokesH1Mk_eq_zero_iff _ _ _).mpr
    (hd.pairing_vanish_left x.1 (AddMonoidHom.mem_ker.mp x.2) fun y hy => ?_)
  exact DFunLike.congr_fun hh (stokesH1Mk _ _ (⟨y, AddMonoidHom.mem_ker.mpr hy⟩ :
    ↥(heisD1 (A := ElemDual A) c w).ker))

/-- **Nondegeneracy, right half**: the `χ¹`-functionals separate `H¹(A^∨)` — the descended form
of `pairing_vanish_right`.  Together with `stokesChi1_injective` this is the two-sided
nondegeneracy clause of `GQ2.FoxH.IsSelfDual`, at the degree-generic marking. -/
theorem stokesChi1_separating [Finite A] {c : ι → C} {w : ρ → FreeGroup ι}
    (hd : StokesDuality c w A) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) (h' : WordH1 c w (ElemDual A)) (hne : h' ≠ 0) :
    ∃ h : WordH1 c w A, stokesChi1 c w hr hend h h' ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨y, rfl⟩ := stokesH1Mk_surjective _ _ h'
  refine hne ((stokesH1Mk_eq_zero_iff _ _ _).mpr
    (hd.pairing_vanish_right y.1 (AddMonoidHom.mem_ker.mp y.2) fun x hx => ?_))
  exact hno (stokesH1Mk _ _ (⟨x, AddMonoidHom.mem_ker.mpr hx⟩ : ↥(heisD1 (A := A) c w).ker))

/-! ### The card clauses -/

/-- **Card clause, degree `1`**: `#H¹(A) = #H¹(A^∨)`.  The quasi-isomorphism identifies `H¹(A)`
with the target's `H¹`, universal coefficients identify that with `Hom(H¹(A^∨), 𝔽₂)`, and the
elementary-dual dimension count closes it. -/
theorem card_wordH1 [Finite A] {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card (WordH1 c w A) = Nat.card (WordH1 c w (ElemDual A)) := by
  rw [stokesQuasiIso_card_H1 hd (stokes_square₀ c w hr hend) (stokes_square₁ c w hr hend),
    Nat.card_eq_of_bijective _ (wordH1_target_uc (A := A) c w hr),
    card_elemDual (stokesH1_two_torsion _ _ wordDual_two_torsion)]

/-- **Card clause, degree `0`**: `#H⁰(A) = #H²(A^∨)` — the degree-generic form of the
`IsSelfDual` numeric clause `#H²w = #(A^∨)^C`, read on the other side. -/
theorem card_wordH0 [Finite A] {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card ↥(heisD0 (A := A) c).ker = Nat.card (WordH2 c w (ElemDual A)) := by
  rw [stokesQuasiIso_card_H0 hd (stokes_square₀ c w hr hend),
    Nat.card_eq_of_bijective _ (stokesUC0_bijective (heisD1 (A := ElemDual A) c w)),
    card_elemDual (stokesH2_two_torsion _ wordDual_two_torsion)]

/-- **Card clause, degree `2`**: `#H²(A) = #H⁰(A^∨)` — the degree-generic form of the
`IsSelfDual` numeric clause `#H²w = #(A^∨)^C` (the fixed points are `H⁰` at a generating
marking). -/
theorem card_wordH2 [Finite A] {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card (WordH2 c w A) = Nat.card ↥(heisD0 (A := ElemDual A) c).ker := by
  rw [stokesQuasiIso_card_H2 hd (stokes_square₁ c w hr hend),
    Nat.card_eq_of_bijective _ (stokesUC2_bijective ElemDual.add_self_eq_zero
      wordDual_two_torsion (heisD0 (A := ElemDual A) c))]
  exact card_elemDual (two_torsion_of_injective (heisD0 (A := ElemDual A) c).ker.subtype
    (AddSubgroup.subtype_injective _) ElemDual.add_self_eq_zero)

/-- **`χ¹` is bijective**: injectivity plus the degree-`1` card clause.  This is the strongest
form of the perfect-pairing statement — `H¹(A)` *is* `Hom(H¹(A^∨), 𝔽₂)` via the traced Stokes
pairing. -/
theorem stokesChi1_bijective [Finite A] {c : ι → C} {w : ρ → FreeGroup ι}
    (hd : StokesDuality c w A) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    Function.Bijective (stokesChi1 (A := A) c w hr hend) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨stokesChi1_injective hd hr hend, ?_⟩
  rw [card_elemDual (stokesH1_two_torsion _ _ wordDual_two_torsion)]
  exact card_wordH1 hd hr hend

end WordDuality

end GQ2.Dyadic
