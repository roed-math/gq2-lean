/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import GQ2.TauCeti.GaloisDictK
public import GQ2.TauCeti.B5
public import GQ2.Dyadic.MarkedRecipBundle
public import GQ2.TraceForm
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.LocalField.Unramified.Basic

@[expose] public section

/-!
# B5-K: marked local reciprocity at a finite `K/ℚ₂`, discharged from Tau Ceti

Ticket **B5-K** of the dyadic Tau Ceti discharge campaign
(`docs/dyadic/tauceti-discharge-tickets.md`, memo `docs/dyadic/tauceti-discharge-recon.md`, §B5-K
and questions Q1, Q2; prototypes `docs/dyadic/tauceti-t2-evidence/recipK/b5k.lean` and
`kiunram/ki.lean`).  This file provides

* `GQ2.TauCetiBridge.markedRecipAt_tauceti K : Dyadic.MarkedRecip localReciprocity_tauceti K`,
  for every finite `K : IntermediateField ℚ_[2] ℚ̄₂`, a term of the type of the census axiom
  `GQ2.markedRecipAt K` with B5's `localReciprocity_tauceti` in place of `localReciprocity`, built
  from Tau Ceti's local class field theory at `↥K`, with no `sorry` and at the standard three
  axioms;
* the exported equations `markedRecipAt_tauceti_recip` (`recip` is `recipK K`, Tau Ceti's Artin
  map of `↥K` transported along `abEquivK`) and `markedRecipAt_tauceti_nu_ur`, by `rfl`, which
  B10-K (`B10K.lean`) reads its hypotheses through;
* the pieces, among them the valuation lemma `nuUrK_recipK : ν_ur(rec_K x) = −v_K(x)`.

## Translation (memo §B5-K)

All Tau Ceti objects at `↥K` use A1's package (`valuativeRel K`, `localTopology K`,
`isNonarchimedeanLocalField K`, and `valuativeExtension K` where an extension is needed; see
`GaloisDictK.lean`).

* `recip := recipK K = abEquivK⁻¹ ∘ TauCeti.ClassFieldTheory.artinMap ↥K`; both are arithmetic.
  `continuous_recip` needs A1-K's `localTopology_eq`, applied with explicit instances.
* `nu_ur := nuUrK K`, B5's `nuUr` at `↥K`: the inverse of the `ℤ₂`-reduction of Tau Ceti's
  arithmetic `unramifiedCoordinate ↥K`.  The unit and uniformizer clauses are
  `nuUrK_recipK` plus A1-K's normalized-valuation lemmas.
* `norm_compat` is Tau Ceti's `artinMap_norm` at `(ℚ₂, ↥K)` with the embedding `sepEmb K`, read
  through A1's `absGalEquivFixing`; `normUnitsK K` agrees with Tau Ceti's `Algebra.normUnits ℚ_[2]`
  only propositionally (`normUnitsK_eq_normUnits`).
* `r`, `nu_ker_chi_le`, `nu_ker_chi_ge` (memo Q1): `ν_ur(ker χ_K)` is a nonzero closed subgroup of
  `ℤ₂`, hence `2^r ℤ₂` (`exists_two_pow_level`), nonzero because `rec_K(2) ∈ ker χ_K` has
  `ν_ur(rec_K 2) = −v_K(2) ≠ 0`.  No ramification fact about `ℚ₂(μ_{2^∞})` is used.
* `ki_unramified` (memo Q2): an element of Tau Ceti's inertia lies in `ker ν_ur`
  (`nuUrK_toAbK_of_mem_inertia`; only this inclusion holds, `ker ν_ur` also contains the
  prime-to-2 part of the unramified quotient), so under the clause's hypothesis it acts on `μ₄`
  trivially and fixes `E = K(δi)`; Tau Ceti's inertia criterion makes `E/↥K` unramified, and the
  bridge at `↥E` turns that into gq2's `HasEqualNormValueGroups K δi`.

## Instance notes

* `ValuativeExtension ℚ_[2] ↥K` is `haveI`'d from A1's `valuativeExtension K` for
  `artinMap_norm` (memo, finding 5).
* `CompactSpace (GalKab K)` is passed explicitly (`compactSpace_galKab_of_fixingSubgroup`) to
  `exists_two_pow_level`; instance search misses it.
* The package on `E = sqrtNegOneLayer K δi` is Tau Ceti's `finiteIntermediateField*` over `↥K`,
  with `FiniteDimensional ↥K ↥E` from `finiteDimensional_sqrtNegOneLayer`.
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel GQ2.Dyadic

section K

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-! ## The reciprocity map and its two topological clauses -/

/-- **The `recip` of B5-K**: Tau Ceti's Artin map of `↥K`,
`TauCeti.ClassFieldTheory.artinMap ↥K : (↥K)ˣ →* Field.absoluteGaloisGroupAbelianization ↥K`
(`TauCeti/NumberTheory/ClassFieldTheory/Local/ArtinMap.lean:114`), transported to gq2's
`G_K^{ab}` along `abEquivK K`.  Both maps are arithmetic (a uniformizer goes to arithmetic
Frobenius). -/
def recipK : Kˣ →* GalKab K :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  (abEquivK K).symm.toMulEquiv.toMonoidHom.comp (TauCeti.ClassFieldTheory.artinMap K)

theorem abEquivK_recipK (x : Kˣ) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    abEquivK K (recipK K x) = TauCeti.ClassFieldTheory.artinMap K x :=
  (abEquivK K).apply_symm_apply _

/-- **B5-K `denseRange_recip`**: Tau Ceti's `denseRange_artinMap` (`ArtinMap.lean:188`) through
the homeomorphism `abEquivK⁻¹`; no topology on `↥K` is involved. -/
theorem denseRange_recipK : DenseRange (recipK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact (abEquivK K).symm.surjective.denseRange.comp
    (TauCeti.ClassFieldTheory.denseRange_artinMap K) (abEquivK K).symm.continuous

/-- **B5-K `continuous_recip`**, for the subspace topology on `(↥K)ˣ` that gq2's statement uses:
Tau Ceti's `continuous_artinMap` (`ArtinMap.lean:248`) is for `localTopology K`, and the two
topologies agree by A1-K's `localTopology_eq`.  `Continuous.comp` is applied with the `Units`
topology of `localTopology K` written explicitly, since re-synthesized instance arguments would
not be definitionally equal (memo, finding 3). -/
theorem continuous_recipK : Continuous (recipK K) := by
  have hU : @Units.instTopologicalSpaceUnits K (localTopology K) _ =
      (inferInstance : TopologicalSpace Kˣ) := by
    rw [localTopology_eq]
  letI := valuativeRel K
  haveI := isNonarchimedeanLocalField K
  have h := @TauCeti.ClassFieldTheory.continuous_artinMap K _ (valuativeRel K) (localTopology K)
    (isNonarchimedeanLocalField K)
  have hid : @Continuous Kˣ Kˣ (inferInstance : TopologicalSpace Kˣ)
      (@Units.instTopologicalSpaceUnits K (localTopology K) _) id := by
    rw [hU]; exact continuous_id
  exact (abEquivK K).symm.continuous.comp
    (@Continuous.comp _ _ _ _ (@Units.instTopologicalSpaceUnits K (localTopology K) _) _ _ _ h hid)

/-! ## The unramified coordinate -/

/-- **The `nu_ur` of B5-K**: the inverse of the `ℤ₂`-reduction `TauCeti.zHat.lift (ofAdd 1)`
(`TauCeti/Topology/Algebra/Group/Profinite/ZHat/Basic.lean:140`) of Tau Ceti's arithmetic
unramified coordinate `TauCeti.unramifiedCoordinate ↥K`
(`TauCeti/NumberTheory/LocalField/Unramified/Coordinate.lean:77`), transported along `abEquivK`.
This is B5's `nuUr` at `↥K`; the inversion converts to gq2's geometric normalization. -/
def nuUrK : GalKab K →* Multiplicative ℤ_[2] :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  (invMonoidHom : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2]).comp
    ((TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))).toMonoidHom.comp
      ((TauCeti.unramifiedCoordinate K).toMonoidHom.comp (abEquivK K).toMulEquiv.toMonoidHom))

theorem nuUrK_apply (g : GalKab K) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    nuUrK K g = (TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))
      (TauCeti.unramifiedCoordinate K (abEquivK K g)))⁻¹ := rfl

/-- **B5-K `continuous_nu_ur`**: a composite of continuous homomorphisms. -/
theorem continuous_nuUrK : Continuous (nuUrK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact continuous_inv.comp ((TauCeti.zHat.lift _).continuous.comp
    ((TauCeti.unramifiedCoordinate K).continuous.comp (abEquivK K).continuous))

/-- **The valuation lemma behind the unit, uniformizer and level clauses**:
`ν_ur(rec_K x) = −v_K(x)`, from Tau Ceti's `ClassFieldTheory.unramifiedCoordinate_artinMap`
(`TauCeti/NumberTheory/ClassFieldTheory/Local/Unramified.lean:407`) and `zHat.lift_ofInt`
(`ZHat/Basic.lean:146`). -/
theorem nuUrK_recipK (x : Kˣ) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    nuUrK K (recipK K x) =
      Multiplicative.ofAdd (-((TauCeti.normalizedValuation K x).toAdd : ℤ_[2])) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [nuUrK_apply, abEquivK_recipK, TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap,
    TauCeti.zHat.lift_ofInt, ← ofAdd_zsmul, ← ofAdd_neg]
  simp

/-- **B5-K `nu_ur_recip_unit`**: `nuUrK_recipK` with A1-K's
`normalizedValuation_eq_one_of_norm_eq_one`. -/
theorem nuUrK_recipK_unit (u : Kˣ) (hu : ‖((u : K) : ℚ̄₂)‖ = 1) : nuUrK K (recipK K u) = 1 := by
  rw [nuUrK_recipK, normalizedValuation_eq_one_of_norm_eq_one K u hu]
  simp

/-- **B5-K `nu_ur_recip_uniformizer`**: `nuUrK_recipK` with A1-K's
`normalizedValuation_eq_ofAdd_one_of_norm` (gq2's spectral uniformizer has `v_K = 1`). -/
theorem nuUrK_recipK_uniformizer (π : Kˣ) (hπ : ‖((π : K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((π : K) : ℚ̄₂)‖) :
    nuUrK K (recipK K π) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  rw [nuUrK_recipK, normalizedValuation_eq_ofAdd_one_of_norm K π hπ hmax]
  simp

/-! ## Norm functoriality -/

/-- gq2's norm on units is Tau Ceti's `Algebra.normUnits ℚ_[2]`
(`TauCeti/RingTheory/Norm/Units.lean:49`), propositionally (`Algebra.coe_normUnits`, `:54`):
`normUnits` is not exposed, so this is not `rfl`. -/
theorem normUnitsK_eq_normUnits (x : Kˣ) :
    normUnitsK K x = TauCeti.Algebra.normUnits ℚ_[2] x :=
  Units.ext (by rw [normUnitsK_val, TauCeti.Algebra.coe_normUnits])

/-- **B5-K `norm_compat`**: `inclAbK (rec_K x) = rec_{ℚ₂}(N_{K/ℚ₂} x)`.  Tau Ceti's
`ClassFieldTheory.artinMap_norm` (`ArtinMap.lean:345`) at `(ℚ₂, ↥K)` with `iota = sepEmb K`,
under the package plus `valuativeExtension K`; a lift `τ` of `artinMap ↥K x` is read in `G_K` by
A1's `absGalEquivFixing` (`coe_galKEquiv_symm_absGalEquivFixing`), and the right side is B5's
`localReciprocity_tauceti.recip = artinMap ℚ_[2]` (`localReciprocity_tauceti_recip`). -/
theorem inclAbK_recipK (x : Kˣ) :
    inclAbK K (recipK K x) = localReciprocity_tauceti.recip (normUnitsK K x) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk'_surjective
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
    (TauCeti.ClassFieldTheory.artinMap K x)
  have hτ' : (τ : Field.absoluteGaloisGroupAbelianization K) =
      TauCeti.ClassFieldTheory.artinMap K x := hτ
  have hrec : recipK K x = toAbK K ((galKEquiv K).symm (absGalEquivFixing K τ)) := by
    rw [← abEquivK_symm_mk, hτ']
    rfl
  rw [hrec, inclAbK_toAbK, coe_galKEquiv_symm_absGalEquivFixing, localReciprocity_tauceti_recip,
    normUnitsK_eq_normUnits]
  exact TauCeti.ClassFieldTheory.artinMap_norm (K := ℚ_[2]) K (sepEmb K) x τ hτ'

/-! ## The marked level `r` (memo Q1)

In a compact group, if `χ` and `ν` are continuous and some `g₀ ∈ ker χ` has `ν g₀ ≠ 0`, then
`ν(ker χ)` is a nonzero closed subgroup of `ℤ₂`, hence an ideal, hence `2^r ℤ₂`.  At `↥K` the
witness is `g₀ = rec_K(2)`: `χ_K(rec_K 2) = χ(rec_{ℚ₂}(N 2)) = χ(rec_{ℚ₂}(2)^d) = 1` and
`ν(rec_K 2) = −v_K(2) ≠ 0`. -/

omit [FiniteDimensional ℚ_[2] K] in
/-- A closed additive subgroup of `ℤ_[2]` is closed under multiplication by `ℤ_[2]` (the integers
are dense, Mathlib's `PadicInt.denseRange_intCast`). -/
theorem padicInt_mul_mem_of_isClosed {A : AddSubgroup ℤ_[2]} (hA : IsClosed (A : Set ℤ_[2]))
    (c : ℤ_[2]) {a : ℤ_[2]} (ha : a ∈ A) : c * a ∈ A := by
  have hcl : (fun t : ℤ_[2] => t * a) ⁻¹' (A : Set ℤ_[2]) ⊇ Set.range (Int.cast : ℤ → ℤ_[2]) := by
    rintro _ ⟨n, rfl⟩
    simpa [zsmul_eq_mul] using A.zsmul_mem ha n
  have hclosed : IsClosed ((fun t : ℤ_[2] => t * a) ⁻¹' (A : Set ℤ_[2])) :=
    hA.preimage (continuous_id.mul continuous_const)
  have := (hclosed.closure_subset_iff.2 hcl) (PadicInt.denseRange_intCast c)
  exact this

omit [FiniteDimensional ℚ_[2] K] in
/-- **The level lemma** (generic).  In a compact commutative group `A` with continuous
`χ : A →* ℤ₂ˣ` and `ν : A →* Multiplicative ℤ₂`, if some `g₀ ∈ ker χ` has `ν g₀ ≠ 0` then
`ν(ker χ) = 2^r ℤ₂` for some `r`, stated as the two inclusions of the B5-K clauses
`nu_ker_chi_le`, `nu_ker_chi_ge`.  The image is compact, hence closed, hence an ideal
(`padicInt_mul_mem_of_isClosed`), nonzero, hence `2^r ℤ₂` (Mathlib's
`PadicInt.ideal_eq_span_pow_p`). -/
theorem exists_two_pow_level {A : Type*} [CommGroup A] [TopologicalSpace A] [CompactSpace A]
    (chi : A →* ℤ_[2]ˣ) (hchi : Continuous chi) (nu : A →* Multiplicative ℤ_[2])
    (hnu : Continuous nu) (g₀ : A) (hg₀ : chi g₀ = 1) (hne : (nu g₀).toAdd ≠ 0) :
    ∃ r : ℕ, (∀ g : A, chi g = 1 → ∃ y : ℤ_[2], (nu g).toAdd = 2 ^ r * y) ∧
      ∀ y : ℤ_[2], ∃ g : A, chi g = 1 ∧ (nu g).toAdd = 2 ^ r * y := by
  -- `S = ν(ker χ)` as an additive subgroup of `ℤ₂`
  let S : AddSubgroup ℤ_[2] :=
    (Subgroup.map nu chi.ker).toAddSubgroup'.map
      (AddMonoidHom.mk' (fun x : Additive (Multiplicative ℤ_[2]) => x.toMul.toAdd) (fun _ _ => rfl))
  have hmemS : ∀ z : ℤ_[2], z ∈ S ↔ ∃ g : A, chi g = 1 ∧ (nu g).toAdd = z := by
    intro z
    simp only [S]
    constructor
    · rintro ⟨x, ⟨g, hg, hgx⟩, rfl⟩
      exact ⟨g, hg, by rw [hgx]; rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨Additive.ofMul (nu g), ⟨g, hg, rfl⟩, rfl⟩
  have hSset : (S : Set ℤ_[2]) = (fun g => (nu g).toAdd) '' (chi.ker : Set A) := by
    ext z
    rw [SetLike.mem_coe, hmemS]
    simp [MonoidHom.mem_ker]
  have hSclosed : IsClosed (S : Set ℤ_[2]) := by
    rw [hSset]
    have hker : IsClosed (chi.ker : Set A) := by
      rw [MonoidHom.coe_ker]; exact isClosed_singleton.preimage hchi
    exact (hker.isCompact.image (continuous_toAdd.comp hnu)).isClosed
  -- `S` is an ideal
  let I : Ideal ℤ_[2] :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c _ ha => padicInt_mul_mem_of_isClosed hSclosed c ha }
  have hI : I ≠ ⊥ := by
    intro h
    have : (nu g₀).toAdd ∈ I := (hmemS _).2 ⟨g₀, hg₀, rfl⟩
    rw [h, Ideal.mem_bot] at this
    exact hne this
  obtain ⟨r, hr⟩ := PadicInt.ideal_eq_span_pow_p hI
  have hmemI : ∀ z : ℤ_[2], z ∈ I ↔ ∃ y : ℤ_[2], z = 2 ^ r * y := by
    intro z
    rw [hr, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, by push_cast; ring⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, by push_cast; ring⟩
  refine ⟨r, fun g hg => (hmemI _).1 ((hmemS _).2 ⟨g, hg, rfl⟩), fun y => ?_⟩
  obtain ⟨g, hg, hgy⟩ := (hmemS _).1 ((hmemI (2 ^ r * y)).2 ⟨y, rfl⟩)
  exact ⟨g, hg, hgy⟩

/-- `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}` (Mathlib's `Algebra.norm_algebraMap`). -/
theorem normUnitsK_two :
    normUnitsK K (Units.mk0 (2 : K) two_ne_zero) = uniformizer ^ Module.finrank ℚ_[2] K := by
  refine Units.ext ?_
  rw [normUnitsK_val, Units.val_pow_eq_pow_val, uniformizer_val, Units.val_mk0,
    show (2 : K) = algebraMap ℚ_[2] K 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap]

/-- `χ_K(rec_K 2) = 1`: by `norm_compat` (`inclAbK_recipK`) it is `χ(rec_{ℚ₂}(2))^d`, and B5's
`chiCyc_recip_uniformizer` gives `χ(rec_{ℚ₂}(2)) = 1`. -/
theorem chiCycKAb_recipK_two : chiCycKAb K (recipK K (Units.mk0 (2 : K) two_ne_zero)) = 1 := by
  rw [← chiCycAb_inclAbK, inclAbK_recipK, normUnitsK_two, map_pow, map_pow,
    localReciprocity_tauceti.chiCyc_recip_uniformizer, one_pow]

/-- `ν_ur(rec_K 2) = −v_K(2) ≠ 0` (`nuUrK_recipK` and A1-K's `normalizedValuation_two_ne_one`). -/
theorem nuUrK_recipK_two_ne_zero :
    (nuUrK K (recipK K (Units.mk0 (2 : K) two_ne_zero))).toAdd ≠ 0 := by
  rw [nuUrK_recipK, toAdd_ofAdd, neg_ne_zero, Int.cast_ne_zero]
  intro h
  exact normalizedValuation_two_ne_one K (toAdd_eq_zero.mp h)

/-- **B5-K `r`, `nu_ker_chi_le`, `nu_ker_chi_ge`**: `exists_two_pow_level` at `A = G_K^{ab}`,
`χ = chiCycKAb K`, `ν = nuUrK K`, witness `rec_K(2)`, with `CompactSpace (GalKab K)` passed
explicitly (A1-K's `compactSpace_galKab_of_fixingSubgroup`). -/
theorem exists_levelK : ∃ r : ℕ,
    (∀ g : GalKab K, chiCycKAb K g = 1 → ∃ y : ℤ_[2], (nuUrK K g).toAdd = 2 ^ r * y) ∧
      ∀ y : ℤ_[2], ∃ g : GalKab K, chiCycKAb K g = 1 ∧ (nuUrK K g).toAdd = 2 ^ r * y :=
  @exists_two_pow_level (GalKab K) _ _ (compactSpace_galKab_of_fixingSubgroup K) (chiCycKAb K)
    (continuous_quot_lift _ (continuous_chiCycK K)) (nuUrK K)
    (continuous_nuUrK K) _ (chiCycKAb_recipK_two K) (nuUrK_recipK_two_ne_zero K)

/-! ## The clause `ki_unramified` (memo Q2)

The chain: (1) an element `τ` of Tau Ceti's inertia subgroup of `G_{↥K}` gives `g ∈ G_K` with
`ν_ur(toAbK g) = 1` (only `inertia ⊆ ker ν_ur` is used, not equality); (2) the clause's hypothesis
gives `χ(g) ≡ 1 (mod 4)`, so `g` fixes `δi`; (3) so inertia fixes `E = K(δi)` inside `↥K`'s
separable closure (A1's `fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff`), hence `E/↥K` is
unramified (Tau Ceti's `map_inertiaSubgroup_le_fixingSubgroup_iff`); (4) unramified `E/↥K` and
the norm ↔ valuation bridge at `↥E` give equal norm value groups. -/

/-- The `ki_unramified` clause of `Dyadic.MarkedRecip` for the unramified coordinate `nuUrK K`,
as a `Prop` (its statement verbatim, with `nu_ur := nuUrK K`). -/
def KiUnramifiedClause : Prop :=
  (∀ g : GalKab K, nuUrK K g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
    ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi

/-- Step (1): inertia lies in the kernel of `ν_ur`.  Tau Ceti's
`unramifiedCoordinate_mk_eq_one_iff` (`Unramified/Coordinate.lean:148`): the unramified
coordinate of `σ` is `1` iff `σ ∈ TauCeti.inertiaSubgroup ↥K`
(`Unramified/Inertia/Basic.lean:110`). -/
theorem nuUrK_toAbK_of_mem_inertia (τ : Field.absoluteGaloisGroup K)
    (hτ : letI := valuativeRel K; letI := localTopology K; haveI := isNonarchimedeanLocalField K
      τ ∈ TauCeti.inertiaSubgroup K) :
    nuUrK K (toAbK K ((galKEquiv K).symm (absGalEquivFixing K τ))) = 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  have h1 : abEquivK K (toAbK K ((galKEquiv K).symm (absGalEquivFixing K τ))) =
      (τ : Field.absoluteGaloisGroupAbelianization K) := by
    rw [← abEquivK_symm_mk, ContinuousMulEquiv.apply_symm_apply]
  rw [nuUrK_apply, h1, (TauCeti.unramifiedCoordinate_mk_eq_one_iff τ).2 hτ, map_one, inv_one]

omit [FiniteDimensional ℚ_[2] K] in
/-- Step (2): `χ ≡ 1 (mod 4)` fixes a square root of `−1`: Mathlib's `cyclotomicCharacter.spec`
at `δi^{2^2} = 1` (gq2's `chiCycKAb` is Mathlib's `cyclotomicCharacter ℚ̄₂ 2` on a lift, by
`rfl`). -/
theorem fixes_of_chiCyc_mod_four (g : GalK K) (hg : PadicInt.toZModPow 2
      ((chiCycKAb K (toAbK K g) : ℤ_[2]ˣ) : ℤ_[2]) = 1)
    (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    (show GQ2.Kummer.GaloisGroup ℚ_[2] from g.1) • δi = δi := by
  let gr : ℚ̄₂ ≃+* ℚ̄₂ := MulSemiringAction.toRingAut (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) ℚ̄₂
    (show GQ2.Kummer.GaloisGroup ℚ_[2] from g.1)
  have h4 : δi ^ (2 ^ 2) = 1 := by
    calc δi ^ (2 ^ 2) = (δi ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hδi]; norm_num
  have hspec := cyclotomicCharacter.spec 2 gr δi h4
  have hchi : (cyclotomicCharacter ℚ̄₂ 2) gr = chiCycKAb K (toAbK K g) := rfl
  rw [hchi, hg] at hspec
  change gr δi = δi
  rw [hspec]
  exact pow_one δi

omit [FiniteDimensional ℚ_[2] K] in
/-- `K(δi)/K` is finite for a square root `δi` of `−1` (gq2's `finiteDimensional_quadExt`). -/
theorem finiteDimensional_quadExt_sqrtNegOne (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    FiniteDimensional K (quadExt K δi) :=
  finiteDimensional_quadExt K (-1) (by rw [hδi]; simp)

/-- The field `E = K(δi)` inside `↥K`'s separable closure: the image of `quadExt K δi` under A1's
layer embedding `layerEmb K`. -/
abbrev sqrtNegOneLayer (δi : ℚ̄₂) : IntermediateField K (SeparableClosure K) :=
  (layerEmb K (quadExt K δi)).fieldRange

omit [FiniteDimensional ℚ_[2] K] in
theorem finiteDimensional_sqrtNegOneLayer (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    FiniteDimensional K (sqrtNegOneLayer K δi) :=
  haveI := finiteDimensional_quadExt_sqrtNegOne K δi hδi
  (AlgHom.equivFieldRange (layerEmb K (quadExt K δi))).toLinearEquiv.finiteDimensional

/-- Step (3): under the clause's hypothesis, inertia fixes `E`, so `E/↥K` is unramified.  Tau
Ceti's `map_inertiaSubgroup_le_fixingSubgroup_iff`
(`TauCeti/NumberTheory/LocalField/Unramified/Inertia/SeparableClosure.lean:99`) with
`galoisSubgroup_toSubgroup`
(`TauCeti/FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:146`), the package on `↥E`
being Tau Ceti's `finiteIntermediateField*` over `↥K`. -/
theorem isUnramified_sqrtNegOneLayer (hki : ∀ g : GalKab K, nuUrK K g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1)
    (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    haveI := finiteDimensional_sqrtNegOneLayer K δi hδi
    letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K)
      (sqrtNegOneLayer K δi)
    letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (sqrtNegOneLayer K δi)
    haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
      (sqrtNegOneLayer K δi)
    haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
      (sqrtNegOneLayer K δi)
    TauCeti.IsUnramified K (sqrtNegOneLayer K δi) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := finiteDimensional_sqrtNegOneLayer K δi hδi
  haveI := finiteDimensional_quadExt_sqrtNegOne K δi hδi
  letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (sqrtNegOneLayer K δi)
  haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  rw [← TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff]
  rintro _ ⟨τ, hτ, rfl⟩
  have hg := fixes_of_chiCyc_mod_four K ((galKEquiv K).symm (absGalEquivFixing K τ))
    (hki _ (nuUrK_toAbK_of_mem_inertia K τ hτ)) δi hδi
  have hmem := (fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff K δi
    (absGalEquivFixing K τ)).2 hg
  rw [fixingEquivAbsGal_apply, ContinuousMulEquiv.symm_apply_apply] at hmem
  rw [← TauCeti.galoisSubgroup_toSubgroup]
  exact hmem

/-- gq2's spectral norm on `E = sqrtNegOneLayer K δi`, through A1's
`sepClosureEquiv K : Kˢᵉᵖ ≃ₐ[↥K] ℚ̄₂`: the `w` of the bridge `vle_iff_of_isEquiv` at `(↥K, ↥E)`. -/
def normValuationLayer (δi : ℚ̄₂) : Valuation (sqrtNegOneLayer K δi) NNReal :=
  (NormedField.valuation : Valuation ℚ̄₂ NNReal).comap
    ((sepClosureEquiv K).toAlgHom.toRingHom.comp (sqrtNegOneLayer K δi).val.toRingHom)

omit [FiniteDimensional ℚ_[2] K] in
theorem normValuationLayer_apply (δi : ℚ̄₂) (x : sqrtNegOneLayer K δi) :
    normValuationLayer K δi x = ‖sepClosureEquiv K (x : SeparableClosure K)‖₊ := rfl

omit [FiniteDimensional ℚ_[2] K] in
theorem normValuationLayer_algebraMap (δi : ℚ̄₂) (a : K) :
    normValuationLayer K δi (algebraMap K (sqrtNegOneLayer K δi) a) = ‖(a : ℚ̄₂)‖₊ := by
  rw [normValuationLayer_apply]
  exact congrArg (fun t => ‖t‖₊) (sepClosureEquiv_algebraMap K a)

/-- The hypothesis of the bridge at `(↥K, ↥E)`: on `↥K ⊆ ↥E` the norm of `E` is the norm of `↥K`,
which orders `↥K` like Tau Ceti's valuation (A1-K's `valuation_le_iff_norm_le`). -/
theorem isEquiv_normValuationLayer (δi : ℚ̄₂) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    ((normValuationLayer K δi).comap (algebraMap K (sqrtNegOneLayer K δi))).IsEquiv
      (valuation K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  intro a b
  rw [Valuation.comap_apply, Valuation.comap_apply, normValuationLayer_algebraMap,
    normValuationLayer_algebraMap, valuation_le_iff_norm_le, ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

/-- Step (4): unramified `E/↥K` gives gq2's `HasEqualNormValueGroups K δi`.  Tau Ceti's
`isUnramified_iff_normalizedValuation_comp_unitsMap_surjective`
(`TauCeti/NumberTheory/LocalField/Unramified/Basic.lean:134`, direction `⇒` only) gives every
`z ∈ Eˣ` the normalized valuation of some `w ∈ (↥K)ˣ`; equal normalized valuations give equal
valuations (`toAdd_normalizedValuation_le_iff_valuation_le`), and the bridge at `↥E`
(`vle_iff_of_isEquiv` with `isEquiv_normValuationLayer`) gives equal spectral norms. -/
theorem hasEqualNormValueGroups_of_isUnramified (δi : ℚ̄₂) (hδi : δi ^ 2 = -1)
    (hU : letI := valuativeRel K
      letI := localTopology K
      haveI := isNonarchimedeanLocalField K
      haveI := finiteDimensional_sqrtNegOneLayer K δi hδi
      letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K)
        (sqrtNegOneLayer K δi)
      letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K)
        (sqrtNegOneLayer K δi)
      haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
        (sqrtNegOneLayer K δi)
      haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
        (sqrtNegOneLayer K δi)
      TauCeti.IsUnramified K (sqrtNegOneLayer K δi)) :
    HasEqualNormValueGroups K δi := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := finiteDimensional_sqrtNegOneLayer K δi hδi
  letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (sqrtNegOneLayer K δi)
  haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (sqrtNegOneLayer K δi)
  haveI : Algebra.IsAlgebraic K (sqrtNegOneLayer K δi) := Algebra.IsAlgebraic.of_finite K _
  intro z hz ⟨x, y, hxy⟩
  have hzmem : z ∈ quadExt K δi := by
    rw [hxy]
    exact add_mem (IntermediateField.algebraMap_mem _ x)
      (mul_mem (IntermediateField.algebraMap_mem _ y)
        (IntermediateField.mem_adjoin_simple_self K δi))
  let z₁ : quadExt K δi := ⟨z, hzmem⟩
  let z' : sqrtNegOneLayer K δi := ⟨layerEmb K (quadExt K δi) z₁, ⟨z₁, rfl⟩⟩
  have hz'norm : normValuationLayer K δi z' = ‖z‖₊ := by
    rw [normValuationLayer_apply]
    exact congrArg (fun t => ‖t‖₊) (sepClosureEquiv_layerEmb K (quadExt K δi) z₁)
  have hz' : z' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz'norm
    exact hz (nnnorm_eq_zero.mp hz'norm.symm)
  obtain ⟨w, hw⟩ := (TauCeti.isUnramified_iff_normalizedValuation_comp_unitsMap_surjective K
    (sqrtNegOneLayer K δi)).1 hU
    (TauCeti.normalizedValuation (sqrtNegOneLayer K δi) (Units.mk0 z' hz'))
  rw [MonoidHom.comp_apply] at hw
  -- equal normalized valuations give equal valuations
  have h1 := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le _ _).1
    (congrArg Multiplicative.toAdd hw).le
  have h2 := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le _ _).1
    (congrArg Multiplicative.toAdd hw).ge
  have hv : valuation (sqrtNegOneLayer K δi) (algebraMap K (sqrtNegOneLayer K δi) (w : K)) =
      valuation (sqrtNegOneLayer K δi) z' := le_antisymm h2 h1
  -- the bridge at `E`
  have hbr : ∀ a b : sqrtNegOneLayer K δi,
      valuation (sqrtNegOneLayer K δi) a ≤ valuation (sqrtNegOneLayer K δi) b ↔
        normValuationLayer K δi a ≤ normValuationLayer K δi b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := valuation (sqrtNegOneLayer K δi)) a b).symm.trans
      (vle_iff_of_isEquiv (isEquiv_normValuationLayer K δi) a b)
  have heq : normValuationLayer K δi (algebraMap K (sqrtNegOneLayer K δi) (w : K)) =
      normValuationLayer K δi z' :=
    le_antisymm ((hbr _ _).1 hv.le) ((hbr _ _).1 hv.ge)
  rw [normValuationLayer_algebraMap, hz'norm] at heq
  exact ⟨w, w.ne_zero, (congrArg NNReal.toReal heq).symm⟩

/-- **B5-K `ki_unramified`**: steps (3) and (4). -/
theorem kiUnramifiedClause_holds : KiUnramifiedClause K := fun hki δi hδi =>
  hasEqualNormValueGroups_of_isUnramified K δi hδi (isUnramified_sqrtNegOneLayer K hki δi hδi)

end K

/-! ## The bundle -/

/-- **B5-K, discharged.** gq2's marked local reciprocity bundle at a finite `K/ℚ₂`, for the B5
reciprocity datum `localReciprocity_tauceti`: the type of the census axiom `GQ2.markedRecipAt K`
(`GQ2/Foundations/Axioms.lean`) with `localReciprocity_tauceti` in place of `localReciprocity`.
`recip` is Tau Ceti's Artin map of `↥K` (`recipK`), `nu_ur` the geometric unramified coordinate
(`nuUrK`); the twelve fields are filled by the lemmas above. -/
def markedRecipAt_tauceti (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] : Dyadic.MarkedRecip localReciprocity_tauceti K where
  recip := recipK K
  continuous_recip := continuous_recipK K
  denseRange_recip := denseRange_recipK K
  nu_ur := nuUrK K
  continuous_nu_ur := continuous_nuUrK K
  norm_compat := inclAbK_recipK K
  nu_ur_recip_unit := nuUrK_recipK_unit K
  nu_ur_recip_uniformizer := nuUrK_recipK_uniformizer K
  r := (exists_levelK K).choose
  nu_ker_chi_le := (exists_levelK K).choose_spec.1
  nu_ker_chi_ge := (exists_levelK K).choose_spec.2
  ki_unramified := kiUnramifiedClause_holds K

section Equations

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- The reciprocity map of `markedRecipAt_tauceti K` is `recipK K` (B10-K reads its hypotheses
`toAbK g = (markedRecipAt_tauceti K).recip x` through this). -/
@[simp]
theorem markedRecipAt_tauceti_recip : (markedRecipAt_tauceti K).recip = recipK K := rfl

/-- Pointwise form of `markedRecipAt_tauceti_recip`. -/
theorem markedRecipAt_tauceti_recip_apply (x : Kˣ) :
    (markedRecipAt_tauceti K).recip x = recipK K x := rfl

/-- The unramified coordinate of `markedRecipAt_tauceti K` is `nuUrK K`. -/
@[simp]
theorem markedRecipAt_tauceti_nu_ur : (markedRecipAt_tauceti K).nu_ur = nuUrK K := rfl

end Equations

end GQ2.TauCetiBridge
