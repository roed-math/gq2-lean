/-
T2 recon (dyadic Tau Ceti discharge), lane `recipK`: B5-K, every field of
`GQ2.Dyadic.MarkedRecip localReciprocity_tauceti K` except `ki_unramified` (which is lane `kiunram`).
Scratch prototype, not library code.  Self-contained (prototype files cannot import each other):
the bridge lemmas of `../bridge/bridge.lean` are restated here, under the heavy B5 imports.
-/
module

public import GQ2.TauCeti.B5
public import GQ2.Dyadic.MarkedRecipBundle
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

@[expose] public section

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel GQ2.Dyadic

/-! ## A1-K: the bridge (restated from `bridge/bridge.lean`) -/

theorem vle_iff_of_isEquiv {F M : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field M] [Algebra F M] [Algebra.IsAlgebraic F M]
    [ValuativeRel M] [ValuativeExtension F M] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation M Γ} (hw : (w.comap (algebraMap F M)).IsEquiv (valuation F)) (x y : M) :
    x ≤ᵥ y ↔ w x ≤ w y :=
  (TauCeti.vle_iff_algebraicExtensionNormedField_norm_le F x y).trans
    (TauCeti.algebraicExtensionNormedField_norm_le_norm_iff hw x y)

section K

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

def normValuation : Valuation K NNReal :=
  (NormedField.valuation : Valuation ℚ̄₂ NNReal).comap (K.val : K →+* ℚ̄₂)

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem normValuation_apply (x : K) : normValuation K x = ‖(x : ℚ̄₂)‖₊ := rfl

omit [FiniteDimensional ℚ_[2] K] in
theorem isEquiv_normValuation :
    ((normValuation K).comap (algebraMap ℚ_[2] K)).IsEquiv (valuation ℚ_[2]) := by
  intro a b
  simp only [Valuation.comap_apply, normValuation_apply]
  rw [← TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff,
    ← NNRat.cast_le (K := NNReal),
    Padic.normalizedAbsoluteValue_eq_nnnorm, Padic.normalizedAbsoluteValue_eq_nnnorm]
  change ‖algebraMap ℚ_[2] ℚ̄₂ a‖₊ ≤ ‖algebraMap ℚ_[2] ℚ̄₂ b‖₊ ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    norm_algebraMap' (𝕜' := ℚ̄₂), norm_algebraMap' (𝕜' := ℚ̄₂), ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

theorem valuation_le_iff_norm_le (x y : K) :
    letI := valuativeRel K
    valuation K x ≤ valuation K y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  rw [← Valuation.Compatible.vle_iff_le (v := valuation K) x y,
    vle_iff_of_isEquiv (isEquiv_normValuation K) x y, normValuation_apply, normValuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]

theorem vle_iff_norm_le (x y : K) :
    letI := valuativeRel K
    x ≤ᵥ y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y).trans (valuation_le_iff_norm_le K x y)

theorem valuation_eq_iff_norm_eq (x y : K) :
    letI := valuativeRel K
    valuation K x = valuation K y ↔ ‖(x : ℚ̄₂)‖ = ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_iff_norm_le, valuation_le_iff_norm_le]

theorem normalizedValuation_eq_one_of_norm_eq_one (u : Kˣ) (hu : ‖((u : K) : ℚ̄₂)‖ = 1) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K u = 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K), valuation_eq_iff_norm_eq]
  simpa using hu

theorem normalizedValuation_eq_ofAdd_one_of_norm (π : Kˣ) (hπ : ‖((π : K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((π : K) : ℚ̄₂)‖) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K π = Multiplicative.ofAdd 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  obtain ⟨ϖ, hϖ⟩ := TauCeti.normalizedValuation_surjective (K := K) (Multiplicative.ofAdd 1)
  have h1 : 1 ≤ (TauCeti.normalizedValuation K π).toAdd := by
    have hle : (0 : ℤ) ≤ (TauCeti.normalizedValuation K π).toAdd := by
      rw [show (0 : ℤ) = (TauCeti.normalizedValuation K 1).toAdd by simp,
        TauCeti.toAdd_normalizedValuation_le_iff_valuation_le, Units.val_one,
        valuation_le_iff_norm_le, OneMemClass.coe_one, norm_one]
      exact hπ.le
    have hne : (TauCeti.normalizedValuation K π).toAdd ≠ 0 := by
      intro h0
      have : TauCeti.normalizedValuation K π = 1 := toAdd_eq_zero.mp h0
      rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K),
        valuation_eq_iff_norm_eq] at this
      simp at this
      exact absurd this hπ.ne
    omega
  have hϖlt : ‖((ϖ : K) : ℚ̄₂)‖ < 1 := by
    have h := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le (K := K) 1 ϖ).1
      (by rw [hϖ]; simp)
    rw [Units.val_one, valuation_le_iff_norm_le] at h
    rcases h.lt_or_eq with h | h
    · simpa using h
    · exfalso
      have : TauCeti.normalizedValuation K ϖ = 1 := by
        rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K),
          valuation_eq_iff_norm_eq]
        simpa using h
      rw [hϖ] at this
      exact absurd (congrArg Multiplicative.toAdd this) (by simp)
  have h2 : (TauCeti.normalizedValuation K π).toAdd ≤ 1 := by
    have := hmax ϖ ϖ.ne_zero hϖlt
    rw [← valuation_le_iff_norm_le, ← TauCeti.toAdd_normalizedValuation_le_iff_valuation_le,
      hϖ] at this
    simpa using this
  exact Multiplicative.toAdd.injective (by simp; omega)

theorem normalizedValuation_two_ne_one :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K (Units.mk0 (2 : K) two_ne_zero) ≠ 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [Ne, TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K), valuation_eq_iff_norm_eq]
  intro h
  have h2 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [← map_ofNat (algebraMap ℚ_[2] ℚ̄₂) 2, norm_algebraMap' (𝕜' := ℚ̄₂)]
    exact_mod_cast Padic.norm_p_lt_one (p := 2)
  simp only [Units.val_mk0, OneMemClass.coe_one, norm_one] at h
  exact absurd h (by exact_mod_cast h2.ne)

theorem isValuativeTopology_subtype :
    @IsValuativeTopology K _ (valuativeRel K) inferInstance := by
  letI := valuativeRel K
  haveI : (NormedField.valuation (K := K)).Compatible :=
    ⟨fun x y => by
      rw [vle_iff_norm_le, NormedField.valuation_apply, NormedField.valuation_apply,
        ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      rfl⟩
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

theorem localTopology_eq :
    localTopology K = (inferInstance : TopologicalSpace K) := by
  have h1 := @TauCeti.finiteIntermediateField_isValuativeTopology ℚ_[2] _ _ _ _ ℚ̄₂ _ _ K _
  have h2 := isValuativeTopology_subtype K
  letI := valuativeRel K
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@IsValuativeTopology.mem_nhds_iff _ _ _ (localTopology K) h1,
    @IsValuativeTopology.mem_nhds_iff _ _ _ _ h2]

/-! ## A1-K: `G_K^{ab}` in Tau Ceti's model -/

/-- gq2's `GalK K` (subgroup of `AbsGalQ2`) is A1's `↥K.fixingSubgroup` (subgroup of
`Kummer.GaloisGroup ℚ₂`): the same type with two registered instance paths (bundle memo R6). -/
def galKEquiv : GalK K ≃ₜ* ↥(K.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])) :=
  ContinuousMulEquiv.refl _

/-- **`abEquivK`**: `G_K^{ab}` (gq2) `≃ₜ* Field.absoluteGaloisGroupAbelianization ↥K` (Tau Ceti). -/
def abEquivK : GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization K :=
  ((galKEquiv K).trans (absGalEquivFixing K).symm).topologicalAbelianizationCongr

theorem abEquivK_toAbK (g : GalK K) :
    abEquivK K (toAbK K g) =
      (((absGalEquivFixing K).symm (galKEquiv K g) : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) :=
  ContinuousMulEquiv.topologicalAbelianizationCongr_mk _ g

theorem abEquivK_symm_mk (τ : Field.absoluteGaloisGroup K) :
    (abEquivK K).symm (τ : Field.absoluteGaloisGroupAbelianization K) =
      toAbK K ((galKEquiv K).symm (absGalEquivFixing K τ)) := by
  rw [ContinuousMulEquiv.symm_apply_eq, abEquivK_toAbK]
  show _ = (((absGalEquivFixing K).symm (absGalEquivFixing K τ) : Field.absoluteGaloisGroup K) :
    Field.absoluteGaloisGroupAbelianization K)
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- The `G_K`-element attached to `τ ∈ G_{↥K}`, read in `AbsGalQ2`, is
`absoluteGaloisGroupExtend ℚ₂ ↥K (sepEmb K) τ` (A1). -/
theorem coe_galKEquiv_symm_absGalEquivFixing (τ : Field.absoluteGaloisGroup K) :
    (((galKEquiv K).symm (absGalEquivFixing K τ) : GalK K) : AbsGalQ2) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) τ :=
  coe_absGalEquivFixing_apply K τ

/-! ## B5-K: the reciprocity map and its two topological clauses -/

/-- **`recip`**: Tau Ceti's Artin map of `↥K`, transported along `abEquivK`. -/
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

theorem denseRange_recipK : DenseRange (recipK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact (abEquivK K).symm.surjective.denseRange.comp
    (TauCeti.ClassFieldTheory.denseRange_artinMap K) (abEquivK K).symm.continuous

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

/-! ## B5-K: the unramified coordinate -/

/-- **`nu_ur`**: inverse of the `ℤ₂`-reduction of Tau Ceti's (arithmetic) unramified coordinate
of `↥K`, transported along `abEquivK` (B5's `nuUr` at `↥K`). -/
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

theorem continuous_nuUrK : Continuous (nuUrK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact continuous_inv.comp ((TauCeti.zHat.lift _).continuous.comp
    ((TauCeti.unramifiedCoordinate K).continuous.comp (abEquivK K).continuous))

/-- **The valuation lemma behind (b_K) and the level.** `ν_ur(rec_K x) = −v_K(x)`. -/
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

theorem nuUrK_recipK_unit (u : Kˣ) (hu : ‖((u : K) : ℚ̄₂)‖ = 1) : nuUrK K (recipK K u) = 1 := by
  rw [nuUrK_recipK, normalizedValuation_eq_one_of_norm_eq_one K u hu]
  simp

theorem nuUrK_recipK_uniformizer (π : Kˣ) (hπ : ‖((π : K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((π : K) : ℚ̄₂)‖) :
    nuUrK K (recipK K π) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  rw [nuUrK_recipK, normalizedValuation_eq_ofAdd_one_of_norm K π hπ hmax]
  simp

/-! ## B5-K: norm functoriality (`artinMap_norm` at `(ℚ₂, ↥K)`) -/

theorem normUnitsK_eq_normUnits (x : Kˣ) :
    normUnitsK K x = TauCeti.Algebra.normUnits ℚ_[2] x :=
  Units.ext (by rw [normUnitsK_val, TauCeti.Algebra.coe_normUnits])

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

/-! ## B5-K: the marked level `r` (recon question Q1)

Generic: in a compact group, if `χ`, `ν` are continuous and some `g₀ ∈ ker χ` has `ν g₀ ≠ 0`,
then `ν(ker χ)` is a nonzero closed subgroup of `ℤ₂`, hence an ideal, hence `2^r ℤ₂`.  At `↥K`,
`g₀ = rec_K(2)`: `χ_K(rec_K 2) = χ(rec_{ℚ₂}(N 2)) = χ(rec_{ℚ₂}(2^d)) = 1` and `ν(rec_K 2) = −v_K(2) ≠ 0`.
No ramification fact about `ℚ₂(μ_{2^∞})` is needed. -/

/-- A closed additive subgroup of `ℤ_[2]` is closed under multiplication by `ℤ_[2]`. -/
theorem mul_mem_of_isClosed {A : AddSubgroup ℤ_[2]} (hA : IsClosed (A : Set ℤ_[2])) (c : ℤ_[2])
    {a : ℤ_[2]} (ha : a ∈ A) : c * a ∈ A := by
  have hcl : (fun t : ℤ_[2] => t * a) ⁻¹' (A : Set ℤ_[2]) ⊇ Set.range (Int.cast : ℤ → ℤ_[2]) := by
    rintro _ ⟨n, rfl⟩
    simpa [zsmul_eq_mul] using A.zsmul_mem ha n
  have hclosed : IsClosed ((fun t : ℤ_[2] => t * a) ⁻¹' (A : Set ℤ_[2])) :=
    hA.preimage (continuous_id.mul continuous_const)
  have := (hclosed.closure_subset_iff.2 hcl) (PadicInt.denseRange_intCast c)
  exact this

theorem exists_level {A : Type*} [CommGroup A] [TopologicalSpace A] [CompactSpace A]
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
    simp only [S, AddSubgroup.mem_map, Subgroup.mem_toAddSubgroup', Subgroup.mem_map,
      MonoidHom.mem_ker, AddMonoidHom.mk'_apply]
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
      smul_mem' := fun c _ ha => mul_mem_of_isClosed hSclosed c ha }
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

/-- `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}`. -/
theorem normUnitsK_two :
    normUnitsK K (Units.mk0 (2 : K) two_ne_zero) = uniformizer ^ Module.finrank ℚ_[2] K := by
  refine Units.ext ?_
  rw [normUnitsK_val, Units.val_pow_eq_pow_val, uniformizer_val, Units.val_mk0,
    show (2 : K) = algebraMap ℚ_[2] K 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap]

theorem chiCycKAb_recipK_two : chiCycKAb K (recipK K (Units.mk0 (2 : K) two_ne_zero)) = 1 := by
  rw [← chiCycAb_inclAbK, inclAbK_recipK, normUnitsK_two, map_pow, map_pow,
    localReciprocity_tauceti.chiCyc_recip_uniformizer, one_pow]

theorem nuUrK_recipK_two_ne_zero :
    (nuUrK K (recipK K (Units.mk0 (2 : K) two_ne_zero))).toAdd ≠ 0 := by
  rw [nuUrK_recipK, toAdd_ofAdd, neg_ne_zero, Int.cast_ne_zero]
  intro h
  exact normalizedValuation_two_ne_one K (toAdd_eq_zero.mp h)

omit [FiniteDimensional ℚ_[2] K] in
theorem compactSpace_galK : CompactSpace (GalK K) := compactSpace_fixingSubgroup K

omit [FiniteDimensional ℚ_[2] K] in
theorem compactSpace_galKab : CompactSpace (GalKab K) :=
  haveI := compactSpace_galK K
  Quotient.compactSpace

theorem exists_levelK : ∃ r : ℕ,
    (∀ g : GalKab K, chiCycKAb K g = 1 → ∃ y : ℤ_[2], (nuUrK K g).toAdd = 2 ^ r * y) ∧
      ∀ y : ℤ_[2], ∃ g : GalKab K, chiCycKAb K g = 1 ∧ (nuUrK K g).toAdd = 2 ^ r * y :=
  @exists_level (GalKab K) _ _ (compactSpace_galKab K) (chiCycKAb K) (continuous_quot_lift _ (continuous_chiCycK K)) (nuUrK K)
    (continuous_nuUrK K) _ (chiCycKAb_recipK_two K) (nuUrK_recipK_two_ne_zero K)

/-! ## B5-K assembled, with `ki_unramified` as a hypothesis (lane `kiunram` supplies it) -/

/-- The `ki_unramified` clause for `nuUrK`, as a `Prop` (proved in `kiunram/ki.lean`). -/
def KiClause : Prop :=
  (∀ g : GalKab K, nuUrK K g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
    ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi

/-- **B5-K**, every field except `ki_unramified`, which is the hypothesis. -/
def markedRecipOfKi (hki : KiClause K) : MarkedRecip localReciprocity_tauceti K where
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
  ki_unramified := hki

end K

end GQ2.TauCetiBridge

#print axioms GQ2.TauCetiBridge.markedRecipOfKi
