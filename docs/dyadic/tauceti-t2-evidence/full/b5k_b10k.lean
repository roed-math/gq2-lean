/-
T2 recon (dyadic Tau Ceti discharge), lane `full`: B5-K and B10-K assembled, and checked against
the exact types of the two census axioms `GQ2.markedRecipAt` / `GQ2.orientedTameQuotientAt`
(`GQ2/Foundations/Axioms.lean`), whose `localReciprocity` is `TauCetiBridge.localReciprocity_tauceti`
by definition (`GQ2/Foundations/TauCetiInstance.lean`).  Concatenation of `../kiunram/ki.lean`,
the Q3 part of `../bridge/bridge.lean` and the B10-K part of `../tameK/b10k.lean`, plus the
assembly at the end.  Scratch prototype, not library code.
-/
module

public import GQ2.TauCeti.B10
public import GQ2.Dyadic.MarkedRecipBundle
public import GQ2.Dyadic.OrientedTameBundle
public import GQ2.UnitFiltrationCounts
public import GQ2.Foundations.TauCetiInstance
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
public import GQ2.TraceForm

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

/-! ## Q2: `ki_unramified`

Chain: (1) an inertia element `τ` of `G_{↥K}` gives `g ∈ G_K` with `ν_ur(toAbK g) = 1`
(`unramifiedCoordinate_mk_eq_one_iff`; only `inertia ⊆ ker ν_ur` is used, not equality);
(2) the hypothesis gives `χ(g) ≡ 1 (mod 4)`, so `g` fixes `δi` (`cyclotomicCharacter.spec`);
(3) so inertia fixes `E = layerEmb(K(δi))` (A1's `fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff`),
hence `IsUnramified ↥K ↥E` (`map_inertiaSubgroup_le_fixingSubgroup_iff`);
(4) `e(E/K) = 1` plus the bridge at `↥E` gives equal norm value groups. -/

/-- The `ki_unramified` clause for `nuUrK`, as a `Prop`. -/
def KiClause : Prop :=
  (∀ g : GalKab K, nuUrK K g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
    ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi

/-- Step (1): inertia lies in the kernel of `ν_ur`. -/
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

/-- Step (2): `χ ≡ 1 (mod 4)` fixes a square root of `−1`. -/
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

theorem finiteDimensional_quadExt_i (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    FiniteDimensional K (quadExt K δi) :=
  finiteDimensional_quadExt K (-1) (by rw [hδi]; simp)

/-- The field `E = K(δi)` inside `↥K`'s separable closure. -/
abbrev layerE (δi : ℚ̄₂) : IntermediateField K (SeparableClosure K) :=
  (layerEmb K (quadExt K δi)).fieldRange

theorem finiteDimensional_layerE (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    FiniteDimensional K (layerE K δi) :=
  haveI := finiteDimensional_quadExt_i K δi hδi
  (AlgHom.equivFieldRange (layerEmb K (quadExt K δi))).toLinearEquiv.finiteDimensional

/-- Step (3): inertia fixes `E`, so `E/↥K` is unramified (Tau Ceti). -/
theorem isUnramified_layerE (hki : ∀ g : GalKab K, nuUrK K g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1)
    (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    haveI := finiteDimensional_layerE K δi hδi
    letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) (layerE K δi)
    letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (layerE K δi)
    haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
      (layerE K δi)
    haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
      (layerE K δi)
    TauCeti.IsUnramified K (layerE K δi) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := finiteDimensional_layerE K δi hδi
  haveI := finiteDimensional_quadExt_i K δi hδi
  letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) (layerE K δi)
  letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (layerE K δi)
  haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (layerE K δi)
  haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (layerE K δi)
  rw [← TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff]
  rintro _ ⟨τ, hτ, rfl⟩
  have hg := fixes_of_chiCyc_mod_four K ((galKEquiv K).symm (absGalEquivFixing K τ))
    (hki _ (nuUrK_toAbK_of_mem_inertia K τ hτ)) δi hδi
  have hmem := (fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff K δi
    (absGalEquivFixing K τ)).2 hg
  rw [fixingEquivAbsGal_apply, ContinuousMulEquiv.symm_apply_apply] at hmem
  rw [← TauCeti.galoisSubgroup_toSubgroup]
  exact hmem

/-- gq2's spectral norm on `E`, through `e = sepClosureEquiv K : Kˢᵉᵖ ≃ ℚ̄₂`. -/
def normValuationE (δi : ℚ̄₂) : Valuation (layerE K δi) NNReal :=
  (NormedField.valuation : Valuation ℚ̄₂ NNReal).comap
    ((sepClosureEquiv K).toAlgHom.toRingHom.comp (layerE K δi).val.toRingHom)

omit [FiniteDimensional ℚ_[2] K] in
theorem normValuationE_apply (δi : ℚ̄₂) (x : layerE K δi) :
    normValuationE K δi x = ‖sepClosureEquiv K (x : SeparableClosure K)‖₊ := rfl

omit [FiniteDimensional ℚ_[2] K] in
theorem normValuationE_algebraMap (δi : ℚ̄₂) (a : K) :
    normValuationE K δi (algebraMap K (layerE K δi) a) = ‖(a : ℚ̄₂)‖₊ := by
  rw [normValuationE_apply]
  exact congrArg (fun t => ‖t‖₊) (sepClosureEquiv_algebraMap K a)

theorem isEquiv_normValuationE (δi : ℚ̄₂) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    ((normValuationE K δi).comap (algebraMap K (layerE K δi))).IsEquiv (valuation K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  intro a b
  rw [Valuation.comap_apply, Valuation.comap_apply, normValuationE_algebraMap,
    normValuationE_algebraMap, valuation_le_iff_norm_le, ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

/-- Step (4): unramified `E/↥K` gives equal norm value groups. -/
theorem hasEqualNormValueGroups_of_isUnramified (δi : ℚ̄₂) (hδi : δi ^ 2 = -1)
    (hU : letI := valuativeRel K
      letI := localTopology K
      haveI := isNonarchimedeanLocalField K
      haveI := finiteDimensional_layerE K δi hδi
      letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) (layerE K δi)
      letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (layerE K δi)
      haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
        (layerE K δi)
      haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
        (layerE K δi)
      TauCeti.IsUnramified K (layerE K δi)) :
    HasEqualNormValueGroups K δi := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := finiteDimensional_layerE K δi hδi
  letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) (layerE K δi)
  letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) (layerE K δi)
  haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (layerE K δi)
  haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (layerE K δi)
  haveI : Algebra.IsAlgebraic K (layerE K δi) := Algebra.IsAlgebraic.of_finite K _
  intro z hz ⟨x, y, hxy⟩
  have hzmem : z ∈ quadExt K δi := by
    rw [hxy]
    exact add_mem (IntermediateField.algebraMap_mem _ x)
      (mul_mem (IntermediateField.algebraMap_mem _ y) (IntermediateField.mem_adjoin_simple_self K δi))
  let z₁ : quadExt K δi := ⟨z, hzmem⟩
  let z' : layerE K δi := ⟨layerEmb K (quadExt K δi) z₁, ⟨z₁, rfl⟩⟩
  have hz'norm : normValuationE K δi z' = ‖z‖₊ := by
    rw [normValuationE_apply]
    exact congrArg (fun t => ‖t‖₊) (sepClosureEquiv_layerEmb K (quadExt K δi) z₁)
  have hz' : z' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz'norm
    exact hz (nnnorm_eq_zero.mp hz'norm.symm)
  obtain ⟨w, hw⟩ := (TauCeti.isUnramified_iff_normalizedValuation_comp_unitsMap_surjective K
    (layerE K δi)).1 hU (TauCeti.normalizedValuation (layerE K δi) (Units.mk0 z' hz'))
  rw [MonoidHom.comp_apply] at hw
  -- equal normalized valuations give equal valuations
  have h1 := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le _ _).1
    (congrArg Multiplicative.toAdd hw).le
  have h2 := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le _ _).1
    (congrArg Multiplicative.toAdd hw).ge
  have hv : valuation (layerE K δi) (algebraMap K (layerE K δi) (w : K)) =
      valuation (layerE K δi) z' := le_antisymm h2 h1
  -- the bridge at `E`
  have hbr : ∀ a b : layerE K δi, valuation (layerE K δi) a ≤ valuation (layerE K δi) b ↔
      normValuationE K δi a ≤ normValuationE K δi b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := valuation (layerE K δi)) a b).symm.trans
      (vle_iff_of_isEquiv (isEquiv_normValuationE K δi) a b)
  have heq : normValuationE K δi (algebraMap K (layerE K δi) (w : K)) = normValuationE K δi z' :=
    le_antisymm ((hbr _ _).1 hv.le) ((hbr _ _).1 hv.ge)
  rw [normValuationE_algebraMap, hz'norm] at heq
  exact ⟨w, w.ne_zero, (congrArg NNReal.toReal heq).symm⟩

/-- **Q2: `ki_unramified`, proved.** -/
theorem kiClause : KiClause K := fun hki δi hδi =>
  hasEqualNormValueGroups_of_isUnramified K δi hδi (isUnramified_layerE K hki δi hδi)

/-! ## B5-K assembled -/

/-- **B5-K, discharged in scratch:** `MarkedRecip localReciprocity_tauceti K`. -/
def markedRecipAt_tauceti : MarkedRecip localReciprocity_tauceti K where
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
  ki_unramified := kiClause K


/-! ### Q3: the residue field (`Nat.card 𝓀[↥K] = 2 ^ FF.f`) -/

/-- gq2's unit ball `Osub K = {‖x‖ ≤ 1}` is Tau Ceti's `𝒪[↥K]` (same subring of `↥K`). -/
theorem osub_eq_integer :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K = (valuation K).integer := by
  letI := valuativeRel K
  ext x
  change ‖x‖ ≤ 1 ↔ valuation K x ≤ 1
  rw [← map_one (valuation K), valuation_le_iff_norm_le]
  simp only [OneMemClass.coe_one, norm_one]
  rfl

/-- The residue map `Osub K →+* 𝓀[↥K]`. -/
def osubToResidue :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K →+* IsLocalRing.ResidueField (valuation K).integer :=
  letI := valuativeRel K
  (IsLocalRing.residue _).comp (RingEquiv.subringCongr (osub_eq_integer K)).toRingHom

theorem osubToResidue_surjective :
    letI := valuativeRel K
    Function.Surjective (osubToResidue K) := by
  letI := valuativeRel K
  exact (IsLocalRing.residue_surjective).comp (RingEquiv.subringCongr (osub_eq_integer K)).surjective

theorem ker_osubToResidue :
    letI := valuativeRel K
    RingHom.ker (osubToResidue K) = UnitFiltrationCounts.maxIdeal K := by
  letI := valuativeRel K
  ext x
  rw [RingHom.mem_ker, osubToResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K (x : K) < 1 ↔ ‖(x : K)‖ < 1
  rw [← map_one (valuation K), lt_iff_lt_of_le_iff_le (valuation_le_iff_norm_le K 1 (x : K))]
  simp

/-- **Q3, the residue-degree bridge.** `#𝓀[↥K] = #(O/𝔪)` (gq2's intrinsic residue field). -/
theorem natCard_residueField_eq :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) =
      Nat.card (UnitFiltrationCounts.ResidueField K) := by
  letI := valuativeRel K
  refine Nat.card_congr ((Ideal.quotEquivOfEq (ker_osubToResidue K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (osubToResidue_surjective K))).toEquiv.symm

/-- **Q3 answered:** with gq2's `card_gradeI`-based `residueField_card_eq_pow_f` (public), Tau
Ceti's residue cardinality is `qOf K FF = 2 ^ FF.f`.  No private lemma is needed. -/
theorem natCard_residueField_eq_two_pow (FF : DyadicUnitFiltration K) :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) = 2 ^ FF.f :=
  (natCard_residueField_eq K).trans (UnitFiltrationCounts.residueField_card_eq_pow_f K FF)



/-! ## B10-K, generic part: the geometric Iwasawa group of a local field `L` with `#𝓀[L] = q`
is gq2's `Tq q` (B10's `iwasawaGeometricEquivTtame` with `Padic.natCard_residueField` replaced by
the hypothesis `hq`). -/

end K

section Generic

variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  (q : ℕ) (hq : Nat.card (IsLocalRing.ResidueField (valuation L).integer) = q)

def iwasawaGeometricToTq : TauCeti.IwasawaGroupGeometric L →ₜ* Tq q :=
  TauCeti.presentedProfiniteGroup.lift
    (TauCeti.freeProfiniteGroup.lift fun i : ULift.{0} (Fin 2) => ![tqSigma q, tqTau q] i.down)
    (by
      rintro r rfl
      rw [TauCeti.iwasawaRelatorGeometric_def, hq]
      simp only [map_mul, map_inv, map_pow, TauCeti.freeProfiniteGroup.lift_of]
      have h := tame_relation_q q
      simp only [conjP] at h
      simp [h])

theorem iwasawaGeometricToTq_sigma :
    iwasawaGeometricToTq L q hq (TauCeti.iwasawaSigmaGeometric L) = tqSigma q := by
  simp [iwasawaGeometricToTq, TauCeti.presentedProfiniteGroup.lift_of,
    TauCeti.freeProfiniteGroup.lift_of]

theorem iwasawaGeometricToTq_tau :
    iwasawaGeometricToTq L q hq (TauCeti.iwasawaTauGeometric L) = tqTau q := by
  simp [iwasawaGeometricToTq, TauCeti.presentedProfiniteGroup.lift_of,
    TauCeti.freeProfiniteGroup.lift_of]

def iwasawaGeometricGrpL : ProfiniteGrp.{0} := ProfiniteGrp.of (TauCeti.IwasawaGroupGeometric L)

def freeToIwasawaGeometricL : FreeProfiniteGroup (Fin 2) ⟶ iwasawaGeometricGrpL L :=
  (FreeProfiniteGroup.homEquiv (Fin 2) (iwasawaGeometricGrpL L)).symm
    ![TauCeti.iwasawaSigmaGeometric L, TauCeti.iwasawaTauGeometric L]

theorem freeToIwasawaGeometricL_of_zero :
    (freeToIwasawaGeometricL L).hom (FreeProfiniteGroup.of 0) = TauCeti.iwasawaSigmaGeometric L :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem freeToIwasawaGeometricL_of_one :
    (freeToIwasawaGeometricL L).hom (FreeProfiniteGroup.of 1) = TauCeti.iwasawaTauGeometric L :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

include hq in
theorem freeToIwasawaGeometricL_tameWordQ : (freeToIwasawaGeometricL L).hom (tameWordQ q) = 1 := by
  have hrel := TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul L
  rw [hq] at hrel
  rw [tameWordQ, conjP]
  simp only [map_mul, map_inv, map_pow, freeToIwasawaGeometricL_of_zero,
    freeToIwasawaGeometricL_of_one]
  change (TauCeti.iwasawaSigmaGeometric L)⁻¹ * TauCeti.iwasawaTauGeometric L *
    TauCeti.iwasawaSigmaGeometric L * (TauCeti.iwasawaTauGeometric L ^ q)⁻¹ = 1
  rw [hrel]
  exact mul_inv_cancel _

def tqToIwasawaGeometric : ContinuousMonoidHom (Tq q) (TauCeti.IwasawaGroupGeometric L) :=
  presentationLift {tameWordQ q} (freeToIwasawaGeometricL L).hom fun r hr => by
    rcases hr with rfl
    exact freeToIwasawaGeometricL_tameWordQ L q hq

theorem tqToIwasawaGeometric_sigma :
    tqToIwasawaGeometric L q hq (tqSigma q) = TauCeti.iwasawaSigmaGeometric L := by
  show tqToIwasawaGeometric L q hq
    (quotientMk (relatorSubgroup {tameWordQ q}) (FreeProfiniteGroup.of 0)) = _
  exact (presentationLift_mk _ _ _ _).trans (freeToIwasawaGeometricL_of_zero L)

theorem tqToIwasawaGeometric_tau :
    tqToIwasawaGeometric L q hq (tqTau q) = TauCeti.iwasawaTauGeometric L := by
  show tqToIwasawaGeometric L q hq
    (quotientMk (relatorSubgroup {tameWordQ q}) (FreeProfiniteGroup.of 1)) = _
  exact (presentationLift_mk _ _ _ _).trans (freeToIwasawaGeometricL_of_one L)

theorem iwasawaGeometricToTq_tqToIwasawaGeometric (x : Tq q) :
    iwasawaGeometricToTq L q hq (tqToIwasawaGeometric L q hq x) = x := by
  obtain ⟨w, rfl⟩ := quotientMk_surjective (relatorSubgroup {tameWordQ q}) x
  let f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) (Tq q) :=
    ((iwasawaGeometricToTq L q hq).comp (tqToIwasawaGeometric L q hq)).comp
      (quotientMk (relatorSubgroup {tameWordQ q}))
  let g : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) (Tq q) :=
    quotientMk (relatorSubgroup {tameWordQ q})
  have hfg : (CategoryTheory.ConcreteCategory.ofHom f : FreeProfiniteGroup (Fin 2) ⟶ Tq q) =
      CategoryTheory.ConcreteCategory.ofHom g := by
    apply (FreeProfiniteGroup.homEquiv (Fin 2) (Tq q)).injective
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]
    fin_cases i
    · change iwasawaGeometricToTq L q hq (tqToIwasawaGeometric L q hq (tqSigma q)) = tqSigma q
      rw [tqToIwasawaGeometric_sigma, iwasawaGeometricToTq_sigma]
    · change iwasawaGeometricToTq L q hq (tqToIwasawaGeometric L q hq (tqTau q)) = tqTau q
      rw [tqToIwasawaGeometric_tau, iwasawaGeometricToTq_tau]
  exact DFunLike.congr_fun (congrArg ProfiniteGrp.Hom.hom hfg) w

theorem tqToIwasawaGeometric_iwasawaGeometricToTq (x : TauCeti.IwasawaGroupGeometric L) :
    tqToIwasawaGeometric L q hq (iwasawaGeometricToTq L q hq x) = x := by
  have h : (tqToIwasawaGeometric L q hq).comp (iwasawaGeometricToTq L q hq) =
      ContinuousMonoidHom.id _ := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · exact (congrArg (tqToIwasawaGeometric L q hq) (iwasawaGeometricToTq_sigma L q hq)).trans
        (tqToIwasawaGeometric_sigma L q hq)
    · exact (congrArg (tqToIwasawaGeometric L q hq) (iwasawaGeometricToTq_tau L q hq)).trans
        (tqToIwasawaGeometric_tau L q hq)
  exact DFunLike.congr_fun h x

/-- **The geometric Iwasawa group of `L` is gq2's `Tq q`** (`q = #𝓀[L]`). -/
def iwasawaGeometricEquivTq : TauCeti.IwasawaGroupGeometric L ≃ₜ* Tq q where
  toFun := iwasawaGeometricToTq L q hq
  invFun := tqToIwasawaGeometric L q hq
  left_inv := tqToIwasawaGeometric_iwasawaGeometricToTq L q hq
  right_inv := iwasawaGeometricToTq_tqToIwasawaGeometric L q hq
  map_mul' := map_mul (iwasawaGeometricToTq L q hq)
  continuous_toFun := (iwasawaGeometricToTq L q hq).continuous
  continuous_invFun := (tqToIwasawaGeometric L q hq).continuous

/-- The sign of `ν_t` at general `q`. -/
theorem nuTq_iwasawaGeometricToTq (x : TauCeti.IwasawaGroupGeometric L) :
    nuTq q (iwasawaGeometricToTq L q hq x) =
      TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric L x) := by
  have key : (nuTq q).comp (iwasawaGeometricToTq L q hq) =
      (TauCeti.zHat.lift ztwoOne⁻¹).comp (TauCeti.iwasawaCoordinateGeometric L) := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · change nuTq q (iwasawaGeometricToTq L q hq (TauCeti.iwasawaSigmaGeometric L)) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric L
          (TauCeti.iwasawaSigmaGeometric L))
      rw [iwasawaGeometricToTq_sigma, nuTq_tqSigma,
        TauCeti.iwasawaCoordinateGeometric_iwasawaSigmaGeometric, map_inv,
        TauCeti.zHat.lift_gen, inv_inv]
    · change nuTq q (iwasawaGeometricToTq L q hq (TauCeti.iwasawaTauGeometric L)) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric L
          (TauCeti.iwasawaTauGeometric L))
      rw [iwasawaGeometricToTq_tau, nuTq_tqTau,
        TauCeti.iwasawaCoordinateGeometric_iwasawaTauGeometric, map_one]
  exact DFunLike.congr_fun key x

end Generic

/-! ## B10-K at `↥K` -/

section K2

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- `G_{↥K} ≃ₜ* GalK K` (A1's `absGalEquivFixing`, at gq2's instance path). -/
def phiK : Field.absoluteGaloisGroup K ≃ₜ* GalK K :=
  (absGalEquivFixing K).trans (galKEquiv K).symm

/-- **`W`**: Tau Ceti's wild inertia of `↥K`, transported to `GalK K`. -/
def wildK : Subgroup (GalK K) :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  (TauCeti.wildInertiaSubgroup K).map (phiK K).toMulEquiv.toMonoidHom

theorem map_wild_eq_wildK :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    (TauCeti.wildInertiaSubgroup K).map (phiK K).toMulEquiv.toMonoidHom = wildK K := rfl

instance wildK_normal : (wildK K).Normal := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact Subgroup.Normal.map (TauCeti.wildInertiaSubgroup_normal K) _ (phiK K).surjective

theorem isClosed_wildK : IsClosed (wildK K : Set (GalK K)) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [wildK, Subgroup.coe_map]
  exact (phiK K).toHomeomorph.isClosedMap _ (TauCeti.isClosed_wildInertiaSubgroup K)

theorem isProP_wildK : IsProP 2 (wildK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  haveI := TauCeti.charP_residueField K 2
  have h := TauCeti.isProP_wildInertiaSubgroup K 2
  refine TauCeti.isProP_iff.mp (h.of_surjective
    ((phiK K).toMulEquiv.toMonoidHom.subgroupMap (TauCeti.wildInertiaSubgroup K))
    (continuous_induced_rng.2 ((phiK K).continuous.comp continuous_subtype_val))
    ((phiK K).toMulEquiv.toMonoidHom.subgroupMap_surjective _))

/-- **`equiv`**: `GalK K ⧸ W ≃ₜ* Tq (qOf K FF)`. -/
def tameEquivK (FF : DyadicUnitFiltration K) : ContinuousMulEquiv (GalK K ⧸ wildK K) (Tq (qOf K FF)) :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  ((phiK K).quotientCongr (TauCeti.wildInertiaSubgroup K) (wildK K) (map_wild_eq_wildK K)).symm.trans
    ((TauCeti.tameQuotientGeometricEquiv
        (Classical.choose_spec (TauCeti.exists_isArithFrobeniusLift K))
        (Classical.choose (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K))
        (Classical.choose_spec
          (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K))).trans
      (iwasawaGeometricEquivTq K (qOf K FF)
        ((natCard_residueField_eq_two_pow K FF).trans (qOf_eq K FF).symm)))

/-- **The lemma behind both orientation clauses**: `ν_t(equiv (mk g)) = ztwoOne⁻¹ ^ v_K(x)`
for any lift `g` of `rec_K x`. -/
theorem nuTq_tameEquivK_mk (FF : DyadicUnitFiltration K) (g : GalK K) (x : Kˣ)
    (hg : toAbK K g = recipK K x) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    nuTq (qOf K FF) (tameEquivK K FF (QuotientGroup.mk g)) =
      ztwoOne⁻¹ ^ (TauCeti.normalizedValuation K x).toAdd := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  have h1 : abEquivK K (toAbK K g) =
      (((phiK K).symm g : Field.absoluteGaloisGroup K) : Field.absoluteGaloisGroupAbelianization K) :=
    abEquivK_toAbK K g
  rw [hg, abEquivK_recipK] at h1
  rw [tameEquivK, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.quotientCongr_symm_mk]
  change nuTq (qOf K FF) (iwasawaGeometricToTq K (qOf K FF) _ _) = _
  rw [nuTq_iwasawaGeometricToTq, TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv,
    ← TauCeti.toTameQuotient_apply, TauCeti.tameQuotientToZHat_toTameQuotient,
    ← TauCeti.unramifiedCoordinate_mk]
  change TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.unramifiedCoordinate K
    (((phiK K).symm g : Field.absoluteGaloisGroup K) : Field.absoluteGaloisGroupAbelianization K)) = _
  rw [← h1, TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap, TauCeti.zHat.lift_ofInt]

/-- **B10-K**, for any marked bundle whose `recip` is `recipK K`. -/
def orientedTameQuotientOfRecip {R : LocalReciprocity} (B : MarkedRecip R K)
    (hB : ∀ x, B.recip x = recipK K x) (FF : DyadicUnitFiltration K) :
    OrientedTameQuotientK B FF where
  W := wildK K
  normal := wildK_normal K
  isClosed := isClosed_wildK K
  isProP := isProP_wildK K
  equiv := tameEquivK K FF
  nuT_recip_unit u g hu hg := by
    rw [hB] at hg
    rw [nuTq_tameEquivK_mk K FF g u hg, normalizedValuation_eq_one_of_norm_eq_one K u hu]
    exact zpow_zero _
  nuT_recip_uniformizer g hg := by
    rw [hB] at hg
    rw [nuTq_tameEquivK_mk K FF g _ hg, normalizedValuation_eq_ofAdd_one_of_norm K _
      (norm_uniformizerK_lt_one K FF) (uniformizerK_max K FF)]
    exact zpow_one _

end K2


/-! ## Assembly against the census-axiom types -/

section Assembly

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- **B10-K, discharged in scratch:** `OrientedTameQuotientK (markedRecipAt_tauceti K) FF`. -/
def orientedTameQuotientAt_tauceti (FF : DyadicUnitFiltration K) :
    OrientedTameQuotientK (markedRecipAt_tauceti K) FF :=
  orientedTameQuotientOfRecip K (markedRecipAt_tauceti K) (fun _ => rfl) FF

/-
Against the census-axiom types: `GQ2.markedRecipAt K : Dyadic.MarkedRecip GQ2.localReciprocity K`.
`GQ2.localReciprocity := TauCetiBridge.localReciprocity_tauceti` is **not exposed** outside
`GQ2/Foundations/TauCetiInstance.lean`, so from this (or any other) module

  example : Dyadic.MarkedRecip GQ2.localReciprocity K := markedRecipAt_tauceti K

fails ("definitions not unfolded because not exposed: localReciprocity").  The C1' same-name
`noncomputable def`s must therefore be written inside `TauCetiInstance.lean` itself (where the
body of `localReciprocity` is visible, exactly as its `tameQuotient := tameQuotient_tauceti`
already is), or that file must export `localReciprocity_eq : localReciprocity =
TauCetiBridge.localReciprocity_tauceti := rfl` for a cast.
-/

end Assembly

end GQ2.TauCetiBridge

#print axioms GQ2.TauCetiBridge.markedRecipAt_tauceti
#print axioms GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti
