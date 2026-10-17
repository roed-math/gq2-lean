/-
T2 recon (dyadic Tau Ceti discharge), lane `tameK`: B10-K, every field of
`GQ2.Dyadic.OrientedTameQuotientK B FF` for any `B : MarkedRecip R K` whose `recip` is Tau Ceti's
Artin map of `↥K` (`recipK K`; the B5-K term of `../kiunram/ki.lean` has this by `rfl`).
Scratch prototype, not library code.  Self-contained: the bridge, Q3 and `abEquivK`/`recipK`
pieces are copied from `../bridge/bridge.lean` and `../kiunram/ki.lean`; the new part starts at
`## B10-K`.
-/
module

public import GQ2.TauCeti.B10
public import GQ2.Dyadic.OrientedTameBundle
public import GQ2.UnitFiltrationCounts
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

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

end GQ2.TauCetiBridge

#print axioms GQ2.TauCetiBridge.orientedTameQuotientOfRecip
