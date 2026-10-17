module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.LocalField.Unramified.Coordinate
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.NumberTheory.LocalField.Tame.Geometric
public import GQ2.Reciprocity
public import GQ2.TameQuotient

/-!
T2 recon draft (lane `recip`): complete sorry-free B5 and B10 terms, for the adapter tickets.
Not a deliverable; scratch evidence that the translation in `section.md` closes.
-/

open GQ2

/-- The embedding of a finite layer into the separable closure (copied from the proof of
`mem_normGroup_of_mk_eq_artinMap_of_fixes`). -/
noncomputable def layerEmb (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] : L →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] :=
  haveI : Algebra.IsSeparable ℚ_[2] L := IsGalois.to_isSeparable
  L.val.codRestrict (separableClosure ℚ_[2] (AlgebraicClosure ℚ_[2])).toSubalgebra
    fun z ↦ mem_separableClosure_iff.2 ((Algebra.IsSeparable.isSeparable ℚ_[2] z).map L.val
      L.val.injective)

theorem layerEmb_restrict (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] (σ : AbsGalQ2) :
    (layerEmb L).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] σ) =
      restrictHom L σ := by
  refine AlgEquiv.ext fun y ↦ (layerEmb L).injective <|
    ((layerEmb L).restrictNormalHom_commutes _ y).trans (Subtype.ext ?_)
  refine (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) σ _).trans ?_
  have h1 : ((layerEmb L y : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2]) = y :=
    AlgHom.coe_codRestrict _ _ _ y
  have h2 : ((layerEmb L (restrictHom L σ y) : SeparableClosure ℚ_[2]) :
      AlgebraicClosure ℚ_[2]) = (restrictHom L σ y : L) :=
    AlgHom.coe_codRestrict _ _ _ _
  change DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[2]/ℚ_[2])) σ ((layerEmb L y : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2]) =
    ((layerEmb L (restrictHom L σ y) : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2])
  rw [h1, h2]
  exact (AlgEquiv.restrictNormal_commutes σ L y).symm

theorem restrictAb_artinMap (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) (x : ℚ_[2]ˣ) :
    TauCeti.ClassFieldTheory.localArtinMap ℚ_[2] L (layerEmb L) (Additive.ofMul x) =
      Additive.ofMul (Abelianization.of
        (restrictAb L hab (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x))) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
    (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x)
  rw [← hg]
  change _ = Additive.ofMul (Abelianization.of (restrictAb L hab (toAb g)))
  rw [restrictAb_toAb, ← layerEmb_restrict]
  exact TauCeti.ClassFieldTheory.artinMap_restrict ℚ_[2] L (layerEmb L) x g hg

theorem norm_reciprocity_tauceti (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) :
    Function.Surjective ((restrictAb L hab).comp
        (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* AbsGalQ2ab)) ∧
      ((restrictAb L hab).comp
        (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* AbsGalQ2ab)).ker = normSubgroup L := by
  let _ : CommGroup (L ≃ₐ[ℚ_[2]] L) := { (inferInstance : Group (L ≃ₐ[ℚ_[2]] L)) with mul_comm := hab }
  have hinj : Function.Injective (Abelianization.of (G := L ≃ₐ[ℚ_[2]] L)) :=
    (Abelianization.equivOfComm (H := L ≃ₐ[ℚ_[2]] L)).injective
  refine ⟨fun τ ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := TauCeti.ClassFieldTheory.surjective_localArtinMap ℚ_[2] L (layerEmb L)
      (Additive.ofMul (Abelianization.of τ))
    refine ⟨Additive.toMul a, hinj (Additive.ofMul.injective ?_)⟩
    rw [MonoidHom.comp_apply, ← restrictAb_artinMap, ofMul_toMul, ha]
  · ext x
    have hn : normSubgroup L = TauCeti.normGroup ℚ_[2] L := by
      ext y
      rw [TauCeti.mem_normGroup_iff]
      simp [normSubgroup, Units.ext_iff]
    rw [MonoidHom.mem_ker, hn, ← TauCeti.ClassFieldTheory.localArtinMap_eq_zero_iff ℚ_[2] L
      (layerEmb L), restrictAb_artinMap L hab, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one, ofMul_one]
    · intro h
      apply hinj
      rw [map_one]
      exact Additive.ofMul.injective h

noncomputable def nuUr : AbsGalQ2ab →* Multiplicative ℤ_[2] :=
  (invMonoidHom : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2]).comp
    ((TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))).toMonoidHom.comp
      (TauCeti.unramifiedCoordinate ℚ_[2]).toMonoidHom)

noncomputable def localReciprocity_tauceti : LocalReciprocity where
  recip := TauCeti.ClassFieldTheory.artinMap ℚ_[2]
  continuous_recip := TauCeti.ClassFieldTheory.continuous_artinMap ℚ_[2]
  denseRange_recip := TauCeti.ClassFieldTheory.denseRange_artinMap ℚ_[2]
  nu_ur := nuUr
  continuous_nu_ur := continuous_inv.comp ((TauCeti.zHat.lift _).continuous.comp
    (TauCeti.unramifiedCoordinate ℚ_[2]).continuous)
  surjective_nu_ur := by
    intro y
    obtain ⟨z, hz⟩ := TauCeti.zHat.component_surjective 2 (-(Multiplicative.toAdd y))
    obtain ⟨x, hx⟩ := TauCeti.unramifiedCoordinate_surjective ℚ_[2] (Additive.toMul z)
    refine ⟨x, ?_⟩
    simp only [nuUr, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass, invMonoidHom_apply, hx, TauCeti.zHat.lift_ofAdd_one_padicInt_apply]
    simp [hz]
  norm_reciprocity := norm_reciprocity_tauceti
  nu_ur_recip := by
    intro x
    simp only [nuUr, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass, TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap,
      TauCeti.zHat.lift_ofInt, invMonoidHom_apply, v2,
      ← Padic.toAdd_normalizedValuation_eq_valuation]
    rw [← ofAdd_zsmul, ← ofAdd_neg]
    simp
  chiCyc_recip_unit := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
      (TauCeti.ClassFieldTheory.artinMap ℚ_[2] (unitEmbed u))
    rw [← hg]
    change chiCycAb (toAb g) = u⁻¹
    rw [chiCycAb_toAb]
    have := TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic 2 u g hg
    rwa [TauCeti.localCyclotomicCharacter_apply] at this
  chiCyc_recip_uniformizer := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
      (TauCeti.ClassFieldTheory.artinMap ℚ_[2] uniformizer)
    rw [← hg]
    change chiCycAb (toAb g) = 1
    rw [chiCycAb_toAb]
    have := TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer 2 g hg
    rwa [TauCeti.localCyclotomicCharacter_apply] at this


-- chosen Frobenius lift and tame generator
noncomputable def sigma0 : Field.absoluteGaloisGroup ℚ_[2] :=
  Classical.choose (TauCeti.exists_isArithFrobeniusLift ℚ_[2])
theorem hsigma0 : TauCeti.IsArithFrobeniusLift ℚ_[2] sigma0 :=
  Classical.choose_spec (TauCeti.exists_isArithFrobeniusLift ℚ_[2])
noncomputable def tau0 : TauCeti.inertiaSubgroup ℚ_[2] :=
  Classical.choose (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2])
theorem htau0 : (Subgroup.zpowers (TauCeti.inertiaTameCharacter ℚ_[2] tau0)).topologicalClosure = ⊤ :=
  Classical.choose_spec (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2])

noncomputable def tameEquiv0 : TauCeti.tameQuotient ℚ_[2] ≃ₜ* TauCeti.IwasawaGroupGeometric ℚ_[2] :=
  TauCeti.tameQuotientGeometricEquiv hsigma0 tau0 htau0

-- the TameQuotientData fields other than `equiv`
example : (TauCeti.wildInertiaSubgroup ℚ_[2] : Subgroup AbsGalQ2).Normal := inferInstance
example : IsClosed (TauCeti.wildInertiaSubgroup ℚ_[2] : Set AbsGalQ2) :=
  TauCeti.isClosed_wildInertiaSubgroup ℚ_[2]
example : GQ2.IsProP 2 (TauCeti.wildInertiaSubgroup ℚ_[2]) :=
  haveI := TauCeti.charP_residueField ℚ_[2] 2
  TauCeti.isProP_iff.mp (TauCeti.isProP_wildInertiaSubgroup ℚ_[2] 2)

/-- `equiv` given any generator-preserving identification `e` of the geometric Iwasawa group with
`Ttame` (constructed below as `iwEquiv`, without the P1 dictionary). -/
noncomputable def equivOf (e : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame) :
    ContinuousMulEquiv (AbsGalQ2 ⧸ TauCeti.wildInertiaSubgroup ℚ_[2]) Ttame :=
  tameEquiv0.trans e

/-- the transported ν_t: `nuT ∘ e = lift (ztwoOne⁻¹) ∘ iwasawaCoordinateGeometric`, i.e. the
INVERSE of the ℤ₂-reduction of Tau Ceti's (arithmetic-normalized) coordinate. -/
theorem nuT_comp (e : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame)
    (he0 : e (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma)
    (he1 : e (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau)
    (x : TauCeti.IwasawaGroupGeometric ℚ_[2]) :
    nuT (e x) = TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2] x) := by
  have key : (nuT.comp (e : TauCeti.IwasawaGroupGeometric ℚ_[2] →ₜ* Ttame)) =
      (TauCeti.zHat.lift ztwoOne⁻¹).comp (TauCeti.iwasawaCoordinateGeometric ℚ_[2]) := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · change nuT (e (TauCeti.iwasawaSigmaGeometric ℚ_[2])) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2]
          (TauCeti.iwasawaSigmaGeometric ℚ_[2]))
      rw [he0, nuT_tameSigma, TauCeti.iwasawaCoordinateGeometric_iwasawaSigmaGeometric, map_inv,
        TauCeti.zHat.lift_gen, inv_inv]
    · change nuT (e (TauCeti.iwasawaTauGeometric ℚ_[2])) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2]
          (TauCeti.iwasawaTauGeometric ℚ_[2]))
      rw [he1, nuT_tameTau, TauCeti.iwasawaCoordinateGeometric_iwasawaTauGeometric, map_one]
  exact DFunLike.congr_fun key x

theorem tameZHat_eq_unramifiedCoordinate (g : AbsGalQ2) :
    TauCeti.tameQuotientToZHat ℚ_[2] (TauCeti.toTameQuotient ℚ_[2] g) =
      TauCeti.unramifiedCoordinate ℚ_[2] (toAb g) := by
  rw [TauCeti.tameQuotientToZHat_toTameQuotient]
  exact (TauCeti.unramifiedCoordinate_mk g).symm

example (g : AbsGalQ2) : (QuotientGroup.mk g : AbsGalQ2 ⧸ TauCeti.wildInertiaSubgroup ℚ_[2]) =
    TauCeti.toTameQuotient ℚ_[2] g := (TauCeti.toTameQuotient_apply g).symm

/-- The two orientation clauses, for any reciprocity datum whose `recip` is Tau Ceti's Artin map. -/
theorem nuT_recip (e : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame)
    (he0 : e (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma)
    (he1 : e (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau)
    (x : ℚ_[2]ˣ) (g : AbsGalQ2) (hg : toAb g = TauCeti.ClassFieldTheory.artinMap ℚ_[2] x) :
    nuT (equivOf e (QuotientGroup.mk g)) = ztwoOne⁻¹ ^ v2 x := by
  rw [equivOf, ContinuousMulEquiv.trans_apply, nuT_comp e he0 he1, tameEquiv0,
    ← TauCeti.toTameQuotient_apply, TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv,
    tameZHat_eq_unramifiedCoordinate, hg, TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap,
    TauCeti.zHat.lift_ofInt, v2, Padic.toAdd_normalizedValuation_eq_valuation]


theorem unit_valuation (u : ℤ_[2]ˣ) : v2 (unitEmbed u) = 0 := by
  have hv : (u : ℤ_[2]).valuation = 0 := by
    have h := PadicInt.valuation_mul (p := 2) u.ne_zero u⁻¹.ne_zero
    rw [Units.mul_inv, PadicInt.valuation_one] at h
    omega
  simp [v2, unitEmbed, hv]

/-- B10 for any generator-preserving `e : IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame`. -/
noncomputable def tameQuotient_tauceti_of (e : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame)
    (he0 : e (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma)
    (he1 : e (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau) :
    OrientedTameQuotient localReciprocity_tauceti where
  W := TauCeti.wildInertiaSubgroup ℚ_[2]
  normal := TauCeti.wildInertiaSubgroup_normal ℚ_[2]
  isClosed := TauCeti.isClosed_wildInertiaSubgroup ℚ_[2]
  isProP :=
    haveI := TauCeti.charP_residueField ℚ_[2] 2
    TauCeti.isProP_iff.mp (TauCeti.isProP_wildInertiaSubgroup ℚ_[2] 2)
  equiv := equivOf e
  nuT_recip_unit u g hg := by
    rw [nuT_recip e he0 he1 _ g hg, unit_valuation, zpow_zero]
  nuT_recip_uniformizer g hg := by
    rw [nuT_recip e he0 he1 _ g hg]
    simp [v2, uniformizer]


/-- Forward map: geometric Iwasawa group → gq2 `Ttame`, `γ ↦ σ`, `τ ↦ τ`. -/
noncomputable def iwFwd : TauCeti.IwasawaGroupGeometric ℚ_[2] →ₜ* Ttame :=
  TauCeti.presentedProfiniteGroup.lift
    (TauCeti.freeProfiniteGroup.lift fun i : ULift.{0} (Fin 2) => ![tameSigma, tameTau] i.down)
    (by
      rintro r rfl
      rw [TauCeti.iwasawaRelatorGeometric_def, Padic.natCard_residueField]
      simp only [map_mul, map_inv, map_pow, TauCeti.freeProfiniteGroup.lift_of]
      have h := tame_relation
      simp only [conjP] at h
      simp [h])

theorem iwFwd_sigma : iwFwd (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma := by
  simp [iwFwd, TauCeti.presentedProfiniteGroup.lift_of, TauCeti.freeProfiniteGroup.lift_of]

theorem iwFwd_tau : iwFwd (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau := by
  simp [iwFwd, TauCeti.presentedProfiniteGroup.lift_of, TauCeti.freeProfiniteGroup.lift_of]

noncomputable def IwG : ProfiniteGrp.{0} := ProfiniteGrp.of (TauCeti.IwasawaGroupGeometric ℚ_[2])

noncomputable def iwBwdBase : FreeProfiniteGroup (Fin 2) ⟶ IwG :=
  (FreeProfiniteGroup.homEquiv (Fin 2) IwG).symm
    ![TauCeti.iwasawaSigmaGeometric ℚ_[2], TauCeti.iwasawaTauGeometric ℚ_[2]]

theorem iwBwdBase_tameWord : iwBwdBase.hom.toMonoidHom tameWord = 1 := by
  have h0 : iwBwdBase.hom.toMonoidHom (FreeProfiniteGroup.of 0) =
      TauCeti.iwasawaSigmaGeometric ℚ_[2] := FreeProfiniteGroup.homEquiv_symm_of _ _ _
  have h1 : iwBwdBase.hom.toMonoidHom (FreeProfiniteGroup.of 1) =
      TauCeti.iwasawaTauGeometric ℚ_[2] := FreeProfiniteGroup.homEquiv_symm_of _ _ _
  have hrel := TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul ℚ_[2]
  rw [Padic.natCard_residueField] at hrel
  rw [tameWord, conjP]
  simp only [map_mul, map_inv, map_pow, h0, h1]
  change (TauCeti.iwasawaSigmaGeometric ℚ_[2])⁻¹ * TauCeti.iwasawaTauGeometric ℚ_[2] *
    TauCeti.iwasawaSigmaGeometric ℚ_[2] * (TauCeti.iwasawaTauGeometric ℚ_[2] ^ 2)⁻¹ = 1
  rw [hrel]
  exact mul_inv_cancel _

noncomputable def iwBwd : ContinuousMonoidHom Ttame (TauCeti.IwasawaGroupGeometric ℚ_[2]) :=
  presentationLift {tameWord} iwBwdBase.hom fun r hr => by
    rcases hr with rfl
    exact iwBwdBase_tameWord

theorem iwBwd_sigma : iwBwd tameSigma = TauCeti.iwasawaSigmaGeometric ℚ_[2] := by
  show iwBwd (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 0)) = _
  exact (presentationLift_mk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

theorem iwBwd_tau : iwBwd tameTau = TauCeti.iwasawaTauGeometric ℚ_[2] := by
  show iwBwd (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 1)) = _
  exact (presentationLift_mk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

theorem iwFwd_iwBwd (x : Ttame) : iwFwd (iwBwd x) = x := by
  -- maps out of `Ttame` are determined on generators: pull back to the free profinite group
  obtain ⟨w, rfl⟩ := quotientMk_surjective (relatorSubgroup {tameWord}) x
  let f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) Ttame :=
    (iwFwd.comp iwBwd).comp (quotientMk (relatorSubgroup {tameWord}))
  let g : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) Ttame :=
    quotientMk (relatorSubgroup {tameWord})
  have hfg : (CategoryTheory.ConcreteCategory.ofHom f : FreeProfiniteGroup (Fin 2) ⟶ Ttame) =
      CategoryTheory.ConcreteCategory.ofHom g := by
    apply (FreeProfiniteGroup.homEquiv (Fin 2) Ttame).injective
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]
    fin_cases i
    · change iwFwd (iwBwd tameSigma) = tameSigma
      rw [iwBwd_sigma, iwFwd_sigma]
    · change iwFwd (iwBwd tameTau) = tameTau
      rw [iwBwd_tau, iwFwd_tau]
  exact DFunLike.congr_fun (congrArg ProfiniteGrp.Hom.hom hfg) w

theorem iwBwd_iwFwd (x : TauCeti.IwasawaGroupGeometric ℚ_[2]) : iwBwd (iwFwd x) = x := by
  have h : iwBwd.comp iwFwd = ContinuousMonoidHom.id _ := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · exact (congrArg iwBwd iwFwd_sigma).trans iwBwd_sigma
    · exact (congrArg iwBwd iwFwd_tau).trans iwBwd_tau
  exact DFunLike.congr_fun h x

noncomputable def iwEquiv : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame where
  toFun := iwFwd
  invFun := iwBwd
  left_inv := iwBwd_iwFwd
  right_inv := iwFwd_iwBwd
  map_mul' := map_mul iwFwd
  continuous_toFun := iwFwd.continuous
  continuous_invFun := iwBwd.continuous


/-- B10, complete. -/
noncomputable def tameQuotient_tauceti : OrientedTameQuotient localReciprocity_tauceti :=
  tameQuotient_tauceti_of iwEquiv iwFwd_sigma iwFwd_tau

#print axioms localReciprocity_tauceti
#print axioms tameQuotient_tauceti
