/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.NumberTheory.LocalField.Tame.Geometric
public import GQ2.TameQuotient
public import GQ2.TauCeti.B5

@[expose] public section

/-!
# B10: the oriented tame quotient, discharged from Tau Ceti

Ticket **B10** of the Tau Ceti discharge campaign
(`docs/orchestration/tauceti-tickets.md`, memo `docs/orchestration/tauceti-t2-recon.md`, §B10).
This file provides

* `GQ2.TauCetiBridge.tameQuotient_tauceti : GQ2.OrientedTameQuotient localReciprocity_tauceti`,
  a term of the type of the `tameQuotient` field of `GQ2.LiteratureInputs` (with the reciprocity
  datum the B5 bundle `localReciprocity_tauceti`), built from Tau Ceti's wild inertia, tame
  quotient and geometric Iwasawa presentation for `ℚ₂`, with no `sorry` and at the standard
  three axioms;
* the pieces it is assembled from, for the assembly ticket C1 and later consumers:
  `wildInertiaSubgroup_isProP_two` (gq2's `IsProP 2` for Tau Ceti's wild inertia),
  the identification `iwasawaGeometricEquivTtame : IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame` with
  its `@[simp]` values on the generators, `nuT_iwasawaGeometricToTtame` (gq2's `ν_t` along it),
  the chosen Frobenius lift `arithFrobeniusLift` and tame generator `tameGenerator`, the B10
  `equiv` as `tameQuotientEquivTtame`, and the lift lemma
  `nuT_tameQuotientEquivTtame_mk_of_toAb_eq_artinMap` (`ν_t(equiv g) = ztwoOne⁻¹ ^ v₂ x` for any
  lift `g` of `artinMap x`) from which both orientation clauses follow.

## Translation (memo §B10, with its corrections)

* `W := TauCeti.wildInertiaSubgroup ℚ_[2]`; normality and closedness are Tau Ceti's instance and
  theorem. `AbsGalQ2 ⧸ W` is `TauCeti.tameQuotient ℚ_[2]` (an `abbrev`), and
  `QuotientGroup.mk g = toTameQuotient ℚ_[2] g` is `toTameQuotient_apply`.
* `isProP`: `isProP_wildInertiaSubgroup ℚ_[2] 2` needs `CharP 𝓀[ℚ_[2]] 2`, which does not
  synthesize; it is supplied as `TauCeti.charP_residueField ℚ_[2] 2`. Tau Ceti's `IsProP` is not
  exposed, so `isProP_iff.mp` (not `Iff.rfl`) lands in gq2's `IsProP`.
* `equiv := tameQuotientGeometricEquiv hσ τ hτ` (for a chosen arithmetic Frobenius lift `σ` and
  tame generator `τ`, from `exists_isArithFrobeniusLift` and
  `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`), followed by
  `iwasawaGeometricEquivTtame`, which is built here directly from the two universal properties
  (no P1 dictionary): forward through `presentedProfiniteGroup.lift`, backward through gq2's
  `presentationLift`, with inverse laws from `presentedProfiniteGroup.hom_ext_of` and
  `FreeProfiniteGroup.homEquiv`. **The relators match**: both are `γ⁻¹τγ(τ^q)⁻¹` with
  `q = Nat.card 𝓀[ℚ_[2]] = 2` (`Padic.natCard_residueField`); gq2's `tameSigma` is geometric
  Frobenius, as is Tau Ceti's `iwasawaSigmaGeometric`.
* **The sign of `ν_t`.** `nuT ∘ iwasawaGeometricEquivTtame = zHat.lift ztwoOne⁻¹ ∘ iwasawaCoordinateGeometric`:
  `nuT tameSigma = ztwoOne` while the geometric generator has (arithmetic) coordinate
  `zHat.gen⁻¹`, so `ν_t` is the **inverse** of the `ℤ₂`-reduction `gen ↦ ztwoOne`.
* **Both orientation clauses from one lemma.** For any lift `g` of `artinMap ℚ_[2] x`,
  `ν_t(equiv (mk g)) = ztwoOne⁻¹ ^ v₂ x`, by the chain
  `iwasawaCoordinateGeometric_tameQuotientGeometricEquiv` → `tameQuotientToZHat_toTameQuotient`
  = `unramifiedCoordinate_mk` → B5's `zHat_lift_unramifiedCoordinate_artinMap`. At `unitEmbed u`
  the valuation is `0` (`v2_unitEmbed`), at `uniformizer` it is `1` (`v2_uniformizer`); `rec 2`
  is arithmetic Frobenius, which is why the uniformizer lands at `ztwoOne⁻¹`. Tau Ceti's
  `tameQuotientGeometricEquiv_toTameQuotient_frobenius` is not used: it covers only the chosen
  `σ`, not an arbitrary lift.
* The hypotheses `toAb g = localReciprocity_tauceti.recip x` of the clauses are read through
  B5's `@[expose]`d bundle (`localReciprocity_tauceti_recip`).

This file needs B5 only; none of the Wave 1 dictionaries (A1 beyond what B5 imports, A2, P1).
-/

namespace GQ2.TauCetiBridge

/-! ## Wild inertia is pro-2 -/

/-- Tau Ceti's wild inertia subgroup of `G_{ℚ₂}` is pro-2 in gq2's sense (`GQ2.IsProP`), from
`isProP_wildInertiaSubgroup` with `CharP 𝓀[ℚ_[2]] 2` supplied by `charP_residueField`. -/
theorem wildInertiaSubgroup_isProP_two : IsProP 2 (TauCeti.wildInertiaSubgroup ℚ_[2]) :=
  haveI := TauCeti.charP_residueField ℚ_[2] 2
  TauCeti.isProP_iff.mp (TauCeti.isProP_wildInertiaSubgroup ℚ_[2] 2)

/-! ## The geometric Iwasawa group of `ℚ₂` is `Ttame`

Tau Ceti's `IwasawaGroupGeometric ℚ_[2]` is `⟨γ, τ ∣ γ⁻¹τγ = τ^q⟩_prof` on `ULift (Fin 2)` with
`q = Nat.card 𝓀[ℚ_[2]] = 2`; gq2's `Ttame` is `⟨σ, τ ∣ σ⁻¹τσ = τ²⟩_prof` on `Fin 2`. The
generator-preserving identification is assembled from the two universal properties. -/

/-- `IwasawaGroupGeometric ℚ_[2] →ₜ* Ttame`, `γ ↦ tameSigma`, `τ ↦ tameTau`. The relator
`γ⁻¹τγ(τ^q)⁻¹` is killed by gq2's `tame_relation` once `q = 2` is rewritten. -/
noncomputable def iwasawaGeometricToTtame : TauCeti.IwasawaGroupGeometric ℚ_[2] →ₜ* Ttame :=
  TauCeti.presentedProfiniteGroup.lift
    (TauCeti.freeProfiniteGroup.lift fun i : ULift.{0} (Fin 2) => ![tameSigma, tameTau] i.down)
    (by
      rintro r rfl
      rw [TauCeti.iwasawaRelatorGeometric_def, Padic.natCard_residueField]
      simp only [map_mul, map_inv, map_pow, TauCeti.freeProfiniteGroup.lift_of]
      have h := tame_relation
      simp only [conjP] at h
      simp [h])

@[simp]
theorem iwasawaGeometricToTtame_iwasawaSigmaGeometric :
    iwasawaGeometricToTtame (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma := by
  simp [iwasawaGeometricToTtame, TauCeti.presentedProfiniteGroup.lift_of,
    TauCeti.freeProfiniteGroup.lift_of]

@[simp]
theorem iwasawaGeometricToTtame_iwasawaTauGeometric :
    iwasawaGeometricToTtame (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau := by
  simp [iwasawaGeometricToTtame, TauCeti.presentedProfiniteGroup.lift_of,
    TauCeti.freeProfiniteGroup.lift_of]

/-- Tau Ceti's geometric Iwasawa group of `ℚ₂` as a gq2 `ProfiniteGrp` object (the target of
`FreeProfiniteGroup.homEquiv`). A `def`, not an `abbrev`: `simp` must not unfold the carrier, or
the generator lemmas below stop matching. -/
noncomputable def iwasawaGeometricGrp : ProfiniteGrp.{0} :=
  ProfiniteGrp.of (TauCeti.IwasawaGroupGeometric ℚ_[2])

/-- The hom `FreeProfiniteGroup (Fin 2) ⟶ IwasawaGroupGeometric ℚ_[2]`, `of 0 ↦ γ`, `of 1 ↦ τ`. -/
noncomputable def freeToIwasawaGeometric : FreeProfiniteGroup (Fin 2) ⟶ iwasawaGeometricGrp :=
  (FreeProfiniteGroup.homEquiv (Fin 2) iwasawaGeometricGrp).symm
    ![TauCeti.iwasawaSigmaGeometric ℚ_[2], TauCeti.iwasawaTauGeometric ℚ_[2]]

@[simp]
theorem freeToIwasawaGeometric_of_zero :
    freeToIwasawaGeometric.hom (FreeProfiniteGroup.of 0) = TauCeti.iwasawaSigmaGeometric ℚ_[2] :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp]
theorem freeToIwasawaGeometric_of_one :
    freeToIwasawaGeometric.hom (FreeProfiniteGroup.of 1) = TauCeti.iwasawaTauGeometric ℚ_[2] :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- gq2's tame relator `σ⁻¹τσ(τ²)⁻¹` dies in the geometric Iwasawa group: it is Tau Ceti's
relation `inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` at `q = 2`. -/
theorem freeToIwasawaGeometric_tameWord : freeToIwasawaGeometric.hom tameWord = 1 := by
  have hrel := TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul ℚ_[2]
  rw [Padic.natCard_residueField] at hrel
  rw [tameWord, conjP]
  simp only [map_mul, map_inv, map_pow, freeToIwasawaGeometric_of_zero,
    freeToIwasawaGeometric_of_one]
  change (TauCeti.iwasawaSigmaGeometric ℚ_[2])⁻¹ * TauCeti.iwasawaTauGeometric ℚ_[2] *
    TauCeti.iwasawaSigmaGeometric ℚ_[2] * (TauCeti.iwasawaTauGeometric ℚ_[2] ^ 2)⁻¹ = 1
  rw [hrel]
  exact mul_inv_cancel _

/-- `Ttame →ₜ* IwasawaGroupGeometric ℚ_[2]`, `tameSigma ↦ γ`, `tameTau ↦ τ`. -/
noncomputable def ttameToIwasawaGeometric :
    ContinuousMonoidHom Ttame (TauCeti.IwasawaGroupGeometric ℚ_[2]) :=
  presentationLift {tameWord} freeToIwasawaGeometric.hom fun r hr => by
    rcases hr with rfl
    exact freeToIwasawaGeometric_tameWord

@[simp]
theorem ttameToIwasawaGeometric_tameSigma :
    ttameToIwasawaGeometric tameSigma = TauCeti.iwasawaSigmaGeometric ℚ_[2] := by
  show ttameToIwasawaGeometric (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 0)) = _
  exact (presentationLift_mk _ _ _ _).trans freeToIwasawaGeometric_of_zero

@[simp]
theorem ttameToIwasawaGeometric_tameTau :
    ttameToIwasawaGeometric tameTau = TauCeti.iwasawaTauGeometric ℚ_[2] := by
  show ttameToIwasawaGeometric (quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 1)) = _
  exact (presentationLift_mk _ _ _ _).trans freeToIwasawaGeometric_of_one

theorem iwasawaGeometricToTtame_ttameToIwasawaGeometric (x : Ttame) :
    iwasawaGeometricToTtame (ttameToIwasawaGeometric x) = x := by
  -- maps out of `Ttame` are determined on generators: pull back to the free profinite group
  obtain ⟨w, rfl⟩ := quotientMk_surjective (relatorSubgroup {tameWord}) x
  let f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) Ttame :=
    (iwasawaGeometricToTtame.comp ttameToIwasawaGeometric).comp
      (quotientMk (relatorSubgroup {tameWord}))
  let g : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) Ttame :=
    quotientMk (relatorSubgroup {tameWord})
  have hfg : (CategoryTheory.ConcreteCategory.ofHom f : FreeProfiniteGroup (Fin 2) ⟶ Ttame) =
      CategoryTheory.ConcreteCategory.ofHom g := by
    apply (FreeProfiniteGroup.homEquiv (Fin 2) Ttame).injective
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]
    fin_cases i
    · change iwasawaGeometricToTtame (ttameToIwasawaGeometric tameSigma) = tameSigma
      rw [ttameToIwasawaGeometric_tameSigma, iwasawaGeometricToTtame_iwasawaSigmaGeometric]
    · change iwasawaGeometricToTtame (ttameToIwasawaGeometric tameTau) = tameTau
      rw [ttameToIwasawaGeometric_tameTau, iwasawaGeometricToTtame_iwasawaTauGeometric]
  exact DFunLike.congr_fun (congrArg ProfiniteGrp.Hom.hom hfg) w

theorem ttameToIwasawaGeometric_iwasawaGeometricToTtame (x : TauCeti.IwasawaGroupGeometric ℚ_[2]) :
    ttameToIwasawaGeometric (iwasawaGeometricToTtame x) = x := by
  have h : ttameToIwasawaGeometric.comp iwasawaGeometricToTtame = ContinuousMonoidHom.id _ := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · exact (congrArg ttameToIwasawaGeometric iwasawaGeometricToTtame_iwasawaSigmaGeometric).trans
        ttameToIwasawaGeometric_tameSigma
    · exact (congrArg ttameToIwasawaGeometric iwasawaGeometricToTtame_iwasawaTauGeometric).trans
        ttameToIwasawaGeometric_tameTau
  exact DFunLike.congr_fun h x

/-- **Tau Ceti's geometric Iwasawa group of `ℚ₂` is gq2's `Ttame`**, generators to generators:
`γ ↦ tameSigma` (both geometric Frobenius), `τ ↦ tameTau`. -/
noncomputable def iwasawaGeometricEquivTtame : TauCeti.IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame where
  toFun := iwasawaGeometricToTtame
  invFun := ttameToIwasawaGeometric
  left_inv := ttameToIwasawaGeometric_iwasawaGeometricToTtame
  right_inv := iwasawaGeometricToTtame_ttameToIwasawaGeometric
  map_mul' := map_mul iwasawaGeometricToTtame
  continuous_toFun := iwasawaGeometricToTtame.continuous
  continuous_invFun := ttameToIwasawaGeometric.continuous

@[simp]
theorem iwasawaGeometricEquivTtame_apply (x : TauCeti.IwasawaGroupGeometric ℚ_[2]) :
    iwasawaGeometricEquivTtame x = iwasawaGeometricToTtame x := rfl

@[simp]
theorem iwasawaGeometricEquivTtame_symm_apply (x : Ttame) :
    iwasawaGeometricEquivTtame.symm x = ttameToIwasawaGeometric x := rfl

theorem iwasawaGeometricEquivTtame_iwasawaSigmaGeometric :
    iwasawaGeometricEquivTtame (TauCeti.iwasawaSigmaGeometric ℚ_[2]) = tameSigma :=
  iwasawaGeometricToTtame_iwasawaSigmaGeometric

theorem iwasawaGeometricEquivTtame_iwasawaTauGeometric :
    iwasawaGeometricEquivTtame (TauCeti.iwasawaTauGeometric ℚ_[2]) = tameTau :=
  iwasawaGeometricToTtame_iwasawaTauGeometric

theorem iwasawaGeometricEquivTtame_symm_tameSigma :
    iwasawaGeometricEquivTtame.symm tameSigma = TauCeti.iwasawaSigmaGeometric ℚ_[2] :=
  ttameToIwasawaGeometric_tameSigma

theorem iwasawaGeometricEquivTtame_symm_tameTau :
    iwasawaGeometricEquivTtame.symm tameTau = TauCeti.iwasawaTauGeometric ℚ_[2] :=
  ttameToIwasawaGeometric_tameTau

/-! ## `ν_t` along the identification -/

/-- **The sign of `ν_t`.** gq2's `nuT` after `iwasawaGeometricToTtame` is the `ℤ̂`-lift
`gen ↦ ztwoOne⁻¹` of Tau Ceti's (arithmetically normalized) `iwasawaCoordinateGeometric`: the
**inverse** of the `ℤ₂`-reduction along `gen ↦ ztwoOne`, because `nuT tameSigma = ztwoOne` while
the geometric generator has coordinate `zHat.gen⁻¹`. -/
theorem nuT_iwasawaGeometricToTtame (x : TauCeti.IwasawaGroupGeometric ℚ_[2]) :
    nuT (iwasawaGeometricToTtame x) =
      TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2] x) := by
  have key : nuT.comp iwasawaGeometricToTtame =
      (TauCeti.zHat.lift ztwoOne⁻¹).comp (TauCeti.iwasawaCoordinateGeometric ℚ_[2]) := by
    apply TauCeti.presentedProfiniteGroup.hom_ext_of
    rintro ⟨i⟩
    fin_cases i
    · change nuT (iwasawaGeometricToTtame (TauCeti.iwasawaSigmaGeometric ℚ_[2])) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2]
          (TauCeti.iwasawaSigmaGeometric ℚ_[2]))
      rw [iwasawaGeometricToTtame_iwasawaSigmaGeometric, nuT_tameSigma,
        TauCeti.iwasawaCoordinateGeometric_iwasawaSigmaGeometric, map_inv,
        TauCeti.zHat.lift_gen, inv_inv]
    · change nuT (iwasawaGeometricToTtame (TauCeti.iwasawaTauGeometric ℚ_[2])) =
        TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.iwasawaCoordinateGeometric ℚ_[2]
          (TauCeti.iwasawaTauGeometric ℚ_[2]))
      rw [iwasawaGeometricToTtame_iwasawaTauGeometric, nuT_tameTau,
        TauCeti.iwasawaCoordinateGeometric_iwasawaTauGeometric, map_one]
  exact DFunLike.congr_fun key x

/-! ## The chosen Frobenius lift and tame generator, and the B10 `equiv` -/

/-- A chosen arithmetic Frobenius lift in `G_{ℚ₂}` (`TauCeti.exists_isArithFrobeniusLift`). -/
noncomputable def arithFrobeniusLift : Field.absoluteGaloisGroup ℚ_[2] :=
  Classical.choose (TauCeti.exists_isArithFrobeniusLift ℚ_[2])

theorem isArithFrobeniusLift_arithFrobeniusLift :
    TauCeti.IsArithFrobeniusLift ℚ_[2] arithFrobeniusLift :=
  Classical.choose_spec (TauCeti.exists_isArithFrobeniusLift ℚ_[2])

/-- A chosen inertia element whose tame character topologically generates `ℤ̂^{(2')}(1)`
(`TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`). -/
noncomputable def tameGenerator : TauCeti.inertiaSubgroup ℚ_[2] :=
  Classical.choose (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2])

theorem topologicalClosure_zpowers_inertiaTameCharacter_tameGenerator :
    (Subgroup.zpowers (TauCeti.inertiaTameCharacter ℚ_[2] tameGenerator)).topologicalClosure =
      ⊤ :=
  Classical.choose_spec
    (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2])

/-- Tau Ceti's identification of the tame quotient `G_{ℚ₂}/W` with the geometric Iwasawa group,
marked by `arithFrobeniusLift` and `tameGenerator`. -/
noncomputable def tameQuotientEquivIwasawaGeometric :
    TauCeti.tameQuotient ℚ_[2] ≃ₜ* TauCeti.IwasawaGroupGeometric ℚ_[2] :=
  TauCeti.tameQuotientGeometricEquiv isArithFrobeniusLift_arithFrobeniusLift tameGenerator
    topologicalClosure_zpowers_inertiaTameCharacter_tameGenerator

@[simp]
theorem iwasawaCoordinateGeometric_tameQuotientEquivIwasawaGeometric (x : TauCeti.tameQuotient ℚ_[2]) :
    TauCeti.iwasawaCoordinateGeometric ℚ_[2] (tameQuotientEquivIwasawaGeometric x) =
      TauCeti.tameQuotientToZHat ℚ_[2] x :=
  TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv _ _ _ x

/-- Tau Ceti's `ℤ̂`-coordinate of the tame quotient, on the class of `g`, is the unramified
coordinate of `g`'s abelianized class (both are `restrictMaximalUnramifiedHom` read in `ℤ̂`). -/
theorem tameQuotientToZHat_toTameQuotient_eq_unramifiedCoordinate (g : AbsGalQ2) :
    TauCeti.tameQuotientToZHat ℚ_[2] (TauCeti.toTameQuotient ℚ_[2] g) =
      TauCeti.unramifiedCoordinate ℚ_[2] (toAb g) := by
  rw [TauCeti.tameQuotientToZHat_toTameQuotient]
  exact (TauCeti.unramifiedCoordinate_mk g).symm

/-- **The B10 `equiv`**: `G_{ℚ₂}/W ≅ Ttame`, Tau Ceti's marked identification with the geometric
Iwasawa group followed by `iwasawaGeometricEquivTtame`. -/
noncomputable def tameQuotientEquivTtame :
    ContinuousMulEquiv (AbsGalQ2 ⧸ TauCeti.wildInertiaSubgroup ℚ_[2]) Ttame :=
  tameQuotientEquivIwasawaGeometric.trans iwasawaGeometricEquivTtame

/-- `ν_t` of the class of `g` in `Ttame` is the `gen ↦ ztwoOne⁻¹` lift of the unramified
coordinate of `g`. -/
theorem nuT_tameQuotientEquivTtame_mk (g : AbsGalQ2) :
    nuT (tameQuotientEquivTtame (QuotientGroup.mk g)) =
      TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.unramifiedCoordinate ℚ_[2] (toAb g)) := by
  rw [tameQuotientEquivTtame, ContinuousMulEquiv.trans_apply, iwasawaGeometricEquivTtame_apply,
    nuT_iwasawaGeometricToTtame, ← TauCeti.toTameQuotient_apply,
    iwasawaCoordinateGeometric_tameQuotientEquivIwasawaGeometric,
    tameQuotientToZHat_toTameQuotient_eq_unramifiedCoordinate]

/-- **The lemma behind both orientation clauses.** For any lift `g ∈ G_{ℚ₂}` of the Artin image
of `x`, `ν_t(equiv (mk g)) = ztwoOne⁻¹ ^ v₂ x`: units land at `1`, the uniformizer (arithmetic
Frobenius) at the geometric-Frobenius coordinate `ztwoOne⁻¹`. -/
theorem nuT_tameQuotientEquivTtame_mk_of_toAb_eq_artinMap (x : ℚ_[2]ˣ) (g : AbsGalQ2)
    (hg : toAb g = TauCeti.ClassFieldTheory.artinMap ℚ_[2] x) :
    nuT (tameQuotientEquivTtame (QuotientGroup.mk g)) = ztwoOne⁻¹ ^ v2 x := by
  rw [nuT_tameQuotientEquivTtame_mk, hg, zHat_lift_unramifiedCoordinate_artinMap]

/-! ## The bundle -/

/-- **B10, discharged.** gq2's oriented tame quotient of `G_{ℚ₂}` for the B5 reciprocity datum
`localReciprocity_tauceti`: `W` is Tau Ceti's wild inertia, `equiv` is `tameQuotientEquivTtame`,
and the orientation clauses are `nuT_tameQuotientEquivTtame_mk_of_toAb_eq_artinMap` at
`v₂ = 0` (units) and `v₂ = 1` (uniformizer). -/
noncomputable def tameQuotient_tauceti : OrientedTameQuotient localReciprocity_tauceti where
  W := TauCeti.wildInertiaSubgroup ℚ_[2]
  normal := TauCeti.wildInertiaSubgroup_normal ℚ_[2]
  isClosed := TauCeti.isClosed_wildInertiaSubgroup ℚ_[2]
  isProP := wildInertiaSubgroup_isProP_two
  equiv := tameQuotientEquivTtame
  nuT_recip_unit u g hg := by
    rw [nuT_tameQuotientEquivTtame_mk_of_toAb_eq_artinMap _ g hg, v2_unitEmbed, zpow_zero]
  nuT_recip_uniformizer g hg := by
    rw [nuT_tameQuotientEquivTtame_mk_of_toAb_eq_artinMap _ g hg, v2_uniformizer, zpow_one]

@[simp]
theorem tameQuotient_tauceti_W : tameQuotient_tauceti.W = TauCeti.wildInertiaSubgroup ℚ_[2] := rfl

@[simp]
theorem tameQuotient_tauceti_equiv : tameQuotient_tauceti.equiv = tameQuotientEquivTtame := rfl

end GQ2.TauCetiBridge
