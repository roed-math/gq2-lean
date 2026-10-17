/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import GQ2.TauCeti.B5K
public import GQ2.TauCeti.B10
public import GQ2.Dyadic.OrientedTameBundle
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section

/-!
# B10-K: the oriented tame quotient at a finite `K/ℚ₂`, discharged from Tau Ceti

Ticket **B10-K** of the dyadic Tau Ceti discharge campaign
(`docs/dyadic/tauceti-discharge-tickets.md`, memo `docs/dyadic/tauceti-discharge-recon.md`,
§B10-K; prototype `docs/dyadic/tauceti-t2-evidence/tameK/b10k.lean`, assembled in
`full/b5k_b10k.lean`).  This file provides

* `GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti K FF :
  Dyadic.OrientedTameQuotientK (markedRecipAt_tauceti K) FF`, for every finite
  `K : IntermediateField ℚ_[2] ℚ̄₂` and dyadic unit filtration `FF`, a term of the type of the
  census axiom `GQ2.orientedTameQuotientAt K FF` with B5-K's `markedRecipAt_tauceti K` in place of
  `markedRecipAt K`, built from Tau Ceti's wild inertia, tame quotient and geometric Iwasawa
  presentation at `↥K`, with no `sorry` and at the standard three axioms;
* `orientedTameQuotientOfRecip B hB FF`, the same bundle for any `B : MarkedRecip R K` whose
  `recip` is `recipK K`;
* the generic identification `iwasawaGeometricEquivTq L q hq : IwasawaGroupGeometric L ≃ₜ* Tq q`
  for any local field `L` with `#𝓀[L] = q` (B10's `iwasawaGeometricEquivTtame` with `q` a
  parameter), and the lift lemma `nuTq_tameEquivK_mk` from which both orientation clauses follow.

## Translation (memo §B10-K)

Here `absGalEquivGalK K := (absGalEquivFixing K).trans (galKEquiv K).symm : G_{↥K} ≃ₜ* GalK K`.

* `W := wildInertiaK K`, Tau Ceti's wild inertia of `↥K` mapped along `absGalEquivGalK K`;
  normality, closedness and the pro-2 property are transported from Tau Ceti's.  `isProP` needs
  `CharP 𝓀[↥K] 2`, supplied as `TauCeti.charP_residueField K 2` once `valuativeExtension K` is in
  context.
* `equiv := tameEquivK K FF`: `quotientCongr` along `absGalEquivGalK K`, then Tau Ceti's
  `tameQuotientGeometricEquiv` for a chosen arithmetic Frobenius lift and tame generator, then
  `iwasawaGeometricEquivTq ↥K (qOf K FF) hq`.  Tau Ceti's relator is at `Nat.card 𝓀[↥K]` and
  gq2's at `qOf K FF = 2 ^ FF.f`; they are bridged by A1-K's `natCard_residueField_eq_two_pow`
  through the hypothesis `hq`, with no cast on `Tq`.
* **Both orientation clauses from one lemma.** For any lift `g ∈ G_K` of `rec_K x`,
  `ν_t(equiv (mk g)) = ztwoOne⁻¹ ^ v_K(x)` (`nuTq_tameEquivK_mk`); `v_K(u) = 0` for a norm-one
  unit and `v_K(uniformizerK K FF) = 1` by A1-K's normalized-valuation lemmas.  The sign comes from
  `nuTq_iwasawaGeometricToTq`: `ν_t` is the inverse of the `ℤ₂`-reduction `gen ↦ ztwoOne` of Tau
  Ceti's arithmetic coordinate, as at `ℚ₂`.
* The hypotheses `toAbK K g = (markedRecipAt_tauceti K).recip x` are read through B5-K's exported
  equation `markedRecipAt_tauceti_recip_apply`.

This file needs B5-K (for `recipK` and the bundle), A1-K (bridge and residue count) and the
Tau Ceti imports of B10; it does not need the pro-`p` dictionary P1.
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel GQ2.Dyadic

/-! ## The geometric Iwasawa group of a local field `L` with `#𝓀[L] = q` is `Tq q`

Tau Ceti's `IwasawaGroupGeometric L` is `⟨γ, τ ∣ γ⁻¹τγ = τ^{#𝓀[L]}⟩_prof` on `ULift (Fin 2)`;
gq2's `Tq q` is `⟨σ, τ ∣ σ⁻¹τσ = τ^q⟩_prof` on `Fin 2`.  Given `hq : #𝓀[L] = q`, the
generator-preserving identification is assembled from the two universal properties, exactly as
B10's `iwasawaGeometricEquivTtame` (which is the case `L = ℚ₂`, `q = 2`). -/

section Generic

variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  (q : ℕ) (hq : Nat.card (IsLocalRing.ResidueField (valuation L).integer) = q)

/-- `IwasawaGroupGeometric L →ₜ* Tq q`, `γ ↦ tqSigma q`, `τ ↦ tqTau q`, by Tau Ceti's
`presentedProfiniteGroup.lift`
(`TauCeti/Topology/Algebra/Group/Profinite/Presentation/Basic.lean:166`) and
`freeProfiniteGroup.lift` (`…/Profinite/Free/Basic.lean:124`).  The relator
`γ⁻¹τγ(τ^{#𝓀[L]})⁻¹` (`iwasawaRelatorGeometric_def`,
`TauCeti/NumberTheory/LocalField/Tame/Geometric.lean:53`) is killed by gq2's `tame_relation_q`
once `hq` is rewritten. -/
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

/-- Tau Ceti's geometric Iwasawa group of `L` as a gq2 `ProfiniteGrp` object (the target of
`FreeProfiniteGroup.homEquiv`); a `def`, as B10's `iwasawaGeometricGrp`. -/
def iwasawaGeometricGrpL : ProfiniteGrp.{0} := ProfiniteGrp.of (TauCeti.IwasawaGroupGeometric L)

/-- The hom `FreeProfiniteGroup (Fin 2) ⟶ IwasawaGroupGeometric L`, `of 0 ↦ γ`, `of 1 ↦ τ`. -/
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
/-- gq2's relator `tameWordQ q` dies in the geometric Iwasawa group: Tau Ceti's relation
`inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` (`Tame/Geometric.lean:160`) at
`#𝓀[L] = q`. -/
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

/-- `Tq q →ₜ* IwasawaGroupGeometric L`, `tqSigma q ↦ γ`, `tqTau q ↦ τ` (gq2's
`presentationLift`). -/
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
  -- maps out of `Tq q` are determined on generators: pull back to the free profinite group
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

/-- **The geometric Iwasawa group of `L` is gq2's `Tq q`** (`q = #𝓀[L]`), generators to
generators: `γ ↦ tqSigma q` (both geometric Frobenius), `τ ↦ tqTau q`.  Inverse laws from Tau
Ceti's `presentedProfiniteGroup.hom_ext_of` (`Presentation/Basic.lean:214`) and gq2's
`FreeProfiniteGroup.homEquiv`. -/
def iwasawaGeometricEquivTq : TauCeti.IwasawaGroupGeometric L ≃ₜ* Tq q where
  toFun := iwasawaGeometricToTq L q hq
  invFun := tqToIwasawaGeometric L q hq
  left_inv := tqToIwasawaGeometric_iwasawaGeometricToTq L q hq
  right_inv := iwasawaGeometricToTq_tqToIwasawaGeometric L q hq
  map_mul' := map_mul (iwasawaGeometricToTq L q hq)
  continuous_toFun := (iwasawaGeometricToTq L q hq).continuous
  continuous_invFun := (tqToIwasawaGeometric L q hq).continuous

/-- **The sign of `ν_t` at general `q`.** gq2's `nuTq q` after `iwasawaGeometricToTq` is the
`ℤ̂`-lift `gen ↦ ztwoOne⁻¹` of Tau Ceti's arithmetic `iwasawaCoordinateGeometric`: `nuTq` sends
`tqSigma q` to `ztwoOne` while the geometric generator has coordinate `zHat.gen⁻¹`
(`iwasawaCoordinateGeometric_iwasawaSigmaGeometric`, `Tame/Geometric.lean:178`; `_TauGeometric`,
`:184`; `zHat.lift_gen`, `ZHat/Basic.lean:154`). -/
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

/-! ## The bundle's pieces at `↥K` -/

section K

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- `G_{↥K} ≃ₜ* GalK K`: A1's `absGalEquivFixing K` followed by `galKEquiv K` inverted (to gq2's
`AbsGalQ2` instance path). -/
def absGalEquivGalK : Field.absoluteGaloisGroup K ≃ₜ* GalK K :=
  (absGalEquivFixing K).trans (galKEquiv K).symm

/-- **The `W` of B10-K**: Tau Ceti's wild inertia subgroup of `↥K`,
`TauCeti.wildInertiaSubgroup ↥K` (`TauCeti/NumberTheory/LocalField/WildInertia.lean:245`), mapped
to `GalK K` along `absGalEquivGalK K`. -/
def wildInertiaK : Subgroup (GalK K) :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  (TauCeti.wildInertiaSubgroup K).map (absGalEquivGalK K).toMulEquiv.toMonoidHom

/-- The defining equation of `wildInertiaK`, as a named lemma: `quotientCongr` needs it as an
argument, and an inline `rfl` there makes later `rw`s fail with "not type-correct under the
implicit transparency" (memo §B10-K, field 5). -/
theorem map_wildInertiaSubgroup_eq_wildInertiaK :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    (TauCeti.wildInertiaSubgroup K).map (absGalEquivGalK K).toMulEquiv.toMonoidHom =
      wildInertiaK K := rfl

/-- **B10-K `normal`**: Tau Ceti's instance `wildInertiaSubgroup_normal` (`WildInertia.lean:284`)
transported along the surjection `absGalEquivGalK K`.  A `Prop`-valued instance on this one
subgroup, needed for the quotient `GalK K ⧸ wildInertiaK K`. -/
instance wildInertiaK_normal : (wildInertiaK K).Normal := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  exact Subgroup.Normal.map (TauCeti.wildInertiaSubgroup_normal K) _ (absGalEquivGalK K).surjective

/-- **B10-K `isClosed`**: Tau Ceti's `isClosed_wildInertiaSubgroup` (`WildInertia.lean:279`)
through the homeomorphism `absGalEquivGalK K`. -/
theorem isClosed_wildInertiaK : IsClosed (wildInertiaK K : Set (GalK K)) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [wildInertiaK, Subgroup.coe_map]
  exact (absGalEquivGalK K).toHomeomorph.isClosedMap _ (TauCeti.isClosed_wildInertiaSubgroup K)

/-- **B10-K `isProP`**: Tau Ceti's `isProP_wildInertiaSubgroup ↥K 2` (`WildInertia.lean:473`),
which needs `CharP 𝓀[↥K] 2` (`TauCeti.charP_residueField`,
`TauCeti/NumberTheory/LocalField/AbsoluteRamificationIndex.lean:173`, found once
`valuativeExtension K` is in context), pushed onto `wildInertiaK K` by
`TauCeti.IsProP.of_surjective` (`TauCeti/Topology/Algebra/Group/Profinite/ProP/Basic.lean:146`)
and read in gq2's `IsProP` by `TauCeti.isProP_iff` (`:75`). -/
theorem isProP_wildInertiaK : IsProP 2 (wildInertiaK K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  haveI := TauCeti.charP_residueField K 2
  have h := TauCeti.isProP_wildInertiaSubgroup K 2
  refine TauCeti.isProP_iff.mp (h.of_surjective
    ((absGalEquivGalK K).toMulEquiv.toMonoidHom.subgroupMap (TauCeti.wildInertiaSubgroup K))
    (continuous_induced_rng.2 ((absGalEquivGalK K).continuous.comp continuous_subtype_val))
    ((absGalEquivGalK K).toMulEquiv.toMonoidHom.subgroupMap_surjective _))

/-- **The `equiv` of B10-K**: `GalK K ⧸ W ≃ₜ* Tq (qOf K FF)`.  Tau Ceti's
`ContinuousMulEquiv.quotientCongr` (`TauCeti/Topology/Algebra/Group/ClosedSubgroup.lean:153`)
along `absGalEquivGalK K`, then `tameQuotientGeometricEquiv` (`Tame/Geometric.lean:194`) for an
arithmetic Frobenius lift from `exists_isArithFrobeniusLift`
(`TauCeti/NumberTheory/LocalField/Unramified/Inertia/Basic.lean:384`) and a tame generator from
`exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`
(`TauCeti/NumberTheory/LocalField/Tame/Quotient.lean:186`), then `iwasawaGeometricEquivTq` with
`hq` the residue-degree bridge `natCard_residueField_eq_two_pow` (A1-K). -/
def tameEquivK (FF : DyadicUnitFiltration K) :
    ContinuousMulEquiv (GalK K ⧸ wildInertiaK K) (Tq (qOf K FF)) :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  ((absGalEquivGalK K).quotientCongr (TauCeti.wildInertiaSubgroup K) (wildInertiaK K)
      (map_wildInertiaSubgroup_eq_wildInertiaK K)).symm.trans
    ((TauCeti.tameQuotientGeometricEquiv
        (Classical.choose_spec (TauCeti.exists_isArithFrobeniusLift K))
        (Classical.choose (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K))
        (Classical.choose_spec
          (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K))).trans
      (iwasawaGeometricEquivTq K (qOf K FF)
        ((natCard_residueField_eq_two_pow K FF).trans (qOf_eq K FF).symm)))

/-- **The lemma behind both orientation clauses.** For any lift `g ∈ G_K` of `rec_K x`,
`ν_t(equiv (mk g)) = ztwoOne⁻¹ ^ v_K(x)`.  The chain: `quotientCongr_symm_mk`
(`ClosedSubgroup.lean:174`), `nuTq_iwasawaGeometricToTq`,
`iwasawaCoordinateGeometric_tameQuotientGeometricEquiv` (`Tame/Geometric.lean:231`),
`toTameQuotient_apply` and `tameQuotientToZHat_toTameQuotient` (`Tame/Quotient.lean:164, :404`),
`unramifiedCoordinate_mk` (`Unramified/Coordinate.lean:88`), then
`ClassFieldTheory.unramifiedCoordinate_artinMap` and `zHat.lift_ofInt` through B5-K's `recipK`. -/
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
      (((absGalEquivGalK K).symm g : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) :=
    abEquivK_toAbK K g
  rw [hg, abEquivK_recipK] at h1
  rw [tameEquivK, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.quotientCongr_symm_mk]
  change nuTq (qOf K FF) (iwasawaGeometricToTq K (qOf K FF) _ _) = _
  rw [nuTq_iwasawaGeometricToTq, TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv,
    ← TauCeti.toTameQuotient_apply, TauCeti.tameQuotientToZHat_toTameQuotient,
    ← TauCeti.unramifiedCoordinate_mk]
  change TauCeti.zHat.lift ztwoOne⁻¹ (TauCeti.unramifiedCoordinate K
    (((absGalEquivGalK K).symm g : Field.absoluteGaloisGroup K) :
      Field.absoluteGaloisGroupAbelianization K)) = _
  rw [← h1, TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap, TauCeti.zHat.lift_ofInt]

/-- **B10-K for any marked bundle whose `recip` is `recipK K`.**  `W := wildInertiaK K`,
`equiv := tameEquivK K FF`; the orientation clauses are `nuTq_tameEquivK_mk` at `v_K(u) = 0`
(A1-K's `normalizedValuation_eq_one_of_norm_eq_one`) and at `v_K(uniformizerK K FF) = 1` (A1-K's
`normalizedValuation_eq_ofAdd_one_of_norm` with `norm_uniformizerK_lt_one`, `uniformizerK_max`). -/
def orientedTameQuotientOfRecip {R : LocalReciprocity} (B : MarkedRecip R K)
    (hB : ∀ x, B.recip x = recipK K x) (FF : DyadicUnitFiltration K) :
    OrientedTameQuotientK B FF where
  W := wildInertiaK K
  normal := wildInertiaK_normal K
  isClosed := isClosed_wildInertiaK K
  isProP := isProP_wildInertiaK K
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

end K

/-! ## The bundle -/

/-- **B10-K, discharged.** gq2's oriented tame quotient of `G_K` at `q_K = qOf K FF`, for B5-K's
marked reciprocity `markedRecipAt_tauceti K`: the type of the census axiom
`GQ2.orientedTameQuotientAt K FF` (`GQ2/Foundations/Axioms.lean`) with `markedRecipAt_tauceti K`
in place of `markedRecipAt K`.  It is `orientedTameQuotientOfRecip` at
`B := markedRecipAt_tauceti K`, whose `recip` is `recipK K` by
`markedRecipAt_tauceti_recip_apply`. -/
def orientedTameQuotientAt_tauceti (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) :
    Dyadic.OrientedTameQuotientK (markedRecipAt_tauceti K) FF :=
  orientedTameQuotientOfRecip K (markedRecipAt_tauceti K) (markedRecipAt_tauceti_recip_apply K) FF

section Equations

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K)

@[simp]
theorem orientedTameQuotientAt_tauceti_W :
    (orientedTameQuotientAt_tauceti K FF).W = wildInertiaK K := rfl

@[simp]
theorem orientedTameQuotientAt_tauceti_equiv :
    (orientedTameQuotientAt_tauceti K FF).equiv = tameEquivK K FF := rfl

end Equations

end GQ2.TauCetiBridge
