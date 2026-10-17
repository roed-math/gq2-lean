module

public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Identities
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2

open CategoryTheory

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] TopRep.distribMulAction

/-- the local instance every Tau Ceti `Evens` file declares; the adapter needs it too -/
local instance continuousSMul_trivialF2_adapter (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ContinuousSMul G (TauCeti.trivialF2 G).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul

variable {K L : Type} [Field K] [Field L] [Invertible (2 : L)] [Algebra K L]
  [FiniteDimensional K L]

/-- **Evens norm of a Kummer class = class of the explicit graph cocycle of its Kummer
character, at any `s ∉ G_L`.** -/
theorem galoisEvens_kummerClass_eq_evensGraphCochainClass (σ : L →ₐ[K] SeparableClosure K)
    (hL : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : TauCeti.AbsoluteGaloisGroup K) (hs : s ∉ TauCeti.galoisSubgroup K L σ) :
    TauCeti.galoisEvens K L σ hL (TauCeti.kummerClass a) =
      TauCeti.ContCohomology.evensGraphCochainClass (TauCeti.galoisSubgroup K L σ) s
        (TauCeti.galoisKummerCharacter σ a r hr) ((TauCeti.galoisSubgroup_index K L σ).trans hL) hs
        (TauCeti.continuous_galoisKummerCharacter σ a r hr) := by
  rw [TauCeti.galoisEvens_def, TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.evensNormIndexTwo_homClass,
    TauCeti.ContCohomology.graphClass_eq_evensGraphCochainClass _ _ s hs]

/-- **Corestriction of a Kummer class = class of the explicit Shapiro-sum cocycle of its
Kummer character, at any `s ∉ G_L`.** -/
theorem galoisCor_kummerClass_eq_evensCorCocycle [Invertible (2 : K)] (σ : L →ₐ[K] SeparableClosure K)
    (hL : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : TauCeti.AbsoluteGaloisGroup K) (hs : s ∉ TauCeti.galoisSubgroup K L σ) :
    TauCeti.galoisCor K L σ 1 (TauCeti.kummerClass a) =
      (eqToHom (congrArg (continuousCohomology 1)
          (TauCeti.ofDiscreteModule_trivialF2 (TauCeti.AbsoluteGaloisGroup K)))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
          (TauCeti.AbsoluteGaloisGroup K)
          (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K)).V
          (TauCeti.ContCohomology.evensCorCocycle (TauCeti.galoisSubgroup K L σ) s
            (TauCeti.galoisKummerCharacter σ a r hr)
            ((TauCeti.galoisSubgroup_index K L σ).trans hL) hs
            (TauCeti.continuous_galoisKummerCharacter σ a r hr))) := by
  rw [TauCeti.galoisCor_def, ConcreteCategory.comp_apply,
    TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.homClass_eq_evensHomCocycleAmbient,
    TauCeti.trivialF2CorMap_explicitH1AddEquivContinuousCohomology,
    TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient _
      ((TauCeti.galoisSubgroup_index K L σ).trans hL) s hs]
