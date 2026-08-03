/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleVectorwise
import GQ2.Dyadic.Instances.GammaLRelationModuleRefined

/-!
# Vectorwise refined relation characters for the improved L presentation

The continuous relator-realization predicate permits its finite quotient to depend on the
requested vector.  This file specializes the generic vectorwise transgression criterion to the
improved L presentation without replacing that quantifier order by a fixed-target or
fixed-refinement surjectivity statement.

For each requested `r : Fin 2 → A`, the supply below may choose

* an open normal `V` contained in the kernel of the finite action map,
* the quotient-specific improved word
  `lSqFam h q (omega2Exp (4 * exponent (GammaL / V)))`, and
* one equivariant character of the free relation kernel at `GammaL / V`.

The character values only have to agree with `r` modulo the target Fox differential.  Generator
closure, death of the quotient-specific words, split word resolution, and resolution in the
single transgressed module extension are all automatic and are discharged in the conversion
theorem.

This supply is sufficient for all-elementary relator realization.  It is deliberately not
claimed to be necessary: a realizing finite cocycle need not be presented as the transgression
of a relation character with the chosen resolver.  In particular, the existing `q = 2`, `h = 0`
theorem constructs direct cocycle witnesses and does not by itself inhabit this supply.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section UniformVectorwiseSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)

/-- A vectorwise, refinement-dependent relation-character supply for the improved L
presentation.

The quantifier over `r` precedes the choice of `V` and `chi`, so both may depend on the requested
relator vector.  The resolving word is fixed only after `V` is chosen, using the exponent of the
actual refinement.  Requiring equality only modulo the fixed target differential is exactly the
input accepted by `RefinedRelationCharacterWitness`; exact character values are a stronger
sufficient special case.

This predicate is sufficient for the continuous comparison, but is not asserted to be
equivalent to it. -/
noncomputable abbrev UniformElementaryVectorwiseRefinedRelationCharacterSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (hA₂ : ∀ a : A, a + a = 0) →
        ∀ r : Fin 2 → A,
          ∃ (V : OpenNormalSubgroup GammaL)
            (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
            letI : DiscreteTopology (GammaL ⧸ V.toSubgroup) :=
              Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup
            letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
              DistribMulAction.compHom A (quotientActionHom rho V hV)
            ∃ chi : FreeRelationCharacter
                (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i)) A,
              (fun k ↦ chi.val
                  ⟨(lSqFam h q
                    (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup)))) k,
                    MonoidHom.mem_ker.mpr
                      ((lUniform_rel_death (GQ2.quotientMk V.toSubgroup)) k)⟩) - r ∈
                (heisD1 (A := A) (fun i ↦ rho (genL i))
                  (lSqFam h q (omega2Exp (4 * Monoid.exponent C)))).range

local instance gammaLVectorwiseQuotientDiscreteTopology
    (V : OpenNormalSubgroup GammaL) : DiscreteTopology (GammaL ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

private theorem continuousSMul_comp_vectorwiseRelationCharacter
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The specialized supply constructs the generic vectorwise refined relation-character
criterion.  All structural fields of the witness are supplied by the improved L presentation;
the hypothesis contributes only `V` and the one character needed for the requested vector. -/
theorem vectorwiseRefinedRelationCharacterRealization_of_supply
    {C A : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology A] [Finite A]
    [DistribMulAction GammaL A] [ContinuousSMul GammaL A]
    [DistribMulAction C A]
    (hsupply : UniformElementaryVectorwiseRefinedRelationCharacterSupply
      (h := h) (q := q))
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hA₂ : ∀ a : A, a + a = 0) :
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
      rho (fun i ↦ rho (genL i))
        (lSqFam h q (omega2Exp (4 * Monoid.exponent C))) := by
  intro r
  obtain ⟨V, hV, chi, hchi⟩ := hsupply C rho hrho A hA₂ r
  let rhoV : (GammaL ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  let wV : Fin 2 → FreeGroup (Generator (2 * h + 1)) :=
    lSqFam h q (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup)))
  have hgen : Subgroup.closure
      (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i))) = ⊤ :=
    closure_range_lower_eq_top (GQ2.quotientMk V.toSubgroup) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 * h + 1) q (Words.LSq.lSqW h))
      (GQ2.quotientMk_surjective V.toSubgroup)
  refine ⟨{
    V := V
    hV := hV
    word := wV
    generators := hgen
    resolves := lUniform_wordLift_resolver hA₂
    relation := lUniform_rel_death (GQ2.quotientMk V.toSubgroup)
    character := chi
    resolvesExtension := lUniform_moduleExt_resolver hA₂ _
    values_mod_range := ?_
  }⟩
  exact hchi

/-- The vectorwise relation-character supply implies the exact all-elementary finite relator
realization interface.  The witness quotient and character are forgotten after transgression. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_vectorwiseRelationCharacters
    (hsupply : UniformElementaryVectorwiseRefinedRelationCharacterSupply
      (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalAddGroup A := by infer_instance
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_vectorwiseRelationCharacter rho (fun _ _ ↦ rfl)
  exact moduleRelatorRealization_of_vectorwise_refined_relationCharacters rho
    (fun _ ↦ rfl) (lUniform_wordLift_resolver hA₂)
    (vectorwiseRefinedRelationCharacterRealization_of_supply hsupply rho hrho hA₂)

/-- The vectorwise refined relation-character supply proves the continuous H² right-exact
tail for all finite elementary coefficient modules. -/
theorem gammaLH2RightExactSupply_of_vectorwiseRelationCharacters
    (hsupply : UniformElementaryVectorwiseRefinedRelationCharacterSupply
      (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_vectorwiseRelationCharacters
      hsupply)

/-- For even `q`, the vectorwise refined relation-character supply implies the full
`TateDualityG` package for the improved L presentation. -/
noncomputable def tateDualityG_of_vectorwiseRelationCharacters
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hsupply : UniformElementaryVectorwiseRefinedRelationCharacterSupply
      (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_vectorwiseRelationCharacters hsupply)

end UniformVectorwiseSupply

end

end GQ2.Dyadic.LSquare
