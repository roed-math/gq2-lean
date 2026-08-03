/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleVectorwise

/-!
# Recovering a relation character from a finite module cocycle

For a marking `m : X → L` and a normalized module cocycle `z`, the canonical free lift

`FreeGroup X → A ⋊_z L`

sends the relation kernel into the additive fibre.  Restriction to that kernel is therefore
an equivariant relation character.  Transgressing this character using the normalized
Schreier section recovers `z` up to the explicit coboundary of the fibre coordinate of the
lifted section.

This is the inverse, at the level of extension classes, to the relation-character
transgression in `HTwoRelationModule`.  It does not by itself say that an arbitrary resolving
word for `WordLift A L` also resolves in either twisted extension; that compatibility is
recorded separately below.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH GQ2.Dyadic

section InverseCharacter

variable {X L A : Type} [Group L] [AddCommGroup A] [DistribMulAction L A]
  {m : X → L}

local notation "F" => FreeGroup X
local notation "ev" => FreeGroup.lift m

/-- The homomorphism from the abstract free group to the twisted extension obtained by
choosing the zero-fibre lift of every marked generator. -/
def moduleFreeLift (z : ModuleTwoCocycle L A) (m : X → L) :
    F →* ModuleExt z :=
  FreeGroup.lift (ModuleExt.lift z m)

@[simp] theorem moduleFreeLift_of (z : ModuleTwoCocycle L A) (m : X → L) (x : X) :
    moduleFreeLift z m (FreeGroup.of x) = ModuleExt.lift z m x := by
  simp [moduleFreeLift]

/-- The base coordinate of the canonical free lift is ordinary evaluation at the marking. -/
@[simp] theorem moduleFreeLift_g (z : ModuleTwoCocycle L A) (m : X → L) (f : F) :
    (moduleFreeLift z m f).g = FreeGroup.lift m f := by
  have h : (ModuleExt.baseProj z).comp (moduleFreeLift z m) = FreeGroup.lift m := by
    apply FreeGroup.ext_hom
    intro x
    simp [moduleFreeLift]
  exact DFunLike.congr_fun h f

/-- Restrict a finite module cocycle's canonical free lift to the relation kernel. -/
def ModuleTwoCocycle.relationCharacter (z : ModuleTwoCocycle L A) (m : X → L) :
    FreeRelationCharacter m A where
  toMonoidHom :=
    { toFun := fun r ↦ Multiplicative.ofAdd (moduleFreeLift z m r.1).u
      map_one' := by simp [moduleFreeLift]
      map_mul' := by
        intro r s
        apply Multiplicative.toAdd.injective
        change (moduleFreeLift z m (r.1 * s.1)).u =
          (moduleFreeLift z m r.1).u + (moduleFreeLift z m s.1).u
        rw [map_mul]
        have hr : FreeGroup.lift m r.1 = 1 := MonoidHom.mem_ker.mp r.property
        simp only [ModuleExt.mul_u, moduleFreeLift_g, hr, one_smul,
          z.κ_one_left, add_zero] }
  conjugation := by
    intro f r
    apply Multiplicative.toAdd.injective
    change (moduleFreeLift z m (f * r.1 * f⁻¹)).u =
      FreeGroup.lift m f • (moduleFreeLift z m r.1).u
    have hrbase : (moduleFreeLift z m r.1).g = 1 := by
      rw [moduleFreeLift_g]
      exact r.property
    have hr : moduleFreeLift z m r.1 =
        ModuleExt.incl z (moduleFreeLift z m r.1).u :=
      (ModuleExt.base_eq_one_iff _).mp hrbase
    have hconj : moduleFreeLift z m (f * r.1 * f⁻¹) =
        ModuleExt.incl z
          (FreeGroup.lift m f • (moduleFreeLift z m r.1).u) := by
      calc
        moduleFreeLift z m (f * r.1 * f⁻¹) =
            moduleFreeLift z m f * moduleFreeLift z m r.1 *
              (moduleFreeLift z m f)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = moduleFreeLift z m f *
              ModuleExt.incl z (moduleFreeLift z m r.1).u *
                (moduleFreeLift z m f)⁻¹ :=
            congrArg (fun p ↦ moduleFreeLift z m f * p *
              (moduleFreeLift z m f)⁻¹) hr
        _ = ModuleExt.incl z
              ((moduleFreeLift z m f).g • (moduleFreeLift z m r.1).u) :=
            (ModuleExt.conj_incl _ _).symm
        _ = ModuleExt.incl z
              (FreeGroup.lift m f • (moduleFreeLift z m r.1).u) := by
            rw [moduleFreeLift_g]
    exact congrArg ModuleExt.u hconj

@[simp] theorem ModuleTwoCocycle.relationCharacter_val
    (z : ModuleTwoCocycle L A) (m : X → L) (r : FreeRelationKernel m) :
    (z.relationCharacter m).val r = (moduleFreeLift z m r.1).u := rfl

/-- The explicit normalized cochain measuring the difference between the zero-fibre section
of `ModuleExt z` and the free lift of the normalized Schreier section. -/
def relationSectionLiftCoord (z : ModuleTwoCocycle L A)
    (heval : Function.Surjective ev) (g : L) : A :=
  (moduleFreeLift z m (relationSection heval g)).u

@[simp] theorem relationSectionLiftCoord_one (z : ModuleTwoCocycle L A)
    (heval : Function.Surjective ev) :
    relationSectionLiftCoord z heval 1 = 0 := by
  simp [relationSectionLiftCoord, moduleFreeLift]

/-- The relation character recovered from `z` takes the Schreier defect to `z` plus the
coboundary of the lifted-section coordinate. -/
theorem relationCharacter_relationDefect
    (z : ModuleTwoCocycle L A) (heval : Function.Surjective ev) (g h : L) :
    (z.relationCharacter m).val (relationDefect heval g h) =
      z.κ g h + (ModuleTwoCocycle.coboundary
        (relationSectionLiftCoord z heval)
        (relationSectionLiftCoord_one z heval)).κ g h := by
  let H := moduleFreeLift z m
  let sg := relationSection heval g
  let sh := relationSection heval h
  let sgh := relationSection heval (g * h)
  have hprod : H (relationDefect heval g h).1 * H sgh = H sg * H sh := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [relationDefect, sg, sh, sgh]
    group
  have hu := congrArg ModuleExt.u hprod
  change (H (relationDefect heval g h).1).u +
      (H (relationDefect heval g h).1).g • (H sgh).u +
        z.κ (H (relationDefect heval g h).1).g (H sgh).g =
      (H sg).u + (H sg).g • (H sh).u + z.κ (H sg).g (H sh).g at hu
  have hdefbase : (H (relationDefect heval g h).1).g = 1 := by
    rw [moduleFreeLift_g]
    exact (relationDefect heval g h).property
  have hsg : (H sg).g = g := by
    rw [moduleFreeLift_g, relationSection_spec]
  have hsh : (H sh).g = h := by
    rw [moduleFreeLift_g, relationSection_spec]
  have hsgh : (H sgh).g = g * h := by
    rw [moduleFreeLift_g, relationSection_spec]
  rw [hdefbase, hsg, hsh, hsgh, one_smul, z.κ_one_left, add_zero] at hu
  calc
    (z.relationCharacter m).val (relationDefect heval g h) =
        (H sg).u + g • (H sh).u + z.κ g h - (H sgh).u := by
      change (H (relationDefect heval g h).1).u = _
      exact (eq_sub_iff_add_eq).2 hu
    _ = z.κ g h + (ModuleTwoCocycle.coboundary
        (relationSectionLiftCoord z heval)
        (relationSectionLiftCoord_one z heval)).κ g h := by
      change (H sg).u + g • (H sh).u + z.κ g h - (H sgh).u =
        z.κ g h + (g • (H sh).u - (H sgh).u + (H sg).u)
      abel

/-- Schreier transgression of the relation character recovered from `z` is cohomologous to
`z`, with an explicit normalized cochain. -/
theorem relationCharacterCocycle_relationCharacter
    (z : ModuleTwoCocycle L A) (heval : Function.Surjective ev) :
    relationCharacterCocycle heval (z.relationCharacter m) =
      z + ModuleTwoCocycle.coboundary
        (relationSectionLiftCoord z heval)
        (relationSectionLiftCoord_one z heval) := by
  apply ModuleTwoCocycle.ext
  funext g h
  exact relationCharacter_relationDefect z heval g h

end InverseCharacter

section RelatorEvaluation

variable {X rel L A : Type} [Group L] [TopologicalSpace L]
  [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]
  {m : X → L}

/-- If the selected free word resolves the profinite relator in `ModuleExt z`, then the
relation character recovered from `z` evaluates that word to the intrinsic relator fibre
`moduleRel`. -/
theorem ModuleTwoCocycle.relationCharacter_val_relator
    (W : rel → PWord X) (w : rel → FreeGroup X)
    (z : ModuleTwoCocycle L A)
    (hres : ResolvesAt W w (ModuleExt z))
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1) (k : rel) :
    (z.relationCharacter m).val
        ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩ =
      moduleRel (W k) m z := by
  change (FreeGroup.lift (ModuleExt.lift z m) (w k)).u =
    (PWord.eval (ModuleExt.lift z m) (W k)).u
  rw [hres _ k]

end RelatorEvaluation

section RefinedWitnessConstructor

variable {iota rel : Type} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota}

local instance relationModuleInverseQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Resolver data sufficient to turn every cocycle at one finite refinement into a relation
character witness.  The module-extension clause is uniform in the cocycle; applying it once
to `z` and once to the transgression of `z.relationCharacter` supplies both twisted targets
needed by `RefinedRelationCharacterWitness.ofModuleTwoCocycle`. -/
structure RefinedModuleExtensionResolver
    (rho : ContinuousMonoidHom G C)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker) where
  word : rel → FreeGroup iota
  generators : Subgroup.closure
    (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) = ⊤
  resolves :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup))
  relation : ∀ k, FreeGroup.lift
    (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) (word k) = 1
  resolvesModule :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ∀ z : ModuleTwoCocycle (G ⧸ V.toSubgroup) A,
      ResolvesAt W word (ModuleExt z)

namespace RefinedRelationCharacterWitness

/-- Turn one direct finite cocycle realization into a refined relation-character witness.

The recovered character has exactly the cocycle's intrinsic relator values.  Besides the
split resolver already carried by a refined witness, the constructor asks for resolution in
`ModuleExt z` to identify those values and resolution in the transgressed extension to meet
the character interface.  For the improved L words both assumptions follow uniformly from
`lUniform_moduleExt_resolver`. -/
noncomputable def ofModuleTwoCocycle
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota) (r : rel → A)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (word : rel → FreeGroup iota)
    (generators : Subgroup.closure
      (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) = ⊤)
    (resolves :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup)))
    (relation : ∀ k, FreeGroup.lift
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) (word k) = 1)
    (z :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleTwoCocycle (G ⧸ V.toSubgroup) A)
    (resolvesCocycle :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W word (ModuleExt z))
    (resolvesTransgression :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W word
        (ModuleExt (relationCharacterCocycle
          (freeGroup_lift_surjective_of_closure generators)
          (z.relationCharacter
            (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))))))
    (values_mod_range :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      (fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) - r ∈
          (heisD1 (A := A) c targetWord).range) :
    RefinedRelationCharacterWitness (gen := gen) (W := W)
      rho c targetWord r := by
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  exact
    { V := V
      hV := hV
      word := word
      generators := generators
      resolves := resolves
      relation := relation
      character := z.relationCharacter
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))
      resolvesExtension := resolvesTransgression
      values_mod_range := by
        have hvalues :
            (fun k ↦ (z.relationCharacter
              (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))).val
                ⟨word k, MonoidHom.mem_ker.mpr (relation k)⟩) =
              (fun k ↦ moduleRel (W k)
                (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) := by
          funext k
          exact z.relationCharacter_val_relator W word resolvesCocycle relation k
        rw [hvalues]
        exact values_mod_range }

end RefinedRelationCharacterWitness

/-- Under a quotient-wise resolver uniform in all module cocycles, every exact finite cocycle
realization witness canonically yields a vectorwise refined relation character witness. -/
theorem vectorwiseRefinedRelationCharacters_of_moduleRelatorRealization
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota)
    (hresolver : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      Nonempty (RefinedModuleExtensionResolver
        (A := A) (gen := gen) (W := W) rho V hV))
    (hreal : ModuleRelatorRealization (A := A) W gen rho c targetWord) :
    VectorwiseRefinedRelationCharacterRealization
      (A := A) (gen := gen) (W := W) rho c targetWord := by
  intro r
  obtain ⟨V, hV, z, hz⟩ := hreal r
  obtain ⟨R⟩ := hresolver V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  exact ⟨RefinedRelationCharacterWitness.ofModuleTwoCocycle
    rho c targetWord r V hV R.word R.generators R.resolves R.relation z
    (R.resolvesModule z)
    (R.resolvesModule (relationCharacterCocycle
      (freeGroup_lift_surjective_of_closure R.generators)
      (z.relationCharacter
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))))) hz⟩

/-- With the ordinary target resolver and quotient-wise module-extension resolvers, the exact
finite cocycle interface and the vectorwise refined relation-character interface are
equivalent. -/
theorem vectorwiseRefinedRelationCharacters_iff_moduleRelatorRealization
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota)
    (hc0 : ∀ i, rho (gen i) = c i)
    (htarget : ResolvesAt W targetWord (WordLift A C))
    (hresolver : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      Nonempty (RefinedModuleExtensionResolver
        (A := A) (gen := gen) (W := W) rho V hV)) :
    VectorwiseRefinedRelationCharacterRealization
        (A := A) (gen := gen) (W := W) rho c targetWord ↔
      ModuleRelatorRealization (A := A) W gen rho c targetWord := by
  constructor
  · exact moduleRelatorRealization_of_vectorwise_refined_relationCharacters
      rho hc0 htarget
  · exact vectorwiseRefinedRelationCharacters_of_moduleRelatorRealization
      rho c targetWord hresolver

end RefinedWitnessConstructor

end

end GQ2.Dyadic.Count
