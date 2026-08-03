/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleFlexible

/-!
# A finite relation-level criterion for surjectivity in degree two

The flexible comparison sends a continuous module cocycle to its vector of relator
fibres, modulo the Fox differential.  This file proves the converse bookkeeping
statement: it is enough to realize every relator vector, modulo that differential,
by a normalized cocycle on a finite action-compatible quotient.

This is deliberately stated without the final `H²` map.  The hypothesis
`ModuleRelatorRealizationAt` contains no continuous cohomology and no cohomology quotient;
its witnesses are explicit finite-group cocycles.  The theorems below nevertheless prove that
the vector-dependent version is equivalent to surjectivity of the canonical comparison.  Thus
this is a concrete reformulation of the obstruction, not by itself an independently stronger
relation-module or asphericity theorem.

The remaining mathematical direction for the L presentation is therefore isolated
as follows.  Given a relator functional `r`, construct an action-compatible finite
quotient and a module extension of that quotient whose lifted defining relators have
fibre vector congruent to `r` modulo `heisD1.range`.  Everything after that
construction is proved here.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

section Inflation

variable {G C A : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]

local instance relatorRealizationQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Inflate a normalized module cocycle from an action-compatible finite quotient.

The resulting continuous cocycle is already normalized.  We nevertheless keep it as
an ordinary `Z2`, so it can be fed directly to the canonical continuous-to-word map. -/
noncomputable def inflateModuleTwoCocycle
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (z : @ModuleTwoCocycle (G ⧸ V.toSubgroup) A _ _
      (DistribMulAction.compHom A (quotientActionHom rho V hV))) : Z2 G A := by
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  refine ⟨fun p ↦ z.κ
      (QuotientGroup.mk' V.toSubgroup p.1)
      (QuotientGroup.mk' V.toSubgroup p.2), ?_⟩
  rw [mem_Z2_iff]
  constructor
  · have hz : Continuous (fun p : (G ⧸ V.toSubgroup) × (G ⧸ V.toSubgroup) ↦
        z.κ p.1 p.2) := continuous_of_discreteTopology
    exact hz.comp
      (((GQ2.quotientMk V.toSubgroup).continuous_toFun.comp continuous_fst).prodMk
        ((GQ2.quotientMk V.toSubgroup).continuous_toFun.comp continuous_snd))
  · intro g h k
    calc
      g • z.κ (QuotientGroup.mk' V.toSubgroup h)
            (QuotientGroup.mk' V.toSubgroup k) +
          z.κ (QuotientGroup.mk' V.toSubgroup g)
            (QuotientGroup.mk' V.toSubgroup (h * k))
          = rho g • z.κ (QuotientGroup.mk' V.toSubgroup h)
                (QuotientGroup.mk' V.toSubgroup k) +
              z.κ (QuotientGroup.mk' V.toSubgroup g)
                (QuotientGroup.mk' V.toSubgroup (h * k)) := by
              rw [hcompat]
      _ = rhoV (QuotientGroup.mk' V.toSubgroup g) •
              z.κ (QuotientGroup.mk' V.toSubgroup h)
                (QuotientGroup.mk' V.toSubgroup k) +
            z.κ (QuotientGroup.mk' V.toSubgroup g)
              (QuotientGroup.mk' V.toSubgroup (h * k)) := by
              rw [quotientActionHom_mk]
      _ = z.κ (QuotientGroup.mk' V.toSubgroup (g * h))
              (QuotientGroup.mk' V.toSubgroup k) +
            z.κ (QuotientGroup.mk' V.toSubgroup g)
              (QuotientGroup.mk' V.toSubgroup h) := by
              have hc := z.cocyc
                (QuotientGroup.mk' V.toSubgroup g)
                (QuotientGroup.mk' V.toSubgroup h)
                (QuotientGroup.mk' V.toSubgroup k)
              change rhoV (QuotientGroup.mk' V.toSubgroup g) •
                  z.κ (QuotientGroup.mk' V.toSubgroup h)
                    (QuotientGroup.mk' V.toSubgroup k) +
                z.κ (QuotientGroup.mk' V.toSubgroup g)
                    (QuotientGroup.mk' V.toSubgroup h *
                      QuotientGroup.mk' V.toSubgroup k) = _ at hc
              simpa only [map_mul] using hc

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Finite C] [Finite A]
  [DiscreteTopology C] [DiscreteTopology A] [ContinuousSMul G A] in
/-- Inflating and then applying the module normalization does nothing. -/
theorem moduleNormalize_inflateModuleTwoCocycle
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (z : @ModuleTwoCocycle (G ⧸ V.toSubgroup) A _ _
      (DistribMulAction.compHom A (quotientActionHom rho V hV))) :
    moduleNormalize (inflateModuleTwoCocycle rho hcompat V hV z).1 =
      (inflateModuleTwoCocycle rho hcompat V hV z).1 := by
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  funext p
  change z.κ (QuotientGroup.mk' V.toSubgroup p.1)
        (QuotientGroup.mk' V.toSubgroup p.2) -
      p.1 • z.κ (QuotientGroup.mk' V.toSubgroup (1 : G))
        (QuotientGroup.mk' V.toSubgroup (1 : G)) = _
  rw [show QuotientGroup.mk' V.toSubgroup (1 : G) = 1 from map_one _, z.norm,
    smul_zero, sub_zero]
  change z.κ (QuotientGroup.mk' V.toSubgroup p.1)
      (QuotientGroup.mk' V.toSubgroup p.2) =
    z.κ (QuotientGroup.mk' V.toSubgroup p.1)
      (QuotientGroup.mk' V.toSubgroup p.2)
  rfl

end Inflation

section RelatorRealization

variable {iota rel : Type*} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C} {J : Set iota}

local instance relatorRealizationAssemblyQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- A finite quotient realizes every relator fibre vector modulo the target Fox
differential.

This is the precise relation-level conclusion needed from an asphericity or
relation-module theorem.  It mentions only normalized cocycles on the finite quotient
and the relator-evaluation map `moduleRel`; in particular it does not quantify over
continuous cohomology classes. -/
def ModuleRelatorRealizationAt
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker) : Prop :=
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  ∀ r : rel → A, ∃ z : ModuleTwoCocycle (G ⧸ V.toSubgroup) A,
    (fun k ↦ moduleRel (W k)
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) - r ∈
        (heisD1 (A := A) c w).range

/-- Every relator fibre vector is realized at some action-compatible finite
quotient.  The quotient is allowed to depend on the vector; this is the weakest
finite presentation-level condition used in this file. -/
def ModuleRelatorRealization
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota) : Prop :=
  ∀ r : rel → A, ∃ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ∃ z : ModuleTwoCocycle (G ⧸ V.toSubgroup) A,
      (fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) - r ∈
          (heisD1 (A := A) c w).range

omit [Fintype iota] [Fintype rel] [DecidableEq iota]
  [TotallyDisconnectedSpace G] [DiscreteTopology C] [Finite C]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] in
/-- A single finite quotient realizing every vector supplies the vector-dependent
realization condition. -/
theorem moduleRelatorRealization_of_at
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hreal : ModuleRelatorRealizationAt (A := A) W gen rho c w V hV) :
    ModuleRelatorRealization (A := A) W gen rho c w := by
  intro r
  exact ⟨V, hV, hreal r⟩

/-- Surjectivity of the canonical flexible comparison produces finite relator
realizations.

For a requested relator vector, choose a continuous `H²` class mapping to its word
class, choose a normalized cocycle representative, and factor that representative
through an action-compatible finite quotient.  The defining representative formula
for the comparison then says that the finite cocycle's relator fibres realize the
requested vector modulo the Fox differential.

Thus this direction does not assume a finite relation-module splitting.  It extracts
the exact finite witnesses encoded by surjectivity, and is useful both for base-case
regressions and for auditing the strength of `ModuleRelatorRealization`. -/
theorem moduleRelatorRealization_of_surjective
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup G,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hsurj : Function.Surjective
      (globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve)) :
    ModuleRelatorRealization (A := A) W gen rho c w := by
  intro r
  obtain ⟨x, hx⟩ := hsurj
    (QuotientAddGroup.mk' (heisD1 (A := A) c w).range r)
  obtain ⟨f, rfl⟩ := H2mk_surjective x
  obtain ⟨V, hV, z, hfactor⟩ := exists_moduleTwoCocycle_factor rho hcompat f
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  refine ⟨V, hV, z, ?_⟩
  rw [globalModuleH2WordFlexible_mk] at hx
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := z
      hfact := hfactor }
  have hread : moduleObsFam W gen rho hcompat f =
      fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z := by
    change moduleObsFun W gen rho hcompat f = _
    rw [moduleObsFun_eq W gen rho hcompat f F]
    rfl
  rw [hread] at hx
  exact QuotientAddGroup.eq_iff_sub_mem.mp hx

omit [Fintype iota] [Fintype rel] [DecidableEq iota] in
/-- The global obstruction of an inflated finite cocycle is exactly its finite
relator-fibre vector.  This is the representative-level regression behind the
surjectivity criterion. -/
theorem moduleObsFam_inflateModuleTwoCocycle
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (z : @ModuleTwoCocycle (G ⧸ V.toSubgroup) A _ _
      (DistribMulAction.compHom A (quotientActionHom rho V hV))) :
    moduleObsFam W gen rho hcompat
        (inflateModuleTwoCocycle rho hcompat V hV z) =
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z := by
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  let f := inflateModuleTwoCocycle rho hcompat V hV z
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := z
      hfact := by
        intro x y
        rw [moduleNormalize_inflateModuleTwoCocycle rho hcompat V hV z]
        rfl }
  change moduleObsFun W gen rho hcompat f = _
  rw [moduleObsFun_eq W gen rho hcompat f F]
  rfl

/-- A finite relation-level realization theorem makes the flexible continuous-to-word
`H²` comparison surjective.

All presentation, reflection, and quotient-dependent resolver hypotheses remain in
the construction of the map.  The only new input is `ModuleRelatorRealizationAt`,
which supplies the genuinely missing inverse cocycle. -/
theorem globalModuleH2WordFlexible_surjective_of_relatorRealization
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup G,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hreal : ModuleRelatorRealization (A := A) W gen rho c w) :
    Function.Surjective
      (globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H r =>
      obtain ⟨V, hV, z, hz⟩ := hreal r
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      let f := inflateModuleTwoCocycle rho hcompat V hV z
      refine ⟨H2mk G A f, ?_⟩
      rw [globalModuleH2WordFlexible_mk,
        moduleObsFam_inflateModuleTwoCocycle W gen rho hcompat V hV z]
      exact QuotientAddGroup.eq_iff_sub_mem.mpr hz

/-- Finite relator realization is exactly surjectivity of the canonical flexible
continuous-to-word `H²` comparison.

The forward implication factors a chosen continuous cocycle representative through a
finite quotient.  The reverse implication inflates a finite realizing cocycle.  This
equivalence identifies the mathematical content of the remaining relation-module
theorem without replacing it by a differently named cohomological hypothesis. -/
theorem globalModuleH2WordFlexible_surjective_iff_relatorRealization
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup G,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) :
    Function.Surjective
        (globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve) ↔
      ModuleRelatorRealization (A := A) W gen rho c w :=
  ⟨moduleRelatorRealization_of_surjective hpres rho hcompat hwildLevel hA₂ hresolve,
    globalModuleH2WordFlexible_surjective_of_relatorRealization
      hpres rho hcompat hwildLevel hA₂ hresolve⟩

/-- Fixed-quotient convenience form of
`globalModuleH2WordFlexible_surjective_of_relatorRealization`. -/
theorem globalModuleH2WordFlexible_surjective_of_relatorRealizationAt
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup G,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hreal : ModuleRelatorRealizationAt (A := A) W gen rho c w V hV) :
    Function.Surjective
      (globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve) :=
  globalModuleH2WordFlexible_surjective_of_relatorRealization hpres rho hcompat
    hwildLevel hA₂ hresolve
      (moduleRelatorRealization_of_at W gen rho c w V hV hreal)

end RelatorRealization

end GQ2.Dyadic.Count
