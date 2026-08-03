/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleAsphericity

/-!
# Relator realization gives finite-extension asphericity

`HTwoModuleAsphericity` constructs a relator-realizing cocycle from a finite extension.
This file proves the converse.  A normalized module cocycle already has a canonical finite
twisted extension `ModuleExt z`.  If its relator vector differs from a requested vector by a
Fox differential, shifting the chosen generator lifts by the negative Fox cochain makes the
relator fibres equal the requested vector on the nose.

Consequently the finite-cocycle and finite-extension formulations of the remaining degree-two
input are equivalent (once the defining relators hold at the finite marking).  In particular,
`FiniteRelatorExtensionAsphericity` is not a stronger hidden asphericity assertion than relator
realization; it is a concrete extension model for precisely the same obstruction.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic

namespace FiniteModuleExtension

variable {L A : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]

/-- The canonical finite extension attached to a normalized module cocycle. -/
noncomputable def ofModuleTwoCocycle (z : ModuleTwoCocycle L A) :
    FiniteModuleExtension L A where
  E := ModuleExt z
  incl :=
    { toFun := fun a => ModuleExt.incl z a.toAdd
      map_one' := ModuleExt.incl_zero
      map_mul' := by
        intro a b
        exact ModuleExt.incl_add a.toAdd b.toAdd }
  proj := ModuleExt.baseProj z
  incl_injective := by
    intro a b hab
    cases a with
    | ofAdd a =>
      cases b with
      | ofAdd b =>
        exact congrArg ModuleExt.u hab
  range_eq_ker := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hp
      rw [MonoidHom.mem_ker] at hp
      refine ⟨Multiplicative.ofAdd p.u, ?_⟩
      apply ModuleExt.ext
      · rfl
      · simpa using hp.symm
  sec := fun g => ModuleExt.lift z id g
  sec_one := by
    apply ModuleExt.ext <;> rfl
  proj_sec := fun _ => rfl
  conj_incl := by
    intro e a
    exact (ModuleExt.conj_incl e a).symm

@[simp] theorem ofModuleTwoCocycle_incl (z : ModuleTwoCocycle L A) (a : A) :
    (ofModuleTwoCocycle z).incl (Multiplicative.ofAdd a) = ModuleExt.incl z a := rfl

@[simp] theorem ofModuleTwoCocycle_proj (z : ModuleTwoCocycle L A) (p : ModuleExt z) :
    (ofModuleTwoCocycle z).proj p = p.g := rfl

@[simp] theorem ofModuleTwoCocycle_sec (z : ModuleTwoCocycle L A) (g : L) :
    (ofModuleTwoCocycle z).sec g = ModuleExt.lift z id g := rfl

end FiniteModuleExtension

section FiniteConverse

variable {iota rel L A : Type}
  [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]

/-- A cocycle whose relator vector realizes `r` modulo the Fox differential gives an actual
finite extension with generator lifts whose relator fibres are exactly `r`.

The relation hypothesis is necessary only to identify the evaluated relator with the identity
fibre in `ModuleExt z`; it is automatic for finite quotients of a marked presentation. -/
noncomputable def finiteRelatorExtensionWitness_of_realization
    (W : rel → PWord iota) (m : iota → L) (w : rel → FreeGroup iota)
    (hres : ResolvesAt W w (WordLift A L))
    (hrel : ∀ k, PWord.eval m (W k) = 1)
    (r : rel → A) (z : ModuleTwoCocycle L A)
    (hz : (fun k => moduleRel (W k) m z) - r ∈
      (heisD1 (A := A) m w).range) :
    FiniteRelatorExtensionWitness W m r := by
  classical
  let a : iota → A := -Classical.choose hz
  have ha : ∀ k, heisD1 (A := A) m w a k + moduleRel (W k) m z = r k := by
    intro k
    have hchosen := congrFun (Classical.choose_spec hz) k
    rw [show a = -Classical.choose hz from rfl]
    rw [map_neg]
    change -(heisD1 (A := A) m w (Classical.choose hz) k) +
      moduleRel (W k) m z = r k
    rw [hchosen]
    simp
  exact
    { extension := FiniteModuleExtension.ofModuleTwoCocycle z
      liftGen := fun i => ModuleExt.incl z (a i) * ModuleExt.lift z m i
      proj_liftGen := by
        intro i
        change (ModuleExt.baseProj z)
          (ModuleExt.incl z (a i) * ModuleExt.lift z m i) = m i
        simp only [map_mul, ModuleExt.baseProj_apply, ModuleExt.incl_g,
          ModuleExt.lift_g, one_mul]
      relator_lift := by
        intro k
        change PWord.eval
          (fun i => ModuleExt.incl z (a i) * ModuleExt.lift z m i) (W k) =
            ModuleExt.incl z (r k)
        rw [moduleWord_eval_shift W w m z hres a k]
        rw [moduleWord_eval_lift_eq_incl (W k) m z (hrel k)]
        rw [← ModuleExt.incl_add, ha k] }

/-- Finite relator realization and finite-extension asphericity are equivalent when the
relators hold at the finite marking. -/
theorem finiteRelatorExtensionAsphericity_iff_realization
    (W : rel → PWord iota) (m : iota → L) (w : rel → FreeGroup iota)
    (hres : ResolvesAt W w (WordLift A L))
    (hrel : ∀ k, PWord.eval m (W k) = 1) :
    FiniteRelatorExtensionAsphericity (A := A) W m ↔
      ∀ r : rel → A, ∃ z : ModuleTwoCocycle L A,
        (fun k => moduleRel (W k) m z) - r ∈
          (heisD1 (A := A) m w).range := by
  constructor
  · exact finiteRelatorRealization_of_extensionAsphericity W m w hres
  · intro hreal r
    obtain ⟨z, hz⟩ := hreal r
    exact ⟨finiteRelatorExtensionWitness_of_realization W m w hres hrel r z hz⟩

end FiniteConverse

section ProfiniteConverse

variable {iota rel : Type} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {J : Set iota}

local instance asphericityConverseQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Relator realization for a marked profinite presentation produces finite-extension
asphericity.  The presentation's finite-quotient relation clause supplies the only extra fact
needed by the canonical `ModuleExt` construction. -/
theorem moduleFiniteExtensionAsphericity_of_relatorRealization
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hreal : ModuleRelatorRealization (A := A) W gen rho c w) :
    ModuleFiniteExtensionAsphericity (A := A) W gen rho := by
  intro r
  obtain ⟨V, hV, z, hz⟩ := hreal r
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  let m : iota → G ⧸ V.toSubgroup :=
    fun i => QuotientGroup.mk' V.toSubgroup (gen i)
  let R := hresolve V hV
  have hrel : ∀ k, PWord.eval m (W k) = 1 := by
    intro k
    let pi : ContinuousMonoidHom G (G ⧸ V.toSubgroup) :=
      ⟨QuotientGroup.mk' V.toSubgroup, continuous_quot_mk⟩
    exact hpres.rel pi k
  have hz' : (fun k => moduleRel (W k) m z) - r ∈
      (heisD1 (A := A) m R.word).range := by
    rw [R.range_eq]
    exact hz
  exact ⟨V, hV, ⟨finiteRelatorExtensionWitness_of_realization
    W m R.word R.resolves hrel r z hz'⟩⟩

/-- For a marked profinite presentation, the finite-extension and finite-cocycle formulations
are equivalent. -/
theorem moduleFiniteExtensionAsphericity_iff_relatorRealization
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i => QuotientGroup.mk' V.toSubgroup (gen i))) :
    ModuleFiniteExtensionAsphericity (A := A) W gen rho ↔
      ModuleRelatorRealization (A := A) W gen rho c w := by
  constructor
  · exact moduleRelatorRealization_of_extensionAsphericity W gen rho c w hresolve
  · exact moduleFiniteExtensionAsphericity_of_relatorRealization
      hpres rho c w hresolve

end ProfiniteConverse

end GQ2.Dyadic.Count
