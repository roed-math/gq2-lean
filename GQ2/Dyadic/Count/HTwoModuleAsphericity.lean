/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleSurjectivity

/-!
# Finite extension asphericity for the degree-two module comparison

This file isolates a finite-group extension-realization input that implies finite relator
realization.  A `FiniteModuleExtension L A` is an exact finite extension

`1 → A → E → L → 1`

with the prescribed conjugation action and a normalized set section.  A
`FiniteRelatorExtensionWitness W m r` additionally gives generator lifts in `E`
whose defining relators have the prescribed fibre labels `r`.

The factor set of the section is constructed here and proved to be a normalized
module cocycle.  Comparing the chosen generator lifts with the section shows that
its relator vector is `r` modulo the Fox differential.  Consequently:

`ModuleFiniteExtensionAsphericity → ModuleRelatorRealization`.

Unlike `ModuleRelatorRealization`, the new hypothesis contains no cocycle or
cohomology object and no word-cokernel.  It is a concrete finite-extension formulation
of the same relator-realization obstruction.

Terminological warning: `FiniteRelatorExtensionAsphericity` and
`ModuleFiniteExtensionAsphericity` are not definitions of classical presentation
asphericity (`π₂ = 0`) or of relation-module freeness/projectivity.  The converse file proves
that, once the relators hold and a resolver is fixed, these predicates are equivalent to the
finite-cocycle relator-realization criterion.  A genuine relation-module or profinite
asphericity theorem could imply them, but that stronger structural assertion is not encoded
here.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic

structure FiniteModuleExtension (L A : Type*) [Group L] [AddCommGroup A]
    [DistribMulAction L A] where
  E : Type
  [groupE : Group E]
  [topE : TopologicalSpace E]
  [discE : DiscreteTopology E]
  [finiteE : Finite E]
  incl : Multiplicative A →* E
  proj : E →* L
  incl_injective : Function.Injective incl
  range_eq_ker : incl.range = proj.ker
  sec : L → E
  sec_one : sec 1 = 1
  proj_sec : ∀ g, proj (sec g) = g
  conj_incl : ∀ (e : E) (a : A),
    e * incl (Multiplicative.ofAdd a) * e⁻¹ =
      incl (Multiplicative.ofAdd (proj e • a))

namespace FiniteModuleExtension

variable {L A : Type*} [Group L] [AddCommGroup A] [DistribMulAction L A]

attribute [instance] groupE topE discE finiteE

/-- Package an exact finite group extension.  The normalized set section is
constructed by choice from surjectivity; it is not additional mathematical data. -/
noncomputable def ofSurjective {E : Type} [Group E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E]
    (incl : Multiplicative A →* E) (proj : E →* L)
    (hincl : Function.Injective incl) (hrange : incl.range = proj.ker)
    (hsurj : Function.Surjective proj)
    (hconj : ∀ (e : E) (a : A),
      e * incl (Multiplicative.ofAdd a) * e⁻¹ =
        incl (Multiplicative.ofAdd (proj e • a))) : FiniteModuleExtension L A := by
  classical
  exact
    { E := E
      incl := incl
      proj := proj
      incl_injective := hincl
      range_eq_ker := hrange
      sec := fun g => if g = 1 then 1 else Function.surjInv hsurj g
      sec_one := if_pos rfl
      proj_sec := by
        intro g
        split
        · rename_i hg
          simp [hg]
        · exact Function.surjInv_eq hsurj g
      conj_incl := hconj }

noncomputable def factor (D : FiniteModuleExtension L A) (g h : L) : A :=
  Multiplicative.toAdd (Function.invFun D.incl
    (D.sec g * D.sec h * (D.sec (g * h))⁻¹))

theorem factor_spec (D : FiniteModuleExtension L A) (g h : L) :
    D.incl (Multiplicative.ofAdd (D.factor g h)) =
      D.sec g * D.sec h * (D.sec (g * h))⁻¹ := by
  rw [factor, ofAdd_toAdd]
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, D.range_eq_ker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, D.proj_sec]
  group

noncomputable def factorCocycle (D : FiniteModuleExtension L A) : ModuleTwoCocycle L A where
  κ := D.factor
  norm := by
    apply Multiplicative.ofAdd.injective
    apply D.incl_injective
    simp [D.factor_spec, D.sec_one]
  cocyc := by
    intro g h k
    apply Multiplicative.ofAdd.injective
    apply D.incl_injective
    rw [ofAdd_add, map_mul, ofAdd_add, map_mul]
    have hconj := D.conj_incl (D.sec g) (D.factor h k)
    rw [D.proj_sec] at hconj
    rw [← hconj]
    rw [show D.incl (Multiplicative.ofAdd (D.factor (g * h) k)) *
          D.incl (Multiplicative.ofAdd (D.factor g h)) =
        D.incl (Multiplicative.ofAdd (D.factor g h)) *
          D.incl (Multiplicative.ofAdd (D.factor (g * h) k)) from
      (Commute.all
        (Multiplicative.ofAdd (D.factor (g * h) k))
        (Multiplicative.ofAdd (D.factor g h))).map D.incl]
    rw [D.factor_spec, D.factor_spec, D.factor_spec, D.factor_spec]
    group

theorem proj_incl (D : FiniteModuleExtension L A) (a : A) :
    D.proj (D.incl (Multiplicative.ofAdd a)) = 1 := by
  rw [← MonoidHom.mem_ker, ← D.range_eq_ker]
  exact ⟨Multiplicative.ofAdd a, rfl⟩

/-- The factor-set model of an extension maps back to the extension. -/
noncomputable def factorToExtension (D : FiniteModuleExtension L A) :
    ModuleExt D.factorCocycle →* D.E where
  toFun p := D.incl (Multiplicative.ofAdd p.u) * D.sec p.g
  map_one' := by simp [D.sec_one]
  map_mul' p q := by
    simp only [ModuleExt.mul_u, ModuleExt.mul_g, ofAdd_add, map_mul]
    have hconj := D.conj_incl (D.sec p.g) q.u
    rw [D.proj_sec] at hconj
    have hmove : D.sec p.g * D.incl (Multiplicative.ofAdd q.u) =
        D.incl (Multiplicative.ofAdd (p.g • q.u)) * D.sec p.g := by
      rw [← hconj]
      group
    have hfactor : D.sec p.g * D.sec q.g =
        D.incl (Multiplicative.ofAdd (D.factor p.g q.g)) * D.sec (p.g * q.g) := by
      rw [D.factor_spec]
      group
    change D.incl (Multiplicative.ofAdd p.u) *
          D.incl (Multiplicative.ofAdd (p.g • q.u)) *
          D.incl (Multiplicative.ofAdd (D.factor p.g q.g)) * D.sec (p.g * q.g) = _
    calc
      _ = D.incl (Multiplicative.ofAdd p.u) *
            D.incl (Multiplicative.ofAdd (p.g • q.u)) *
            (D.incl (Multiplicative.ofAdd (D.factor p.g q.g)) *
              D.sec (p.g * q.g)) := by group
      _ = D.incl (Multiplicative.ofAdd p.u) *
            D.incl (Multiplicative.ofAdd (p.g • q.u)) *
            (D.sec p.g * D.sec q.g) := by rw [← hfactor]
      _ = D.incl (Multiplicative.ofAdd p.u) *
            (D.sec p.g * D.incl (Multiplicative.ofAdd q.u)) * D.sec q.g := by
          rw [hmove]
          group
      _ = _ := by group

@[simp] theorem factorToExtension_apply (D : FiniteModuleExtension L A)
    (p : ModuleExt D.factorCocycle) :
    D.factorToExtension p = D.incl (Multiplicative.ofAdd p.u) * D.sec p.g := rfl

theorem factorToExtension_injective (D : FiniteModuleExtension L A) :
    Function.Injective D.factorToExtension := by
  intro p q hpq
  have hg : p.g = q.g := by
    have h := congrArg D.proj hpq
    simpa [D.proj_incl, D.proj_sec] using h
  apply ModuleExt.ext
  · apply Multiplicative.ofAdd.injective
    apply D.incl_injective
    apply mul_right_cancel (b := D.sec p.g)
    simpa [hg] using hpq
  · exact hg

@[simp] theorem factorToExtension_lift {X : Type*} (D : FiniteModuleExtension L A)
    (m : X → L) (i : X) :
    D.factorToExtension (ModuleExt.lift D.factorCocycle m i) = D.sec (m i) := by
  simp [factorToExtension_apply]

end FiniteModuleExtension

/-! Relation-level finite extension witnesses. -/

structure FiniteRelatorExtensionWitness {iota rel L A : Type}
    [Group L] [AddCommGroup A] [DistribMulAction L A]
    (W : rel → PWord iota) (m : iota → L) (r : rel → A) where
  extension : FiniteModuleExtension L A
  liftGen : iota → extension.E
  proj_liftGen : ∀ i, extension.proj (liftGen i) = m i
  relator_lift : ∀ k, PWord.eval liftGen (W k) =
    extension.incl (Multiplicative.ofAdd (r k))

namespace FiniteRelatorExtensionWitness

variable {iota rel L A : Type}
  [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]

noncomputable def offset {W : rel → PWord iota} {m : iota → L} {r : rel → A}
    (D : FiniteRelatorExtensionWitness W m r) (i : iota) : A :=
  Multiplicative.toAdd (Function.invFun D.extension.incl
    (D.liftGen i * (D.extension.sec (m i))⁻¹))

omit [TopologicalSpace L] [DiscreteTopology L] [Finite L] [Finite A] in
theorem offset_spec {W : rel → PWord iota} {m : iota → L} {r : rel → A}
    (D : FiniteRelatorExtensionWitness W m r) (i : iota) :
    D.extension.incl (Multiplicative.ofAdd (D.offset i)) *
        D.extension.sec (m i) = D.liftGen i := by
  have hker : D.liftGen i * (D.extension.sec (m i))⁻¹ ∈
      D.extension.proj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, D.proj_liftGen,
      D.extension.proj_sec]
    group
  have hincl : D.extension.incl (Multiplicative.ofAdd (D.offset i)) =
      D.liftGen i * (D.extension.sec (m i))⁻¹ := by
    rw [offset, ofAdd_toAdd]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, D.extension.range_eq_ker]
    exact hker
  rw [hincl]
  group

theorem relator_fibre_eq {W : rel → PWord iota} {m : iota → L} {r : rel → A}
    (D : FiniteRelatorExtensionWitness W m r)
    (w : rel → FreeGroup iota)
    (hres : ResolvesAt W w (WordLift A L)) (k : rel) :
    heisD1 (A := A) m w D.offset k +
        moduleRel (W k) m D.extension.factorCocycle = r k := by
  let F : ContinuousMonoidHom
      (ModuleExt D.extension.factorCocycle) D.extension.E :=
    ⟨D.extension.factorToExtension, continuous_of_discreteTopology⟩
  let shifted : iota → ModuleExt D.extension.factorCocycle := fun i =>
    ModuleExt.incl D.extension.factorCocycle (D.offset i) *
      ModuleExt.lift D.extension.factorCocycle m i
  have hgen : (fun i => F (shifted i)) = D.liftGen := by
    funext i
    dsimp only [F, shifted]
    change D.extension.factorToExtension
        (ModuleExt.incl D.extension.factorCocycle (D.offset i) *
          ModuleExt.lift D.extension.factorCocycle m i) = D.liftGen i
    rw [map_mul, FiniteModuleExtension.factorToExtension_lift]
    change (D.extension.incl (Multiplicative.ofAdd (D.offset i)) *
        D.extension.sec 1) * D.extension.sec (m i) = D.liftGen i
    rw [D.extension.sec_one, mul_one]
    exact D.offset_spec i
  have hmap := PWord.map_eval F shifted (W k)
  rw [hgen, D.relator_lift] at hmap
  have hinternal : PWord.eval shifted (W k) =
      ModuleExt.incl D.extension.factorCocycle (r k) := by
    apply D.extension.factorToExtension_injective
    have hrhs : F (ModuleExt.incl D.extension.factorCocycle (r k)) =
        D.extension.incl (Multiplicative.ofAdd (r k)) := by
      dsimp only [F]
      change D.extension.incl (Multiplicative.ofAdd (r k)) *
          D.extension.sec 1 = D.extension.incl (Multiplicative.ofAdd (r k))
      rw [D.extension.sec_one, mul_one]
    exact hmap.trans hrhs.symm
  have hformula := moduleRel_shift W w m D.extension.factorCocycle hres D.offset k
  exact hformula.symm.trans (congrArg ModuleExt.u hinternal)

theorem relator_vector_mod_range {W : rel → PWord iota} {m : iota → L}
    {r : rel → A} (D : FiniteRelatorExtensionWitness W m r)
    (w : rel → FreeGroup iota) (hres : ResolvesAt W w (WordLift A L)) :
    (fun k => moduleRel (W k) m D.extension.factorCocycle) - r ∈
      (heisD1 (A := A) m w).range := by
  refine ⟨-D.offset, ?_⟩
  funext k
  rw [map_neg]
  have h := D.relator_fibre_eq w hres k
  change -(heisD1 (A := A) m w D.offset k) =
    moduleRel (W k) m D.extension.factorCocycle - r k
  have hz : heisD1 (A := A) m w D.offset k +
      (moduleRel (W k) m D.extension.factorCocycle - r k) = 0 := by
    rw [add_sub, h, sub_self]
  exact neg_eq_of_add_eq_zero_right hz

end FiniteRelatorExtensionWitness

/-- Every assignment of fibre labels to the defining relators is realized by a
finite extension of the marked finite group.  This is a finite extension-realization
condition: it mentions neither cocycles nor cohomology.  Despite the historical name, it is
not classical presentation asphericity. -/
def FiniteRelatorExtensionAsphericity {iota rel L A : Type}
    [Group L] [AddCommGroup A] [DistribMulAction L A]
    (W : rel → PWord iota) (m : iota → L) : Prop :=
  ∀ r : rel → A, Nonempty (FiniteRelatorExtensionWitness W m r)

section FiniteExtensionCriterion

variable {iota rel L A : Type}
  [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]

/-- Finite-extension asphericity realizes all relator vectors modulo the Fox
differential at the same finite level. -/
theorem finiteRelatorRealization_of_extensionAsphericity
    (W : rel → PWord iota) (m : iota → L) (w : rel → FreeGroup iota)
    (hres : ResolvesAt W w (WordLift A L))
    (hasph : FiniteRelatorExtensionAsphericity (A := A) W m) :
    ∀ r : rel → A, ∃ z : ModuleTwoCocycle L A,
      (fun k => moduleRel (W k) m z) - r ∈ (heisD1 (A := A) m w).range := by
  intro r
  let D := Classical.choice (hasph r)
  exact ⟨D.extension.factorCocycle, D.relator_vector_mod_range w hres⟩

end FiniteExtensionCriterion

section ProfiniteExtensionCriterion

variable {iota rel : Type} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C}

local instance extensionAsphericityQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- The profinite finite-extension realization input: each requested relator
vector is realized in a finite extension of some action-compatible quotient.

The quotient and extension may depend on the vector.  There is no cocycle,
continuous cohomology group, or word-cokernel in this definition.  This is not a conventional
asphericity or relation-module projectivity predicate. -/
def ModuleFiniteExtensionAsphericity
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) : Prop :=
  ∀ r : rel → A, ∃ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    Nonempty (FiniteRelatorExtensionWitness W
      (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) r)

omit [Fintype iota] [Fintype rel] [DecidableEq iota]
  [TotallyDisconnectedSpace G] [DiscreteTopology C] [Finite C]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] in
/-- Finite-extension asphericity implies the finite-cocycle relator realization
criterion.  The proof constructs the factor-set cocycle of each extension; the
resolver is used only to identify changes of generator lifts with `heisD1`. -/
theorem moduleRelatorRealization_of_extensionAsphericity
    (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (w : rel → FreeGroup iota)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hasph : ModuleFiniteExtensionAsphericity (A := A) W gen rho) :
    ModuleRelatorRealization (A := A) W gen rho c w := by
  intro r
  obtain ⟨V, hV, hD⟩ := hasph r
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  let D := Classical.choice hD
  let R := hresolve V hV
  refine ⟨V, hV, D.extension.factorCocycle, ?_⟩
  have hlocal := D.relator_vector_mod_range R.word R.resolves
  rw [R.range_eq] at hlocal
  exact hlocal

end ProfiniteExtensionCriterion

end GQ2.Dyadic.Count
