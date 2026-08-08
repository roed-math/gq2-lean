/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenModel
import GQ2.Dyadic.Instances.EvenForwardRouteSkeleton

/-!
# W51-EV3G: even finite-level compactness and the forward supply

Ticket **EV-3g** of `docs/dyadic/ev4b-stage-abstraction.md` §4: the model-side
compactness/limit station of the even-degree forward route, cloned from the model half of
`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteFinite.lean` (the `OpenTuple`-to-`EpiData`
adapter at lines 678–830, then the inverse-limit argument at lines 276–430).

The station takes the levelwise output of the even stage induction — a nonempty generic
`StageGeneric.OpenTuple` at every open normal subgroup of `G_K(2)`, which is exactly what
`Tuple.openTuple_nonempty_of_base_and_corrections` produces from EV-3e's level-three base and
EV-3f's per-stage defect reachability — and returns the even forward-generator package
`EvenForward.NForwardGeneratorData α h chiCycKTwo` (respectively the `M` twin), i.e. the
supplies `EvenForward.EvenDegreeGalK{N,M}ForwardGeneratorSupply α` that
`EvenForwardRouteSkeleton.lean` §5 consumes.

## Where the compactness actually lives

The committed L station runs König and compactness on `SqCyclotomicFiniteLevelEpiData`, whose
elements carry a marked epimorphism out of the presented model `DSq h`.  Nothing in that
argument uses the model: the compactness input is the *tuple* in each finite quotient, and the
model enters only to name the datum.  Since W50's `OpenTuple` already isolates that
model-independent content, §2 below runs the whole cofiltered/König/compactness argument once,
generically in `(W, v, G, chi)`, ending at

  `OpenTuple.exists_globalMarking` :
      `(∀ U, Nonempty (OpenTuple W v G chi U))` →
      `∃ gen, (∀ i, chi (gen i) = v i) ∧ W.word gen = 1 ∧ ⟪range gen⟫‾ = ⊤`.

The `N` and `M` endpoints are then two-line readings of that theorem against the EV-3b tables
`vN α` / `vM α`, and the even `FiniteLevelEpiData` layer of §3–§4 — the DN/DM-specific adapter
the board asks for, built on the committed `nLiftHom` / `mLiftHom` — sits beside the limit
argument rather than inside it.  Both structures come with the cofiltered functor and the
`Finite` instance, in the committed shape, so a future finite-level *presentation* statement
(the even analogue of `OddDegreeGalKSqCyclotomicFiniteLevelPresentation`) has them ready.

## Restated private helpers

Five declarations of the committed template are `private` and are restated here with their
committed proofs, verbatim: `projMap_quotientMk`, `projMap_self`, `projMap_comp_apply` (needed
for the functoriality of the restriction maps) and the two compactness helpers
`mem_closedSet_of_finiteQuotient_approximations` and
`mem_closedSubgroup_of_finiteQuotient_approximations`.  The board flagged the last two; the
three `projMap` lemmas are the same situation and are recorded here as drift from the ticket
text.  All five are `private` here as well, so no public name of this file collides with the
committed template.

## The `α` hypothesis

The two finite-level structures, their functors, their `Finite` instances and both model
adapters need **no** hypothesis on `α`: they mention only `MarkedCore.nRelWord α`,
`MarkedCore.dnGen α h` and the row table `vN α`, none of which constrains `α`.  The hypothesis
`1 ≤ α` appears exactly where a `StageWord` does, since `nStageWord α h hα` / `mStageWord α h hα`
carry EV-3a's honest `1 ≤ α`: in the `OpenTuple`-shaped statements of §5–§6.  Nothing here is
stated at the even lane's standing `2 ≤ α`.

## Nothing here is consumed by the committed route

As with the EV-4b and EV-3a/b files, this module is imported by nothing.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 CategoryTheory
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Restated private helpers of the committed template

`GammaLSylowPreimageFieldLabuteFinite.lean` keeps these five facts `private`, so they are not
importable.  Each is restated below with the committed statement and the committed proof. -/

@[simp] private theorem projMap_quotientMk
    {G : Type} [Group G] [TopologicalSpace G]
    {U U' : Subgroup G} [U.Normal] [U'.Normal]
    [DiscreteTopology (G ⧸ U)] (hle : U ≤ U') (x : G) :
    projMap hle (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

@[simp] private theorem projMap_self
    {G : Type} [Group G] [TopologicalSpace G]
    {U : Subgroup G} [U.Normal] [DiscreteTopology (G ⧸ U)] (hle : U ≤ U) :
    projMap hle = ContinuousMonoidHom.id (G ⧸ U) := by
  exact ContinuousMonoidHom.ext fun y ↦ QuotientGroup.induction_on y fun _ ↦ rfl

@[simp] private theorem projMap_comp_apply
    {G : Type} [Group G] [TopologicalSpace G]
    {U U' U'' : Subgroup G} [U.Normal] [U'.Normal] [U''.Normal]
    [DiscreteTopology (G ⧸ U)] [DiscreteTopology (G ⧸ U')]
    (hle : U ≤ U') (hle' : U' ≤ U'') (y : G ⧸ U) :
    projMap hle' (projMap hle y) = projMap (hle.trans hle') y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

/-- A closed subset of a profinite group contains any element which can be approximated by
that subset in every finite quotient.  The subset form is needed for nontrivial cyclotomic
fibres; the subgroup form below is the special case used for the handle rows. -/
private theorem mem_closedSet_of_finiteQuotient_approximations
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (S : Set G) (hS : IsClosed S) (x : G)
    (happrox : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G),
      ∃ y : G, y ∈ S ∧ QuotientGroup.mk y =
        (QuotientGroup.mk x : G ⧸ U.toSubgroup)) :
    x ∈ S := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  haveI : Nonempty (OpenNormalSubgroup (ProfiniteGrp.of G)) :=
    ⟨⟨⊤, Subgroup.normal_top⟩⟩
  haveI hdisc : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G),
      DiscreteTopology (G ⧸ U.toSubgroup) := fun U ↦ inferInstance
  have hnonempty :
      (⋂ U : OpenNormalSubgroup (ProfiniteGrp.of G),
        {y : S | QuotientGroup.mk y.1 =
          (QuotientGroup.mk x : G ⧸ U.toSubgroup)}).Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro U U'
      refine ⟨U ⊓ U', fun y hy ↦ ?_, fun y hy ↦ ?_⟩ <;>
        simp only [Set.mem_setOf_eq] at hy ⊢
      · rw [QuotientGroup.eq] at hy ⊢
        exact (show (U ⊓ U').toSubgroup ≤ U.toSubgroup from inf_le_left) hy
      · rw [QuotientGroup.eq] at hy ⊢
        exact (show (U ⊓ U').toSubgroup ≤ U'.toSubgroup from inf_le_right) hy
    · intro U
      obtain ⟨y, hyH, hy⟩ := happrox U
      exact ⟨⟨y, hyH⟩, hy⟩
    · intro U
      exact (isClosed_singleton.preimage
        (continuous_quotient_mk'.comp continuous_subtype_val)).isCompact
    · intro U
      exact isClosed_singleton.preimage
        (continuous_quotient_mk'.comp continuous_subtype_val)
  obtain ⟨y, hy⟩ := hnonempty
  have hyx : y.1 = x := by
    rw [← inv_mul_eq_one]
    apply eq_one_of_forall_mem_openNormalSubgroup
    intro U
    have hq : QuotientGroup.mk y.1 =
        (QuotientGroup.mk x : G ⧸ U.toSubgroup) := Set.mem_iInter.mp hy U
    rw [QuotientGroup.eq] at hq
    exact hq
  rw [← hyx]
  exact y.property

/-- Subgroup specialization of `mem_closedSet_of_finiteQuotient_approximations`. -/
private theorem mem_closedSubgroup_of_finiteQuotient_approximations
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (x : G)
    (happrox : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G),
      ∃ y : G, y ∈ H ∧ QuotientGroup.mk y =
        (QuotientGroup.mk x : G ⧸ U.toSubgroup)) :
    x ∈ H :=
  mem_closedSet_of_finiteQuotient_approximations (H : Set G) hH x happrox

/-! ## §2 The generic open-quotient limit

The cofiltered system of open-quotient markings, its `Finite` instances, and the König plus
compactness argument, all stated for the W50 `OpenTuple`.  This is the committed template's
lines 276–430 with the presented model deleted; the even cores enter only in §3 onwards. -/

namespace OpenTuple

variable {n : ℕ} {W : StageWord n} {v : Fin n → ℤ_[2]ˣ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {U U' : OpenNormalSubgroup (ProfiniteGrp.of G)}

omit [T2Space G] in
/-- Two open-quotient markings at the same level agree as soon as their tuples do: the three
remaining fields are proofs. -/
theorem eq_of_generators_eq {O O' : OpenTuple W v G chi U}
    (hgen : O.generators = O'.generators) : O = O' := by
  cases O
  cases O'
  cases hgen
  rfl

/-- Restrict an open-quotient marking along a coarser quotient (the `map` clone). -/
def map (hle : U ≤ U') (O : OpenTuple W v G chi U) : OpenTuple W v G chi U' where
  generators i := projMap hle (O.generators i)
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := O.rows i
    refine ⟨x, hxchi, ?_⟩
    rw [hx, projMap_quotientMk]
  relation := by
    rw [← W.map_word (projMap hle) O.generators, O.relation, map_one]
  topGen := by
    have hmap := congrArg (Subgroup.map (projMap hle).toMonoidHom) O.topGen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (projMap_surjective hle), ← Set.range_comp] at hmap
    exact hmap

omit [T2Space G] in
@[simp] theorem map_generators (hle : U ≤ U') (O : OpenTuple W v G chi U) (i : Fin n) :
    (O.map hle).generators i = projMap hle (O.generators i) := rfl

/-- Open-quotient markings form a cofiltered functor under quotient restriction (the
`SqCyclotomicFiniteLevelEpiData.functor` clone). -/
def functor (W : StageWord n) (v : Fin n → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) :
    OpenNormalSubgroup (ProfiniteGrp.of G) ⥤ Type where
  obj U := OpenTuple W v G chi U
  map {_ _} f := ↾(map (leOfHom f))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro O
    apply eq_of_generators_eq
    funext i
    simp [map]
  map_comp {_ _ _} f g := by
    apply ConcreteCategory.hom_ext
    intro O
    apply eq_of_generators_eq
    funext i
    simp [map]

/-- Each open-quotient marking set is finite: it injects into the finitely many tuples in the
finite quotient.  (The committed template counts continuous homomorphisms out of the presented
model instead; with the model removed, the count is immediate.) -/
instance finite (W : StageWord n) (v : Fin n → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) (U : OpenNormalSubgroup (ProfiniteGrp.of G)) :
    Finite (OpenTuple W v G chi U) := by
  haveI : Finite (G ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  exact Finite.of_injective (fun O ↦ O.generators) fun O O' he ↦ eq_of_generators_eq he

end OpenTuple

end

end GQ2.Dyadic.StageGeneric
