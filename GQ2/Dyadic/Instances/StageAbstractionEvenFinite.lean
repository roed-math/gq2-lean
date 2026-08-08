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

/-- **The generic inverse limit.**  Pointwise nonemptiness of the open-quotient marking sets is
enough to produce one global marking of `G`: König's lemma supplies a coherent family,
compactness of `G` realizes the tuple coordinates, and finite-quotient separation supplies the
literal relation, the exact `chi`-values of every row, and topological generation.

This is `forwardGeneratorData_of_finiteLevel` (the committed template, lines 276–430) with the
presented model deleted from both ends.  Every even endpoint of §5 below is a reading of this
statement against the EV-3b row tables. -/
theorem exists_globalMarking
    (hne : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G), Nonempty (OpenTuple W v G chi U)) :
    ∃ gen : Fin n → G, (∀ i, chi (gen i) = v i) ∧ W.word gen = 1 ∧
      (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤ := by
  classical
  let F := functor W v G chi
  haveI hne' : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G), Nonempty (F.obj U) := hne
  haveI hfin' : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G), Finite (F.obj U) := fun U ↦ by
    change Finite (OpenTuple W v G chi U)
    infer_instance
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_cofiltered_system F
  let D : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G), OpenTuple W v G chi U := fun U ↦ sec U
  have hcompat : ∀ {U U' : OpenNormalSubgroup (ProfiniteGrp.of G)} (hle : U ≤ U') (i : Fin n),
      projMap hle ((D U).generators i) = (D U').generators i := by
    intro U U' hle i
    have hs := hsec hle.hom
    exact congrArg (fun E : OpenTuple W v G chi U' ↦ E.generators i) hs
  haveI : Nonempty (OpenNormalSubgroup (ProfiniteGrp.of G)) :=
    ⟨⟨⊤, Subgroup.normal_top⟩⟩
  haveI hdisc : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G),
      DiscreteTopology (G ⧸ U.toSubgroup) := fun U ↦ inferInstance
  -- Compactness realizes each coordinate of the coherent family by a global element.
  have hrealise : ∀ i : Fin n, ∃ g : G, ∀ U, QuotientGroup.mk g = (D U).generators i := by
    intro i
    have hmeet :
        (⋂ U : OpenNormalSubgroup (ProfiniteGrp.of G),
          {g : G | QuotientGroup.mk g = (D U).generators i}).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U U'
        refine ⟨U ⊓ U', fun g hg ↦ ?_, fun g hg ↦ ?_⟩ <;>
          simp only [Set.mem_setOf_eq] at hg ⊢
        · have hle : U ⊓ U' ≤ U := inf_le_left
          rw [← hcompat hle i, ← hg, projMap_quotientMk]
        · have hle : U ⊓ U' ≤ U' := inf_le_right
          rw [← hcompat hle i, ← hg, projMap_quotientMk]
      · intro U
        exact QuotientGroup.mk_surjective ((D U).generators i)
      · intro U
        exact (isClosed_singleton.preimage continuous_quotient_mk').isCompact
      · intro U
        exact isClosed_singleton.preimage continuous_quotient_mk'
    obtain ⟨g, hg⟩ := hmeet
    exact ⟨g, fun U ↦ Set.mem_iInter.mp hg U⟩
  let gen : Fin n → G := fun i ↦ (hrealise i).choose
  have hgen (U : OpenNormalSubgroup (ProfiniteGrp.of G)) (i : Fin n) :
      QuotientGroup.mk (gen i) = (D U).generators i := (hrealise i).choose_spec U
  refine ⟨gen, ?_, ?_, ?_⟩
  · -- Every row value is exact: it is approximated by the exact fibre in every finite quotient.
    intro i
    have hmem : gen i ∈ {x : G | chi x = v i} := by
      apply mem_closedSet_of_finiteQuotient_approximations
        {x : G | chi x = v i} (isClosed_singleton.preimage chi.continuous_toFun)
      intro U
      obtain ⟨x, hxchi, hx⟩ := (D U).rows i
      exact ⟨x, hxchi, hx.symm.trans (hgen U i).symm⟩
    exact hmem
  · -- The literal relator dies, by separation through the finite quotients.
    apply eq_one_of_forall_mem_openNormalSubgroup
    intro U
    apply (QuotientGroup.eq_one_iff _).mp
    calc
      QuotientGroup.mk (W.word gen) =
          W.word (fun i ↦ (QuotientGroup.mk (gen i) : G ⧸ U.toSubgroup)) :=
        W.map_word (QuotientGroup.mk' U.toSubgroup) gen
      _ = W.word (D U).generators := by
        congr 1
        funext i
        exact hgen U i
      _ = 1 := (D U).relation
  · -- Topological generation, again by approximation inside the closed generated subgroup.
    set A : Subgroup G := Subgroup.closure (Set.range gen) with hA
    have hAclosed : IsClosed ((A.topologicalClosure : Subgroup G) : Set G) :=
      Subgroup.isClosed_topologicalClosure A
    rw [eq_top_iff]
    intro y _
    apply mem_closedSubgroup_of_finiteQuotient_approximations A.topologicalClosure hAclosed y
    intro U
    have hy : (QuotientGroup.mk y : G ⧸ U.toSubgroup) ∈
        Subgroup.closure (Set.range (D U).generators) := by
      rw [(D U).topGen]
      trivial
    have himage : Set.range (D U).generators =
        QuotientGroup.mk' U.toSubgroup '' Set.range gen := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨gen i, ⟨i, rfl⟩, hgen U i⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hgen U i).symm⟩
    rw [himage, ← MonoidHom.map_closure] at hy
    obtain ⟨z, hzA, hz⟩ := hy
    exact ⟨z, Subgroup.le_topologicalClosure A hzA, hz⟩

end OpenTuple

/-! ## §3 The even finite-level marked epimorphisms at the `N` core

The `SqCyclotomicFiniteLevelEpiData` clone at `D_N α h`.  As in the generic layer, the
template's five separate fibre fields are replaced by the one uniform row field over the EV-3b
table `vN α`: a pinned constructor row records its cyclotomic value, and a handle row records
the value `1`, which is exactly membership of a lift in `ker χ`.

No hypothesis on `α` occurs anywhere in this section: the structure, its restriction maps, the
functor, the `Finite` instance and both adapters mention only `MarkedCore.nRelWord α`,
`MarkedCore.dnGen α h` and `vN α`. -/

/-- A finite-quotient output of the even-degree `N` route.  The homomorphism comes from the
presented core `D_N α h`; the fields record its literal generator table.

The orientation clauses are stated by **liftability to the appropriate cyclotomic fibre**, not
by equality with particular witnesses: such witnesses are chosen noncanonically, fibre
liftability is preserved on passing to a coarser quotient, and it is exactly what compactness
needs to recover the global orientation equalities. -/
structure EvenFiniteLevelNEpiData
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) where
  /-- The marked epimorphism out of the presented `N_α` core. -/
  epi : ContSurj (MarkedCore.DN α h : Type)
    ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup)
  /-- Every marked generator lifts into the exact cyclotomic fibre of its `vN α` row. -/
  rows : ∀ i : Fin (MarkedCore.coreRank h), ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = vN α i ∧
      epi.1 (MarkedCore.dnGen α h i) = QuotientGroup.mk x
  /-- The finite quotient is generated by the displayed tuple. -/
  topGen : Subgroup.closure
    (Set.range fun i ↦ epi.1 (MarkedCore.dnGen α h i)) = ⊤
  /-- Regression field: the relation is literally the committed `MarkedCore.nRelWord α`. -/
  relation : MarkedCore.nRelWord α (fun i ↦ epi.1 (MarkedCore.dnGen α h i)) = 1

namespace EvenFiniteLevelNEpiData

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  {α h : ℕ}
  {U U' : OpenNormalSubgroup
    (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))}

/-- Two finite-level data at the same quotient agree as soon as their epimorphisms do. -/
theorem eq_of_epi_eq {D E : EvenFiniteLevelNEpiData (K := K) α h U}
    (hepi : D.epi = E.epi) : D = E := by
  cases D
  cases E
  cases hepi
  rfl

/-- Restrict finite-level data along a coarser quotient. -/
noncomputable def map (hle : U ≤ U')
    (D : EvenFiniteLevelNEpiData (K := K) α h U) :
    EvenFiniteLevelNEpiData (K := K) α h U' where
  epi := ⟨(projMap hle).comp D.epi.1, (projMap_surjective hle).comp D.epi.2⟩
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := D.rows i
    refine ⟨x, hxchi, ?_⟩
    change projMap hle (D.epi.1 (MarkedCore.dnGen α h i)) = QuotientGroup.mk x
    rw [hx, projMap_quotientMk]
  topGen := by
    change Subgroup.closure
      (Set.range fun i ↦ projMap hle (D.epi.1 (MarkedCore.dnGen α h i))) = ⊤
    have hmap := congrArg (Subgroup.map (projMap hle).toMonoidHom) D.topGen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (projMap_surjective hle), ← Set.range_comp] at hmap
    exact hmap
  relation := by
    change MarkedCore.nRelWord α
      (fun i ↦ projMap hle (D.epi.1 (MarkedCore.dnGen α h i))) = 1
    rw [← MarkedCore.map_nRelWord (projMap hle) α
      (fun i ↦ D.epi.1 (MarkedCore.dnGen α h i)), D.relation, map_one]

/-- Finite-level markings at the `N` core form a cofiltered functor under quotient
restriction. -/
noncomputable def functor
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ) :
    OpenNormalSubgroup (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))) ⥤ Type where
  obj U := EvenFiniteLevelNEpiData (K := K) α h U
  map {_ _} f := ↾(map (leOfHom f))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro D
    apply eq_of_epi_eq
    apply Subtype.ext
    ext x
    simp [map]
  map_comp {_ _ _} f g := by
    apply ConcreteCategory.hom_ext
    intro D
    apply eq_of_epi_eq
    apply Subtype.ext
    ext x
    simp [map]

/-- Each finite-level data type is finite: it injects into the finite set of continuous
homomorphisms from the topologically finitely generated `D_N α h` to the finite quotient. -/
instance finite (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Finite (EvenFiniteLevelNEpiData (K := K) α h U) := by
  haveI : Finite ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  haveI := finite_continuousMonoidHom (dnFinsetTopGen α h)
    ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup)
  exact Finite.of_injective (fun D ↦ D.epi.1) fun D E he ↦
    eq_of_epi_eq (Subtype.ext he)

/-- Forget the presented model: the marked epimorphism's generator table is a generic
open-quotient marking for the even `N` word datum and the `vN α` row table.  This is the
direction the inverse limit consumes. -/
def toOpenTuple (hα : 1 ≤ α) (D : EvenFiniteLevelNEpiData (K := K) α h U) :
    OpenTuple (nStageWord α h hα) (vN α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) U where
  generators i := D.epi.1 (MarkedCore.dnGen α h i)
  rows := D.rows
  relation := D.relation
  topGen := D.topGen

end EvenFiniteLevelNEpiData

/-- Construct even `N` finite-level data from a generating tuple of the finite quotient which
kills the literal `MarkedCore.nRelWord α` and whose rows lift into the exact cyclotomic fibres
of `vN α`.  The epimorphism is the committed universal property `MarkedCore.nLiftHom`; this is
the `finiteLevelEpiDataOfTuple` clone (the committed template, lines 678–744). -/
noncomputable def evenFiniteLevelNEpiDataOfTuple
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (generators : Fin (MarkedCore.coreRank h) →
      (maxProPQuotient 2 (GalK K) ⧸ U.toSubgroup))
    (hrows : ∀ i, ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = vN α i ∧ generators i = QuotientGroup.mk x)
    (hrelation : MarkedCore.nRelWord α generators = 1)
    (htopGen : Subgroup.closure (Set.range generators) = ⊤) :
    EvenFiniteLevelNEpiData (K := K) α h U := by
  let Q := maxProPQuotient 2 (GalK K) ⧸ U.toSubgroup
  have hproQ : IsProP 2 Q := isProP_of_isPGroup (isProP_maxProPQuotient U)
  let f : ContinuousMonoidHom (MarkedCore.DN α h : Type) Q :=
    MarkedCore.nLiftHom α h hproQ generators hrelation
  have hfgen (i : Fin (MarkedCore.coreRank h)) :
      f (MarkedCore.dnGen α h i) = generators i :=
    MarkedCore.nLiftHom_gen α h hproQ generators hrelation i
  have hfsurj : Function.Surjective f := by
    intro y
    have hle : Subgroup.closure (Set.range generators) ≤ f.toMonoidHom.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨MarkedCore.dnGen α h i, hfgen i⟩
    exact hle (by rw [htopGen]; trivial)
  exact
    { epi := ⟨f, hfsurj⟩
      rows := by
        intro i
        obtain ⟨x, hxchi, hx⟩ := hrows i
        exact ⟨x, hxchi, by rw [hfgen, hx]⟩
      topGen := by simpa only [hfgen] using htopGen
      relation := by simpa only [hfgen] using hrelation }

/-- **The `OpenTuple`-to-`EpiData` adapter at the `N` core.**  A generic open-quotient marking
for the even `N` word datum is exactly the data of a marked epimorphism out of `D_N α h`; the
model is reinstated by `MarkedCore.nLiftHom`. -/
noncomputable def evenFiniteLevelNEpiDataOfOpenTuple
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {α h : ℕ} (hα : 1 ≤ α)
    {U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))}
    (O : OpenTuple (nStageWord α h hα) (vN α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) U) :
    EvenFiniteLevelNEpiData (K := K) α h U :=
  evenFiniteLevelNEpiDataOfTuple α h U O.generators O.rows O.relation O.topGen

/-! ## §4 The `M` twin

The same layer at `D_M α h`, over the EV-3b table `vM α` and the committed universal property
`MarkedCore.mLiftHom`.  Every declaration is the `N` one with `n` replaced by `m`; the only
mathematical difference is the row table, whose `B` row is `-1` (the `-1 ∈ im χ_cyc` branch
condition recorded in `EvenForwardRouteSkeleton.lean:139`) and whose `D` row is
`MarkedCore.mUnit α`. -/

/-- A finite-quotient output of the even-degree `M` route, at the presented core `D_M α h`. -/
structure EvenFiniteLevelMEpiData
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) where
  /-- The marked epimorphism out of the presented `M_α` core. -/
  epi : ContSurj (MarkedCore.DM α h : Type)
    ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup)
  /-- Every marked generator lifts into the exact cyclotomic fibre of its `vM α` row. -/
  rows : ∀ i : Fin (MarkedCore.coreRank h), ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = vM α i ∧
      epi.1 (MarkedCore.dmGen α h i) = QuotientGroup.mk x
  /-- The finite quotient is generated by the displayed tuple. -/
  topGen : Subgroup.closure
    (Set.range fun i ↦ epi.1 (MarkedCore.dmGen α h i)) = ⊤
  /-- Regression field: the relation is literally the committed `MarkedCore.mRelWord α`. -/
  relation : MarkedCore.mRelWord α (fun i ↦ epi.1 (MarkedCore.dmGen α h i)) = 1

namespace EvenFiniteLevelMEpiData

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  {α h : ℕ}
  {U U' : OpenNormalSubgroup
    (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))}

/-- Two finite-level data at the same quotient agree as soon as their epimorphisms do. -/
theorem eq_of_epi_eq {D E : EvenFiniteLevelMEpiData (K := K) α h U}
    (hepi : D.epi = E.epi) : D = E := by
  cases D
  cases E
  cases hepi
  rfl

/-- Restrict finite-level data along a coarser quotient. -/
noncomputable def map (hle : U ≤ U')
    (D : EvenFiniteLevelMEpiData (K := K) α h U) :
    EvenFiniteLevelMEpiData (K := K) α h U' where
  epi := ⟨(projMap hle).comp D.epi.1, (projMap_surjective hle).comp D.epi.2⟩
  rows i := by
    obtain ⟨x, hxchi, hx⟩ := D.rows i
    refine ⟨x, hxchi, ?_⟩
    change projMap hle (D.epi.1 (MarkedCore.dmGen α h i)) = QuotientGroup.mk x
    rw [hx, projMap_quotientMk]
  topGen := by
    change Subgroup.closure
      (Set.range fun i ↦ projMap hle (D.epi.1 (MarkedCore.dmGen α h i))) = ⊤
    have hmap := congrArg (Subgroup.map (projMap hle).toMonoidHom) D.topGen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (projMap_surjective hle), ← Set.range_comp] at hmap
    exact hmap
  relation := by
    change MarkedCore.mRelWord α
      (fun i ↦ projMap hle (D.epi.1 (MarkedCore.dmGen α h i))) = 1
    rw [← MarkedCore.map_mRelWord (projMap hle) α
      (fun i ↦ D.epi.1 (MarkedCore.dmGen α h i)), D.relation, map_one]

/-- Finite-level markings at the `M` core form a cofiltered functor under quotient
restriction. -/
noncomputable def functor
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ) :
    OpenNormalSubgroup (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))) ⥤ Type where
  obj U := EvenFiniteLevelMEpiData (K := K) α h U
  map {_ _} f := ↾(map (leOfHom f))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro D
    apply eq_of_epi_eq
    apply Subtype.ext
    ext x
    simp [map]
  map_comp {_ _ _} f g := by
    apply ConcreteCategory.hom_ext
    intro D
    apply eq_of_epi_eq
    apply Subtype.ext
    ext x
    simp [map]

/-- Each finite-level data type is finite: it injects into the finite set of continuous
homomorphisms from the topologically finitely generated `D_M α h` to the finite quotient. -/
instance finite (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Finite (EvenFiniteLevelMEpiData (K := K) α h U) := by
  haveI : Finite ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  haveI := finite_continuousMonoidHom (dmFinsetTopGen α h)
    ((maxProPQuotient 2 (GalK K)) ⧸ U.toSubgroup)
  exact Finite.of_injective (fun D ↦ D.epi.1) fun D E he ↦
    eq_of_epi_eq (Subtype.ext he)

/-- Forget the presented model, `M` side. -/
def toOpenTuple (hα : 1 ≤ α) (D : EvenFiniteLevelMEpiData (K := K) α h U) :
    OpenTuple (mStageWord α h hα) (vM α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) U where
  generators i := D.epi.1 (MarkedCore.dmGen α h i)
  rows := D.rows
  relation := D.relation
  topGen := D.topGen

end EvenFiniteLevelMEpiData

/-- Construct even `M` finite-level data from a generating tuple of the finite quotient which
kills the literal `MarkedCore.mRelWord α` and whose rows lift into the exact cyclotomic fibres
of `vM α`, through the committed universal property `MarkedCore.mLiftHom`. -/
noncomputable def evenFiniteLevelMEpiDataOfTuple
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (α h : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (generators : Fin (MarkedCore.coreRank h) →
      (maxProPQuotient 2 (GalK K) ⧸ U.toSubgroup))
    (hrows : ∀ i, ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = vM α i ∧ generators i = QuotientGroup.mk x)
    (hrelation : MarkedCore.mRelWord α generators = 1)
    (htopGen : Subgroup.closure (Set.range generators) = ⊤) :
    EvenFiniteLevelMEpiData (K := K) α h U := by
  let Q := maxProPQuotient 2 (GalK K) ⧸ U.toSubgroup
  have hproQ : IsProP 2 Q := isProP_of_isPGroup (isProP_maxProPQuotient U)
  let f : ContinuousMonoidHom (MarkedCore.DM α h : Type) Q :=
    MarkedCore.mLiftHom α h hproQ generators hrelation
  have hfgen (i : Fin (MarkedCore.coreRank h)) :
      f (MarkedCore.dmGen α h i) = generators i :=
    MarkedCore.mLiftHom_gen α h hproQ generators hrelation i
  have hfsurj : Function.Surjective f := by
    intro y
    have hle : Subgroup.closure (Set.range generators) ≤ f.toMonoidHom.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨MarkedCore.dmGen α h i, hfgen i⟩
    exact hle (by rw [htopGen]; trivial)
  exact
    { epi := ⟨f, hfsurj⟩
      rows := by
        intro i
        obtain ⟨x, hxchi, hx⟩ := hrows i
        exact ⟨x, hxchi, by rw [hfgen, hx]⟩
      topGen := by simpa only [hfgen] using htopGen
      relation := by simpa only [hfgen] using hrelation }

/-- **The `OpenTuple`-to-`EpiData` adapter at the `M` core**, through `MarkedCore.mLiftHom`. -/
noncomputable def evenFiniteLevelMEpiDataOfOpenTuple
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {α h : ℕ} (hα : 1 ≤ α)
    {U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))}
    (O : OpenTuple (mStageWord α h hα) (vM α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) U) :
    EvenFiniteLevelMEpiData (K := K) α h U :=
  evenFiniteLevelMEpiDataOfTuple α h U O.generators O.rows O.relation O.topGen

/-! ## §5 The forward-generator endpoints

The two readings of `OpenTuple.exists_globalMarking` against the EV-3b row tables.  Each row
field of `EvenForward.NForwardGeneratorData` is one entry of `vN α`, in the order fixed by the
frozen constructor table of `MarkedCore.chiN`: index `0` is `x₀` at value `1`, index `1` is
`x₁` at the orientation unit `MarkedCore.nUnit α`, index `2` is `σ` at `1`, index `3` is `x₂`
at `1`, and every handle row is `1`.  So the skeleton's structure and the row table agree
entry for entry, and no re-indexing is needed.

`1 ≤ α` enters only because the *type* of the hypothesis mentions `nStageWord α h hα`, which
carries EV-3a's hypothesis; the conclusions themselves constrain `α` no further. -/

section Endpoints

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The even `N` inverse limit.**  Levelwise nonemptiness of the generic open-quotient
markings for the `N_α` word datum and the `vN α` row table produces the even forward-generator
package at `G_K(2)`.  This is the `forwardGeneratorData_of_finiteLevel` endpoint of the
committed template, at the `N` core. -/
theorem evenForwardGeneratorDataN_of_openTuple {α h : ℕ} (hα : 1 ≤ α)
    (hne : ∀ U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
      Nonempty (OpenTuple (nStageWord α h hα) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) U)) :
    Nonempty (EvenForward.NForwardGeneratorData α h (chiCycKTwo (K := K))) := by
  obtain ⟨gen, hrows, hrelation, htopGen⟩ := OpenTuple.exists_globalMarking hne
  exact ⟨{ generators := gen
           relation := hrelation
           topGen := htopGen
           x0 := (hrows 0).trans (vN_zero α)
           x1 := (hrows 1).trans (vN_one α)
           sigma := (hrows 2).trans (vN_two α)
           x2 := (hrows 3).trans (vN_three α)
           handleU := fun j ↦ (hrows _).trans (vN_handleU α j)
           handleV := fun j ↦ (hrows _).trans (vN_handleV α j) }⟩

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The even `M` inverse limit.** -/
theorem evenForwardGeneratorDataM_of_openTuple {α h : ℕ} (hα : 1 ≤ α)
    (hne : ∀ U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
      Nonempty (OpenTuple (mStageWord α h hα) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) U)) :
    Nonempty (EvenForward.MForwardGeneratorData α h (chiCycKTwo (K := K))) := by
  obtain ⟨gen, hrows, hrelation, htopGen⟩ := OpenTuple.exists_globalMarking hne
  exact ⟨{ generators := gen
           relation := hrelation
           topGen := htopGen
           a := (hrows 0).trans (vM_zero α)
           b := (hrows 1).trans (vM_one α)
           c := (hrows 2).trans (vM_two α)
           d := (hrows 3).trans (vM_three α)
           handleU := fun j ↦ (hrows _).trans (vM_handleU α j)
           handleV := fun j ↦ (hrows _).trans (vM_handleV α j) }⟩

/-- The same endpoint stated at the model-marked finite data, which is the shape the committed
template uses: nonempty even `N` finite-level epimorphism sets at every open normal subgroup
produce the forward-generator package. -/
theorem evenForwardGeneratorDataN_of_finiteLevel {α h : ℕ} (hα : 1 ≤ α)
    (hne : ∀ U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
      Nonempty (EvenFiniteLevelNEpiData (K := K) α h U)) :
    Nonempty (EvenForward.NForwardGeneratorData α h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataN_of_openTuple hα fun U ↦ (hne U).map fun D ↦ D.toOpenTuple hα

/-- The `M` twin at the model-marked finite data. -/
theorem evenForwardGeneratorDataM_of_finiteLevel {α h : ℕ} (hα : 1 ≤ α)
    (hne : ∀ U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
      Nonempty (EvenFiniteLevelMEpiData (K := K) α h U)) :
    Nonempty (EvenForward.MForwardGeneratorData α h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataM_of_openTuple hα fun U ↦ (hne U).map fun D ↦ D.toOpenTuple hα

omit [FiniteDimensional ℚ_[2] K] in
/-- **The `N` station, end to end at one field.**  EV-3e's level-three base and EV-3f's
per-stage defect reachability produce the even forward-generator package: the generic stage
induction climbs the two-central tower, open-quotient descent lands at every open normal
subgroup, and the inverse limit of §2 assembles the global tuple. -/
theorem evenForwardGeneratorDataN_of_base_and_corrections {α h : ℕ} (hα : 1 ≤ α)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (base : Tuple (nStageWord α h hα) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (nStageWord α h hα) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T) :
    Nonempty (EvenForward.NForwardGeneratorData α h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataN_of_openTuple hα fun U ↦
    Tuple.openTuple_nonempty_of_base_and_corrections base
      hfg isProP_maxProPQuotient Hcorr U

omit [FiniteDimensional ℚ_[2] K] in
/-- **The `M` station, end to end at one field.** -/
theorem evenForwardGeneratorDataM_of_base_and_corrections {α h : ℕ} (hα : 1 ≤ α)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (base : Tuple (mStageWord α h hα) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (mStageWord α h hα) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T) :
    Nonempty (EvenForward.MForwardGeneratorData α h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataM_of_openTuple hα fun U ↦
    Tuple.openTuple_nonempty_of_base_and_corrections base
      hfg isProP_maxProPQuotient Hcorr U

/-- Model-marked form of the same station: the even `N` finite-level data are nonempty at every
open normal subgroup.  This is the `finiteLevelEpiData_nonempty_of_base_and_corrections`
analogue, and it is what an even finite-level *presentation* statement would carry. -/
theorem evenFiniteLevelNEpiData_nonempty_of_base_and_corrections {α h : ℕ} (hα : 1 ≤ α)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (base : Tuple (nStageWord α h hα) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (nStageWord α h hα) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T)
    (U : OpenNormalSubgroup (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Nonempty (EvenFiniteLevelNEpiData (K := K) α h U) :=
  (Tuple.openTuple_nonempty_of_base_and_corrections base
    hfg isProP_maxProPQuotient Hcorr U).map (evenFiniteLevelNEpiDataOfOpenTuple hα)

/-- Model-marked form of the `M` station. -/
theorem evenFiniteLevelMEpiData_nonempty_of_base_and_corrections {α h : ℕ} (hα : 1 ≤ α)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (base : Tuple (mStageWord α h hα) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hcorr : ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (mStageWord α h hα) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T)
    (U : OpenNormalSubgroup (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Nonempty (EvenFiniteLevelMEpiData (K := K) α h U) :=
  (Tuple.openTuple_nonempty_of_base_and_corrections base
    hfg isProP_maxProPQuotient Hcorr U).map (evenFiniteLevelMEpiDataOfOpenTuple hα)

end Endpoints

/-! ## §6 The uniform supplies, and the EV-3h seam

The `Prop`s below are the *exact* input interface of this station, each stated purely in the
vocabulary of the W50 generic layer and the EV-3a/b even instances — no bespoke datum.  EV-3e
produces the base supply, EV-3f the correction supply, and the fin-gen supply is the committed
`LSquare.maxProTwoGalK_isTopologicallyFinGen`, carried as a hypothesis here so that the axiom
prints of this file stay at std-3; it is discharged once, at assembly time.

Composing them gives the board's endpoint: the even analogues of
`OddDegreeGalKSqForwardGeneratorSupply`. -/

/-- Topological finite generation of `G_K(2)`, uniformly over dyadic fields.  The committed
`LSquare.maxProTwoGalK_isTopologicallyFinGen` discharges this. -/
def EvenFiniteLevelGalKFinGenSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))

/-- **The EV-3e interface at the `N` core**: a level-three stage for the even `N` word datum at
every even-degree dyadic field. -/
def EvenFiniteLevelNStageBaseSupply (α : ℕ) (hα : 1 ≤ α) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      Nonempty (Tuple (nStageWord α h hα) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)

/-- **The EV-3f interface at the `N` core**: every stage at level `k ≥ 3` has a reachable actual
defect. -/
def EvenFiniteLevelNCorrectionSupply (α : ℕ) (hα : 1 ≤ α) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (nStageWord α h hα) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T

/-- **The EV-3e interface at the `M` core.** -/
def EvenFiniteLevelMStageBaseSupply (α : ℕ) (hα : 1 ≤ α) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      Nonempty (Tuple (mStageWord α h hα) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)

/-- **The EV-3f interface at the `M` core.** -/
def EvenFiniteLevelMCorrectionSupply (α : ℕ) (hα : 1 ≤ α) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      ∀ k : ℕ, 3 ≤ k → ∀ T : Tuple (mStageWord α h hα) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k, Tuple.DefectReachable T

/-- **The EV-3g endpoint at the `N` core.**  The even level-three base and the even stage climb
produce the uniform even-degree `N` forward-generator supply of
`EvenForwardRouteSkeleton.lean:415`, which `orientedEquivN_of_supplies` closes into the `N`-row
classification. -/
theorem evenForwardGeneratorDataN_supply_of_base_and_corrections (α : ℕ) (hα : 1 ≤ α)
    (hfg : EvenFiniteLevelGalKFinGenSupply)
    (hbase : EvenFiniteLevelNStageBaseSupply α hα)
    (hcorr : EvenFiniteLevelNCorrectionSupply α hα) :
    EvenForward.EvenDegreeGalKNForwardGeneratorSupply α := by
  intro K _ _ _ _ h hev
  obtain ⟨base⟩ := hbase K h hev
  exact evenForwardGeneratorDataN_of_base_and_corrections hα (hfg K) base (hcorr K h hev)

/-- **The EV-3g endpoint at the `M` core.** -/
theorem evenForwardGeneratorDataM_supply_of_base_and_corrections (α : ℕ) (hα : 1 ≤ α)
    (hfg : EvenFiniteLevelGalKFinGenSupply)
    (hbase : EvenFiniteLevelMStageBaseSupply α hα)
    (hcorr : EvenFiniteLevelMCorrectionSupply α hα) :
    EvenForward.EvenDegreeGalKMForwardGeneratorSupply α := by
  intro K _ _ _ _ h hev
  obtain ⟨base⟩ := hbase K h hev
  exact evenForwardGeneratorDataM_of_base_and_corrections hα (hfg K) base (hcorr K h hev)

end

end GQ2.Dyadic.StageGeneric

/-! ## §7 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`: the committed finite-level template prints std-3 on
its whole model half, and this file adds no arithmetic input — topological finite generation of
`G_K(2)`, the one place where the odd route's endpoints acquire
`absGalQ2_isTopologicallyFinitelyGenerated`, is a hypothesis here (§6). -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §2 the generic open-quotient limit
#print axioms OpenTuple.eq_of_generators_eq
#print axioms OpenTuple.map
#print axioms OpenTuple.map_generators
#print axioms OpenTuple.functor
#print axioms OpenTuple.finite
#print axioms OpenTuple.exists_globalMarking

-- §3 the `N` finite-level layer
#print axioms EvenFiniteLevelNEpiData
#print axioms EvenFiniteLevelNEpiData.eq_of_epi_eq
#print axioms EvenFiniteLevelNEpiData.map
#print axioms EvenFiniteLevelNEpiData.functor
#print axioms EvenFiniteLevelNEpiData.finite
#print axioms EvenFiniteLevelNEpiData.toOpenTuple
#print axioms evenFiniteLevelNEpiDataOfTuple
#print axioms evenFiniteLevelNEpiDataOfOpenTuple

-- §4 the `M` finite-level layer
#print axioms EvenFiniteLevelMEpiData
#print axioms EvenFiniteLevelMEpiData.eq_of_epi_eq
#print axioms EvenFiniteLevelMEpiData.map
#print axioms EvenFiniteLevelMEpiData.functor
#print axioms EvenFiniteLevelMEpiData.finite
#print axioms EvenFiniteLevelMEpiData.toOpenTuple
#print axioms evenFiniteLevelMEpiDataOfTuple
#print axioms evenFiniteLevelMEpiDataOfOpenTuple

-- §5 the forward-generator endpoints
#print axioms evenForwardGeneratorDataN_of_openTuple
#print axioms evenForwardGeneratorDataM_of_openTuple
#print axioms evenForwardGeneratorDataN_of_finiteLevel
#print axioms evenForwardGeneratorDataM_of_finiteLevel
#print axioms evenForwardGeneratorDataN_of_base_and_corrections
#print axioms evenForwardGeneratorDataM_of_base_and_corrections
#print axioms evenFiniteLevelNEpiData_nonempty_of_base_and_corrections
#print axioms evenFiniteLevelMEpiData_nonempty_of_base_and_corrections

-- §6 the uniform supplies
#print axioms EvenFiniteLevelGalKFinGenSupply
#print axioms EvenFiniteLevelNStageBaseSupply
#print axioms EvenFiniteLevelNCorrectionSupply
#print axioms EvenFiniteLevelMStageBaseSupply
#print axioms EvenFiniteLevelMCorrectionSupply
#print axioms evenForwardGeneratorDataN_supply_of_base_and_corrections
#print axioms evenForwardGeneratorDataM_supply_of_base_and_corrections

end AxiomPins
