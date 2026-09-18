/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Reconstruction

/-!
# Profinite reconstruction retaining finite-level constraints

Plain finite-quotient reconstruction forgets the selected boundary maps. This additive
compactness theorem instead retains an arbitrary collection of allowed quotient surjections,
provided these collections are nonempty, finite, and stable under quotient projection.
The frozen unmarked reconstruction theorem is not changed.
-/

namespace GQ2
noncomputable section
open CategoryTheory
open scoped Classical

variable {S R : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  [CompactSpace S] [TotallyDisconnectedSpace S]
  [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
  [CompactSpace R] [TotallyDisconnectedSpace R]

/-- The finite quotient of a continuous surjection. -/
def ContSurj.quotient (f : ContSurj S R) (U : OpenNormalSubgroup (ProfiniteGrp.of R)) :
    ContSurj S (R ⧸ U.toSubgroup) :=
  ⟨(⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩ :
    ContinuousMonoidHom R (R ⧸ U.toSubgroup)).comp f.1,
    QuotientGroup.mk_surjective.comp f.2⟩

/-- Restriction from one finite quotient target to a coarser target. -/
def ContSurj.project {U V : OpenNormalSubgroup (ProfiniteGrp.of R)}
    (hUV : U ≤ V) (f : ContSurj S (R ⧸ U.toSubgroup)) :
    ContSurj S (R ⧸ V.toSubgroup) :=
  ⟨(projMap hUV).comp f.1, (projMap_surjective hUV).comp f.2⟩

private def allowedQuotientFunctor
    (allowed : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      Set (ContSurj S (R ⧸ U.toSubgroup)))
    (hproject : ∀ {U V : OpenNormalSubgroup (ProfiniteGrp.of R)} (hUV : U ≤ V)
      (f : ContSurj S (R ⧸ U.toSubgroup)), f ∈ allowed U → f.project hUV ∈ allowed V) :
    OpenNormalSubgroup (ProfiniteGrp.of R) ⥤ Type where
  obj U := {f : ContSurj S (R ⧸ U.toSubgroup) // f ∈ allowed U}
  map {U V} hh := ↾(fun f => ⟨f.1.project (leOfHom hh), hproject (leOfHom hh) f.1 f.2⟩)
  map_id U := by
    ext f
    apply Subtype.ext
    ext x
    change projMap (show U ≤ U from le_rfl) (f.1.1 x) = f.1.1 x
    exact QuotientGroup.induction_on (f.1.1 x) (fun _ => rfl)
  map_comp {U V W} hh hh' := by
    ext f
    apply Subtype.ext
    ext x
    change projMap ((leOfHom hh).trans (leOfHom hh')) (f.1.1 x) =
      projMap (leOfHom hh') (projMap (leOfHom hh) (f.1.1 x))
    exact QuotientGroup.induction_on (f.1.1 x) (fun _ => rfl)

omit [IsTopologicalGroup S] [TotallyDisconnectedSpace S] in
/-- A stable nonempty finite collection of allowed maps at every finite quotient has a
global continuous surjection satisfying all of the finite-level constraints. -/
theorem exists_contSurj_of_allowed_levels
    (allowed : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      Set (ContSurj S (R ⧸ U.toSubgroup)))
    (hproject : ∀ {U V : OpenNormalSubgroup (ProfiniteGrp.of R)} (hUV : U ≤ V)
      (f : ContSurj S (R ⧸ U.toSubgroup)), f ∈ allowed U → f.project hUV ∈ allowed V)
    (hne : ∀ U, (allowed U).Nonempty)
    (hfin : ∀ U, Finite {f : ContSurj S (R ⧸ U.toSubgroup) // f ∈ allowed U}) :
    ∃ f : ContSurj S R, ∀ U, f.quotient U ∈ allowed U := by
  classical
  let F := allowedQuotientFunctor allowed hproject
  haveI : ∀ U, Nonempty (F.obj U) := fun U => by
    obtain ⟨f, hf⟩ := hne U
    exact ⟨⟨f, hf⟩⟩
  haveI : ∀ U, Finite (F.obj U) := hfin
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_cofiltered_system F
  let sigma : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      ContinuousMonoidHom S (R ⧸ U.toSubgroup) := fun U => (sec U).1.1
  have hsurj : ∀ U, Function.Surjective (sigma U) := fun U => (sec U).1.2
  have hcompat : ∀ {U V : OpenNormalSubgroup (ProfiniteGrp.of R)} (hUV : U ≤ V) (s : S),
      projMap hUV (sigma U s) = sigma V s := by
    intro U V hUV s
    exact congrArg (fun f : F.obj V => f.1.1 s) (hsec hUV.hom)
  let Q : Type := ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R), R ⧸ U.toSubgroup
  let e : R →* Q := MonoidHom.pi fun U => QuotientGroup.mk' U.toSubgroup
  let Phi : S →* Q := MonoidHom.pi fun U => (sigma U).toMonoidHom
  have he_cont : Continuous e := continuous_pi fun U => continuous_quotient_mk'
  have hPhi_cont : Continuous Phi := continuous_pi fun U => (sigma U).continuous_toFun
  haveI : Nonempty (OpenNormalSubgroup (ProfiniteGrp.of R)) := ⟨⟨⊤, Subgroup.normal_top⟩⟩
  haveI : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      DiscreteTopology (R ⧸ U.toSubgroup) := fun U => inferInstance
  have he_inj : Function.Injective e := by
    intro x y hxy
    rw [← inv_mul_eq_one]
    by_contra hne1
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (U := ({x⁻¹ * y}ᶜ : Set R)) isOpen_compl_singleton
      (Set.mem_compl_singleton_iff.mpr fun hc => hne1 hc.symm)
    have hmk : QuotientGroup.mk x = QuotientGroup.mk (s := U.toSubgroup) y := congrFun hxy U
    rw [QuotientGroup.eq] at hmk
    exact hU hmk rfl
  have he_emb : Topology.IsClosedEmbedding e := he_cont.isClosedEmbedding he_inj
  have hrealise : ∀ s : S, ∃ r : R, e r = Phi s := by
    intro s
    have hmeet : (⋂ U, {r : R | QuotientGroup.mk r = sigma U s}).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U V
        refine ⟨U ⊓ V, fun r hr => ?_, fun r hr => ?_⟩ <;>
          simp only [Set.mem_setOf_eq] at hr ⊢
        · rw [← hcompat inf_le_left s, ← hr]
          rfl
        · rw [← hcompat inf_le_right s, ← hr]
          rfl
      · exact fun U => QuotientGroup.mk_surjective (sigma U s)
      · exact fun U => (isClosed_singleton.preimage continuous_quotient_mk').isCompact
      · exact fun U => isClosed_singleton.preimage continuous_quotient_mk'
    obtain ⟨r, hr⟩ := hmeet
    exact ⟨r, funext fun U => Set.mem_iInter.mp hr U⟩
  let psi : S → R := fun s => Function.invFun e (Phi s)
  have hpsi : ∀ s, e (psi s) = Phi s := by
    intro s
    obtain ⟨r, hr⟩ := hrealise s
    change e (Function.invFun e (Phi s)) = Phi s
    rw [← hr, Function.leftInverse_invFun he_inj r]
  have hmul : ∀ a b, psi (a * b) = psi a * psi b := by
    intro a b
    apply he_inj
    rw [hpsi, map_mul, map_mul, hpsi, hpsi]
  have hcont : Continuous psi := by
    rw [he_emb.isEmbedding.continuous_iff]
    exact hPhi_cont.congr fun s => (hpsi s).symm
  have honto : Function.Surjective psi := by
    intro r
    have hmeet : (⋂ U, {s : S | sigma U s = QuotientGroup.mk r}).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U V
        refine ⟨U ⊓ V, fun s hs => ?_, fun s hs => ?_⟩ <;>
          simp only [Set.mem_setOf_eq] at hs ⊢
        · rw [← hcompat inf_le_left s, hs]
          rfl
        · rw [← hcompat inf_le_right s, hs]
          rfl
      · exact fun U => hsurj U (QuotientGroup.mk r)
      · exact fun U => (isClosed_singleton.preimage (sigma U).continuous_toFun).isCompact
      · exact fun U => isClosed_singleton.preimage (sigma U).continuous_toFun
    obtain ⟨s, hs⟩ := hmeet
    refine ⟨s, he_inj ?_⟩
    rw [hpsi]
    exact funext fun U => Set.mem_iInter.mp hs U
  let f : ContSurj S R := ⟨⟨MonoidHom.mk' psi hmul, hcont⟩, honto⟩
  refine ⟨f, fun U => ?_⟩
  have heq : f.quotient U = (sec U).1 := by
    apply Subtype.ext
    ext s
    exact congrFun (hpsi s) U
  rw [heq]
  exact (sec U).2

variable {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  [CompactSpace B] [TotallyDisconnectedSpace B]

/-- Every value of a finite quotient map has a lift with exactly the prescribed boundary.
This formulation is stable under coarsening the finite quotient. -/
def ContSurj.OverQuotient (bS : ContinuousMonoidHom S B) (bR : ContinuousMonoidHom R B)
    (U : OpenNormalSubgroup (ProfiniteGrp.of R)) (f : ContSurj S (R ⧸ U.toSubgroup)) : Prop :=
  ∀ s : S, ∃ r : R, QuotientGroup.mk r = f.1 s ∧ bR r = bS s

omit [IsTopologicalGroup S] [CompactSpace S] [TotallyDisconnectedSpace S]
  [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] in
theorem ContSurj.OverQuotient.project
    {bS : ContinuousMonoidHom S B} {bR : ContinuousMonoidHom R B}
    {U V : OpenNormalSubgroup (ProfiniteGrp.of R)} (hUV : U ≤ V)
    {f : ContSurj S (R ⧸ U.toSubgroup)} (hf : f.OverQuotient bS bR U) :
    (f.project hUV).OverQuotient bS bR V := by
  intro s
  obtain ⟨r, hr, hb⟩ := hf s
  refine ⟨r, ?_, hb⟩
  exact congrArg (projMap hUV) hr

/-- Boundary-compatible finite quotient lifts assemble to a boundary-compatible continuous
surjection. Only the source needs finite generation, to make each allowed level finite. -/
theorem exists_contSurj_over_of_quotient_lifts
    (bS : ContinuousMonoidHom S B) (bR : ContinuousMonoidHom R B)
    (hSfg : ∃ s : Finset S, (Subgroup.closure (s : Set S)).topologicalClosure = ⊤)
    (hlift : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      ∃ f : ContSurj S (R ⧸ U.toSubgroup), f.OverQuotient bS bR U) :
    ∃ f : ContSurj S R, ∀ s, bR (f.1 s) = bS s := by
  let allowed := fun U : OpenNormalSubgroup (ProfiniteGrp.of R) =>
    {f : ContSurj S (R ⧸ U.toSubgroup) | f.OverQuotient bS bR U}
  have hfin : ∀ U, Finite {f : ContSurj S (R ⧸ U.toSubgroup) // f ∈ allowed U} := by
    intro U
    haveI := finite_continuousMonoidHom hSfg (R ⧸ U.toSubgroup)
    haveI : Finite (ContSurj S (R ⧸ U.toSubgroup)) := Subtype.finite
    exact Subtype.finite
  obtain ⟨f, hf⟩ := exists_contSurj_of_allowed_levels allowed
    (fun hUV _ h => h.project hUV) hlift hfin
  refine ⟨f, fun s => ?_⟩
  rw [← inv_mul_eq_one]
  by_contra hne
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({(bR (f.1 s))⁻¹ * bS s}ᶜ : Set B)) isOpen_compl_singleton
    (Set.mem_compl_singleton_iff.mpr fun hc => hne hc.symm)
  let U : OpenNormalSubgroup (ProfiniteGrp.of R) :=
    ⟨N.toOpenSubgroup.comap bR.toMonoidHom bR.continuous_toFun,
      Subgroup.Normal.comap N.isNormal' bR.toMonoidHom⟩
  obtain ⟨r, hr, hb⟩ := hf U s
  change QuotientGroup.mk r = QuotientGroup.mk (s := U.toSubgroup) (f.1 s) at hr
  have hmem : (f.1 s)⁻¹ * r ∈ U := QuotientGroup.eq.mp hr.symm
  change bR ((f.1 s)⁻¹ * r) ∈ N at hmem
  rw [map_mul, map_inv, hb] at hmem
  exact hN hmem rfl

/-- A marked equivalence carries the boundary map on the nose. -/
structure MarkedContinuousMulEquiv (bS : ContinuousMonoidHom S B)
    (bR : ContinuousMonoidHom R B) where
  equiv : ContinuousMulEquiv S R
  boundary_eq : ∀ s, bR (equiv s) = bS s

/-- Mutual compatible finite-quotient lifts give an isomorphism retaining the chosen
boundary. Hopfianity is used only to prove bijectivity, not to alter the boundary map. -/
theorem nonempty_markedEquiv_of_quotient_lifts
    (bS : ContinuousMonoidHom S B) (bR : ContinuousMonoidHom R B)
    (hSfg : ∃ s : Finset S, (Subgroup.closure (s : Set S)).topologicalClosure = ⊤)
    (hRfg : ∃ s : Finset R, (Subgroup.closure (s : Set R)).topologicalClosure = ⊤)
    (hliftSR : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      ∃ f : ContSurj S (R ⧸ U.toSubgroup), f.OverQuotient bS bR U)
    (hliftRS : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of S),
      ∃ f : ContSurj R (S ⧸ U.toSubgroup), f.OverQuotient bR bS U) :
    Nonempty (MarkedContinuousMulEquiv bS bR) := by
  obtain ⟨f, hf⟩ := exists_contSurj_over_of_quotient_lifts bS bR hSfg hliftSR
  obtain ⟨g, _hg⟩ := exists_contSurj_over_of_quotient_lifts bR bS hRfg hliftRS
  have hinjcomp : Function.Injective (⇑g.1 ∘ ⇑f.1) :=
    profinite_hopfian hSfg (g.1.comp f.1) (g.2.comp f.2)
  have hinj : Function.Injective f.1 := hinjcomp.of_comp
  exact ⟨⟨continuousMulEquivOfBijective f.1 ⟨hinj, f.2⟩, hf⟩⟩

#print axioms exists_contSurj_of_allowed_levels
#print axioms exists_contSurj_over_of_quotient_lifts
#print axioms nonempty_markedEquiv_of_quotient_lifts

end
end GQ2
