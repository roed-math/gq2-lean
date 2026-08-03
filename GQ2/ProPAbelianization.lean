/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.SectionThree

/-!
# Maximal pro-p quotients commute with topological abelianization

For a profinite group `G`, both `(G^ab)(p)` and `(G(p))^ab` represent continuous homomorphisms
from `G` to abelian pro-`p` groups.  This file realizes that observation as a canonical
continuous multiplicative equivalence

`maxProPQuotient p (topAbelianization G) ≃ₜ*
  topAbelianization (maxProPQuotient p G)`.

The result is purely group-theoretic.  It is the reusable part of the local-reciprocity route to
the Demushkin `q` invariant; no arithmetic or torsion assertion occurs here.
-/

namespace GQ2

open CategoryTheory SectionThree

noncomputable section

/-! The canonical quotient instances are kept local for the same instance-firewall reason as in
`SectionThree.lean`: global generic instances on `topAbelianization` perturb unrelated quotient
instance synthesis. -/

noncomputable local instance instCommGroupTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

local instance instCompactSpaceTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

/-- A maximal pro-`p` quotient of a commutative profinite group is commutative.  The embedded
`Group` field is the bundled quotient's existing group structure, avoiding an instance-path
mismatch with the quotient-derived `CommGroup`. -/
noncomputable local instance instCommGroupMaxProPQuotient {p : ℕ} {A : Type}
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A] :
    CommGroup (maxProPQuotient p A) where
  __ := (inferInstance : Group (maxProPQuotient p A))
  mul_comm := by
    intro x y
    have hsurj : Function.Surjective (maxProPMk p A) := quotientMk_surjective _
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← map_mul, mul_comm, map_mul]

variable {p : ℕ} (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [T2Space G] in
/-- The maximal-pro-`p` projection is surjective. -/
theorem maxProPMk_surjective : Function.Surjective (maxProPMk p G) :=
  quotientMk_surjective _

/-- The canonical map `G^ab → (G(p))^ab`, descended from
`G → G(p) → (G(p))^ab`. -/
def topAbToTopAbMaxProP :
    ContinuousMonoidHom (topAbelianization G)
      (topAbelianization (maxProPQuotient p G)) :=
  abLiftG
    ⟨abMk.comp (maxProPMk p G).toMonoidHom,
      continuous_abMk.comp (maxProPMk p G).continuous_toFun⟩

omit [T2Space G] in
@[simp] theorem topAbToTopAbMaxProP_abMk (g : G) :
    topAbToTopAbMaxProP (p := p) G (abMk g) = abMk (maxProPMk p G g) :=
  abLiftG_abMk _ _

omit [T2Space G] in
/-- The canonical map `G^ab → (G(p))^ab` is surjective. -/
theorem topAbToTopAbMaxProP_surjective :
    Function.Surjective (topAbToTopAbMaxProP (p := p) G) := by
  intro y
  obtain ⟨q, rfl⟩ := abMk_surjective y
  obtain ⟨g, rfl⟩ := maxProPMk_surjective (p := p) G q
  exact ⟨abMk g, topAbToTopAbMaxProP_abMk G g⟩

/-- `(G(p))^ab` is pro-`p`. -/
theorem isProP_topAbelianization_maxProPQuotient :
    IsProP p (topAbelianization (maxProPQuotient p G)) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective isProP_maxProPQuotient

/-- The forward map `(G^ab)(p) → (G(p))^ab`, obtained from the maximal-pro-`p` universal
property applied to `topAbToTopAbMaxProP`. -/
def maxProPTopAbForward :
    ContinuousMonoidHom (maxProPQuotient p (topAbelianization G))
      (topAbelianization (maxProPQuotient p G)) :=
  (maxProPHomEquiv (isProP_topAbelianization_maxProPQuotient (p := p) G)).symm
    (topAbToTopAbMaxProP (p := p) G)

@[simp] theorem maxProPTopAbForward_maxProPMk (x : topAbelianization G) :
    maxProPTopAbForward (p := p) G (maxProPMk p (topAbelianization G) x) =
      topAbToTopAbMaxProP (p := p) G x :=
  maxProPHomEquiv_symm_apply_maxProPMk
    (isProP_topAbelianization_maxProPQuotient (p := p) G)
    (topAbToTopAbMaxProP (p := p) G) x

/-- The map `G(p) → (G^ab)(p)` descended from `G → G^ab → (G^ab)(p)`. -/
def maxProPToMaxProPTopAb :
    ContinuousMonoidHom (maxProPQuotient p G)
      (maxProPQuotient p (topAbelianization G)) :=
  (maxProPHomEquiv (isProP_maxProPQuotient (p := p) (G := topAbelianization G))).symm
    ((maxProPMk p (topAbelianization G)).comp ⟨abMk, continuous_abMk⟩)

@[simp] theorem maxProPToMaxProPTopAb_maxProPMk (g : G) :
    maxProPToMaxProPTopAb (p := p) G (maxProPMk p G g) =
      maxProPMk p (topAbelianization G) (abMk g) :=
  maxProPHomEquiv_symm_apply_maxProPMk
    (isProP_maxProPQuotient (p := p) (G := topAbelianization G)) _ g

/-- The inverse candidate `(G(p))^ab → (G^ab)(p)`, descended through the abelianization of
`G(p)`. -/
def maxProPTopAbBackward :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient p G))
      (maxProPQuotient p (topAbelianization G)) :=
  abLiftG (maxProPToMaxProPTopAb (p := p) G)

@[simp] theorem maxProPTopAbBackward_abMk_maxProPMk (g : G) :
    maxProPTopAbBackward (p := p) G (abMk (maxProPMk p G g)) =
      maxProPMk p (topAbelianization G) (abMk g) := by
  rw [maxProPTopAbBackward, abLiftG_abMk, maxProPToMaxProPTopAb_maxProPMk]

theorem maxProPTopAb_backward_forward
    (x : maxProPQuotient p (topAbelianization G)) :
    maxProPTopAbBackward (p := p) G (maxProPTopAbForward (p := p) G x) = x := by
  obtain ⟨a, rfl⟩ := maxProPMk_surjective (p := p) (topAbelianization G) x
  obtain ⟨g, rfl⟩ := abMk_surjective a
  rw [maxProPTopAbForward_maxProPMk, topAbToTopAbMaxProP_abMk,
    maxProPTopAbBackward_abMk_maxProPMk]

theorem maxProPTopAb_forward_backward
    (y : topAbelianization (maxProPQuotient p G)) :
    maxProPTopAbForward (p := p) G (maxProPTopAbBackward (p := p) G y) = y := by
  obtain ⟨q, rfl⟩ := abMk_surjective y
  obtain ⟨g, rfl⟩ := maxProPMk_surjective (p := p) G q
  rw [maxProPTopAbBackward_abMk_maxProPMk, maxProPTopAbForward_maxProPMk,
    topAbToTopAbMaxProP_abMk]

/-- **Maximal pro-`p` quotient commutes with topological abelianization.** -/
def maxProPTopAbEquiv :
    ContinuousMulEquiv (maxProPQuotient p (topAbelianization G))
      (topAbelianization (maxProPQuotient p G)) :=
  continuousMulEquivOfBijective (maxProPTopAbForward (p := p) G)
    ⟨fun x y h => by
        rw [← maxProPTopAb_backward_forward G x, ← maxProPTopAb_backward_forward G y, h],
      fun y => ⟨maxProPTopAbBackward (p := p) G y, maxProPTopAb_forward_backward G y⟩⟩

@[simp] theorem maxProPTopAbEquiv_maxProPMk_abMk (g : G) :
    maxProPTopAbEquiv (p := p) G (maxProPMk p (topAbelianization G) (abMk g)) =
      abMk (maxProPMk p G g) := by
  change maxProPTopAbForward (p := p) G
    (maxProPMk p (topAbelianization G) (abMk g)) = abMk (maxProPMk p G g)
  rw [maxProPTopAbForward_maxProPMk, topAbToTopAbMaxProP_abMk]

/-! ## Pro-`p` completion of an abstract group -/

/-- The pro-`p` completion of an abstract group: first take its profinite completion, then its
maximal pro-`p` quotient. -/
def proPCompletion (p : ℕ) (A : Type) [Group A] : ProfiniteGrp :=
  maxProPQuotient p
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))

/-- The canonical homomorphism from an abstract group to its pro-`p` completion. -/
def proPCompletionMk (p : ℕ) (A : Type) [Group A] : A →* proPCompletion p A :=
  (maxProPMk p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))).toMonoidHom.comp
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of A)).hom

/-- The universal lift from the pro-`p` completion to a profinite pro-`p` group. -/
def proPCompletionLift {p : ℕ} {A : Type} [Group A]
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (f : A →* P) :
    ContinuousMonoidHom (proPCompletion p A) P :=
  (maxProPHomEquiv hP).symm
    (ProfiniteGrp.ProfiniteCompletion.lift
      (P := ProfiniteGrp.of P) (GrpCat.ofHom f)).hom

@[simp] theorem proPCompletionLift_mk {p : ℕ} {A : Type} [Group A]
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (f : A →* P) (a : A) :
    proPCompletionLift hP f (proPCompletionMk p A a) = f a := by
  change
    (maxProPHomEquiv hP).symm
        (ProfiniteGrp.ProfiniteCompletion.lift
          (P := ProfiniteGrp.of P) (GrpCat.ofHom f)).hom
      (maxProPMk p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))
        ((ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of A)).hom a)) = f a
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact ConcreteCategory.congr_hom
    (ProfiniteGrp.ProfiniteCompletion.lift_eta
      (P := ProfiniteGrp.of P) (GrpCat.ofHom f)) a

/-- A dense homomorphism to a profinite pro-`p` group extends to a surjection from the pro-`p`
completion.  Density is the exact hypothesis needed here; injectivity requires a separate
arithmetic kernel theorem. -/
theorem proPCompletionLift_surjective_of_denseRange
    {p : ℕ} {A : Type} [Group A] [TopologicalSpace A]
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (f : ContinuousMonoidHom A P) (hf : DenseRange f) :
    Function.Surjective (proPCompletionLift hP f.toMonoidHom) := by
  let F := proPCompletionLift hP f.toMonoidHom
  have hclosed : IsClosed (Set.range F) :=
    (isCompact_range F.continuous_toFun).isClosed
  have hsub : Set.range f ⊆ Set.range F := by
    rintro _ ⟨a, rfl⟩
    exact ⟨proPCompletionMk p A a, proPCompletionLift_mk hP f.toMonoidHom a⟩
  rw [← Set.range_eq_univ, ← hclosed.closure_eq,
    (hf.mono hsub).closure_eq]

/-- A continuous homomorphism into `G^ab` induces a map from the pro-`p` completion of its
source to `(G(p))^ab`.  This packages the two universal properties used by local reciprocity. -/
def proPCompletionToTopAbMaxProP {A : Type} [Group A] [TopologicalSpace A]
    (f : ContinuousMonoidHom A (topAbelianization G)) :
    ContinuousMonoidHom (proPCompletion p A)
      (topAbelianization (maxProPQuotient p G)) :=
  proPCompletionLift (isProP_topAbelianization_maxProPQuotient (p := p) G)
    ((topAbToTopAbMaxProP (p := p) G).comp f).toMonoidHom

@[simp] theorem proPCompletionToTopAbMaxProP_mk
    {A : Type} [Group A] [TopologicalSpace A]
    (f : ContinuousMonoidHom A (topAbelianization G)) (a : A) :
    proPCompletionToTopAbMaxProP (p := p) G f (proPCompletionMk p A a) =
      topAbToTopAbMaxProP (p := p) G (f a) := by
  rw [proPCompletionToTopAbMaxProP, proPCompletionLift_mk]
  rfl

/-- If the original map into `G^ab` has dense image, its induced map from the pro-`p`
completion onto `(G(p))^ab` is surjective. -/
theorem proPCompletionToTopAbMaxProP_surjective_of_denseRange
    {A : Type} [Group A] [TopologicalSpace A]
    (f : ContinuousMonoidHom A (topAbelianization G)) (hf : DenseRange f) :
    Function.Surjective (proPCompletionToTopAbMaxProP (p := p) G f) := by
  apply proPCompletionLift_surjective_of_denseRange
    (isProP_topAbelianization_maxProPQuotient (p := p) G)
    ((topAbToTopAbMaxProP (p := p) G).comp f)
  exact (topAbToTopAbMaxProP_surjective (p := p) G).denseRange.comp hf
    (topAbToTopAbMaxProP (p := p) G).continuous_toFun

end

end GQ2
