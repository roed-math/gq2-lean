/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFinite
import GQ2.Roe.Labute.SpanFoundation

/-!
# The reverse finite-quotient boundary for the square Labute presentation

The finite-level square presentation currently asks for a continuous epimorphism from the
arithmetic group onto every finite quotient of `DSq h`.  This file reduces that apparently
large family to the canonical two-central tower.  It then shows that, once the already-built
forward epimorphism `DSq h → G` is available, equality of the orders of the two level quotients
is enough to construct the reverse epimorphism at that level.

Thus the reverse direction does not require a second generator-and-relator construction.  Its
remaining content is the numerical statement that the forward map loses no elements at every
two-central level.  This is the form naturally approachable by a graded Lie or finite-stage
Labute calculation.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute

variable {h : ℕ}

/-! ## The exact cofinal-tower reduction -/

/-- Reverse epimorphisms only at the canonical two-central quotients of `DSq h`. -/
def SqReverseTwoCentralLevelSurjections
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ, Nonempty (ContSurj G (levelQuot (SqCore.DSq h : Type) k))

/-- Reverse epimorphisms onto all open-normal quotients of `DSq h`. -/
def SqReverseFiniteQuotientSurjections
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ V : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
    Nonempty (ContSurj G ((SqCore.DSq h : Type) ⧸ V.toSubgroup))

/-- Every two-central subgroup of `DSq h` is an open normal subgroup. -/
noncomputable def dsqTwoCentralOpenNormal (h k : ℕ) :
    OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)) where
  toSubgroup := twoCentralSeries (SqCore.DSq h : Type) k
  isOpen' := isOpen_twoCentralSeries (SqCore.DSq h : Type)
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h) k

@[simp] theorem dsqTwoCentralOpenNormal_toSubgroup (h k : ℕ) :
    (dsqTwoCentralOpenNormal h k).toSubgroup =
      twoCentralSeries (SqCore.DSq h : Type) k :=
  rfl

/-- The tower condition is exactly equivalent to the original reverse finite-quotient
condition.  Cofinality of the two-central series supplies the nontrivial implication. -/
theorem sqReverseFiniteQuotientSurjections_iff_twoCentralLevel
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (h : ℕ) :
    SqReverseFiniteQuotientSurjections G h ↔
      SqReverseTwoCentralLevelSurjections G h := by
  constructor
  · intro hall k
    change Nonempty (ContSurj G
      ((SqCore.DSq h : Type) ⧸ twoCentralSeries (SqCore.DSq h : Type) k))
    exact hall (dsqTwoCentralOpenNormal h k)
  · intro htower V
    obtain ⟨k, hk⟩ := exists_twoCentralSeries_le (SqCore.DSq h : Type)
      (dsqFinsetTopGen h) (SqCore.isProP_DSq h) V.isOpen'
    letI : DiscreteTopology
        ((SqCore.DSq h : Type) ⧸ twoCentralSeries (SqCore.DSq h : Type) k) :=
      QuotientGroup.discreteTopology
        (isOpen_twoCentralSeries (SqCore.DSq h : Type) (dsqFinsetTopGen h)
          (SqCore.isProP_DSq h) k)
    obtain ⟨⟨f, hf⟩⟩ := htower k
    exact ⟨⟨(projMap hk).comp f, (projMap_surjective hk).comp hf⟩⟩

/-! ## Functoriality on the two-central tower -/

/-- A continuous homomorphism induces a continuous homomorphism on every two-central level. -/
noncomputable def twoCentralLevelMap
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (k : ℕ) :
    ContinuousMonoidHom (levelQuot P k) (levelQuot Q k) := by
  let q : ContinuousMonoidHom P (levelQuot Q k) :=
    ⟨(levelMk Q k).comp f.toMonoidHom,
      (continuous_levelMk Q k).comp f.continuous_toFun⟩
  exact quotientLift (twoCentralSeries P k) q fun x hx ↦ by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr
      (map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun k ⟨x, hx, rfl⟩)

@[simp] theorem twoCentralLevelMap_levelMk
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (k : ℕ) (x : P) :
    twoCentralLevelMap f k (levelMk P k x) = levelMk Q k (f x) :=
  rfl

/-- An epimorphism remains an epimorphism on every two-central quotient. -/
theorem twoCentralLevelMap_surjective
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f) (k : ℕ) :
    Function.Surjective (twoCentralLevelMap f k) := by
  intro y
  obtain ⟨q, rfl⟩ := levelMk_surjective Q k y
  obtain ⟨p, rfl⟩ := hf q
  exact ⟨levelMk P k p, rfl⟩

/-! ## The cardinality endpoint -/

/-- Equality of the finite two-central quotient orders is the numerical reverse input. -/
def SqTwoCentralLevelCardAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ,
    Nat.card (levelQuot (SqCore.DSq h : Type) k) = Nat.card (levelQuot G k)

/-- At one level, a forward epimorphism together with equality of quotient orders produces a
reverse epimorphism. -/
theorem nonempty_reverseTwoCentralLevel_of_card_eq
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (k : ℕ)
    (hcard : Nat.card (levelQuot (SqCore.DSq h : Type) k) =
      Nat.card (levelQuot G k)) :
    Nonempty (ContSurj G (levelQuot (SqCore.DSq h : Type) k)) := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective f.toMonoidHom f.continuous_toFun hf
      (dsqFinsetTopGen h)
  letI : DiscreteTopology (levelQuot (SqCore.DSq h : Type) k) :=
    QuotientGroup.discreteTopology
      (isOpen_twoCentralSeries (SqCore.DSq h : Type) (dsqFinsetTopGen h)
        (SqCore.isProP_DSq h) k)
  letI : DiscreteTopology (levelQuot G k) :=
    QuotientGroup.discreteTopology (isOpen_twoCentralSeries G hGfg hpro k)
  let e : ContinuousMulEquiv
      (levelQuot (SqCore.DSq h : Type) k) (levelQuot G k) := by
    haveI : Finite (levelQuot (SqCore.DSq h : Type) k) :=
      finite_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
        (SqCore.isProP_DSq h) k
    haveI : Finite (levelQuot G k) := finite_levelQuot G hGfg hpro k
    exact continuousMulEquivOfBijective (twoCentralLevelMap f k)
      ((Nat.bijective_iff_surjective_and_card _).mpr
        ⟨twoCentralLevelMap_surjective f hf k, hcard⟩)
  let q : ContinuousMonoidHom G (levelQuot G k) :=
    ⟨levelMk G k, continuous_levelMk G k⟩
  let b : ContinuousMonoidHom G (levelQuot (SqCore.DSq h : Type) k) :=
    (e.symm : ContinuousMonoidHom _ _).comp q
  refine ⟨⟨b, ?_⟩⟩
  intro y
  obtain ⟨z, rfl⟩ := e.symm.surjective y
  obtain ⟨g, rfl⟩ := levelMk_surjective G k z
  exact ⟨g, rfl⟩

/-- The complete reverse finite-quotient condition follows from equality of the natural finite
two-central quotient orders.  The forward epimorphism is exactly the one already assembled from
the improved-relator finite-level markings. -/
theorem reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (hcard : SqTwoCentralLevelCardAgreement G h) :
    SqReverseFiniteQuotientSurjections G h := by
  rw [sqReverseFiniteQuotientSurjections_iff_twoCentralLevel]
  intro k
  exact nonempty_reverseTwoCentralLevel_of_card_eq hpro f hf k (hcard k)

/-- Conversely, the original reverse condition forces equality of the two-central quotient
orders once a forward epimorphism is fixed.  Indeed the reverse finite-level maps assemble to a
global reverse epimorphism, and both global epimorphisms remain onto on the two-central tower. -/
theorem twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (hback : SqReverseFiniteQuotientSurjections G h) :
    SqTwoCentralLevelCardAgreement G h := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective f.toMonoidHom f.continuous_toFun hf
      (dsqFinsetTopGen h)
  have hfin : ∀ V : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
      Finite (ContSurj G ((SqCore.DSq h : Type) ⧸ V.toSubgroup)) := by
    intro V
    haveI : Finite ((SqCore.DSq h : Type) ⧸ V.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
    haveI := finite_continuousMonoidHom hGfg
      ((SqCore.DSq h : Type) ⧸ V.toSubgroup)
    exact Subtype.finite
  obtain ⟨⟨b, hb⟩⟩ := exists_contSurj_of_levelwise_nonempty hback hfin
  intro k
  haveI : Finite (levelQuot (SqCore.DSq h : Type) k) :=
    finite_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
      (SqCore.isProP_DSq h) k
  haveI : Finite (levelQuot G k) := finite_levelQuot G hGfg hpro k
  apply le_antisymm
  · exact Nat.card_le_card_of_surjective _ (twoCentralLevelMap_surjective b hb k)
  · exact Nat.card_le_card_of_surjective _ (twoCentralLevelMap_surjective f hf k)

/-- **Exact reverse boundary.**  In the presence of the already-constructed forward
epimorphism, the old family indexed by all open normal subgroups is equivalent to equality of
the finite two-central quotient orders. -/
theorem reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) :
    SqReverseFiniteQuotientSurjections G h ↔ SqTwoCentralLevelCardAgreement G h :=
  ⟨twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections hpro f hf,
    reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement hpro f hf⟩

/-- Specialization to the forward-generator package used by the odd-degree field theorem. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G)
    (hcard : SqTwoCentralLevelCardAgreement G h) :
    SqReverseFiniteQuotientSurjections G h :=
  reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement hpro
    (D.forward hpro) (D.forward_surjective hpro) hcard

/-- Generator-package regression: after the improved-relator forward map is built, the reverse
hypothesis is *exactly* level-cardinality agreement and need not be stated again over all open
normal subgroups. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G) :
    SqReverseFiniteQuotientSurjections G h ↔ SqTwoCentralLevelCardAgreement G h :=
  reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement hpro
    (D.forward hpro) (D.forward_surjective hpro)

/-! ## Field-facing composition -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Sharpened finite-level field presentation.  The forward clause still uses the literal
improved relator and the corrected cyclotomic value fibres.  The reverse clause is replaced,
equivalently, by the order equality on the canonical two-central tower. -/
def OddDegreeGalKSqCyclotomicLevelCardPresentation : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)],
    (_hodd : Odd (Module.finrank ℚ_[2] K)) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        let h := (Module.finrank ℚ_[2] K - 1) / 2
        (∀ U : OpenNormalSubgroup
            (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
            Nonempty (SqCyclotomicFiniteLevelEpiData (K := K) h U)) ∧
          SqTwoCentralLevelCardAgreement (maxProPQuotient 2 (GalK K)) h

/-- The sharpened tower-cardinality presentation supplies the original finite-level seam; the
equivalence theorem above is the only place where the old all-open-normal reverse family is
reconstructed. -/
theorem oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqCyclotomicFiniteLevelPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, hcard⟩ := hlevel K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  exact ⟨hforward,
    D.reverseFiniteQuotientSurjections_of_levelCardAgreement
      isProP_maxProPQuotient hcard⟩

/-- The original all-open-normal formulation also supplies the sharpened level-cardinality
form.  This is the field-facing converse needed to record that no mathematical strength was
added in the refactoring. -/
theorem oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation
    (hfinite : OddDegreeGalKSqCyclotomicFiniteLevelPresentation) :
    OddDegreeGalKSqCyclotomicLevelCardPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, hback⟩ := hfinite K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  exact ⟨hforward,
    (D.reverseFiniteQuotientSurjections_iff_levelCardAgreement
      isProP_maxProPQuotient).mp hback⟩

/-- **Field-facing regression/equivalence.**  The new natural-number-indexed tower-cardinality
seam is exactly the old reverse finite-quotient seam, once the unchanged improved-relator
forward clause is included. -/
theorem oddDegreeGalKSqCyclotomicLevelCardPresentation_iff_finiteLevelPresentation :
    OddDegreeGalKSqCyclotomicLevelCardPresentation ↔
      OddDegreeGalKSqCyclotomicFiniteLevelPresentation :=
  ⟨oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation,
    oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation⟩

/-- Field-facing endpoint: forward improved-relator finite data plus equality of two-central
quotient orders proves the full oriented Labute classification. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqOrientedLabuteClassification :=
  oddDegreeGalKSqOrientedLabuteClassification_of_finiteLevelPresentation
    (oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation hlevel)

/-- Generator-presentation form of the same sharpened endpoint. -/
theorem oddDegreeGalKSqGeneratorPresentation_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqCyclotomicGeneratorPresentation :=
  oddDegreeGalKSqGeneratorPresentation_of_finiteLevelPresentation
    (oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation hlevel)

#print axioms sqReverseFiniteQuotientSurjections_iff_twoCentralLevel
#print axioms twoCentralLevelMap_surjective
#print axioms nonempty_reverseTwoCentralLevel_of_card_eq
#print axioms reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement
#print axioms twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections
#print axioms reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_levelCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_levelCardAgreement
#print axioms oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation
#print axioms oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation
#print axioms oddDegreeGalKSqCyclotomicLevelCardPresentation_iff_finiteLevelPresentation
#print axioms oddDegreeGalKSqOrientedLabuteClassification_of_levelCardPresentation

end

end GQ2.Dyadic.LSquare
