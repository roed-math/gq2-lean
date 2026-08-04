/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageVariableCore
import GQ2.Dyadic.MaxProTwoCohomology
import GQ2.Dyadic.OrientationCorrection
import GQ2.Reconstruction

/-!
# A field-model route to variable GammaL Sylow cores

This file factors the missing variable-core presentation through the smallest field-specific
interfaces supported by the repository.

First, `maxProPQuotientCongr` records the formal fact that a topological group equivalence
induces an equivalence of maximal pro-`p` quotients.  Thus a field identification

`U ≃ GalK K`

reduces the desired presentation of `U(2)` to the concrete local-field classification

`DSq h' ≃ GalK K(2)`.

The field model also carries the expected degree identity.  What is not currently in the
repository is the final odd-degree dyadic-field square classification (nor the intermediate
general theorem `demushkinQ (GalK K(2)) = 2`).  The classification premise below is deliberately
field-specific: it does not claim that abstract Demushkin rank and `q = 2` determine the group
while forgetting Labute's canonical-orientation image.  The field carrier keeps the canonical
cyclotomic orientation implicit.  No broad all-groups classification and no unproved
isomorphism is introduced.
-/

namespace GQ2

noncomputable section

/-! ## Functoriality of the maximal pro-`p` quotient under equivalence -/

/-- A topological group equivalence induces a topological group equivalence of maximal
pro-`p` quotients. -/
noncomputable def maxProPQuotientCongr {p : ℕ}
    {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) :
    ContinuousMulEquiv (maxProPQuotient p G) (maxProPQuotient p H) := by
  let f0 : ContinuousMonoidHom G (maxProPQuotient p H) :=
    (maxProPMk p H).comp (e : ContinuousMonoidHom G H)
  let g0 : ContinuousMonoidHom H (maxProPQuotient p G) :=
    (maxProPMk p G).comp (e.symm : ContinuousMonoidHom H G)
  let f : ContinuousMonoidHom (maxProPQuotient p G) (maxProPQuotient p H) :=
    (maxProPHomEquiv (isProP_maxProPQuotient (p := p) (G := H))).symm f0
  let g : ContinuousMonoidHom (maxProPQuotient p H) (maxProPQuotient p G) :=
    (maxProPHomEquiv (isProP_maxProPQuotient (p := p) (G := G))).symm g0
  have hf_mk (x : G) : f (maxProPMk p G x) = maxProPMk p H (e x) := rfl
  have hg_mk (y : H) : g (maxProPMk p H y) = maxProPMk p G (e.symm y) := rfl
  have hleft : Function.LeftInverse g f := by
    intro x
    have hsurj : Function.Surjective (maxProPMk p G) := quotientMk_surjective _
    obtain ⟨x, rfl⟩ := hsurj x
    rw [hf_mk, hg_mk, e.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro y
    have hsurj : Function.Surjective (maxProPMk p H) := quotientMk_surjective _
    obtain ⟨y, rfl⟩ := hsurj y
    rw [hg_mk, hf_mk, e.apply_symm_apply]
  exact continuousMulEquivOfBijective f ⟨hleft.injective, hright.surjective⟩

/-- The equivalence induced on maximal pro-`p` quotients carries quotient classes to quotient
classes. -/
@[simp] theorem maxProPQuotientCongr_maxProPMk {p : ℕ}
    {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) (x : G) :
    maxProPQuotientCongr e (maxProPMk p G x) = maxProPMk p H (e x) := rfl

end

end GQ2

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## A two-epimorphism endpoint for a higher-rank Labute proof -/

/-- The improved square core is topologically finitely generated, in the `Finset` form needed
by the profinite Hopfian theorem. -/
theorem dsqFinsetTopGen (h : ℕ) :
    ∃ s : Finset (SqCore.DSq h : Type),
      (Subgroup.closure (s : Set (SqCore.DSq h : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (SqCore.sqGen h), ?_⟩
  have hset : ((Finset.univ.image (SqCore.sqGen h) : Finset (SqCore.DSq h : Type)) :
      Set (SqCore.DSq h : Type)) = Set.range (SqCore.sqGen h) := by
    ext x
    simp
  rw [hset]
  exact SqCore.dsq_topGen h

/-- The concrete output expected from a levelwise Labute argument: an oriented epimorphism out
of the improved square presentation and an epimorphism back.  The orientation is recorded only
on the finite generator table. -/
structure SqCyclotomicBiEpiData (h : ℕ)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) where
  forward : ContinuousMonoidHom (SqCore.DSq h : Type) G
  forward_surjective : Function.Surjective forward
  sigma : chiG (forward (SqCore.dsqSigma h)) = GQ2.Roe.SvalUnit
  x0 : chiG (forward (SqCore.dsqX0 h)) = GQ2.Roe.rootXUnit
  x1 : chiG (forward (SqCore.dsqX1 h)) = GQ2.Roe.YvalUnit
  handleU : ∀ j : Fin h,
    chiG (forward (SqCore.sqGen h (SqCore.sqHandleIdxU j))) = 1
  handleV : ∀ j : Fin h,
    chiG (forward (SqCore.sqGen h (SqCore.sqHandleIdxV j))) = 1
  backward : ContinuousMonoidHom G (SqCore.DSq h : Type)
  backward_surjective : Function.Surjective backward

/-- Generator-level data for the forward epimorphism.  This is exactly what the universal
property of the improved square presentation consumes: the relator dies, the chosen tuple
topologically generates the target, and its cyclotomic values are the five standard rows. -/
structure SqCyclotomicForwardGeneratorData (h : ℕ)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) where
  generators : Fin (SqCore.sqRank h) → G
  relation : SqCore.sqRelWord generators = 1
  topGen :
    (Subgroup.closure (Set.range generators)).topologicalClosure = ⊤
  sigma : chiG (generators 0) = GQ2.Roe.SvalUnit
  x0 : chiG (generators 1) = GQ2.Roe.rootXUnit
  x1 : chiG (generators 2) = GQ2.Roe.YvalUnit
  handleU : ∀ j : Fin h, chiG (generators (SqCore.sqHandleIdxU j)) = 1
  handleV : ∀ j : Fin h, chiG (generators (SqCore.sqHandleIdxV j)) = 1

namespace SqCyclotomicForwardGeneratorData

variable {h : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- The homomorphism classified by a relator-killing generator tuple. -/
noncomputable def forward (D : SqCyclotomicForwardGeneratorData h chiG)
    (hpro : IsProP 2 G) :
    ContinuousMonoidHom (SqCore.DSq h : Type) G :=
  SqCore.sqLiftHom h hpro D.generators D.relation

@[simp] theorem forward_gen (D : SqCyclotomicForwardGeneratorData h chiG)
    (hpro : IsProP 2 G) (i : Fin (SqCore.sqRank h)) :
    D.forward hpro (SqCore.sqGen h i) = D.generators i :=
  SqCore.sqLiftHom_gen h hpro D.generators D.relation i

/-- Topological generation of the chosen tuple makes the classified map surjective. -/
theorem forward_surjective (D : SqCyclotomicForwardGeneratorData h chiG)
    (hpro : IsProP 2 G) : Function.Surjective (D.forward hpro) := by
  let f := D.forward hpro
  have hclosed : IsClosed (f.toMonoidHom.range : Set G) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range f.continuous_toFun).isClosed
  have hgen : Subgroup.closure (Set.range D.generators) ≤ f.toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨SqCore.sqGen h i, D.forward_gen hpro i⟩
  have htop : (Subgroup.closure (Set.range D.generators)).topologicalClosure ≤
      f.toMonoidHom.range :=
    Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [D.topGen] at htop
  intro y
  exact htop (Subgroup.mem_top y)

/-- Add any epimorphism in the reverse direction to obtain the two-epimorphism package. -/
noncomputable def toBiEpiData (D : SqCyclotomicForwardGeneratorData h chiG)
    (hpro : IsProP 2 G) (backward : ContinuousMonoidHom G (SqCore.DSq h : Type))
    (hbackward : Function.Surjective backward) : SqCyclotomicBiEpiData h chiG where
  forward := D.forward hpro
  forward_surjective := D.forward_surjective hpro
  sigma := by rw [SqCore.dsqSigma, D.forward_gen]; exact D.sigma
  x0 := by rw [SqCore.dsqX0, D.forward_gen]; exact D.x0
  x1 := by rw [SqCore.dsqX1, D.forward_gen]; exact D.x1
  handleU j := by rw [D.forward_gen]; exact D.handleU j
  handleV j := by rw [D.forward_gen]; exact D.handleV j
  backward := backward
  backward_surjective := hbackward

/-- The generic reconstruction step for the reverse epimorphism.  Once the forward generator
tuple is known, the target `G` is topologically finitely generated.  Therefore surjections from
`G` onto every finite quotient of `DSq h` assemble to a continuous surjection back to `DSq h`.

This is the exact reusable part of the rank-three Labute assembly; constructing the finite-level
surjections remains the presentation-specific mathematics. -/
theorem backward_of_finiteQuotientSurjections
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G)
    (hne : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
      Nonempty (ContSurj G ((SqCore.DSq h : Type) ⧸ U.toSubgroup))) :
    Nonempty (ContSurj G (SqCore.DSq h : Type)) := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective (D.forward hpro).toMonoidHom
      (D.forward hpro).continuous_toFun (D.forward_surjective hpro) (dsqFinsetTopGen h)
  apply exists_contSurj_of_levelwise_nonempty hne
  intro U
  haveI : Finite ((SqCore.DSq h : Type) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  haveI := finite_continuousMonoidHom hGfg ((SqCore.DSq h : Type) ⧸ U.toSubgroup)
  exact Subtype.finite

/-- Generator data plus the finite-quotient reverse construction give the complete
two-epimorphism package. -/
theorem toBiEpiData_of_finiteQuotientSurjections
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G)
    (hne : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
      Nonempty (ContSurj G ((SqCore.DSq h : Type) ⧸ U.toSubgroup))) :
    Nonempty (SqCyclotomicBiEpiData h chiG) := by
  obtain ⟨⟨backward, hbackward⟩⟩ := D.backward_of_finiteQuotientSurjections hpro hne
  exact ⟨D.toBiEpiData hpro backward hbackward⟩

end SqCyclotomicForwardGeneratorData

/-- The Hopfian endgame for the higher-rank square classification.  Two epimorphisms produce
an equivalence, and the five generator rows orient that equivalence. -/
noncomputable def orientedEquivSq_of_biEpiData {h : ℕ}
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) (D : SqCyclotomicBiEpiData h chiG) :
    OrientedContinuousMulEquiv (SqCore.chiSq h) chiG := by
  have hcomp : Function.Surjective (D.backward.comp D.forward) :=
    D.backward_surjective.comp D.forward_surjective
  have hinj : Function.Injective (⇑D.backward ∘ ⇑D.forward) :=
    profinite_hopfian (dsqFinsetTopGen h) (D.backward.comp D.forward) hcomp
  let e : ContinuousMulEquiv (SqCore.DSq h : Type) G :=
    continuousMulEquivOfBijective D.forward ⟨hinj.of_comp, D.forward_surjective⟩
  exact orientedEquivSq_of_values chiG e D.sigma D.x0 D.x1 D.handleU D.handleV

/-! ## The exact field identification -/

/-- A field model for one open subgroup, including only the carrier identification and the
degree formula needed to verify the variable handle count.

The degree formula says that passing from the ambient odd-degree row `2h+1` to the open subgroup
multiplies the absolute degree by its index.  It does not contain a square presentation. -/
structure GammaLOpenSubgroupFieldIdentification
    (U' : Subgroup (gamma h q : Type)) where
  K : IntermediateField ℚ_[2] ℚ̄₂
  finiteDimensional : FiniteDimensional ℚ_[2] K
  compactSpace : CompactSpace (GalK K)
  t2Space : T2Space (GalK K)
  totallyDisconnectedSpace : TotallyDisconnectedSpace (GalK K)
  equivGalK : ContinuousMulEquiv U' (GalK K)
  degree_eq : Module.finrank ℚ_[2] K =
    U'.index * (2 * h + 1)

/-- Field identifications for all odd-index open subgroups.  This is routine Krull
correspondence data, kept separate from both missing classification inputs below. -/
def GammaLOddIndexOpenSubgroupFieldIdentificationSupply (h q : ℕ) : Prop :=
  ∀ (U' : Subgroup (gamma h q : Type)) [CompactSpace U'],
    IsOpen (U' : Set (gamma h q : Type)) → Odd U'.index →
      Nonempty (GammaLOpenSubgroupFieldIdentification U')

/-! ## Cyclotomic image transport -/

/-- Passing from `G_K` to its maximal pro-`2` quotient loses no cyclotomic values.  Equivalently,
the image of the descended character is exactly the cyclotomic image in `G_K^ab` recorded by
the marked-reciprocity branch selector. -/
theorem range_chiCycKTwo_eq_chiCycKAb
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom =
      MonoidHom.range (chiCycKAb K) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := quotientMk_surjective _ x
    refine ⟨toAbK K g, ?_⟩
    exact (chiCycKAb_toAbK K g).trans (chiCycKTwo_maxProPMk (K := K) g).symm
  · rintro ⟨a, rfl⟩
    obtain ⟨g, rfl⟩ := surjective_toAbK K a
    refine ⟨maxProPMk 2 (GalK K) g, ?_⟩
    exact (chiCycKTwo_maxProPMk (K := K) g).trans (chiCycKAb_toAbK K g).symm

/-- Bundle-facing form: the values available on `G_K(2)` are exactly the subgroup `C` used by
`fieldMarkedPair`.  Thus choosing any of the five square rows is reduced to a concrete
membership statement in the existing branch data; this theorem does not assert those missing
memberships. -/
theorem range_chiCycKTwo_eq_fieldMarkedPairC
    {Rec : LocalReciprocity} (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = (B.fieldMarkedPair FF).C :=
  range_chiCycKTwo_eq_chiCycKAb K

/-! ## The two substantive missing inputs -/

/-- The missing local-reciprocity/completion calculation: the maximal pro-`2` Galois group of
an odd-degree finite dyadic field has Demushkin torsion invariant `q = 2`.

This is a `def`-shaped hypothesis, not an axiom. -/
def OddDegreeGalKDemushkinQTwo : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2

/-! ## The already-proved invariant package -/

/-- The invariant data needed by the square row.  The first two fields are already theorems
for every finite dyadic field; only `qTwo` is the separate local-class-field-theory input.

For odd degree `n`, the equality identifies the field rank `n + 2` with the improved square
rank `sqRank ((n - 1) / 2) = 3 + 2 ((n - 1) / 2)`. -/
structure OddDegreeGalKSqInvariantData
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  demushkin : @IsDemushkin 2 (maxProPQuotient 2 (GalK K)) _ _
    (scalarActionZmodTwo _) (scalarActionZmodTwo_continuousSMul _)
  rank_eq : @demushkinRank 2 (maxProPQuotient 2 (GalK K)) _ _
    (scalarActionZmodTwo _) =
    SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2)
  qTwo : demushkinQ (maxProPQuotient 2 (GalK K)) = 2

/-- Odd degree and the `q = 2` calculation supply all abstract Demushkin invariants of the
improved square presentation.  No classification theorem is used here. -/
theorem oddDegreeGalKSqInvariantData_of_qTwo
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2) :
    OddDegreeGalKSqInvariantData K := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  refine ⟨isDemushkin_maxProTwoGalK (K := K), ?_, hq⟩
  rw [demushkinRank_maxProTwoGalK (K := K)]
  obtain ⟨k, hk⟩ := hodd
  rw [hk]
  simp only [SqCore.sqRank]
  omega

/-- The absent **oriented** odd-degree dyadic-field specialization of Labute's classification.
Conditional on `q = 2`, the improved square presentation with `(degree - 1) / 2` handles is
identified with the maximal pro-`2` Galois group of the concrete field `K`, and its standard
orientation `chiSq` is identified with the descended cyclotomic character `chiCycKTwo`.

The field specialization is essential.  In the exceptional `q = 2` case, abstract Demushkin
rank and `q` alone omit the image of the canonical orientation character.  Quantifying over
`GalK K` and recording the orientation equation avoids the false or underspecified
all-profinite-groups statement.  This is a `def`-shaped hypothesis, not an axiom. -/
def OddDegreeGalKSqOrientedLabuteClassification : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        Nonempty (OrientedContinuousMulEquiv
          (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
          (chiCycKTwo (K := K)))

/-- A concrete, generator-level form of the missing odd-degree field-presentation theorem.
It asks for an equivalence from the **improved square core** `DSq h` and pins exactly the
cyclotomic values on its three distinguished generators and every appended handle pair.

This is the minimal presentation-shaped input: `orientationMatches_chiSq_iff_generatorValues`
shows that no additional global orientation argument remains after these finitely many rows.
Like the oriented classification above, this is a `def`-shaped hypothesis, not an axiom. -/
def OddDegreeGalKSqCyclotomicGeneratorPresentation : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        ∃ f : ContinuousMulEquiv
            (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
            (maxProPQuotient 2 (GalK K)),
          SqOrientationGeneratorValues (chiCycKTwo (K := K)) f

/-- The generator-level field presentation supplies the oriented classification directly. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_generatorPresentation
    (hpres : OddDegreeGalKSqCyclotomicGeneratorPresentation) :
    OddDegreeGalKSqOrientedLabuteClassification := by
  intro K _ _ _ _ hodd hq
  obtain ⟨f, hvalues⟩ := hpres K hodd hq
  exact ⟨orientedEquivSq_of_generatorValues (chiCycKTwo (K := K)) f hvalues⟩

/-- Conversely, an oriented equivalence evaluates to the explicit generator table. -/
theorem oddDegreeGalKSqGeneratorPresentation_of_orientedLabuteClassification
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    OddDegreeGalKSqCyclotomicGeneratorPresentation := by
  intro K _ _ _ _ hodd hq
  obtain ⟨e⟩ := hLab K hodd hq
  exact ⟨e.1, (orientationMatches_chiSq_iff_generatorValues _ _).1 e.2⟩

/-- **Exact reduction of the higher odd-degree seam.**  Proving the oriented classification is
equivalent to constructing the improved square presentation with the displayed cyclotomic
generator values. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_iff_generatorPresentation :
    OddDegreeGalKSqOrientedLabuteClassification ↔
      OddDegreeGalKSqCyclotomicGeneratorPresentation :=
  ⟨oddDegreeGalKSqGeneratorPresentation_of_orientedLabuteClassification,
    oddDegreeGalKSqOrientedLabuteClassification_of_generatorPresentation⟩

/-! ## The finite-level Labute construction boundary -/

/-- The field-uniform two-epimorphism form of the missing classification.  Compared with the
generator-presentation seam, this asks only for the concrete output of a levelwise Labute
argument: a surjection from the improved square core with the five cyclotomic rows, and any
surjection back.  The profinite Hopfian theorem constructs the carrier equivalence. -/
def OddDegreeGalKSqCyclotomicBiEpiPresentation : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        Nonempty (SqCyclotomicBiEpiData
          ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))

/-- A two-epimorphism construction supplies the oriented field classification by the Hopfian
endgame `orientedEquivSq_of_biEpiData`. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_biEpiPresentation
    (hbi : OddDegreeGalKSqCyclotomicBiEpiPresentation) :
    OddDegreeGalKSqOrientedLabuteClassification := by
  intro K _ _ _ _ hodd hq
  obtain ⟨D⟩ := hbi K hodd hq
  exact ⟨orientedEquivSq_of_biEpiData (chiCycKTwo (K := K)) D⟩

/-- An oriented equivalence supplies the two epimorphisms and their five generator rows. -/
theorem oddDegreeGalKSqBiEpiPresentation_of_orientedLabuteClassification
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    OddDegreeGalKSqCyclotomicBiEpiPresentation := by
  intro K _ _ _ _ hodd hq
  obtain ⟨e⟩ := hLab K hodd hq
  have hvalues : SqOrientationGeneratorValues (chiCycKTwo (K := K)) e.1 :=
    (orientationMatches_chiSq_iff_generatorValues _ _).1 e.2
  exact ⟨
    { forward := e.1
      forward_surjective := e.1.surjective
      sigma := hvalues.sigma
      x0 := hvalues.x0
      x1 := hvalues.x1
      handleU := hvalues.handleU
      handleV := hvalues.handleV
      backward := e.1.symm
      backward_surjective := e.1.symm.surjective }⟩

/-- Exact reduction of the higher odd-degree theorem to the output expected from a finite-level
Labute construction. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_iff_biEpiPresentation :
    OddDegreeGalKSqOrientedLabuteClassification ↔
      OddDegreeGalKSqCyclotomicBiEpiPresentation :=
  ⟨oddDegreeGalKSqBiEpiPresentation_of_orientedLabuteClassification,
    oddDegreeGalKSqOrientedLabuteClassification_of_biEpiPresentation⟩

/-- The unmarked carrier shadow of the oriented field-specific classification.  This property
is retained as a convenient statement of the presentation alone, but it is not the primary
classification seam: by itself it forgets the orientation equation used to distinguish the
exceptional `q = 2` Labute type. -/
def OddDegreeGalKSqLabuteClassification : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        Nonempty (ContinuousMulEquiv
          (maxProPQuotient 2 (GalK K))
          (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2)))

/-- Forgetting the explicitly recorded cyclotomic-orientation equation gives the carrier
classification. -/
theorem oddDegreeGalKSqLabuteClassification_of_oriented
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    OddDegreeGalKSqLabuteClassification := by
  intro K _ _ _ _ hodd hq
  obtain ⟨e⟩ := hLab K hodd hq
  exact ⟨e.1.symm⟩

/-! ## Arithmetic and pointwise composition -/

/-- The variable handle-count identity for an arbitrary odd-index open subgroup. -/
theorem gammaLOpenSubgroupHandleCount_rank
    (U' : Subgroup (gamma h q : Type)) (hodd : Odd U'.index) :
    3 + 2 * gammaLOpenSubgroupHandleCount U' =
      2 + U'.index * (1 + 2 * h) := by
  obtain ⟨k, hk⟩ := hodd
  have hprod : (2 * k + 1) * (1 + 2 * h) =
      2 * (2 * k * h + k + h) + 1 := by ring
  rw [gammaLOpenSubgroupHandleCount, hk, hprod]
  rw [Nat.add_sub_cancel, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  ring

/-- A field identification, the `q = 2` calculation, and the honest field-specific Labute
classification give the variable square presentation of one odd-index open subgroup. -/
theorem gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
    (U' : Subgroup (gamma h q : Type)) [CompactSpace U']
    (hodd : Odd U'.index) (F : GammaLOpenSubgroupFieldIdentification U')
    (hqTwo : OddDegreeGalKDemushkinQTwo)
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    Nonempty (ContinuousMulEquiv
      (maxProPQuotient 2 U')
      (SqCore.DSq (gammaLOpenSubgroupHandleCount U'))) := by
  letI : FiniteDimensional ℚ_[2] F.K := F.finiteDimensional
  letI : CompactSpace (GalK F.K) := F.compactSpace
  letI : T2Space (GalK F.K) := F.t2Space
  letI : TotallyDisconnectedSpace (GalK F.K) := F.totallyDisconnectedSpace
  let Q := maxProPQuotient 2 (GalK F.K)
  have hdegreeOdd : Odd (Module.finrank ℚ_[2] F.K) := by
    rw [F.degree_eq]
    exact hodd.mul ⟨h, by omega⟩
  have hq : demushkinQ Q = 2 := hqTwo F.K hdegreeOdd
  obtain ⟨eField⟩ := hLab F.K hdegreeOdd hq
  have hhandle : (Module.finrank ℚ_[2] F.K - 1) / 2 =
      gammaLOpenSubgroupHandleCount U' := by
    rw [F.degree_eq, gammaLOpenSubgroupHandleCount]
    congr 2
    ring
  let eCarrier := eField.1.symm
  rw [hhandle] at eCarrier
  exact ⟨(maxProPQuotientCongr F.equivGalK).trans eCarrier⟩

/-- Regression at ambient handle `0` and subgroup index `1`: the field route lands in the
rank-three improved presentation `DSq 0`, not in an abstract orientation-forgetting core. -/
theorem gammaLOpenSubgroupVariableCorePresentation_indexOne_zero
    {q : ℕ} (U' : Subgroup (gamma 0 q : Type)) [CompactSpace U']
    (hindex : U'.index = 1) (F : GammaLOpenSubgroupFieldIdentification U')
    (hqTwo : OddDegreeGalKDemushkinQTwo)
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    Nonempty (ContinuousMulEquiv (maxProPQuotient 2 U') (SqCore.DSq 0)) := by
  have hodd : Odd U'.index := by rw [hindex]; exact odd_one
  have hhandle : gammaLOpenSubgroupHandleCount U' = 0 := by
    rw [gammaLOpenSubgroupHandleCount, hindex]
  obtain ⟨e⟩ := gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
    U' hodd F hqTwo hLab
  rw [hhandle] at e
  exact ⟨e⟩

/-- Uniform composition to the already-audited variable-core supply.  After the routine field
identification, exactly the two named substantive inputs remain. -/
theorem gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q)
    (hqTwo : OddDegreeGalKDemushkinQTwo)
    (hLab : OddDegreeGalKSqOrientedLabuteClassification) :
    GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q := by
  intro U' _ hUopen hodd
  obtain ⟨F⟩ := hfield U' hUopen hodd
  exact gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
    U' hodd F hqTwo hLab

#print axioms maxProPQuotientCongr
#print axioms maxProPQuotientCongr_maxProPMk
#print axioms dsqFinsetTopGen
#print axioms SqCyclotomicForwardGeneratorData.forward_surjective
#print axioms SqCyclotomicForwardGeneratorData.toBiEpiData
#print axioms SqCyclotomicForwardGeneratorData.backward_of_finiteQuotientSurjections
#print axioms SqCyclotomicForwardGeneratorData.toBiEpiData_of_finiteQuotientSurjections
#print axioms orientedEquivSq_of_biEpiData
#print axioms range_chiCycKTwo_eq_chiCycKAb
#print axioms range_chiCycKTwo_eq_fieldMarkedPairC
#print axioms oddDegreeGalKSqInvariantData_of_qTwo
#print axioms oddDegreeGalKSqLabuteClassification_of_oriented
#print axioms oddDegreeGalKSqOrientedLabuteClassification_of_generatorPresentation
#print axioms oddDegreeGalKSqGeneratorPresentation_of_orientedLabuteClassification
#print axioms oddDegreeGalKSqOrientedLabuteClassification_iff_generatorPresentation
#print axioms oddDegreeGalKSqOrientedLabuteClassification_of_biEpiPresentation
#print axioms oddDegreeGalKSqBiEpiPresentation_of_orientedLabuteClassification
#print axioms oddDegreeGalKSqOrientedLabuteClassification_iff_biEpiPresentation
#print axioms gammaLOpenSubgroupHandleCount_rank
#print axioms gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
#print axioms gammaLOpenSubgroupVariableCorePresentation_indexOne_zero
#print axioms gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field

end


end GQ2.Dyadic.LSquare
