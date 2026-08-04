/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageVariableCore
import GQ2.Dyadic.MaxProTwoCohomology

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

end

end GQ2

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

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

/-! ## The two substantive missing inputs -/

/-- The missing local-reciprocity/completion calculation: the maximal pro-`2` Galois group of
an odd-degree finite dyadic field has Demushkin torsion invariant `q = 2`.

This is a `def`-shaped hypothesis, not an axiom. -/
def OddDegreeGalKDemushkinQTwo : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2

/-- The absent odd-degree dyadic-field specialization of Labute's classification.  Conditional
on `q = 2`, the maximal pro-`2` Galois group of the concrete field `K` has the improved square
presentation with `(degree - 1) / 2` handles.

The field specialization is essential.  In the exceptional `q = 2` case, abstract Demushkin
rank and `q` alone omit the image of the canonical orientation character.  Quantifying over
`GalK K` keeps its canonical cyclotomic orientation implicit rather than asserting the false or
underspecified all-profinite-groups statement.  This is a `def`-shaped hypothesis, not an axiom. -/
def OddDegreeGalKSqLabuteClassification : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        Nonempty (ContinuousMulEquiv
          (maxProPQuotient 2 (GalK K))
          (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2)))

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
    (hLab : OddDegreeGalKSqLabuteClassification) :
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
  rw [hhandle] at eField
  exact ⟨(maxProPQuotientCongr F.equivGalK).trans eField⟩

/-- Regression at ambient handle `0` and subgroup index `1`: the field route lands in the
rank-three improved presentation `DSq 0`, not in an abstract orientation-forgetting core. -/
theorem gammaLOpenSubgroupVariableCorePresentation_indexOne_zero
    {q : ℕ} (U' : Subgroup (gamma 0 q : Type)) [CompactSpace U']
    (hindex : U'.index = 1) (F : GammaLOpenSubgroupFieldIdentification U')
    (hqTwo : OddDegreeGalKDemushkinQTwo)
    (hLab : OddDegreeGalKSqLabuteClassification) :
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
    (hLab : OddDegreeGalKSqLabuteClassification) :
    GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q := by
  intro U' _ hUopen hodd
  obtain ⟨F⟩ := hfield U' hUopen hodd
  exact gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
    U' hodd F hqTwo hLab

#print axioms maxProPQuotientCongr
#print axioms gammaLOpenSubgroupHandleCount_rank
#print axioms gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification
#print axioms gammaLOpenSubgroupVariableCorePresentation_indexOne_zero
#print axioms gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field

end


end GQ2.Dyadic.LSquare
