/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GalKMaxProTwoOpenDescent
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldVariableCoreTate
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldRealizationCore

/-!
# Descending the open-neighbourhood kernel theorem to the GammaL Sylow preimages

`galKMaxProTwoKernelScalarH2Vanishes` proves scalar `H²`-vanishing on the maximal pro-two
kernel of every finite-dimensional dyadic field, with no oddness hypothesis.  This file spends
that theorem on the two remaining explicit premises of the pointwise field Tate route:

1. `OddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply` becomes a theorem;
2. `GammaLSylowPreimageKernelH2Supply` follows from the open-subgroup field identifications
   alone, because *any* Sylow preimage `U` is open of odd index, hence identified with some
   `G_K`, and the kernel statement transports back along that identification.

The transport needed for (2) is the pro-`p` kernel congruence: a topological group equivalence
carries `proPKernel p` onto `proPKernel p` (`map_proPKernel_of_continuousMulEquiv`), so the
scalar kernel `H²`-vanishing is invariant under equivalence
(`maxProTwoKernelScalarH2Vanishes_congr`).  This is the kernel-side analogue of
`maxProPQuotientCongr`, which handles the quotient side.

Consequently every capstone of `GammaLSylowPreimageFieldVariableCoreTate` sheds two of its
three supplies: only `GammaLOddIndexOpenSubgroupFieldIdentificationSupply` remains.  The
sharper capstones are added here alongside the old ones, and the `(h, q) = (0, 2)` row is
discharged outright through `gammaLFieldRealization_zero_two`, using the realization only for
Krull subgroup-to-field identification and never for a pre-existing Tate bundle.
-/

set_option autoImplicit false

namespace GQ2

noncomputable section

/-! ## Functoriality of the pro-`p` kernel under equivalence -/

/-- A topological group equivalence carries the pro-`p` kernel onto the pro-`p` kernel.  Both
inclusions are instances of the surjective-image lemma, applied to the equivalence and to its
inverse. -/
theorem map_proPKernel_of_continuousMulEquiv {p : ℕ} {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) :
    (proPKernel p G).map (e : ContinuousMonoidHom G H).toMonoidHom = proPKernel p H := by
  apply le_antisymm
  · have hback : proPKernel p G ≤
        (proPKernel p H).map (e.symm : ContinuousMonoidHom H G).toMonoidHom :=
      SectionThree.proPKernel_image_ge (e.symm : ContinuousMonoidHom H G) e.symm.surjective
    refine (Subgroup.map_mono (f := (e : ContinuousMonoidHom G H).toMonoidHom) hback).trans
      (le_of_eq ?_)
    rw [Subgroup.map_map]
    convert Subgroup.map_id (proPKernel p H) using 2
    exact MonoidHom.ext fun x ↦ e.apply_symm_apply x
  · exact SectionThree.proPKernel_image_ge (e : ContinuousMonoidHom G H) e.surjective

/-- A topological group equivalence induces a topological group equivalence of pro-`p` kernels.
This is the kernel-side counterpart of `maxProPQuotientCongr`. -/
noncomputable def proPKernelCongr {p : ℕ} {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) :
    ContinuousMulEquiv (proPKernel p G) (proPKernel p H) :=
  (GQ2.ContinuousMulEquiv.subgroupMap e (proPKernel p G)).trans
    (continuousMulEquivSubgroupOfEq (map_proPKernel_of_continuousMulEquiv (p := p) e))

@[simp] theorem proPKernelCongr_coe {p : ℕ} {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) (x : proPKernel p G) :
    ((proPKernelCongr (p := p) e x : proPKernel p H) : H) = e (x : G) := rfl

end

end GQ2

namespace GQ2.ContCoh

noncomputable section

open GQ2

/-! ## Invariance of the scalar kernel statement under equivalence -/

/-- Scalar maximal-pro-two kernel `H²`-vanishing is invariant under topological group
equivalence: the equivalence identifies the two pro-two kernels, and the scalar coefficients
carry the trivial action on both sides. -/
theorem maxProTwoKernelScalarH2Vanishes_congr {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (e : G ≃ₜ* H) (hH : MaxProTwoKernelScalarH2Vanishes (G := H)) :
    MaxProTwoKernelScalarH2Vanishes (G := G) := by
  letI : DistribMulAction (proPKernel 2 G) (ZMod 2) :=
    trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  letI : ContinuousSMul (proPKernel 2 G) (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  letI : DistribMulAction (proPKernel 2 H) (ZMod 2) :=
    trivialAddAction (M := ZMod 2) (proPKernel 2 H)
  letI : ContinuousSMul (proPKernel 2 H) (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) (proPKernel 2 H)
  let E : H2 (proPKernel 2 G) (ZMod 2) ≃+ H2 (proPKernel 2 H) (ZMod 2) :=
    GQ2.Dyadic.H2congrGroup (proPKernelCongr (p := 2) e) (AddEquiv.refl (ZMod 2))
      continuous_id continuous_id (fun _ _ ↦ rfl)
  intro x
  refine E.injective ?_
  rw [hH (E x), map_zero]

end

end GQ2.ContCoh

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

/-! ## The odd-degree field premise is a theorem -/

/-- The open-neighbourhood descent theorem discharges the odd-degree scalar kernel premise.
No oddness is used: the descent holds for every finite-dimensional dyadic field. -/
theorem oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply :
    OddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply := by
  intro K _ _ _ _ _hodd
  exact galKMaxProTwoKernelScalarH2Vanishes

/-! ## Sylow-preimage kernel vanishing from the field identifications alone -/

/-- Field identifications alone supply the Sylow-preimage kernel `H²` premise.  For each finite
coefficient pair take any Sylow `2`-subgroup of the finite action image: its preimage is open of
odd index, hence carries a field identification, and the scalar kernel theorem transports back
along that identification. -/
theorem gammaLSylowPreimageKernelH2Supply_of_field {h q : ℕ}
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q) :
    GammaLSylowPreimageKernelH2Supply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P⟩ : Nonempty (Sylow 2
      (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) := inferInstance
  refine ⟨P, ?_⟩
  let rho := pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)
  let U' := sylowTwoPreimage rho P
  have hUopen : IsOpen (U' : Set (gamma h q : Type)) :=
    isOpen_sylowTwoPreimage rho P
  have hUodd : Odd U'.index :=
    odd_sylowTwoPreimage_index rho pairFiniteActionImageHom_surjective P
  obtain ⟨F⟩ := hfield U' hUopen hUodd
  letI : FiniteDimensional ℚ_[2] F.K := F.finiteDimensional
  letI : CompactSpace (GalK F.K) := F.compactSpace
  letI : T2Space (GalK F.K) := F.t2Space
  letI : TotallyDisconnectedSpace (GalK F.K) := F.totallyDisconnectedSpace
  have hscalar : MaxProTwoKernelScalarH2Vanishes (G := U') :=
    maxProTwoKernelScalarH2Vanishes_congr F.equivGalK galKMaxProTwoKernelScalarH2Vanishes
  exact finiteElementaryMaxProTwoKernelH2VanishesSupply_of_scalar hscalar

/-! ## Hypothesis-reduced pointwise packages -/

/-- The pointwise CD₂ tail on one identified open subgroup, with the scalar kernel hypothesis
discharged. -/
theorem finiteElementaryH2RightExactSupply_maxProTwo_of_fieldIdentification
    {h q : ℕ} (U' : Subgroup (gamma h q : Type)) [CompactSpace U']
    (F : GammaLOpenSubgroupFieldIdentification U') :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 U') := by
  letI : FiniteDimensional ℚ_[2] F.K := F.finiteDimensional
  letI : CompactSpace (GalK F.K) := F.compactSpace
  letI : T2Space (GalK F.K) := F.t2Space
  letI : TotallyDisconnectedSpace (GalK F.K) := F.totallyDisconnectedSpace
  exact finiteElementaryH2RightExactSupply_maxProTwo_of_fieldIdentification_kernelScalarH2
    U' F galKMaxProTwoKernelScalarH2Vanishes

/-- The minimal pointwise field package from the field identifications alone. -/
theorem gammaLSylowPreimageKernelH2FieldCDTwoSupply_of_fieldIdentification {h q : ℕ}
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q) :
    GammaLSylowPreimageKernelH2FieldCDTwoSupply h q :=
  gammaLSylowPreimageKernelH2FieldCDTwoSupply_of_field
    (gammaLSylowPreimageKernelH2Supply_of_field hfield) hfield
    oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply

/-- The combined corrected package from the field identifications and forward rigidity. -/
theorem gammaLSylowPreimageKernelH2VariableCoreFieldCDTwoSupply_of_fieldIdentification_forward
    {h q : ℕ}
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q)
    (hforward : OddDegreeGalKSqOrientedForwardClassification) :
    GammaLSylowPreimageKernelH2VariableCoreFieldCDTwoSupply h q :=
  gammaLSylowPreimageKernelH2VariableCoreFieldCDTwoSupply_of_field_forward
    (gammaLSylowPreimageKernelH2Supply_of_field hfield) hfield hforward
    oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply

/-! ## Reduced Tate capstones -/

/-- **Reduced primary capstone.**  Open-subgroup field identifications are now the complete
explicit premise: Sylow-preimage kernel `H²`-vanishing and the odd-degree field scalar kernel
statement are both theorems. -/
noncomputable def tateDualityG_of_fieldIdentification
    {h q : ℕ} (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_fieldIdentification_kernelScalarH2 hqe
    (gammaLSylowPreimageKernelH2Supply_of_field hfield) hfield
    oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply

/-- Reduced campaign-composition regression: field identifications plus forward generator tables
also retain the corrected variable-rank square core at every chosen Sylow preimage. -/
noncomputable def tateDualityG_of_fieldIdentification_forwardGenerators
    {h q : ℕ} (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q)
    (hforward : OddDegreeGalKSqForwardGeneratorSupply) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_fieldIdentification_forwardGenerators_kernelScalarH2 hqe
    (gammaLSylowPreimageKernelH2Supply_of_field hfield) hfield hforward
    oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply

/-- Reduced realization wrapper: the ambient realization is used only to build the Krull field
identifications, never to consume a Tate bundle. -/
noncomputable def tateDualityG_of_fieldRealizationIdentification
    {h q : ℕ} (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (R : GammaLFieldRealization h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_fieldIdentification hqe
    (gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization R)

/-! ## The base row `(h, q) = (0, 2)` -/

/-- **Noncircular `(0,2)` regression.**  The base-row realization supplies the field
identifications by Krull correspondence, and the reduced capstone then produces Tate duality
without invoking `gammaL_tateDualityG_zero_two` or any Tate bundle stored on `GammaL`. -/
noncomputable def tateDualityG_zero_two_of_fieldRealization
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    [ContinuousSMul (gamma 0 2 : Type) (MuN 2)] :
    TateDualityG (gamma 0 2 : Type) 2 :=
  tateDualityG_of_fieldRealizationIdentification ⟨1, rfl⟩ gammaLFieldRealization_zero_two

/-- Regression in the proposition-valued shape. -/
theorem nonempty_tateDualityG_zero_two_of_fieldRealization
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    [ContinuousSMul (gamma 0 2 : Type) (MuN 2)] :
    Nonempty (TateDualityG (gamma 0 2 : Type) 2) :=
  ⟨tateDualityG_zero_two_of_fieldRealization⟩

#print axioms oddDegreeGalKMaxProTwoKernelScalarH2VanishesSupply
#print axioms gammaLSylowPreimageKernelH2Supply_of_field
#print axioms tateDualityG_of_fieldIdentification
#print axioms tateDualityG_zero_two_of_fieldRealization

end

end GQ2.Dyadic.LSquare
