/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherKummer
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.Dyadic.ProTwoCompletionDecomposition
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Foundations.Axioms

/-!
# Supplying the odd-degree field `q = 2` input

This adapter connects the ramified-`i` torsion calculation to the field-model route for
variable GammaL Sylow cores.  Odd degree supplies ramification of `K(i)/K` internally, and
`ProTwoCompletionDecomposition` proves unconditionally that every torsion point in the pro-`2`
completion of `K×` comes from a field root.  Its single remaining premise is therefore exactly
injectivity of the canonical completed reciprocity map.

There is no separate reciprocity field in the package: `localReciprocity` and
`markedRecipAt K` are the repository's canonical APIs.  Thus the only genuinely variable data
left is the finite local-CFT calculation.  The adapters below retain both interfaces: one
accepts completed reciprocity injectivity directly, while the arithmetic-facing route accepts
`FiniteTwoLocalReciprocitySupply` and derives injectivity internally.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The only remaining field-specific input to the odd-degree `q = 2` calculation:
injectivity of the completed canonical reciprocity map
`(K×)^(2) → G_K(2)^ab`.

Ramification of `K(i)/K` and generation of source torsion by field roots are theorems, not
fields of this structure. -/
structure GalKCompletedReciprocityInjectivityData
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] where
  completedReciprocityInjective :
    Function.Injective (proTwoReciprocityToTopAb (markedRecipAt K))

/-- The uniform arithmetic supply sufficient for the odd-degree field theorem `q = 2`:
completed canonical reciprocity is injective for every odd-degree dyadic field. -/
def OddDegreeGalKCompletedReciprocityInjectivitySupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (GalKCompletedReciprocityInjectivityData K)

/-- **Pointwise end-to-end odd-degree adapter.**  Once completed reciprocity is injective,
the Demushkin invariant is `q = 2`.  The source torsion theorem and ramification of `K(i)/K`
are discharged by the repository. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hrecip : Function.Injective
      (proTwoReciprocityToTopAb (markedRecipAt K))) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_completion
    (markedRecipAt K) hodd (ramifiedIData_of_odd_finrank K hodd) hrecip
      (GQ2.Dyadic.proTwoCompletionTorsionGeneratedByFieldRoots (K := K))

/-- Uniform end-to-end adapter from the sole remaining completed-reciprocity premise to the
field theorem consumed by the variable GammaL Sylow-core route. -/
theorem oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply
    (hSupply : OddDegreeGalKCompletedReciprocityInjectivitySupply) :
    OddDegreeGalKDemushkinQTwo := by
  intro K _ _ _ _ hodd
  obtain ⟨hData⟩ := hSupply K hodd
  exact demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
    K hodd hData.completedReciprocityInjective

/-- Compatibility name for the former torsion-generation package.  The package now contains
only completed-reciprocity injectivity. -/
abbrev GalKTorsionGenerationData := GalKCompletedReciprocityInjectivityData

/-- Compatibility name for the former torsion-generation supply. -/
abbrev OddDegreeGalKTorsionGenerationSupply :=
  OddDegreeGalKCompletedReciprocityInjectivitySupply

/-- Compatibility theorem for the former torsion-generation name. -/
theorem oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply
    (hSupply : OddDegreeGalKTorsionGenerationSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply hSupply

/-- Compatibility name for the earlier two-input adapter; ramification and source torsion are
now proved rather than supplied. -/
abbrev GalKRamifiedITorsionData := GalKCompletedReciprocityInjectivityData

/-! ## Completion-shaped adapters -/

/-- Compatibility spelling of the pointwise completed-injectivity adapter. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_completion
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hinjective : Function.Injective
      (proTwoReciprocityToTopAb (markedRecipAt K))) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
    K hodd hinjective

/-- **Pointwise arithmetic-facing adapter.**  A finite local-CFT supply derives completed
reciprocity injectivity internally; the source-completion torsion and odd-degree ramification
theorems then prove `demushkinQ = 2`. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteTwoLocalReciprocity
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfinite : FiniteTwoLocalReciprocitySupply (markedRecipAt K)) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_odd_completion K hodd
    hfinite.completed_injective

/-- Pointwise adapter from the sharper cyclic-character formulation of finite local CFT. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteCyclicTwoReciprocity
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hcyclic : FiniteCyclicTwoReciprocitySupply (markedRecipAt K)) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteTwoLocalReciprocity K hodd
    hcyclic.toFiniteTwoLocalReciprocitySupply

/-- Compatibility spelling of the uniform completed-injectivity supply. -/
abbrev OddDegreeGalKCompletionReciprocitySupply :=
  OddDegreeGalKCompletedReciprocityInjectivitySupply

/-- The direct injectivity supply implies the uniform odd-degree `q = 2` theorem. -/
theorem oddDegreeGalKDemushkinQTwo_of_completionReciprocitySupply
    (hSupply : OddDegreeGalKCompletionReciprocitySupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply hSupply

/-- The uniform arithmetic-facing supply.  Its reciprocity component is finite local CFT, not
an already-completed injectivity assertion. -/
def OddDegreeGalKFiniteTwoLocalReciprocitySupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      FiniteTwoLocalReciprocitySupply (markedRecipAt K)

/-- Uniform field-facing cyclic-character supply.  This is the natural landing point for the
higher `2^m` Kummer--Tate--Artin theorem: unlike its mod-`2` shadow, it quantifies over every
finite cyclic `2`-group and therefore separates the full pro-`2` completion. -/
def OddDegreeGalKFiniteCyclicTwoReciprocitySupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      FiniteCyclicTwoReciprocitySupply (markedRecipAt K)

/-! ## Field-facing higher Kummer--Tate--Artin adapters -/

/-- The uniform all-`2^m` arithmetic package at odd-degree dyadic fields.  B6 is not a field:
`tateDualityGalKAt` supplies its canonical `G_K` member at every exponent.  The remaining
components are exactly higher Kummer exactness and the pointwise Artin/Hilbert formula. -/
def OddDegreeGalKHigherKummerTateArtinSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      ∀ m : ℕ, ∃ κ : HigherKummerClassData K (2 ^ m),
        HigherTateKummerArtinCompatibilityAt (markedRecipAt K)
          (tateDualityGalKAt K (2 ^ m)) κ

/-- **Pointwise field-facing adapter.**  The all-`2^m` higher Kummer/Artin theorem over one
field produces the abstract cyclic-character supply consumed by the completion argument. -/
theorem finiteCyclicTwoReciprocitySupply_of_higherKummer_tate_artin
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (H : ∀ m : ℕ, ∃ κ : HigherKummerClassData K (2 ^ m),
      HigherTateKummerArtinCompatibilityAt (markedRecipAt K)
        (tateDualityGalKAt K (2 ^ m)) κ) :
    FiniteCyclicTwoReciprocitySupply (markedRecipAt K) :=
  TwoPowerReciprocityCharacterSupply.toFiniteCyclicTwoReciprocitySupply
    (twoPowerReciprocityCharacterSupply_of_canonical_higherKummer_artin H)

/-- **Pointwise campaign closure.**  At an odd-degree field, the all-layer higher
Kummer/Artin package proves the desired Demushkin invariant `q = 2`. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_higherKummer_tate_artin
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (H : ∀ m : ℕ, ∃ κ : HigherKummerClassData K (2 ^ m),
      HigherTateKummerArtinCompatibilityAt (markedRecipAt K)
        (tateDualityGalKAt K (2 ^ m)) κ) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteCyclicTwoReciprocity K hodd
    (finiteCyclicTwoReciprocitySupply_of_higherKummer_tate_artin K H)

/-- The uniform higher Kummer/Artin package supplies the uniform cyclic-character theorem. -/
theorem OddDegreeGalKHigherKummerTateArtinSupply.toFiniteCyclicTwoReciprocitySupply
    (hSupply : OddDegreeGalKHigherKummerTateArtinSupply) :
    OddDegreeGalKFiniteCyclicTwoReciprocitySupply := by
  intro K _ _ _ _ hodd
  exact finiteCyclicTwoReciprocitySupply_of_higherKummer_tate_artin K (hSupply K hodd)

/-- Uniform cyclic characters assemble into the existing uniform finite local-CFT supply. -/
theorem OddDegreeGalKFiniteCyclicTwoReciprocitySupply.toFiniteTwoLocalReciprocitySupply
    (hSupply : OddDegreeGalKFiniteCyclicTwoReciprocitySupply) :
    OddDegreeGalKFiniteTwoLocalReciprocitySupply := by
  intro K _ _ _ _ hodd
  exact (hSupply K hodd).toFiniteTwoLocalReciprocitySupply

/-- A uniform finite local-CFT supply proves the uniform odd-degree `q = 2` theorem, deriving
completed reciprocity injectivity internally at every field. -/
theorem oddDegreeGalKDemushkinQTwo_of_finiteTwoLocalReciprocitySupply
    (hSupply : OddDegreeGalKFiniteTwoLocalReciprocitySupply) :
    OddDegreeGalKDemushkinQTwo := by
  intro K _ _ _ _ hodd
  have hfinite := hSupply K hodd
  exact demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteTwoLocalReciprocity
    K hodd hfinite

/-- A uniform cyclic-character reciprocity supply feeds the campaign endpoint directly. -/
theorem oddDegreeGalKDemushkinQTwo_of_finiteCyclicTwoReciprocitySupply
    (hSupply : OddDegreeGalKFiniteCyclicTwoReciprocitySupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_finiteTwoLocalReciprocitySupply
    hSupply.toFiniteTwoLocalReciprocitySupply

/-- **Uniform campaign closure.**  The all-`2^m` higher Kummer--Tate--Artin package over every
odd-degree dyadic field proves the exact `OddDegreeGalKDemushkinQTwo` input consumed by the
variable GammaL Sylow-core route. -/
theorem oddDegreeGalKDemushkinQTwo_of_higherKummer_tate_artinSupply
    (hSupply : OddDegreeGalKHigherKummerTateArtinSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_finiteCyclicTwoReciprocitySupply
    hSupply.toFiniteCyclicTwoReciprocitySupply

/-- Compatibility name for the earlier uniform supply. -/
abbrev OddDegreeGalKRamifiedITorsionSupply :=
  OddDegreeGalKCompletedReciprocityInjectivitySupply

/-- Compatibility wrapper for the earlier theorem name. -/
theorem oddDegreeGalKDemushkinQTwo_of_ramifiedITorsionSupply
    (hSupply : OddDegreeGalKRamifiedITorsionSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply hSupply

#print axioms oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
#print axioms oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_odd_completion
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_odd_finiteTwoLocalReciprocity
#print axioms oddDegreeGalKDemushkinQTwo_of_completionReciprocitySupply
#print axioms oddDegreeGalKDemushkinQTwo_of_finiteTwoLocalReciprocitySupply
#print axioms oddDegreeGalKDemushkinQTwo_of_finiteCyclicTwoReciprocitySupply
#print axioms finiteCyclicTwoReciprocitySupply_of_higherKummer_tate_artin
#print axioms oddDegreeGalKDemushkinQTwo_of_higherKummer_tate_artinSupply

end

end GQ2.Dyadic.LSquare
