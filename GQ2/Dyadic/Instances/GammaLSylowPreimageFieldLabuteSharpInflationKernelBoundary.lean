/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteTransgressionAtoms
import GQ2.Dyadic.CyclotomicKummerBridge

/-!
# The sharp Labute boundary on the higher inflation kernel

The generic five-term sequence identifies the dual of the stage layer with the kernel of

`H²(G / λ_k, 𝔽₂) → H²(G, 𝔽₂)`.

This file transports the remaining sharp-neutral character boundary across that equivalence.
It thereby isolates the exact missing arithmetic statement as a linear vanishing assertion on
the higher inflation kernel.  The assertion retains all five improved-presentation equations,
including the inseparable diagonal-plus-polarization equation attached to `p²[p,x₂]`.

The existing local Tate/Hilbert API proves the degree-one identity
`cupFormK K (kappaK K) w = cupFormK K w w`.  What is not presently available is a naturality
or higher-Bockstein theorem relating that degree-one identity to the functional below on the
kernel of stage-`k` inflation.  The final equivalence makes that missing bridge precise without
postulating a stronger span or presentation theorem.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

/-- Evaluate a higher inflation-kernel class on a chosen element of the graded layer, using
the inverse of the stage transgression equivalence.  This is an additive functional with the
precise source required by the five-term sequence. -/
noncomputable def lowerTwoCentralInflationKernelEvaluationAt
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 2 ≤ k) (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (r : Additive (zLayer G k)) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    ↥(lowerTwoCentralH2InflationAt G k).ker →+ ZMod 2 := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (AddMonoidHom.eval r).comp
    (lowerTwoCentralTransgressionEquivAt G k hk hfg hpro).symm.toAddMonoidHom

@[simp] theorem lowerTwoCentralInflationKernelEvaluationAt_apply
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 2 ≤ k) (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (r : Additive (zLayer G k))
    (eta :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      let Q := levelQuot G k
      letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      ↥(lowerTwoCentralH2InflationAt G k).ker) :
    lowerTwoCentralInflationKernelEvaluationAt G k hk hfg hpro r eta =
      (lowerTwoCentralTransgressionEquivAt G k hk hfg hpro).symm eta r := rfl

namespace SqCyclotomicStageTuple

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Pull the five explicit cocycle equations back from layer characters to the kernel of
`H²(Q_k,𝔽₂) → H²(G_K(2),𝔽₂)` by the inverse transgression equivalence. -/
noncomputable def SharpNeutralFiveAtomInflationKernelCondition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q :=
      discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    ↥(lowerTwoCentralH2InflationAt G k).ker → Prop := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact fun eta ↦ SharpNeutralFiveAtomTransgressionCocycleCondition T hk hfg
    ((lowerTwoCentralTransgressionEquivAt G k (by omega) hfg
      isProP_maxProPQuotient).symm eta)

/-- The residual element defines a linear functional on the higher inflation kernel. -/
noncomputable def sharpNeutralResidualInflationKernelFunctional {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DiscreteTopology Q :=
      discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    ↥(lowerTwoCentralH2InflationAt G k).ker →+ ZMod 2 := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact lowerTwoCentralInflationKernelEvaluationAt G k (by omega) hfg
    isProP_maxProPQuotient
    (Additive.ofMul (sharpNeutralResidualElement T hk W))

/-- The weakest missing higher local-class-field-theory statement.  Among stage inflation-kernel
classes satisfying the five explicit improved-presentation equations, the residual evaluation
functional vanishes. -/
def SharpCyclotomicInflationKernelResidualCompatibility {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) : Prop :=
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  ∀ eta : ↥(lowerTwoCentralH2InflationAt G k).ker,
    SharpNeutralFiveAtomInflationKernelCondition T hk hfg eta →
      sharpNeutralResidualInflationKernelFunctional T hk W hfg eta = 0

/-- The named higher arithmetic compatibility is neither stronger nor weaker than the remaining
regression goal: transgression duality identifies it exactly with residual bracket-span
membership. -/
theorem sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    SharpCyclotomicInflationKernelResidualCompatibility T hk W hfg ↔
      sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk := by
  rw [sharpNeutralResidual_mem_bracketSpan_iff_transgressionCocycleBoundary W hfg]
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let E := lowerTwoCentralTransgressionEquivAt G k (by omega) hfg
    isProP_maxProPQuotient
  unfold SharpCyclotomicInflationKernelResidualCompatibility
  dsimp only
  constructor
  · intro H phi hphi
    let eta : ↥(lowerTwoCentralH2InflationAt G k).ker := E phi
    have hback : E.symm eta = phi := by
      dsimp only [eta]
      exact E.symm_apply_apply phi
    have heta : SharpNeutralFiveAtomInflationKernelCondition T hk hfg eta := by
      unfold SharpNeutralFiveAtomInflationKernelCondition
      change SharpNeutralFiveAtomTransgressionCocycleCondition T hk hfg (E.symm eta)
      rw [hback]
      exact hphi
    have hzero := H eta heta
    change (E.symm eta)
      (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0 at hzero
    rwa [hback] at hzero
  · intro H eta heta
    let phi : Additive (zLayer G k) →+ ZMod 2 := E.symm eta
    have hphi : SharpNeutralFiveAtomTransgressionCocycleCondition T hk hfg phi := by
      unfold SharpNeutralFiveAtomInflationKernelCondition at heta
      change SharpNeutralFiveAtomTransgressionCocycleCondition T hk hfg (E.symm eta) at heta
      exact heta
    have hzero := H phi hphi
    change (E.symm eta)
      (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0
    exact hzero

end SqCyclotomicStageTuple

#print axioms lowerTwoCentralInflationKernelEvaluationAt_apply
#print axioms SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan

end

end GQ2.Dyadic.LSquare
