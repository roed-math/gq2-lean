/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteTransgressionAtoms
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteCyclotomicBockstein
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherHilbert90

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

/-- Chain-level arithmetic form of the missing compatibility.

For every inflation-kernel class satisfying the five improved-presentation equations, every
primitive of an inflated cocycle representative must vanish, after normalization at `1`, on a
lift of the residual layer element.  The quantification over primitives is harmless:
`lowerTwoCentralPrimitive_restriction_uniqueAt` proves that all primitives have the same
normalized restriction to `λ_k`.

This is the exact datum absent from B11a as currently exposed.  The norm-criterion axiom proves
only equality in `H²`; it does not return the Hilbert-90 cochain whose restriction can be
compared with the sharp cyclotomic digit. -/
def SharpCyclotomicInflationPrimitiveResidualVanishing {h k : ℕ}
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
  ∀ (eta : ↥(lowerTwoCentralH2InflationAt G k).ker),
    SharpNeutralFiveAtomInflationKernelCondition T hk hfg eta →
      ∀ (z : Z2 Q (ZMod 2)) (b : C1 G (ZMod 2)),
        H2mk Q (ZMod 2) z = eta.1 →
        dOne G (ZMod 2) b.1 =
            (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
              (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1 →
          ∀ n : twoCentralSeries G k,
            levelMk G (k + 1) n.1 = (sharpNeutralResidualElement T hk W).1 →
              b.1 n.1 - b.1 1 = 0

/-- The primitive restriction calculation implies the desired residual vanishing on the higher
inflation kernel.  This theorem is the handoff point for an explicit local-class-field-theory
or Hilbert-90 cochain construction. -/
theorem sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (H : SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg) :
    SharpCyclotomicInflationKernelResidualCompatibility T hk W hfg := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  unfold SharpCyclotomicInflationKernelResidualCompatibility
  dsimp only
  intro eta heta
  obtain ⟨z, b, hz, hdb⟩ := exists_lowerTwoCentralInflationPrimitiveAt G k eta
  obtain ⟨g, hg, hgr⟩ := (sharpNeutralResidualElement T hk W).2
  let n : twoCentralSeries G k := ⟨g, hg⟩
  have hbzero : b.1 n.1 - b.1 1 = 0 := by
    apply H eta heta z b hz hdb n
    exact hgr
  change (lowerTwoCentralTransgressionEquivAt G k (by omega) hfg
      isProP_maxProPQuotient).symm eta
        (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0
  have hr : sharpNeutralResidualElement T hk W =
      ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩ := Subtype.ext hgr.symm
  rw [hr, lowerTwoCentralTransgressionEquivAt_symm_apply_eq_primitive
    G k (by omega) hfg isProP_maxProPQuotient eta z hz b hdb]
  exact hbzero

/-- The exact bridge still needed after the all-exponent higher Kummer and Artin campaigns.

The premise is the canonical higher Kummer package together with the (existential) local
Tate--Kummer--Artin compatibility at every `2`-power exponent.  The conclusion asks for its
cochain-level compatibility with Hochschild--Serre transgression: a primitive of an inflated
stage cocycle has zero normalized value on the sharp residual.

This implication is deliberately named rather than folded into either endpoint.  The current
higher Kummer/Hilbert--90 API constructs explicit degree-one Kummer cocycles, while the higher
Artin API identifies only cohomology classes and abelian characters.  Neither endpoint mentions
the `C1` primitive of a vanishing `H2` class occurring here. -/
def HigherKummerArtinSharpPrimitiveRestrictionBridge
    {R : LocalReciprocity} (B : MarkedRecip R K)
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) : Prop :=
  (∀ m : ℕ, HigherTateKummerArtinCompatibilityAt B
      (tateDualityGalKAt K (2 ^ m))
      (canonicalHigherKummerClassData K (2 ^ m))) →
    SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg

/-- The higher Kummer--Artin bridge has exactly the same input strength as finite-layer norm
reciprocity.  This regression follows from the existing all-exponent equivalence and confirms
that no extra higher-Kummer exactness or coefficient scalarization is hidden in the bridge. -/
theorem higherKummerArtinSharpPrimitiveRestrictionBridge_iff_finiteLayerNormReciprocity
    {R : LocalReciprocity} {B : MarkedRecip R K}
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg ↔
      (FiniteLayerNormReciprocity B →
        SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg) := by
  unfold HigherKummerArtinSharpPrimitiveRestrictionBridge
  rw [allCanonicalHigherTateKummerArtinCompatibility_iff_finiteLayerNormReciprocity]

/-- All-exponent higher Tate--Kummer--Artin compatibility, together with the missing
transgression bridge, proves the desired residual vanishing on the higher inflation kernel. -/
theorem sharpCyclotomicInflationKernelResidualCompatibility_of_higherKummerArtinBridge
    {R : LocalReciprocity} {B : MarkedRecip R K}
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (HArtin : ∀ m : ℕ, HigherTateKummerArtinCompatibilityAt B
      (tateDualityGalKAt K (2 ^ m))
      (canonicalHigherKummerClassData K (2 ^ m)))
    (Hbridge : HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg) :
    SharpCyclotomicInflationKernelResidualCompatibility T hk W hfg :=
  sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing W hfg
    (Hbridge HArtin)

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
#print axioms SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing
#print axioms SqCyclotomicStageTuple.higherKummerArtinSharpPrimitiveRestrictionBridge_iff_finiteLayerNormReciprocity
#print axioms SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_of_higherKummerArtinBridge
#print axioms SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan

end

end GQ2.Dyadic.LSquare
