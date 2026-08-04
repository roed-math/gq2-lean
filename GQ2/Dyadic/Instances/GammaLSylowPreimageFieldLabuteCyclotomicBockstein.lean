/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CyclotomicKummerBridge
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHigherTransgression

/-!
# The cyclotomic Bockstein class in the higher inflation kernel

At every lower-two-central stage `k ≥ 2`, lift the mod-four cyclotomic class from `G_K(2)` to
`Q_k`, and form the defect

`x ∪ x - κ_k ∪ x`.

The local Hilbert-symbol identity says that this defect dies after inflation.  Thus it is an
honest element of the higher inflation kernel, and inverse transgression gives a character of
`λ_k/λ_{k+1}`.  The final theorem is the chain-level normalization needed to identify that
character: any primitive of the inflated defect restricts to it on `λ_k`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- A fixed lift to `Q_k` of the mod-four cyclotomic/Kummer class on `G_K(2)`. -/
noncomputable def cyclotomicBocksteinVectorAt (k : ℕ) (hk : 2 ≤ k) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    H1 Q (ZMod 2) := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact lowerTwoCentralH1LiftAt G k hk (cyclotomicModFourClassKTwo (K := K))

@[simp] theorem lowerTwoCentralH1InflationAt_cyclotomicBocksteinVectorAt
    (k : ℕ) (hk : 2 ≤ k) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralH1InflationAt G k (cyclotomicBocksteinVectorAt (K := K) k hk) =
      cyclotomicModFourClassKTwo (K := K) := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact lowerTwoCentralH1InflationAt_lift G k hk _

/-- The stage-`k` quotient Bockstein defect for a degree-one class. -/
noncomputable def cyclotomicBocksteinDefectAt (k : ℕ) (hk : 2 ≤ k)
    (x :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2)) :
    let G := maxProPQuotient 2 (GalK K)
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    H2 Q (ZMod 2) := by
  let G := maxProPQuotient 2 (GalK K)
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact lowerTwoCentralBocksteinDefectAt G k
    (cyclotomicBocksteinVectorAt (K := K) k hk) x

/-- The cyclotomic Bockstein defect dies after inflation to `G_K(2)`.  This is the precise
stage-wise consequence of the local Hilbert-symbol identity `x ∪ x = [-1] ∪ x`. -/
theorem cyclotomicBocksteinDefectAt_mem_inflationKernel (k : ℕ) (hk : 2 ≤ k)
    (x :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2)) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    cyclotomicBocksteinDefectAt (K := K) k hk x ∈
      (lowerTwoCentralH2InflationAt G k).ker := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralBocksteinDefectAt_mem_inflationKernel G k
  rw [lowerTwoCentralH1InflationAt_cyclotomicBocksteinVectorAt]
  exact (trivialCupPairing_cyclotomicModFourClassKTwo
    (K := K) (lowerTwoCentralH1InflationAt G k x)).symm

/-- The Bockstein defect as an actual element of the stage-`k` inflation kernel. -/
noncomputable def cyclotomicBocksteinInflationKernelClassAt (k : ℕ) (hk : 2 ≤ k)
    (x :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2)) :
    let G := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G k
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    ↥(lowerTwoCentralH2InflationAt G k).ker := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact ⟨cyclotomicBocksteinDefectAt (K := K) k hk x,
    cyclotomicBocksteinDefectAt_mem_inflationKernel (K := K) k hk x⟩

/-- The layer character obtained by inverse-transgressing the cyclotomic Bockstein defect. -/
noncomputable def cyclotomicBocksteinLayerCharacterAt (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (x :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DiscreteTopology Q :=
        discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2)) :
    let G := maxProPQuotient 2 (GalK K)
    Additive (zLayer G k) →+ ZMod 2 := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact (lowerTwoCentralTransgressionEquivAt G k hk hfg isProP_maxProPQuotient).symm
    (cyclotomicBocksteinInflationKernelClassAt (K := K) k hk x)

/-- Primitive normalization for the inverse transgression of the cyclotomic Bockstein defect.

To prove that the layer character is a desired explicit character (in particular, the fresh
sharp cyclotomic digit), it is enough to exhibit a cocycle representative `z` of the defect and
a primitive `b` of its inflation whose restriction to `λ_k` is that character. -/
theorem cyclotomicBocksteinLayerCharacterAt_eq_of_primitive
    (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (x :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DiscreteTopology Q :=
        discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2))
    (z :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DiscreteTopology Q :=
        discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      Z2 Q (ZMod 2))
    (hz :
      let G := maxProPQuotient 2 (GalK K)
      let Q := levelQuot G k
      letI : DiscreteTopology Q :=
        discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H2mk Q (ZMod 2) z = cyclotomicBocksteinDefectAt (K := K) k hk x)
    (b :
      let G := maxProPQuotient 2 (GalK K)
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      C1 G (ZMod 2))
    (hdb :
      let G := maxProPQuotient 2 (GalK K)
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      let Q := levelQuot G k
      letI : DiscreteTopology Q :=
        discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      dOne G (ZMod 2) b.1 =
        (Z2comap ⟨levelMk G k, continuous_levelMk G k⟩
          (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1)
    (chi :
      let G := maxProPQuotient 2 (GalK K)
      Additive (zLayer G k) →+ ZMod 2)
    (hchi :
      let G := maxProPQuotient 2 (GalK K)
      ∀ n : twoCentralSeries G k,
        chi (Additive.ofMul
          ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩) = b.1 n.1 - b.1 1) :
    cyclotomicBocksteinLayerCharacterAt (K := K) k hk hfg x = chi := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralTransgressionAt_injective G k hk hfg isProP_maxProPQuotient
  apply Subtype.ext
  change lowerTwoCentralTransgressionH2At G k hfg isProP_maxProPQuotient
      (cyclotomicBocksteinLayerCharacterAt (K := K) k hk hfg x) =
    lowerTwoCentralTransgressionH2At G k hfg isProP_maxProPQuotient chi
  rw [lowerTwoCentralTransgressionH2At_eq_of_primitive G k hfg
    isProP_maxProPQuotient z b hdb chi hchi, hz]
  exact congrArg Subtype.val
    ((lowerTwoCentralTransgressionEquivAt G k hk hfg isProP_maxProPQuotient).apply_symm_apply
      (cyclotomicBocksteinInflationKernelClassAt (K := K) k hk x))

#print axioms cyclotomicBocksteinDefectAt_mem_inflationKernel
#print axioms cyclotomicBocksteinLayerCharacterAt_eq_of_primitive

end

end GQ2.Dyadic.LSquare
