/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CyclotomicKummerBridge
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHigherTransgression
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage

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
  let cQ : ContinuousMonoidHom Q (Multiplicative (ZMod 2)) :=
    (continuousCharacterLevelEquivAt G k hk).symm
      (cyclotomicModFourCharacterKTwo (K := K))
  exact H1mk Q (ZMod 2) (Count.homEquivZ1 cQ)

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
  unfold cyclotomicBocksteinVectorAt cyclotomicModFourClassKTwo
  dsimp only
  rw [show lowerTwoCentralH1InflationAt G k =
      inf1 ⟨levelMk G k, continuous_levelMk G k⟩ (fun _ _ => rfl) from rfl,
    inf1_H1mk]
  congr 1

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

/-- The genuinely fresh cyclotomic shadow on the layer `λ_k/λ_{k+1}`.  Its codomain retains
one digit more than the ordinary level-`k+1` shadow; its kernel is exactly the sharp-neutral
condition on a layer element. -/
noncomputable def sharpCyclotomicLayerShadowAt (k : ℕ) (hk : 2 ≤ k) :
    let G := maxProPQuotient 2 (GalK K)
    zLayer G k →* (ZMod (2 ^ (k + 2)))ˣ := by
  let G := maxProPQuotient 2 (GalK K)
  exact (SqCyclotomicStageTuple.sharpChiLevel
      (chiCycKTwo (K := K)) (k + 1) (by omega)).comp
    (zLayer G k).subtype

@[simp] theorem sharpCyclotomicLayerShadowAt_apply
    (k : ℕ) (hk : 2 ≤ k)
    (n :
      let G := maxProPQuotient 2 (GalK K)
      twoCentralSeries G k) :
    let G := maxProPQuotient 2 (GalK K)
    sharpCyclotomicLayerShadowAt (K := K) k hk
        ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩ =
      Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom
        (chiCycKTwo (K := K) n.1) := by
  let G := maxProPQuotient 2 (GalK K)
  exact SqCyclotomicStageTuple.sharpChiLevel_levelMk
    (chiCycKTwo (K := K)) (k + 1) (by omega) n.1

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

/-- Kernel-level form of the remaining arithmetic calculation.  If a primitive of the
inflated Bockstein defect vanishes on an element of `λ_k` exactly when that element has trivial
fresh cyclotomic digit, then inverse transgression detects precisely the same sharp-neutral
subgroup of the layer.

This avoids choosing a generator of the two-element target digit group: zero/nonzero is the
normalization actually consumed by the sharp correction problem. -/
theorem cyclotomicBocksteinLayerCharacterAt_eq_zero_iff_sharpShadow_of_primitive
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
    (hsharp :
      let G := maxProPQuotient 2 (GalK K)
      ∀ n : twoCentralSeries G k,
        b.1 n.1 - b.1 1 = 0 ↔
          Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom
            (chiCycKTwo (K := K) n.1) = 1) :
    let G := maxProPQuotient 2 (GalK K)
    ∀ r : zLayer G k,
      cyclotomicBocksteinLayerCharacterAt (K := K) k hk hfg x
          (Additive.ofMul r) = 0 ↔
        sharpCyclotomicLayerShadowAt (K := K) k hk r = 1 := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  obtain ⟨chi, hchi⟩ :=
    exists_lowerTwoCentralLayerCharacterAt_of_inflation_coboundary G k hk z b hdb
  have heq : cyclotomicBocksteinLayerCharacterAt (K := K) k hk hfg x = chi :=
    cyclotomicBocksteinLayerCharacterAt_eq_of_primitive
      (K := K) k hk hfg x z hz b hdb chi hchi
  intro r
  obtain ⟨g, hg, hgr⟩ := r.2
  let n : twoCentralSeries G k := ⟨g, hg⟩
  have hr : r =
      ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩ := Subtype.ext hgr.symm
  rw [heq, hr, hchi]
  exact hsharp n

#print axioms cyclotomicBocksteinDefectAt_mem_inflationKernel
#print axioms cyclotomicBocksteinLayerCharacterAt_eq_of_primitive
#print axioms cyclotomicBocksteinLayerCharacterAt_eq_zero_iff_sharpShadow_of_primitive

end

end GQ2.Dyadic.LSquare
