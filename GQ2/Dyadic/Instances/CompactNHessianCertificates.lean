/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactNData
import GQ2.Dyadic.Instances.WordPhaseCompactCertificates

/-!
# Original Hessian records for the actual compact-N source

The two old source comparisons use the same additive compact normal map. We prove
additivity of those very maps and retain them in the original Hessian record. All
head, resolver, and phase premises remain precisely those of the old comparison.
-/

namespace GQ2.Dyadic.Instances.CompactNHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.FoxH GQ2.QuadraticFp2
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.WordPhaseCompactNData
open Instances.WordPhaseAdditiveNormal Instances.WordPhaseCompactCertificates

section Head
variable {alpha h q : Nat}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  (rho : ContinuousMonoidHom
    ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction
    ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
  [ContinuousSMul
    ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
  {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
  (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
  (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
  (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
  (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
  (hcompat : ∀
    (g : ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type))
    (v : DD.Vmod), g • v = rho0 DD rho g • v)
  (hA2 : ∀ v : DD.Vmod, v + v = 0)
  (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
    (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) i)))
  (hq0 : q ≠ 0) (hqe : Even q) (halpha : 2 ≤ alpha)
  (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
    (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i))) = 1)

local notation "Gamma" => ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type)
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul Gamma (ZMod 2) := scalarActionZmodTwo_continuousSMul _
local instance : Fintype DD.Vmod := Fintype.ofFinite _

theorem compactNUnramifiedComparison_add
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma)) • v = v → v = 0)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    let C := wPcNComparison_unramifiedHead rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha htauHead hwildHead hsigmaFpf
    C.phaseEquiv (x+y) = C.phaseEquiv x + C.phaseEquiv y := by
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) := Fintype.ofFinite _
  dsimp only [wPcNComparison_unramifiedHead, wPmCompactPhaseComparison_of_headPhase]
  apply phaseComparison_of_normalForm_add
  exact compactPhaseNormal_add h

theorem compactNRamifiedComparison_add
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v = v → v = 0)
    (htauOdd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v = v)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    let C := wPcNComparison_ramifiedHead rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha hwildHead htauFpf htauOdd
    C.phaseEquiv (x+y) = C.phaseEquiv x + C.phaseEquiv y := by
  dsimp only [wPcNComparison_ramifiedHead]
  apply phaseComparison_of_normalForm_add
  exact compactPhaseNormal_add h

/-- The actual unramified compact-N comparison in the original certificate type. -/
def compactNUnramifiedHessian
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma)) • v = v → v = 0) :
    SourceCompactHessian DD rho (scalarActionZmodTwo_triv _) h :=
  sourceCompactHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (wPcNComparison_unramifiedHead rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha htauHead hwildHead hsigmaFpf)
    (compactNUnramifiedComparison_add rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha hwildHead htauHead hsigmaFpf)

/-- The actual ramified compact-N comparison in the original certificate type. -/
def compactNRamifiedHessian
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v = v → v = 0)
    (htauOdd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v = v) :
    SourceCompactHessian DD rho (scalarActionZmodTwo_triv _) h :=
  sourceCompactHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (wPcNComparison_ramifiedHead rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha hwildHead htauFpf htauOdd)
    (compactNRamifiedComparison_add rho base hbase pi hpi hf hm hcompat hA2
      hwildTwo hq0 hqe halpha hwildHead htauFpf htauOdd)
end Head

#print axioms compactNUnramifiedComparison_add
#print axioms compactNRamifiedComparison_add
#print axioms compactNUnramifiedHessian
#print axioms compactNRamifiedHessian
end
end GQ2.Dyadic.Instances.CompactNHessianCertificates
