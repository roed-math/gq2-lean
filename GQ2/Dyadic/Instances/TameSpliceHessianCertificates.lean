/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactCertificates
import GQ2.Dyadic.Instances.WordPhaseSpliceAdditiveNormal

/-!
# Original Hessian records for actual pair and mobile splice sources

Each adapter retains the original projected-boundary hypotheses, constructs the
actual word's additive phase comparison, and packages its unchanged coordinate map
in the original Hessian record. Cardinality and F2 module structures are derived;
no new normal-form, quadratic identity, matrix, or Gauss-sum premise is added.
-/

namespace GQ2.Dyadic.Instances.TameSpliceHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix GQ2.FoxH
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Certificates GQ2.Dyadic.LSquare
open Instances.WordPhaseCompactCertificates
open Instances.EvenMHeadHandlePairSpliceSupply Instances.EvenMHeadHandlePairUnramifiedComparison
open Instances.MpcMobileNuSource Instances.MpcMobileUnramifiedComparison
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSplice
open Instances.MpcMobileSpliceSupply

section Pair
variable {alpha h q : ℕ} (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
local notation "W" => headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}

/-- The actual pair-spliced source has the original Hessian record in the
unramified branch, with no additional premises beyond its phase comparison. -/
def pairUnramifiedHessian
    (rho : ContinuousMonoidHom ((GammaR (2 + 2 * h) q W) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    [ContinuousSMul ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀ (g : ((GammaR (2 + 2 * h) q W) : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2 + 2 * h) q W i)))
    (htau : pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .tau)) = 1)
    (hwild : ∀ i : Fin (2 + 2 * h + 1),
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i))) = 1)
    (hsigma : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q W .sigma) • v = v → v = 0)
    (hsigma2 : powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) = 1) :
    letI := scalarActionZmodTwo ((GammaR (2 + 2 * h) q W) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceCompactHessian DD rho (scalarActionZmodTwo_triv _) h := by
  letI := scalarActionZmodTwo ((GammaR (2 + 2 * h) q W) : Type)
  letI := scalarActionZmodTwo_continuousSMul ((GammaR (2 + 2 * h) q W) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  exact sourceCompactHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (headHandlePairSplice_unramifiedComparison halpha halpha2 hq0 hqe j nuP
      rho base hbase pi hpi hf hm hphi hcompat hwildTwo htau hwild hsigma hsigma2)
    (headHandlePairSplice_unramifiedComparison_add halpha halpha2 hq0 hqe j nuP
      rho base hbase pi hpi hf hm hphi hcompat hwildTwo htau hwild hsigma hsigma2)
end Pair

section Ramified
variable {alpha h q : ℕ} {R : PWord (Generator (2+2*h))}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator (2+2*h))}
local notation "W" => tameSplice R (Words.MCompact.mCompactW alpha h)
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((GammaR (2+2*h) q W) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR (2+2*h) q W) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The common ramified adapter applies to the actual pair and mobile splices,
including the additive head swap in their existing phase comparison. -/
def tameSpliceRamifiedHessian
    (S : UniformStokesSupply (2+2*h) q W wOf)
    (hspecR : TameSpec.TameSpecializes (2+2*h) q R) (hq0 : q≠0) (hqe : Even q)
    (hend : ∀ N : ℕ, N≠0 → N.factorization 2≠0 → IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
      (gammaFam (2+2*h) q R k)))
    (rho : ContinuousMonoidHom ((GammaR (2+2*h) q W) : Type) (Bg ⧸ D.M))
    [IsTopologicalAddGroup DD.Vmod]
    [DistribMulAction ((GammaR (2+2*h) q W) : Type) DD.Vmod]
    [ContinuousSMul ((GammaR (2+2*h) q W) : Type) DD.Vmod]
    (hcompat : ∀ (g : ((GammaR (2+2*h) q W) : Type)) (v : DD.Vmod),
      g•v=rho0 DD rho g•v)
    (hwildTwo : IsWildTwo (wildAlphabet (2+2*h))
      (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2+2*h) q W i)))
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=pi cc•v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b=base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v=base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hwild : ∀ i : Fin (2+2*h+1), pi (rho0 DD rho (gammaGen (2+2*h) q W (.wild i)))=1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho (gammaGen (2+2*h) q W .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho (gammaGen (2+2*h) q W .tau))•v=v → v=0) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceCompactHessian DD rho (scalarActionZmodTwo_triv _) h := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  exact sourceCompactHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (phaseComparison_tameSplice_mCompact_ramified S hspecR hq0 hqe hend rho hcompat
      hwildTwo base hbase pi hpi hf hm hphi hwild htauOdd htauFpf)
    (phaseComparison_tameSplice_mCompact_ramified_add S hspecR hq0 hqe hend rho hcompat
      hwildTwo base hbase pi hpi hf hm hphi hwild htauOdd htauFpf)
end Ramified

section Mobile
variable {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
  (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
local notation "W" => tameSplice
  (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (MCompact.mCompactW alpha h)
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((GammaR (2+2*h) q W) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR (2+2*h) q W) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

include halpha2 in
/-- The mobile source's actual additive comparison supplies the original Hessian
record uniformly in alpha, level, power parameter, semantic unit and handle count. -/
theorem nonempty_mobileUnramifiedHessian
    (rho : ContinuousMonoidHom ((GammaR (2 + 2 * h) q W) : Type) (Bg ⧸ D.M))
    [DistribMulAction ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    [ContinuousSMul ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀ (g : ((GammaR (2 + 2 * h) q W) : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2 + 2 * h) q W i)))
    (htau : pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .tau)) = 1)
    (hwild : ∀ i : Fin (2 + 2 * h + 1),
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i))) = 1)
    (hsigma2 : powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod,
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma)) • v = v → v = 0) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    Nonempty (SourceCompactHessian DD rho (scalarActionZmodTwo_triv _) h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  obtain ⟨C, hadd⟩ := exists_mpcMobile_unramified_additive_comparison
    (r := r) (p := p) hq0 hqe eta halpha halpha2 nuP rho
    base hbase pi hpi hf hm hphi hcompat hwildTwo htau hwild hsigma2 hsigmaFpf
  exact ⟨sourceCompactHessianOfComparison DD rho (scalarActionZmodTwo_triv _) C hadd⟩
end Mobile

section ConcreteRamified
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} (DD : DescData D)
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]

/-- The pair word supplies all structural inputs of the ramified Hessian adapter.
The remaining arguments are exactly its projected boundary and action data. -/
abbrev pairRamifiedHessian {alpha h q : ℕ}
    (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :=
  tameSpliceRamifiedHessian (DD := DD)
    (uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuP)
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuP)
    hq0 hqe (fun _ hN hNtwo ↦ headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP hN hNtwo)

/-- Every mobile level, power and semantic unit supplies the complete structural
input of the ramified Hessian adapter, including the zero-handle case. -/
abbrev mobileRamifiedHessian {alpha r p h q : ℕ}
    (hq0 : q≠0) (hqe : Even q) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :=
  tameSpliceRamifiedHessian (DD := DD)
    (mpcMobileTameSplice_uniformStokesSupply (r := r) (p := p) hq0 hqe eta halpha halpha2 nuP)
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP) hq0 hqe
    (fun _ hN hNtwo ↦ mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP hN hNtwo)
end ConcreteRamified

#print axioms pairUnramifiedHessian
#print axioms tameSpliceRamifiedHessian
#print axioms nonempty_mobileUnramifiedHessian
#print axioms pairRamifiedHessian
#print axioms mobileRamifiedHessian

end
end GQ2.Dyadic.Instances.TameSpliceHessianCertificates
