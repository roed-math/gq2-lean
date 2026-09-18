/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseAdditiveNormal
import GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
import GQ2.Dyadic.Instances.TameSpliceRamifiedComparison
import GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison

/-!
# Additive phase coordinates for the actual tame-spliced words

The named pair and common ramified comparison maps are additive without changing their
underlying equivalences. The mobile theorem retains an additive witness in the constructive
normal-form assembly; additivity is not inferred from an arbitrary phase-preserving bijection.
All original projected-boundary, factor-set, and representation hypotheses are retained.

Each result supplies the additivity input of `phaseComparisonAddEquiv` and
`phaseComparison_polar_reducedMatrix` in `WordPhaseAdditiveNormal`. Thus the previously
checked common finite polar matrix is literally congruent to the source quotient's polar
form in these coordinates, not merely equinumerous with its values. No determinant or
analytic source premise is assumed, and no source word is changed.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Certificates GQ2.Dyadic.LSquare
open Instances.WordPhase Instances.WordPhaseModel
open Instances.EvenMHeadHandlePairSpliceSupply Instances.EvenMHeadHandlePairSpliceNormal
open Instances.EvenMHeadHandlePairProjectedPhase

variable {alpha h q : ℕ} (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)

local notation "W" => headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}


open Instances.WordPhaseAdditiveNormal
/-- The actual pair splice's existing normal-coordinate equivalence is additive. -/
theorem headHandlePairSplice_unramifiedComparison_add
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
    (hsigma2 : powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) = 1)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI := scalarActionZmodTwo ((GammaR (2 + 2*h) q W) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    let C := headHandlePairSplice_unramifiedComparison halpha halpha2 hq0 hqe j nuP rho base hbase pi hpi hf hm hphi hcompat hwildTwo htau hwild hsigma hsigma2
    C.phaseEquiv (x+y) = C.phaseEquiv x+C.phaseEquiv y := by
  letI := scalarActionZmodTwo ((GammaR (2 + 2*h) q W) : Type)
  letI := scalarActionZmodTwo_continuousSMul ((GammaR (2 + 2*h) q W) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  exact phaseComparison_of_normalForm_add _ _ _ _ hwildTwo _ (compactPhaseNormal_add h)
    _ _ _ _ (fun z c hc ↦ QZero_headHandlePairSplice_unramified_compactPhase
      halpha halpha2 hq0 hqe j nuP rho base hbase pi hpi hf hm hphi
      c htau hwild hsigma2 z hc) x y

#print axioms headHandlePairSplice_unramifiedComparison_add
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open Count Words Certificates LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.WordPhaseSeam
open Instances.WordPhaseCompactMHandleData Instances.WordPhaseCompactMData
open Instances.WordPhaseCompactNData

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


open Instances.WordPhaseAdditiveNormal
/-- The common ramified comparison is additive, including its final head swap. -/
theorem phaseComparison_tameSplice_mCompact_ramified_add
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
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho (gammaGen (2+2*h) q W .tau))•v=v → v=0)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    let C := phaseComparison_tameSplice_mCompact_ramified S hspecR hq0 hqe hend rho hcompat hwildTwo base hbase pi hpi hf hm hphi hwild htauOdd htauFpf
    C.phaseEquiv (x+y) = C.phaseEquiv x+C.phaseEquiv y := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  dsimp only [phaseComparison_tameSplice_mCompact_ramified, Equiv.trans_apply]
  rw [phaseComparison_of_normalForm_add _ _ _ _ hwildTwo _ (compactPhaseNormal_add h)
    _ _ _ _ (fun p c hc ↦ QZero_tameSplice_mCompact_ramified S hspecR hq0 hqe hend
      rho base hbase pi hpi hf hm hphi c hwild htauOdd htauFpf p hc)]
  exact (ramifiedHandleSwapAddEquiv DD.Vmod h).map_add _ _

#print axioms phaseComparison_tameSplice_mCompact_ramified_add
end
end GQ2.Dyadic

namespace GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison
noncomputable section
open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcMobileNuSource
open GQ2.Dyadic.Instances.MpcMobileSpliceSupply
open GQ2.Dyadic.Instances.MpcMobileProjectedPhase
open GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology


open Instances.WordPhaseAdditiveNormal
section Comparison

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
local instance : DistribMulAction ((GammaR (2 + 2 * h) q W) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR (2 + 2 * h) q W) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

include halpha2


/-- The actual mobile splice admits the stronger additive phase comparison at every level
and semantic unit. The normal-form construction is retained to expose this extra property. -/
theorem exists_mpcMobile_unramified_additive_comparison
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
    ∃ C : SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h),
      ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 := ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q W i)⟩
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent DD.C0)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent DD.C0)
  let S := mpcMobileTameSplice_uniformStokesSupply (r := r) (p := p)
    hq0 hqe eta halpha halpha2 nuP
  let k := wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark
  let raw := fun l : Fin 2 ↦ heisToFree E E₂
    (gammaFam (2 + 2 * h) q (Mpc.mpcWUnit alpha r p eta h) l)
  let actual := pinnedResolvedFamily (2 + 2 * h) q W (4 * Monoid.exponent DD.C0)
  have hV₂ := Vmod_exp2 DD
  have htauAct : ∀ a : DD.Vmod, t.τ • a = a := by
    intro a
    rw [hpi]
    change pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .tau)) • a = a
    rw [htau, one_smul]
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (a : DD.Vmod), t.x i • a = a := by
    intro i a
    rw [hpi]
    change pi (rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i))) • a = a
    rw [hwild i, one_smul]
  have hσfpf : ∀ a : DD.Vmod, t.σ • a = a → a = 0 := by
    intro a ha
    apply hsigmaFpf a
    exact (hpi t.σ a).symm.trans ha
  have hS₂ : ∀ a : DD.Vmod, powOmega2 t.σ • a = a := by
    intro a
    rw [hpi, powOmega2_map pi]
    change powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) • a = a
    rw [hsigma2, one_smul]
  have hη : ∀ a : DD.Vmod, t.σ ^ E (etaHatZ (eta : ℤ_[2])) • a = t.σ • a :=
    pinned_eta_smul_eq_sigma t.σ eta hS₂
  have hSk : ∀ (i : Fin (2 + 2 * h + 1)) (a : DD.Vmod),
      t.σ ^ E (padicOmega2 (k i)) • a = a := by
    intro i a
    rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even DD.C0).1
      (fun c : DD.C0 ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _))]
    exact zpowHat_padicOmega2_smul_of_powOmega2 t.σ (k i) hS₂ a
  have hres : ResolverLifts E (WordLift DD.Vmod DD.C0) :=
    omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hV₂
  have hrow := heisD1_mpcUnit_compact_unramified_apply (r := r) (pp := p)
    t eta E E₂ hV₂ halpha hqe hres hwildAct htauAct hS₂ hη
  have hsq : ∀ a : DD.Vmod, heisD1 ⇑t raw (heisD0 ⇑t a) = 0 := by
    intro a
    have ht : heisD0 ⇑t a .tau = 0 := by
      change t.τ • a - a = 0
      rw [htauAct, sub_self]
    have hx : heisD0 ⇑t a (coreLetter h 2) = 0 := by
      change t.x _ • a - a = 0
      rw [hwildAct, sub_self]
    rw [hrow, ht, hx]
    simp
  have hresWord : ResolvesAt (gammaFam (2 + 2 * h) q W) actual
      (WordLift DD.Vmod DD.C0) := S.resolvesWord hV₂
  have hr : ∀ l, FreeGroup.lift ⇑t (actual l) = 1 :=
    lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q W) hresWord
  have hkernel (x : Generator (2 + 2 * h) → DD.Vmod) :
      heisD1 ⇑t actual x = 0 ↔ heisD1 ⇑t raw x = 0 :=
    kernel_iff_normalizedCorrectedSplice_unramified_of_square t E E₂ k hV₂
      hwildAct htauAct hqe hσfpf hSk (omegaPinnedLevelZhatResolver_omega2 _)
      (omega2Exp_fourMulExponent_mod_four DD.C0) _ _ _ hsq hr x
  have hmem : ∀ z : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod),
      heisD1 ⇑t actual (wPmCompactPhaseNormal h z) = 0 := fun z ↦
    (hkernel _).mpr (mpcUnit_compactPhaseNormal_mem t eta E E₂ hV₂ halpha hqe
      hres hwildAct htauAct hS₂ hη z)
  have hnf : ∀ x, heisD1 (A := DD.Vmod) ⇑t actual x = 0 →
      ∃! z : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod),
        x - wPmCompactPhaseNormal h z ∈ Set.range (heisD0 ⇑t) := fun x hx ↦
    mpcUnit_compactPhaseNormalForm t eta E E₂ hV₂ halpha hqe hres hwildAct htauAct
      hS₂ hη hσfpf x ((hkernel x).mp hx)
  let hphase := fun z c hc ↦
    QZero_mpcMobileTameSplice_unramified_compactPhase hq0 hqe eta halpha halpha2 nuP
      rho base hbase pi hpi hf hm hphi c htau hwild hsigma2 z hc
  refine ⟨wPmPhaseComparison_of_normalForm rho hcompat hresWord hV₂ hwildTwo
    (wPmCompactPhaseNormal h) hmem hnf (scalarActionZmodTwo_triv _)
    (wPhCompactWallHandlePhase DD.qbar h) hphase, ?_⟩
  exact phaseComparison_of_normalForm_add rho hcompat hresWord hV₂ hwildTwo
    (wPmCompactPhaseNormal h) (compactPhaseNormal_add h) hmem hnf
    (scalarActionZmodTwo_triv _) (wPhCompactWallHandlePhase DD.qbar h) hphase

end Comparison
#print axioms exists_mpcMobile_unramified_additive_comparison
end
end GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison

