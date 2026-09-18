/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMobileProjectedPhase
import GQ2.Dyadic.SigmaNormalSpliceTransport
import GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal

/-!
# Unramified source-to-word phase comparison for the mobile Mpc splice

The finite resolver and the normal-coordinate calculations remain at the actual lower group.
Only the quadratic phase is projected to its faithful head. In particular, no assertion that
the raw relator dies in the unprojected lower group is used.
-/

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

/-- Semantic eta has the sigma action when the two-primary sigma component acts trivially. -/
theorem pinned_eta_smul_eq_sigma
    {C A : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [DistribMulAction C A]
    (s : C) (eta : ℤ_[2]) (hs : ∀ a : A, powOmega2 s • a = a) (a : A) :
    s ^ omegaPinnedLevelZhatResolver (4 * Monoid.exponent C) (etaHatZ eta) • a = s • a := by
  rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even C).1
    (fun c : C ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _)),
    etaHatZ, zpowHat_mul, zpowHat_ofInt, zpow_one, mul_smul,
    zpowHat_padicOmega2_smul_of_powOmega2 s (eta - 1) hs a]

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

/-- The actual mobile splice has the compact source-to-word phase comparison in the
unramified nontrivial branch. The raw word is used only through its Fox row and chain square. -/
theorem exists_mpcMobile_unramified_comparison
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
    Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h)) := by
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
  refine ⟨wPmPhaseComparison_of_normalForm rho hcompat hresWord hV₂ hwildTwo
    (wPmCompactPhaseNormal h) hmem hnf (scalarActionZmodTwo_triv _)
    (wPhCompactWallHandlePhase DD.qbar h) ?_⟩
  intro z c hc
  exact QZero_mpcMobileTameSplice_unramified_compactPhase hq0 hqe eta halpha halpha2 nuP
    rho base hbase pi hpi hf hm hphi c htau hwild hsigma2 z hc

end Comparison

#print axioms pinned_eta_smul_eq_sigma
#print axioms exists_mpcMobile_unramified_comparison

end
end GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison
