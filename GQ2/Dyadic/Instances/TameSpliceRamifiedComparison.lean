/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceRamifiedNormal

/-!
# Complete ramified phase comparison for a structural tame splice

The projected head is actual and its factor-set descent is explicit. The pinned
full central-extension calculation identifies QZero; full Fox-row transport
identifies the compact normal forms. Their combination gives the common wall-
and-handle phase comparison, without an assumed source equivalence, normal form,
phase identity, or determinant certificate.
-/

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

/-- The normal source obstruction has the template's honest ramified phase. -/
theorem QZero_tameSplice_mCompact_ramified
    (S : UniformStokesSupply (2+2*h) q W wOf)
    (hspecR : TameSpec.TameSpecializes (2+2*h) q R) (hq0 : q≠0) (hqe : Even q)
    (hend : ∀ N : ℕ, N≠0 → N.factorization 2≠0 → IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
      (gammaFam (2+2*h) q R k)))
    (rho : ContinuousMonoidHom ((GammaR (2+2*h) q W) : Type) (Bg ⧸ D.M))
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=pi cc•v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b=base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v=base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (c : VCocycle DD rho)
    (hwild : ∀ i : Fin (2+2*h+1), pi (rho0 DD rho (gammaGen (2+2*h) q W (.wild i)))=1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho (gammaGen (2+2*h) q W .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho (gammaGen (2+2*h) q W .tau))•v=v → v=0)
    (p : (DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen (2+2*h) q W i))=wPmCompactPhaseNormal h p) :
    QZero DD rho c=wPcMRamifiedHandlePhase DD.qbar h p := by
  let L := SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod×DD.C0))
  have hcsigma : c.c (gammaGen (2+2*h) q W .sigma)=0 :=
    (congrFun hc .sigma).trans (wPmCompactPhaseNormal_sigma h p)
  have hctau : c.c (gammaGen (2+2*h) q W .tau)=0 :=
    (congrFun hc .tau).trans (wPmCompactPhaseNormal_tau h p)
  have hwildc : (fun i ↦ c.c (gammaGen (2+2*h) q W (.wild i))) =
      (fun i ↦ wPmCompactPhaseNormal h p (.wild i)) := funext fun i ↦ congrFun hc (.wild i)
  rw [UniformStokesSupply.QZero_eq_pinned_projectedHessian_of_tameNormal S
    (tameSpecializes_tameSplice hspecR (tameSpecializes_mCompact hq0 hqe alpha h)) hqe
    rho base hbase pi hpi hf hm c hwild hcsigma hctau, hwildc]
  exact hessRelZ_tameSplice_mCompact_ramified_pinned base hbase
    (semiProdProjHom (V := DD.Vmod) pi hpi) hphi (Vmod_exp2 DD) hq0 hqe _ _ htauOdd htauFpf
    R hspecR (hend _ (fourMulExponent_ne_zero_and_even L).1
      (fourMulExponent_ne_zero_and_even L).2) p

/-- Ramified phase comparison, including construction and uniqueness of normal forms. -/
noncomputable def phaseComparison_tameSplice_mCompact_ramified
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
    letI : Fintype ((DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod)) := inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod)) := inferInstance
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2+2*h) DD.C0 := ⟨fun i ↦ theta (gammaGen (2+2*h) q W i)⟩
  let E := omegaPinnedLevelZhatResolver (4*Monoid.exponent DD.C0)
  let E₂ := omegaPinnedLevelZtwoResolver (4*Monoid.exponent DD.C0)
  let w : Fin 2 → FreeGroup (Generator (2+2*h)) := fun k ↦ heisToFree E E₂ (gammaFam (2+2*h) q W k)
  have hsurj : Function.Surjective pi := by
    intro a
    obtain ⟨g, hg⟩ := hphi ((0,a) : SemiProd Cbar DD.Vmod)
    exact ⟨g.2, congrArg Prod.snd hg⟩
  have hwildAct : ∀ (i : Fin (2+2*h+1)) (v : DD.Vmod), t.x i•v=v := by
    intro i v
    rw [hpi, show pi (t.x i)=1 from hwild i, one_smul]
  have htauFpf' : ∀ v : DD.Vmod, t.τ•v=v → v=0 := by
    intro v hv
    apply htauFpf v
    rw [← hpi]
    exact hv
  have htauOdd' : Odd (orderOf (pi t.τ)) := htauOdd
  have hodd : ∀ v : DD.Vmod, powOmega2 (pi t.τ)•v=v := by
    intro v
    rw [powOmega2_eq_one_of_odd htauOdd', one_smul]
  have hTodd : ∀ v : DD.Vmod, powOmega2 t.τ•v=v := by
    intro v
    rw [hpi, powOmega2_map]
    exact hodd v
  have htame : t.TameRelAt q := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR (2+2*h) q W).rel theta (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2+2*h) q)=1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hdiff := heisD1_tameSplice_mCompact_ramified_of_projected (alpha := alpha)
    t pi hpi hsurj (Vmod_exp2 DD) hq0 hqe hwild htauFpf hodd R hspecR
    (hend _ (fourMulExponent_ne_zero_and_even DD.C0).1
      (fourMulExponent_ne_zero_and_even DD.C0).2)
  have hrow : ∀ x : Generator (2+2*h) → DD.Vmod, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma-x .sigma) -
          ∑ i ∈ Finset.range q, (t.τ^i)•x .tau, -(t.σ⁻¹•x (coreLetter h 2))] := by
    intro x
    change heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam (2+2*h) q W k)) x = _
    rw [hdiff]
    exact heisD1_mCompactFam_ramified_apply t (Vmod_exp2 DD) htame hwildAct htauFpf' hTodd x
  have hres : ResolvesAt (gammaFam (2+2*h) q W) w (WordLift DD.Vmod DD.C0) :=
    resolvesAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even DD.C0).1
      (fun p ↦ (WordLift.orderOf_dvd_two_mul (Vmod_exp2 DD)
        (fun c : DD.C0 ↦ Monoid.order_dvd_exponent c) p).trans ⟨2, by ring⟩) _
  have hr : ∀ k, FreeGroup.lift ⇑t (w k)=1 := fun k ↦
    Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2+2*h) q W) hres k
  let C := wPmPhaseComparison_of_normalForm rho hcompat hres (Vmod_exp2 DD) hwildTwo
    (wPmCompactPhaseNormal h)
    (wPcN_compactNormal_closed_ramified t w hrow)
    (wPcN_compactNormalForm_ramified t w hrow hwildAct htauFpf' hr)
    (scalarActionZmodTwo_triv _) (wPcMRamifiedHandlePhase DD.qbar h)
    (fun p c hc ↦ QZero_tameSplice_mCompact_ramified S hspecR hq0 hqe hend rho
      base hbase pi hpi hf hm hphi c hwild htauOdd htauFpf p hc)
  refine { phaseEquiv := C.phaseEquiv.trans (wPcMRamifiedHandleSwap DD.Vmod h)
           phase_eq := fun x ↦ ?_ }
  rw [C.phase_eq]
  exact wPcMRamifiedHandlePhase_eq_compactWall_swap DD.qbar h _

#print axioms QZero_tameSplice_mCompact_ramified
#print axioms phaseComparison_tameSplice_mCompact_ramified
end
end GQ2.Dyadic

