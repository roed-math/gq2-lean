/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseAdditiveNormal
import GQ2.Dyadic.Instances.GammaLDeterminantRamifiedData
import GQ2.Dyadic.Instances.GammaLDeterminantUnramifiedData

/-! # Additivity of the actual improved-L phase coordinates -/

namespace GQ2.Dyadic.Instances.LPhaseAdditiveNormal
noncomputable section
open GQ2 GQ2.SectionEight GQ2.FoxH
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open Instances.WordPhaseAdditiveNormal

theorem ramifiedNormal_add {A : Type} [AddCommGroup A] (h : ℕ)
    (p r : A × (Fin h × Fin 2 → A)) :
    lSqRamifiedNormal h (p+r).1 (p+r).2 =
      lSqRamifiedNormal h p.1 p.2 + lSqRamifiedNormal h r.1 r.2 := by
  unfold lSqRamifiedNormal
  rw [← map_add]
  congr 1
  apply Prod.ext
  · funext g
    cases g with
    | sigma => exact (add_zero (0 : A)).symm
    | tau => exact (add_zero (0 : A)).symm
    | wild i => fin_cases i <;> first | rfl | exact (add_zero (0 : A)).symm
  · rfl

theorem phaseNormal_add {A : Type} [AddCommGroup A] (h : ℕ)
    (p r : A × (Fin h → A×A)) :
    lSqPhaseNormal h (p+r) = lSqPhaseNormal h p + lSqPhaseNormal h r := by
  unfold lSqPhaseNormal
  have H := ramifiedNormal_add h
    (p.1,fun jk => (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2)
    (r.1,fun jk => (finTwoProdAddEquiv.symm (r.2 jk.1)) jk.2)
  convert H using 1
  congr 1
  funext jk
  simp only [Prod.snd_add, Pi.add_apply, map_add]

theorem stokesH1NormalEquiv_add
    {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1]
    [AddCommGroup K2] [AddCommGroup P]
    (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
    (hadd : ∀ p r, normal (p+r)=normal p+normal r)
    (hmem : ∀ p, d1 (normal p)=0)
    (hnf : ∀ x, d1 x=0 → ∃! p, x-normal p ∈ Set.range d0)
    (x y : StokesH1 d0 d1) :
    stokesH1NormalEquiv d0 d1 normal hmem hnf (x+y) =
      stokesH1NormalEquiv d0 d1 normal hmem hnf x +
        stokesH1NormalEquiv d0 d1 normal hmem hnf y :=
  stokesNormalEquiv_add d0 d1 normal hadd hmem hnf x y

theorem ramifiedWordH1Equiv_add
    {h q : ℕ} {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2*h+1) C) (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2*h+1+1)) (a : A), t.x i • a=a)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (hL : PWord.evalZ ⇑t (fun _ ↦ (omega2Exp (4*Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4*Monoid.exponent C) : ℤ)) (lSqW h)=1)
    (x y : WordH1 ⇑t (lSqFam h q (omega2Exp (4*Monoid.exponent C))) A) :
    lSqRamifiedWordH1Equiv t hA2 ht hwild hfpf hodd hL (x+y) =
      lSqRamifiedWordH1Equiv t hA2 ht hwild hfpf hodd hL x +
        lSqRamifiedWordH1Equiv t hA2 ht hwild hfpf hodd hL y := by
  unfold lSqRamifiedWordH1Equiv
  simp only [Equiv.trans_apply]
  rw [stokesH1NormalEquiv_add _ _ (fun p : A × (Fin h × Fin 2 → A) =>
    lSqRamifiedNormal h p.1 p.2) (ramifiedNormal_add h)]
  apply Prod.ext
  · rfl
  · exact handlePairsAddEquiv.map_add _ _

section Head
variable {h q e : ℕ}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
  [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((gamma h q : Type)) DD.Vmod]
  [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
  {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
  (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
  (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=pi cc•v)
  (hf : ∀ a b : DD.Vmod, DD.dat.f a b=base.f a b)
  (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v=base.m (pi cc) v)
  (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod), g•v=rho0 DD rho g•v)
  (hA2 : ∀ v : DD.Vmod, v+v=0)
  (hwildTwo : IsWildTwo (wildAlphabet (2*h+1))
    (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2*h+1) q (lSqW h) i)))
  (hqe : Even q)
  (hwildHead : ∀ i : Fin (2*h+1+1), pi (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) (.wild i)))=1)

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : Fintype DD.Vmod := Fintype.ofFinite _
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

set_option backward.isDefEq.respectTransparency false in
theorem ramifiedActionH1Equiv_add
    (hwildAct : ∀ (i : Fin (2*h+1+1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2*h+1) q (lSqW h) (.wild i))•v=v)
    (hfpf : ∀ v : DD.Vmod, rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau)•v=v → v=0)
    (hodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau))•v=v)
    (x y : H1 (gamma h q : Type) DD.Vmod) :
    lSqRamifiedActionSourceH1Equiv rho hcompat hwildAct hfpf hodd (x+y) =
      lSqRamifiedActionSourceH1Equiv rho hcompat hwildAct hfpf hodd x +
        lSqRamifiedActionSourceH1Equiv rho hcompat hwildAct hfpf hodd y := by
  letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
    inferInstanceAs (Finite (DD.Vmod × DD.C0))
  letI : DistribMulAction (SectionSix.SemiProd DD.C0 DD.Vmod) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (sdSnd : SectionSix.SemiProd DD.C0 DD.Vmod →* DD.C0)
  unfold lSqRamifiedActionSourceH1Equiv lSqRamifiedSourceH1Equiv
  simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, map_add]
  apply ramifiedWordH1Equiv_add

theorem headNormalComparison_add
    (hres : ResolvesAt (gammaFam (2*h+1) q (lSqW h)) (lSqFam h q e) (WordLift DD.Vmod DD.C0))
    (hmem : ∀ p : DD.Vmod × (Fin h → DD.Vmod×DD.Vmod),
      heisD1 (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2*h+1) q (lSqW h) i))
        (lSqFam h q e) (lSqPhaseNormal h p)=0)
    (hnf : ∀ x, heisD1 (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2*h+1) q (lSqW h) i))
      (lSqFam h q e) x=0 → ∃! p : DD.Vmod × (Fin h → DD.Vmod×DD.Vmod),
      x-lSqPhaseNormal h p ∈ Set.range (heisD0 (A := DD.Vmod)
        (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2*h+1) q (lSqW h) i))))
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    (sourceWordPhaseComparison_of_lSqHeadNormalForm rho base hbase pi hpi hf hm
      hcompat hres hA2 hwildTwo hqe hwildHead hmem hnf).phaseEquiv (x+y) =
    (sourceWordPhaseComparison_of_lSqHeadNormalForm rho base hbase pi hpi hf hm
      hcompat hres hA2 hwildTwo hqe hwildHead hmem hnf).phaseEquiv x +
    (sourceWordPhaseComparison_of_lSqHeadNormalForm rho base hbase pi hpi hf hm
      hcompat hres hA2 hwildTwo hqe hwildHead hmem hnf).phaseEquiv y := by
  change stokesNormalEquiv _ _ (lSqPhaseNormal h) hmem hnf
      (lSourceH1Equiv (Count.rho0Continuous DD rho) hcompat hA2 hres
        (h1OfVQuot hcompat (x+y))) = _
  rw [h1OfVQuot_add, map_add, stokesNormalEquiv_add _ _ _ (phaseNormal_add h)]
  rfl

theorem unramifiedHeadComparison_add
    (htau : pi (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau))=1)
    (hsfpf : ∀ v : DD.Vmod,
      pi (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .sigma))•v=v → v=0)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    (sourceWordPhaseComparison_of_lSqUnramifiedHead rho base hbase pi hpi hf hm
      hcompat hA2 hwildTwo hqe htau hwildHead hsfpf).phaseEquiv (x+y) =
    (sourceWordPhaseComparison_of_lSqUnramifiedHead rho base hbase pi hpi hf hm
      hcompat hA2 hwildTwo hqe htau hwildHead hsfpf).phaseEquiv x +
    (sourceWordPhaseComparison_of_lSqUnramifiedHead rho base hbase pi hpi hf hm
      hcompat hA2 hwildTwo hqe htau hwildHead hsfpf).phaseEquiv y := by
  unfold sourceWordPhaseComparison_of_lSqUnramifiedHead
  apply headNormalComparison_add

/-- The actual projected ramified comparison, now kept under a stable name. -/
def ramifiedHeadComparison
    (hfpf : ∀ v : DD.Vmod, rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau)•v=v → v=0)
    (hodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau))•v=v) :=
  sourceWordPhaseComparison_of_lRamifiedPointwise (scalarActionZmodTwo_triv _)
    hcompat DD.qbar
    (smulAddEquiv ((pi (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .sigma)) ^
      (omega2Exp (4*Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))⁻¹)) h
    (lSqRamifiedActionSourceH1Equiv rho hcompat
      (fun i v => by rw [hpi, hwildHead, one_smul]) hfpf hodd)
    (lRamifiedPointwisePhaseIdentity_of_headNormalForm rho DD.hdat base hbase pi hpi hf hm
      hqe hcompat hwildHead (fun i v => by rw [hpi, hwildHead, one_smul]) hfpf hodd)

theorem ramifiedHeadComparison_add
    (hfpf : ∀ v : DD.Vmod, rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau)•v=v → v=0)
    (hodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .tau))•v=v)
    (x y : VCocycle DD rho ⧸ vCobRange DD rho) :
    (ramifiedHeadComparison rho base hbase pi hpi hf hm hcompat hqe hwildHead hfpf hodd).phaseEquiv (x+y) =
    (ramifiedHeadComparison rho base hbase pi hpi hf hm hcompat hqe hwildHead hfpf hodd).phaseEquiv x +
    (ramifiedHeadComparison rho base hbase pi hpi hf hm hcompat hqe hwildHead hfpf hodd).phaseEquiv y := by
  change lSqRamifiedActionSourceH1Equiv rho hcompat
    (fun i v => by rw [hpi, hwildHead, one_smul]) hfpf hodd (h1OfVQuot hcompat (x+y)) = _
  rw [h1OfVQuot_add, ramifiedActionH1Equiv_add]
  rfl
end Head

#print axioms ramifiedNormal_add
#print axioms phaseNormal_add
#print axioms stokesH1NormalEquiv_add
#print axioms ramifiedWordH1Equiv_add
#print axioms headNormalComparison_add
#print axioms unramifiedHeadComparison_add
#print axioms ramifiedActionH1Equiv_add
#print axioms ramifiedHeadComparison
#print axioms ramifiedHeadComparison_add

end
end GQ2.Dyadic.Instances.LPhaseAdditiveNormal
