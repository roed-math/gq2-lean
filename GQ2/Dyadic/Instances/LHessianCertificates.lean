/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseOddCertificates
import GQ2.Dyadic.Instances.LPhaseAdditiveNormal

/-!
# Original Hessian records for the actual L source in both branches

The projected head operator and the actual source-coordinate map are retained.
The signed head Gauss value is obtained from the existing completed branch
model by exact Gauss reindexing, not from its polar form. In particular the
unramified record has negative sign at every handle rank.
-/

namespace GQ2.Dyadic.Instances.LHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.FoxH GQ2.QuadraticFp2
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open Instances.WordPhaseOddCertificates Instances.LPhaseAdditiveNormal

section Gauss
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
  [DistribMulAction Gamma (ZMod 2)]
  {htriv : ∀ (g : Gamma) (a : ZMod 2), g•a=a}

/-- The full phase, not only its polar form, transports the signed Gauss value. -/
theorem gauss_eq_of_same_source
    {W W' : Type} [Fintype W] [Fintype W'] {Q : W → ZMod 2} {Q' : W' → ZMod 2}
    (C : SourceWordPhaseComparison DD rho htriv W Q)
    (C' : SourceWordPhaseComparison DD rho htriv W' Q') :
    QuadraticFp2.gaussSum Q = QuadraticFp2.gaussSum Q' := by
  have H : Q = fun x => Q' ((C.phaseEquiv.symm.trans C'.phaseEquiv) x) := by
    funext x
    exact ((C.phase_eq (C.phaseEquiv.symm x)).trans
      (congrArg Q (C.phaseEquiv.apply_symm_apply x))).symm.trans
        (C'.phase_eq (C.phaseEquiv.symm x))
  rw [H, gaussSum_comp_equiv]
end Gauss

theorem headGauss_of_full {V : Type} [AddCommGroup V] [Fintype V]
    (Q : V → ZMod 2) (U : V ≃+ V) (hQ : IsQuadraticFp2 Q)
    (h2 : ∀ v : V, v+v=0) (hns : Nonsingular Q) {m h : ℕ}
    (hcard : Fintype.card V=2^(2*m)) (epsilon : ℤ)
    (H : QuadraticFp2.gaussSum (lSqWallHandlePhase Q U h)=epsilon*2^(m*(2*h+1))) :
    QuadraticFp2.gaussSum (qDouble Q U)=epsilon*2^m := by
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => (two_nsmul v).trans (h2 v))
  change QuadraticFp2.gaussSum (fun p : V × (Fin h → V×V) =>
    qDouble Q U p.1 + ∑ j, polar Q (p.2 j).1 (p.2 j).2)=_ at H
  rw [lSq_handle_form_gaussSum hQ hns hcard (qDouble Q U) h,
    show m*(2*h+1)=m+2*m*h by ring, pow_add, ← mul_assoc] at H
  exact mul_right_cancel₀ (by positivity : (2 : ℤ)^(2*m*h)≠0) H

section Head
variable {h q : ℕ}
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

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : Fintype DD.Vmod := Fintype.ofFinite _
local instance : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
  inferInstanceAs (Finite (DD.Vmod × DD.C0))
local instance : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The same projected graph operator used by the actual L phase comparison. -/
def headOperator : DD.Vmod ≃+ DD.Vmod :=
  smulAddEquiv ((pi (rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .sigma)) ^
    (omega2Exp (4*Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))⁻¹)

include hbase in
omit [DiscreteTopology Bg] [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
  [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((gamma h q : Type)) DD.Vmod]
  [ContinuousSMul ((gamma h q : Type)) DD.Vmod] in
theorem headOperator_isometry (v : DD.Vmod) :
    DD.qbar (headOperator rho pi v)=DD.qbar v :=
  factorSet_q_invariant base hbase (Vmod_exp2 DD) _ v

omit [DiscreteTopology Bg] [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
  [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [DistribMulAction ((gamma h q : Type)) DD.Vmod]
  [ContinuousSMul ((gamma h q : Type)) DD.Vmod] in
/-- The two-primary period is proved before taking the head projection; no
faithfulness or finite-head hypothesis is needed here. -/
theorem headOperator_twoPower : ∃ n, (⇑(headOperator rho pi))^[2^n]=id := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4*Monoid.exponent L
  let c := rho0 DD rho (gammaGen (2*h+1) q (lSqW h) .sigma)
  have hcExp : c ^ Monoid.exponent L=1 := by
    let p : L := (0,c)
    have hp : p ^ Monoid.exponent L=1 := Monoid.pow_exponent_eq_one p
    have H := congrArg (sdSnd : L →* DD.C0) hp
    simpa only [map_pow, map_one, show sdSnd p=c from rfl] using H
  have hcN : c ^ N=1 := by
    rw [show N=Monoid.exponent L*4 by simp [N,Nat.mul_comm], pow_mul, hcExp, one_pow]
  have hr : c ^ omega2Exp N=powOmega2 c :=
    powOmega2_pow_eq c (orderOf_dvd_of_pow_eq_one hcN) (fourMulExponent_ne_zero_and_even L).1
  have hp : ((c ^ omega2Exp N)⁻¹) ^ (2^(orderOf c).factorization 2)=1 := by
    rw [hr, inv_pow, orderOf_dvd_iff_pow_eq_one.mp (orderOf_powOmega2_dvd_two_pow c), inv_one]
  refine ⟨(orderOf c).factorization 2, ?_⟩
  funext v
  change (((pi c ^ (omega2Exp N : ℤ))⁻¹ • ·)^[2^(orderOf c).factorization 2]) v=v
  rw [zpow_natCast, smul_iterate_apply, ← map_pow, ← map_inv, ← map_pow, hp, map_one, one_smul]

/-- Actual-source unramified Hessian record. The completed phase model supplies
the negative sign; no Arf, phase, or normal-form premise has been added. -/
def unramifiedHessian
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1≤m) (hcard : Nat.card DD.Vmod=2^(2*m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    SourceOddHessian DD rho (scalarActionZmodTwo_triv _) (headOperator rho pi)
      (headOperator_twoPower rho pi) h := by
  let C := sourceWordPhaseComparison_of_lSqUnramifiedHead rho base hbase pi hpi hf hm
    hcompat (Vmod_exp2 DD) G.wildTwo hqe G.tau_head G.wild_head G.sigma_fixedPointFree
  have hwhole : QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)=
      (-1 : ℤ)*2^(m*(2*h+1)) := by
    obtain ⟨W, instW, Q, ⟨C'⟩, hG⟩ := lSqUnramifiedPhaseModel_of_headData
      rho base hbase pi hpi hf hm hcompat (Vmod_exp2 DD) hsimple hqe m hm1 hcard G
    letI := instW
    dsimp only [headOperator]
    rw [gauss_eq_of_same_source C C', hG]
    change (-1 : ℤ)^(2*h+1)*2^((2*h+1)*m)=(-1)*2^(m*(2*h+1))
    rw [Odd.neg_one_pow (odd_two_mul_add_one h), Nat.mul_comm (2*h+1) m]
  have hc : Fintype.card DD.Vmod=2^(2*m) := by simpa only [Nat.card_eq_fintype_card] using hcard
  exact sourceOddHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (headOperator rho pi) (headOperator_isometry rho base hbase pi)
    (headOperator_twoPower rho pi) hc (-1)
    (headGauss_of_full DD.qbar _ DD.hquad (Vmod_exp2 DD) DD.hns hc (-1) hwhole) C
    (unramifiedHeadComparison_add rho base hbase pi hpi hf hm hcompat (Vmod_exp2 DD)
      G.wildTwo hqe G.wild_head G.tau_head G.sigma_fixedPointFree)

/-- Actual-source ramified Hessian record. It retains the nontrivial graph
operator and the existing presentation-independent source Arf datum. -/
def ramifiedHessian [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod=2^(2*m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    SourceOddHessian DD rho (scalarActionZmodTwo_triv _) (headOperator rho pi)
      (headOperator_twoPower rho pi) h := by
  let C := ramifiedHeadComparison rho base hbase pi hpi hf hm hcompat hqe G.wild_head
    G.tau_fixedPointFree G.tau_oddPart_fixed
  have hwhole : QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar (headOperator rho pi) h)=
      (1 : ℤ)*2^(m*(2*h+1)) := by
    obtain ⟨W, instW, Q, ⟨C'⟩, hG⟩ := lSqRamifiedPhaseModel_of_headData
      rho base hbase pi hpi hf hm hcompat (Vmod_exp2 DD) hqe m hcard G S
    letI := instW
    dsimp only [headOperator]
    rw [gauss_eq_of_same_source C C', hG]
    change (2 : ℤ)^((2*h+1)*m)=1*2^(m*(2*h+1))
    rw [one_mul, Nat.mul_comm (2*h+1) m]
  have hc : Fintype.card DD.Vmod=2^(2*m) := by simpa only [Nat.card_eq_fintype_card] using hcard
  exact sourceOddHessianOfComparison DD rho (scalarActionZmodTwo_triv _)
    (headOperator rho pi) (headOperator_isometry rho base hbase pi)
    (headOperator_twoPower rho pi) hc 1
    (headGauss_of_full DD.qbar _ DD.hquad (Vmod_exp2 DD) DD.hns hc 1 hwhole) C
    (ramifiedHeadComparison_add rho base hbase pi hpi hf hm hcompat hqe G.wild_head
      G.tau_fixedPointFree G.tau_oddPart_fixed)

local instance : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
  (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
local instance : Module (ZMod 2) (VCocycle DD rho ⧸ vCobRange DD rho) :=
  Instances.WordPhaseCompactCertificates.sourceQuotientModule DD rho

/-- The negative unramified sign is a literal field of the original record. -/
theorem unramifiedHessian_baseSign
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hqe : Even q) (m : ℕ) (hm1 : 1≤m) (hcard : Nat.card DD.Vmod=2^(2*m))
    (G : LUnramifiedHeadData (DD := DD) rho pi) :
    (unramifiedHessian rho base hbase pi hpi hf hm hcompat hsimple hqe m hm1 hcard G).affinePhase.baseSign = -1 := rfl

/-- The ramified sign is positive without changing the literal graph operator. -/
theorem ramifiedHessian_baseSign [Finite Cbar]
    (hqe : Even q) (m : ℕ) (hcard : Nat.card DD.Vmod=2^(2*m))
    (G : LRamifiedHeadData (DD := DD) rho pi)
    (S : LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    (ramifiedHessian rho base hbase pi hpi hf hm hcompat hqe m hcard G S).affinePhase.baseSign = 1 := rfl
end Head

#print axioms gauss_eq_of_same_source
#print axioms headGauss_of_full
#print axioms headOperator_twoPower
#print axioms unramifiedHessian
#print axioms ramifiedHessian
#print axioms unramifiedHessian_baseSign
#print axioms ramifiedHessian_baseSign

end
end GQ2.Dyadic.Instances.LHessianCertificates
