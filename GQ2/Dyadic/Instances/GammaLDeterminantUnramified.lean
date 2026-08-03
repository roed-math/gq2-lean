/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLGraphNormalForm
import GQ2.Dyadic.Instances.GammaLUnramifiedPhase

/-!
# Closing the unramified determinant phase for the improved L presentation

The quotient-level source/word comparison for `L_sq` is now a theorem.  This file combines it
with the unramified Arf calculation.  The resulting phase package has no assumed comparison or
Gauss identity: its only inputs are the literal graph marking on the finite representation and
the usual simple-module cardinality data.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

local instance finiteSemiProdDet {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Finite V] [Finite C] :
    Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))

/-- The genuinely representation-theoretic input to the unramified source/word comparison.
The value of `sigma` is retained because it is the Wall-head operator; `tau` and every wild
letter are required literally trivial in the descended action target. -/
structure LUnramifiedGraphData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] where
  sigma : DD.C0
  sigma_eq : rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma) = sigma
  tau_eq : rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1
  wild_eq : ∀ i : Fin (2 * h + 1 + 1),
    rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1
  sigma_fixedPointFree : ∀ v : DD.Vmod, sigma • v = v → v = 0
  wildTwo : IsWildTwo (wildAlphabet (2 * h + 1))
    (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 * h + 1) q (lSqW h) i))

set_option maxHeartbeats 2400000 in
/-- The complete unramified phase model at one finite descended representation.  The source
comparison is the graph-normal-form theorem; the sign is Proposition 6.9 applied to the actual
finite action image.  In particular, neither a phase comparison nor an Arf/Gauss value is an
input. -/
theorem lSqUnramifiedPhaseModel_of_graphData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hsimple : IsSimpleModTwo (gamma h q : Type) DD.Vmod)
    (hq : Even q) (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LUnramifiedGraphData (DD := DD) rho) :
    letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 1)).gaussUnram m := by
  letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
  letI : Module (ZMod 2) DD.Vmod :=
    AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA2 v)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  let AI := FiniteActionImage h q DD.Vmod
  let t := finiteActionImageMarking h q DD.Vmod
  have htau : t.τ = 1 := by
    apply finiteActionImage_eq_one_of_smul_eq
    intro v
    change gammaGen (2 * h + 1) q (lSqW h) .tau • v = v
    rw [hcompat, G.tau_eq, one_smul]
  have hwild : ∀ i : Fin (2 * h + 1 + 1), t.x i = 1 := by
    intro i
    apply finiteActionImage_eq_one_of_smul_eq
    intro v
    change gammaGen (2 * h + 1) q (lSqW h) (.wild i) • v = v
    rw [hcompat, G.wild_eq i, one_smul]
  have hgen : ∀ x : AI, x ∈ Subgroup.zpowers t.σ := by
    have hle : Subgroup.closure
        (Set.range (finiteActionImageGenerators h q DD.Vmod)) ≤ Subgroup.zpowers t.σ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | sigma => exact Subgroup.mem_zpowers _
      | tau => change t.τ ∈ Subgroup.zpowers t.σ; rw [htau]; exact Subgroup.one_mem _
      | wild i =>
          change t.x i ∈ Subgroup.zpowers t.σ
          rw [hwild i]
          exact Subgroup.one_mem _
    rw [finiteActionImageGenerators_generate] at hle
    exact fun x ↦ hle (Subgroup.mem_top x)
  have hsimpleAI : IsSimpleModTwo AI DD.Vmod :=
    isSimpleModTwo_finiteActionImage hsimple
  have hfaith : ∀ a : AI, (∀ v : DD.Vmod, a • v = v) → a = 1 :=
    finiteActionImage_eq_one_of_smul_eq
  have hinv : ∀ (a : AI) (v : DD.Vmod), DD.qbar (a • v) = DD.qbar v := by
    intro a v
    obtain ⟨g, rfl⟩ :=
      (finiteActionHom (G := (gamma h q : Type)) (M := DD.Vmod)).toMonoidHom.rangeRestrict_surjective a
    change DD.qbar (g • v) = DD.qbar v
    rw [hcompat]
    exact factorSet_q_invariant DD.dat DD.hdat hA2 (rho0 DD rho g) v
  have hsigma2 : ∀ v : DD.Vmod, powOmega2 t.σ • v = v := by
    apply pow2_smul_trivial_of_stable hA2 hsimpleAI (powOmega2 t.σ)
      (isPGroup_zpowers_powOmega2 t.σ)
    intro a v hv
    have hc : powOmega2 t.σ * a = a * powOmega2 t.σ :=
      comm_of_cyclic t.σ hgen _ _
    calc
      powOmega2 t.σ • (a • v) = (powOmega2 t.σ * a) • v :=
        (mul_smul _ _ _).symm
      _ = (a * powOmega2 t.σ) • v := by rw [hc]
      _ = a • (powOmega2 t.σ • v) := mul_smul _ _ _
      _ = a • v := congrArg (a • ·) hv
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  have hN : N ≠ 0 := (Count.fourMulExponent_ne_zero_and_even L).1
  have htsigma : ∀ v : DD.Vmod, t.σ • v = G.sigma • v := by
    intro v
    change gammaGen (2 * h + 1) q (lSqW h) .sigma • v = G.sigma • v
    rw [hcompat, G.sigma_eq]
  have hpow : ∀ (k : ℕ) (v : DD.Vmod), t.σ ^ k • v = G.sigma ^ k • v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ, pow_succ, mul_smul, mul_smul, htsigma, ih]
  have hsExp : G.sigma ^ Monoid.exponent L = 1 := by
    let p : L := (0, G.sigma)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      G.sigma ^ Monoid.exponent L =
          sdSnd (p ^ Monoid.exponent L) := (map_pow sdSnd p _).symm
      _ = 1 := by rw [hp]; exact map_one sdSnd
  have hsN : G.sigma ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm], pow_mul, hsExp, one_pow]
  have htN : t.σ ^ N = 1 := by
    apply finiteActionImage_eq_one_of_smul_eq
    intro v
    rw [hpow, hsN, one_smul]
  have hord : orderOf t.σ ∣ N := orderOf_dvd_of_pow_eq_one htN
  have hresolved : t.σ ^ omega2Exp N = powOmega2 t.σ :=
    powOmega2_pow_eq t.σ hord hN
  have hsUniform : ∀ v : DD.Vmod, G.sigma ^ omega2Exp N • v = v := by
    intro v
    rw [← hpow, hresolved]
    exact hsigma2 v
  have hU : ∀ v : DD.Vmod,
      smulAddEquiv
          ((G.sigma ^ (omega2Exp N : ℤ))⁻¹) v = v := by
    intro v
    change (G.sigma ^ (omega2Exp N : ℤ))⁻¹ • v = v
    rw [zpow_natCast]
    have hv := hsUniform v
    calc
      (G.sigma ^ omega2Exp N)⁻¹ • v =
          (G.sigma ^ omega2Exp N)⁻¹ •
            ((G.sigma ^ omega2Exp N) • v) := congrArg ((G.sigma ^ omega2Exp N)⁻¹ • ·) hv.symm
      _ = v := inv_smul_smul _ _
  let Q : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) → ZMod 2 :=
    lSqWallHandlePhase DD.qbar
      (smulAddEquiv ((G.sigma ^ (omega2Exp N : ℤ))⁻¹)) h
  let C : SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) Q :=
    sourceWordPhaseComparison_of_lSqUnramified_uniform rho hcompat hA2 G.wildTwo hq
      G.sigma G.sigma_eq G.tau_eq G.wild_eq G.sigma_fixedPointFree
  refine ⟨DD.Vmod × (Fin h → DD.Vmod × DD.Vmod), inferInstance, Q, ⟨C⟩, ?_⟩
  exact (lSqWallHandlePhase_unramified_of_cyclic DD.hquad DD.hns hA2 m hm
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
    t.σ hgen hfaith hsimpleAI.2 hinv
    (smulAddEquiv ((G.sigma ^ (omega2Exp N : ℤ))⁻¹)) hU h).2

end

end GQ2.Dyadic.LSquare
