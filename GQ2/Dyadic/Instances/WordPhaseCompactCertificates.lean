/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseAdditiveNormal
import Mathlib.Algebra.Module.ZMod

/-!
# Original phase-cover and Hessian records for the common compact phase

The normal form retains its actual kappa diagonal, common polar edge pairing,
positive Gauss sign and every handle.  An additive source-to-word comparison
then supplies a linear change of variables for the original `HessianCertificate`.
These are records for the actual descended source phase, not a claim that a
changed word equals a previously frozen word.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactCertificates
noncomputable section
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic.LSquare
open Instances.WordPhase Instances.WordPhasePolarNormal Instances.WordPhaseAdditiveNormal

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- The actual diagonal head inclusion; all handles are zero. -/
def headDiagonal (h : ℕ) : V →+ CompactCoordinates V h where
  toFun v := ((v, 0), 0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-- The actual cross-head inclusion; all handles are zero. -/
def headCross (h : ℕ) : V →+ CompactCoordinates V h where
  toFun v := ((0, v), 0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-- The original phase-cover record at every handle count. Its diagonal is fixed
by the factor set, not reconstructed from the polar form. -/
def compactPhaseCover [Fintype V] {q : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
    (hcard : Fintype.card V = 2^d) (h : ℕ) :
    PhaseCoverCertificate dat (fun v => dat.f v v)
      (wPhCompactWallHandlePhase q h) (headDiagonal h) (headCross h) where
  baseDim := (h+1)*d
  baseSign := 1
  card_eq := by
    simp only [Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, hcard, ← pow_add, ← pow_mul]
    congr 1
    ring
  gauss_eq := by
    rw [one_mul]
    change QuadraticFp2.gaussSum (fun p : (V × V) × (Fin h → V × V) =>
      plusFormD q q p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2) = 2 ^ ((h+1)*d)
    rw [Certificates.nCompact_handle_form_gaussSum hq hns hcard h, Nat.mul_comm d (h+1)]
  polar_id v w := by
    rw [polar_compactPhase_blocks q hq]
    simp only [headDiagonal, headCross, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      polar_zero_left q hq, polar_zero_right q hq, add_zero, zero_add,
      Finset.sum_const_zero]
    exact (hdat.f_polar v w).symm
  kappa_id v := by
    change wPhCompactWallHandlePhase q h ((v, 0), 0) = dat.f v v
    simp only [wPhCompactWallHandlePhase, plusFormD_apply, Pi.zero_apply,
      Prod.fst_zero, Prod.snd_zero, polar_zero_left q hq,
      polar_zero_right q hq, Finset.sum_const_zero, add_zero]
    exact (hdat.f_diag v).symm

/-- Additive equivalences over F2 have a canonical linear interpretation, with
exactly the same forward and inverse functions. -/
def fp2LinearEquiv {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 2) M] [Module (ZMod 2) N] (e : M ≃+ N) : M ≃ₗ[ZMod 2] N where
  toAddEquiv := e
  map_smul' r x := addMonoidHom_map_zmod2_smul e.toAddMonoidHom r x

@[simp] theorem fp2LinearEquiv_apply {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 2) M] [Module (ZMod 2) N] (e : M ≃+ N) (x : M) :
    fp2LinearEquiv e x = e x := rfl

section Source
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} (DD : DescData D)
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M))
  [DistribMulAction Gamma (ZMod 2)]
  (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a=a)

/-- A local F2 module structure on the source quotient, derived from the actual
coefficient exponent; no new global module instance is installed. -/
abbrev sourceQuotientModule : Module (ZMod 2) (VCocycle DD rho ⧸ vCobRange DD rho) :=
  AddCommGroup.zmodModule fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      rw [← QuotientAddGroup.mk_nsmul]
      have hc : (2 : ℕ) • c=0 := by
        rw [two_nsmul]
        apply VCocycle.ext
        funext g
        exact Vmod_exp2 DD (c.c g)
      rw [hc]
      rfl

/-- The original Hessian record for the actual descended source phase. All
normal-form facts are supplied by the common phase; the word-specific input is
the existing additive source-to-word comparison, including its quadratic identity. -/
def sourceCompactHessianCertificate [Fintype DD.Vmod] {h d : ℕ}
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y)
    (hcard : Fintype.card DD.Vmod=2^d) :
    letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
      (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
    letI := sourceQuotientModule DD rho
    HessianCertificate DD.dat (fun v => DD.dat.f v v) (QZeroBar DD rho htriv)
      (wPhCompactWallHandlePhase DD.qbar h) (headDiagonal h) (headCross h) := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  exact {
    cov := fp2LinearEquiv (phaseComparisonAddEquiv C hadd)
    cov_eq := C.phase_eq
    hq := isQuadratic_compactPhase DD.qbar DD.hquad h
    hns := nonsingular_compactPhase DD.qbar DD.hquad DD.hns h
    affinePhase := compactPhaseCover DD.dat DD.hdat DD.hquad DD.hns hcard h }

/-- A convenient spelling of the original record with local, derived F2 module
structures.  This is an abbreviation, not a replacement certificate structure. -/
abbrev SourceCompactHessian [Fintype DD.Vmod] (h : ℕ) :=
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  HessianCertificate DD.dat (fun v => DD.dat.f v v) (QZeroBar DD rho htriv)
    (wPhCompactWallHandlePhase DD.qbar h) (headDiagonal h) (headCross h)

/-- No cardinality premise is added to a word-specific additive comparison:
the finite coefficient module supplies its own F2 dimension. -/
def sourceCompactHessianOfComparison [Fintype DD.Vmod] {h : ℕ}
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y) :
    SourceCompactHessian DD rho htriv h := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  have hcard : Fintype.card DD.Vmod = 2 ^ Module.finrank (ZMod 2) DD.Vmod := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := DD.Vmod))
  exact sourceCompactHessianCertificate DD rho htriv C hadd hcard

/-- The Hessian change of variables is the same map as the actual phase
comparison, not a newly chosen isometry. -/
theorem sourceCompactHessianOfComparison_cov_apply [Fintype DD.Vmod] {h : ℕ}
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wPhCompactWallHandlePhase DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y)
    (x : VCocycle DD rho ⧸ vCobRange DD rho) :
    letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
      (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
    letI := sourceQuotientModule DD rho
    (sourceCompactHessianOfComparison DD rho htriv C hadd).cov x = C.phaseEquiv x := rfl
end Source

#print axioms compactPhaseCover
#print axioms fp2LinearEquiv
#print axioms sourceQuotientModule
#print axioms sourceCompactHessianCertificate
#print axioms sourceCompactHessianOfComparison
#print axioms sourceCompactHessianOfComparison_cov_apply

end
end GQ2.Dyadic.Instances.WordPhaseCompactCertificates
