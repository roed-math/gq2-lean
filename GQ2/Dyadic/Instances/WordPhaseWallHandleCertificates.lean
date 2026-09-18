/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactCertificates

/-!
# Phase-cover and Hessian records with an arbitrary quadratic head diagonal

The diagonal `d0` is retained literally.  The head cross pairing and all handle
planes use `polar q`; neither nonsingularity nor the positive Gauss sign requires
`d0=q`.  This includes the twisted diagonals of full-offset normal forms.
-/

namespace GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates
noncomputable section
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh GQ2.Dyadic.LSquare
open Instances.WordPhase Instances.WordPhasePolarNormal Instances.WordPhaseAdditiveNormal
open Instances.WordPhaseCompactCertificates

variable {V : Type} [AddCommGroup V]

/-- The complete wall-head and handle phase, with its actual quadratic diagonal. -/
def wallHandlePhase (d0 q : V → ZMod 2) (h : ℕ) : CompactCoordinates V h → ZMod 2 :=
  fun p => plusFormD d0 q p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2

theorem wallHandlePhase_self (q : V → ZMod 2) (h : ℕ) :
    wallHandlePhase q q h = wPhCompactWallHandlePhase q h := rfl

private theorem polar_handle (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (x y : V × V) :
    polar (fun p : V × V => polar q p.1 p.2) x y =
      polar q x.1 y.2 + polar q x.2 y.1 := by
  change polar q (x.1+y.1) (x.2+y.2) + polar q x.1 x.2 + polar q y.1 y.2 = _
  rw [hq.polar_add_left, hq.polar_add_right, hq.polar_add_right, polar_comm q y.1 x.2]
  have key : ∀ a b c d : ZMod 2, (a+b+(c+d))+a+d=b+c := by decide
  exact key _ _ _ _

/-- The diagonal polar block is `B_d0`, while every cross and handle block is `B_q`. -/
theorem polar_wallHandlePhase (d0 q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wallHandlePhase d0 q h) x y =
      (polar d0 x.1.1 y.1.1 + polar q x.1.1 y.1.2 + polar q x.1.2 y.1.1) +
        ∑ j, (polar q (x.2 j).1 (y.2 j).2 + polar q (x.2 j).2 (y.2 j).1) := by
  have hsplit : polar (wallHandlePhase d0 q h) x y =
      polar (plusFormD d0 q) x.1 y.1 +
        ∑ j, polar (fun p : V × V => polar q p.1 p.2) (x.2 j) (y.2 j) := by
    simp only [polar, wallHandlePhase, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp only [Finset.sum_add_distrib]
    abel
  rw [hsplit, polar_plusFormD d0 q hq]
  simp only [polar_handle q hq, polar_comm q y.1.1 x.1.2]

/-- Quadraticity of the full form needs only quadraticity of the two input forms. -/
theorem isQuadratic_wallHandlePhase (d0 q : V → ZMod 2)
    (hd : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (h : ℕ) :
    IsQuadraticFp2 (wallHandlePhase d0 q h) where
  map_zero := by simp [wallHandlePhase, plusFormD, hd.map_zero, polar_zero_left q hq]
  polar_add_left x y z := by
    simp only [polar_wallHandlePhase d0 q hq, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      hd.polar_add_left, hq.polar_add_left]
    simp only [Finset.sum_add_distrib]
    abel
  polar_add_right x y z := by
    simp only [polar_wallHandlePhase d0 q hq, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      hd.polar_add_right, hq.polar_add_right]
    simp only [Finset.sum_add_distrib]
    abel

/-- All cross blocks remain nonsingular independently of the diagonal. -/
theorem nonsingular_wallHandlePhase (d0 q : V → ZMod 2)
    (hd : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (h : ℕ) :
    Nonsingular (wallHandlePhase d0 q h) := by
  classical
  intro x hx
  by_contra hn
  have H : ∀ y, polar (wallHandlePhase d0 q h) x y=0 := by
    intro y
    by_contra hy
    exact hn ⟨y, hy⟩
  have hz : ∀ v : V, (∀ w, polar q v w=0) → v=0 := by
    intro v hv
    by_contra hn
    obtain ⟨w, hw⟩ := hns v hn
    exact hw (hv w)
  have h0 : x.1.1=0 := hz _ fun w => by
    simpa [polar_wallHandlePhase d0 q hq, polar_zero_right d0 hd,
      polar_zero_right q hq] using H ((0,w),0)
  have h1 : x.1.2=0 := hz _ fun w => by
    simpa [polar_wallHandlePhase d0 q hq, h0, polar_zero_left d0 hd,
      polar_zero_left q hq, polar_zero_right q hq] using H ((w,0),0)
  have hu : ∀ j, (x.2 j).1=0 := fun j => hz _ fun w => by
    simpa [polar_wallHandlePhase d0 q hq, apply_ite, polar_zero_right d0 hd,
      polar_zero_right q hq] using
      H ((0,0), fun k => if k=j then (0,w) else (0,0))
  have hv : ∀ j, (x.2 j).2=0 := fun j => hz _ fun w => by
    simpa [polar_wallHandlePhase d0 q hq, apply_ite, polar_zero_right d0 hd,
      polar_zero_right q hq] using
      H ((0,0), fun k => if k=j then (w,0) else (0,0))
  apply hx
  exact Prod.ext (Prod.ext h0 h1) (funext fun j => Prod.ext (hu j) (hv j))

/-- The complete Gauss value is positive and independent of the quadratic diagonal. -/
theorem gaussSum_wallHandlePhase [Fintype V] (d0 q : V → ZMod 2)
    (hd : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (h : ℕ) :
    QuadraticFp2.gaussSum (wallHandlePhase d0 q h) = (Fintype.card V : ℤ)^(h+1) := by
  have hsplit : wallHandlePhase d0 q h = fun p : CompactCoordinates V h =>
      plusFormD d0 q p.1 + ∑ j, plusFormD (fun _ => 0) q (p.2 j) := by
    funext p
    simp [wallHandlePhase, plusFormD]
  rw [hsplit, gaussSum_prod_add (plusFormD d0 q)
      (fun w : Fin h → V × V => ∑ j, plusFormD (fun _ => 0) q (w j)),
    gaussSum_pi_sum,
    gaussSum_plusFormD hd hq hns,
    gaussSum_plusFormD (Certificates.isQuadraticFp2_zero (V := V)) hq hns, pow_succ']

/-- The original phase-cover record for a general diagonal at every handle count. -/
def wallHandlePhaseCover {C : Type} [Group C] [DistribMulAction C V] [Fintype V]
    (d0 q : V → ZMod 2) (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hd : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {d : ℕ} (hcard : Fintype.card V=2^d) (h : ℕ) :
    PhaseCoverCertificate dat d0 (wallHandlePhase d0 q h) (headDiagonal h) (headCross h) where
  baseDim := (h+1)*d
  baseSign := 1
  card_eq := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hcard,
      ← pow_add, ← pow_mul]
    congr 1
    ring
  gauss_eq := by
    rw [gaussSum_wallHandlePhase d0 q hd hq hns, hcard, one_mul]
    push_cast
    rw [← pow_mul, Nat.mul_comm d (h+1)]
  polar_id v w := by
    rw [polar_wallHandlePhase d0 q hq]
    simp only [headDiagonal, headCross, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      polar_zero_right d0 hd, polar_zero_left q hq,
      add_zero, zero_add, Finset.sum_const_zero]
    exact (hdat.f_polar v w).symm
  kappa_id v := by
    change wallHandlePhase d0 q h ((v,0),0)=d0 v
    simp [wallHandlePhase, plusFormD, polar_zero_right q hq]

section Source
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} (DD : DescData D)
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M))
  [DistribMulAction Gamma (ZMod 2)]
  (htriv : ∀ (g : Gamma) (a : ZMod 2), g•a=a)

/-- Original Hessian-record spelling with derived F2 structures and a literal diagonal. -/
abbrev SourceWallHessian [Fintype DD.Vmod] (d0 : DD.Vmod → ZMod 2) (h : ℕ) :=
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  HessianCertificate DD.dat d0 (QZeroBar DD rho htriv)
    (wallHandlePhase d0 DD.qbar h) (headDiagonal h) (headCross h)

/-- An actual additive phase comparison supplies every field of the original
Hessian record; the only diagonal hypothesis is its established quadraticity. -/
def sourceWallHessianOfComparison [Fintype DD.Vmod] {h : ℕ}
    (d0 : DD.Vmod → ZMod 2) (hd : IsQuadraticFp2 d0)
    (C : SourceWordPhaseComparison DD rho htriv (CompactCoordinates DD.Vmod h)
      (wallHandlePhase d0 DD.qbar h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y) :
    SourceWallHessian DD rho htriv d0 h := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  have hcard : Fintype.card DD.Vmod = 2 ^ Module.finrank (ZMod 2) DD.Vmod := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := DD.Vmod))
  exact {
    cov := fp2LinearEquiv (phaseComparisonAddEquiv C hadd)
    cov_eq := C.phase_eq
    hq := isQuadratic_wallHandlePhase d0 DD.qbar hd DD.hquad h
    hns := nonsingular_wallHandlePhase d0 DD.qbar hd DD.hquad DD.hns h
    affinePhase := wallHandlePhaseCover d0 DD.qbar DD.dat DD.hdat hd DD.hquad DD.hns hcard h }
end Source

#print axioms wallHandlePhase_self
#print axioms polar_wallHandlePhase
#print axioms isQuadratic_wallHandlePhase
#print axioms nonsingular_wallHandlePhase
#print axioms gaussSum_wallHandlePhase
#print axioms wallHandlePhaseCover
#print axioms sourceWallHessianOfComparison

end
end GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates
