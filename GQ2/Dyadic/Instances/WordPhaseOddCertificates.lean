/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactCertificates
import GQ2.Dyadic.Instances.GammaLRamifiedPhase

/-!
# Odd Wall-head phase records, retaining the actual sign and graph operator

The head is one copy of V, not an even wall-head pair. Its polar operator is
literally `1+U+U⁻¹`; the two edge maps use the identity and its inverse. The
diagonal is the full Wall double. No positive Gauss sign is assumed: the sign
parameter is supplied by the actual head Gauss theorem.
-/

namespace GQ2.Dyadic.Instances.WordPhaseOddCertificates
noncomputable section
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh GQ2.Dyadic.LSquare
open Instances.WordPhaseCompactCertificates Instances.WordPhaseAdditiveNormal

variable {V : Type} [AddCommGroup V]

/-- The actual polar operator of the Wall double. -/
def wallPolarHom (U : V ≃+ V) : V →+ V :=
  AddMonoidHom.id V + U.toAddMonoidHom + U.symm.toAddMonoidHom

@[simp] theorem wallPolarHom_apply (U : V ≃+ V) (v : V) :
    wallPolarHom U v = v + U v + U.symm v := rfl

/-- The displayed polar operator is invertible for a two-power-order action.
The inverse is the inverse of this literal map, not a newly chosen isometry. -/
def wallPolarEquiv [Finite V] (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) : V ≃+ V :=
  AddEquiv.ofBijective (wallPolarHom U) (by
    have hinj : Function.Injective (wallPolarHom U) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply onePlusUUsq_injective U h2 hU2 v
      have H := congrArg (⇑U) hv
      simp only [wallPolarHom_apply, map_add, map_zero, AddEquiv.apply_symm_apply] at H
      rw [← H]
      abel
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

@[simp] theorem wallPolarEquiv_apply [Finite V] (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (v : V) :
    wallPolarEquiv U h2 hU2 v = v+U v+U.symm v := rfl

/-- The diagonal inclusion into the single Wall head. -/
def oddHead (h : ℕ) : V →+ (V × (Fin h → V × V)) where
  toFun v := (v,0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-- The second edge map corrects by the actual head polar inverse. -/
def oddCross (h : ℕ) (J : V ≃+ V) : V →+ (V × (Fin h → V × V)) :=
  (oddHead h).comp J.symm.toAddMonoidHom

private theorem polar_handle (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (x y : V×V) :
    polar (fun p : V×V => polar q p.1 p.2) x y =
      polar q x.1 y.2 + polar q x.2 y.1 := by
  change polar q (x.1+y.1) (x.2+y.2) + polar q x.1 x.2 + polar q y.1 y.2 = _
  rw [hq.polar_add_left, hq.polar_add_right, hq.polar_add_right, polar_comm q y.1 x.2]
  have key : ∀ a b c d : ZMod 2, (a+b+(c+d))+a+d=b+c := by decide
  exact key _ _ _ _

theorem polar_oddPhase (q : V → ZMod 2) (U : V ≃+ V)
    (hq : IsQuadraticFp2 q) (hUq : ∀ v, q (U v)=q v) (h : ℕ)
    (x y : V × (Fin h → V×V)) :
    polar (lSqWallHandlePhase q U h) x y =
      polar q x.1 (wallPolarHom U y.1) +
        ∑ j, (polar q (x.2 j).1 (y.2 j).2 + polar q (x.2 j).2 (y.2 j).1) := by
  have hs : polar (lSqWallHandlePhase q U h) x y =
      polar (qDouble q U) x.1 y.1 +
        ∑ j, polar (fun p : V×V => polar q p.1 p.2) (x.2 j) (y.2 j) := by
    simp only [polar, lSqWallHandlePhase, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp only [Finset.sum_add_distrib]
    abel
  rw [hs, polar_qDouble_eq q U hq hUq]
  simp only [wallPolarHom_apply, polar_handle q hq]

theorem isQuadratic_oddPhase (q : V → ZMod 2) (U : V ≃+ V)
    (hq : IsQuadraticFp2 q) (_h2 : ∀ v : V, v+v=0)
    (hUq : ∀ v, q (U v)=q v) (h : ℕ) : IsQuadraticFp2 (lSqWallHandlePhase q U h) where
  map_zero := by simp [lSqWallHandlePhase, qDouble, hq.map_zero, polar_zero_left q hq]
  polar_add_left x y z := by
    simp only [polar_oddPhase q U hq hUq, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, hq.polar_add_left, Finset.sum_add_distrib]
    abel
  polar_add_right x y z := by
    simp only [polar_oddPhase q U hq hUq, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, map_add, hq.polar_add_right, Finset.sum_add_distrib]
    abel

theorem nonsingular_oddPhase [Finite V] (q : V → ZMod 2) (U : V ≃+ V)
    (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v+v=0) (hns : Nonsingular q)
    (hUq : ∀ v, q (U v)=q v) (hU2 : ∃ n, (⇑U)^[2^n]=id) (h : ℕ) :
    Nonsingular (lSqWallHandlePhase q U h) := by
  classical
  intro x hx
  by_contra hn
  have H : ∀ y, polar (lSqWallHandlePhase q U h) x y=0 := by
    intro y
    by_contra hy
    exact hn ⟨y,hy⟩
  have hz : ∀ v : V, (∀ w, polar q v w=0) → v=0 := by
    intro v hv
    by_contra hn
    obtain ⟨w,hw⟩ := hns v hn
    exact hw (hv w)
  have h0 : x.1=0 := hz _ fun w => by
    have H0 := H ((wallPolarEquiv U h2 hU2).symm w,0)
    simpa only [polar_oddPhase q U hq hUq, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
      polar_zero_right q hq, add_zero, Finset.sum_const_zero,
      show wallPolarHom U ((wallPolarEquiv U h2 hU2).symm w)=w from
        (wallPolarEquiv U h2 hU2).apply_symm_apply w] using H0
  have hu : ∀ j, (x.2 j).1=0 := fun j => hz _ fun w => by
    simpa [polar_oddPhase q U hq hUq, apply_ite, polar_zero_right q hq] using
      H (0, fun k => if k=j then (0,w) else (0,0))
  have hv : ∀ j, (x.2 j).2=0 := fun j => hz _ fun w => by
    simpa [polar_oddPhase q U hq hUq, apply_ite, polar_zero_right q hq] using
      H (0, fun k => if k=j then (w,0) else (0,0))
  exact hx (Prod.ext h0 (funext fun j => Prod.ext (hu j) (hv j)))

/-- Original odd-head record with the actual signed head Gauss value. -/
def oddPhaseCover {C : Type} [Group C] [DistribMulAction C V] [Fintype V]
    (q : V → ZMod 2) (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (U : V ≃+ V) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v+v=0)
    (hns : Nonsingular q) (hUq : ∀ v, q (U v)=q v)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) {m : ℕ} (hcard : Fintype.card V=2^(2*m))
    (epsilon : ℤ) (hgauss : QuadraticFp2.gaussSum (qDouble q U)=epsilon*2^m) (h : ℕ) :
    PhaseCoverCertificate dat (qDouble q U) (lSqWallHandlePhase q U h)
      (oddHead h) (oddCross h (wallPolarEquiv U h2 hU2)) where
  baseDim := m*(2*h+1)
  baseSign := epsilon
  card_eq := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hcard,
      ← pow_add, ← pow_mul]
    congr 1
    ring
  gauss_eq := by
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule
      (fun v => (two_nsmul v).trans (h2 v))
    change QuadraticFp2.gaussSum (fun p : V × (Fin h → V×V) =>
      qDouble q U p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2)=_
    rw [Certificates.LSqStokes.lSq_handle_form_gaussSum hq hns hcard (qDouble q U) h, hgauss]
    rw [show m*(2*h+1)=m+2*m*h by ring, pow_add]
    ring
  polar_id v w := by
    rw [polar_oddPhase q U hq hUq]
    dsimp [oddHead, oddCross]
    change polar q v (wallPolarHom U ((wallPolarEquiv U h2 hU2).symm w))+
      ∑ _j : Fin h, (polar q 0 0 + polar q 0 0)=_
    rw [show wallPolarHom U ((wallPolarEquiv U h2 hU2).symm w)=w from
      (wallPolarEquiv U h2 hU2).apply_symm_apply w]
    simpa [polar_zero_left q hq] using (hdat.f_polar v w).symm
  kappa_id v := by
    dsimp [oddHead, lSqWallHandlePhase]
    change qDouble q U v + ∑ _j : Fin h, polar q 0 0=qDouble q U v
    simp [polar_zero_left q hq]

/-- The negative sign in the unramified Arf-one branch is retained literally. -/
def oddPhaseCover_unramified {C : Type} [Group C] [DistribMulAction C V] [Fintype V]
    (q : V → ZMod 2) (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (U : V ≃+ V) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v+v=0)
    (hns : Nonsingular q) (hU : ∀ v, U v=v)
    {m : ℕ} (hcard : Fintype.card V=2^(2*m)) (harf : arf q=1) (h : ℕ) :=
  oddPhaseCover q dat hdat U hq h2 hns (fun v => congrArg q (hU v))
    (by refine ⟨0, ?_⟩; funext v; simpa using hU v) hcard (-1)
    (by rw [qDouble_eq_self_of_fixed q U hq h2 hU,
        gaussSum_eq_neg_pow_of_arf_one q hq hns hcard harf, neg_one_mul]) h

section Source
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} (DD : DescData D)
  {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
  (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M))
  [DistribMulAction Gamma (ZMod 2)]
  (htriv : ∀ (g : Gamma) (a : ZMod 2), g•a=a)

/-- The original Hessian-record type for an actual odd-head source phase. -/
abbrev SourceOddHessian [Fintype DD.Vmod] (U : DD.Vmod ≃+ DD.Vmod)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (h : ℕ) :=
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  HessianCertificate DD.dat (qDouble DD.qbar U) (QZeroBar DD rho htriv)
    (lSqWallHandlePhase DD.qbar U h)
    (oddHead h) (oddCross h (wallPolarEquiv U (Vmod_exp2 DD) hU2))

/-- Same-map promotion of a full source comparison to the original Hessian record.
The sign is not inferred from polar equivalence: its complete Gauss input is retained. -/
def sourceOddHessianOfComparison [Fintype DD.Vmod] {h m : ℕ}
    (U : DD.Vmod ≃+ DD.Vmod) (hUq : ∀ v, DD.qbar (U v)=DD.qbar v)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (hcard : Fintype.card DD.Vmod=2^(2*m))
    (epsilon : ℤ) (hgauss : QuadraticFp2.gaussSum (qDouble DD.qbar U)=epsilon*2^m)
    (C : SourceWordPhaseComparison DD rho htriv
      (DD.Vmod × (Fin h → DD.Vmod×DD.Vmod)) (lSqWallHandlePhase DD.qbar U h))
    (hadd : ∀ x y, C.phaseEquiv (x+y)=C.phaseEquiv x+C.phaseEquiv y) :
    SourceOddHessian DD rho htriv U hU2 h := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rho
  exact {
    cov := fp2LinearEquiv (phaseComparisonAddEquiv C hadd)
    cov_eq := C.phase_eq
    hq := isQuadratic_oddPhase DD.qbar U DD.hquad (Vmod_exp2 DD) hUq h
    hns := nonsingular_oddPhase DD.qbar U DD.hquad (Vmod_exp2 DD) DD.hns hUq hU2 h
    affinePhase := oddPhaseCover DD.qbar DD.dat DD.hdat U DD.hquad (Vmod_exp2 DD)
      DD.hns hUq hU2 hcard epsilon hgauss h }
end Source

#print axioms wallPolarEquiv
#print axioms polar_oddPhase
#print axioms isQuadratic_oddPhase
#print axioms nonsingular_oddPhase
#print axioms oddPhaseCover
#print axioms oddPhaseCover_unramified
#print axioms sourceOddHessianOfComparison

end
end GQ2.Dyadic.Instances.WordPhaseOddCertificates
