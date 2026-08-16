/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcUnramifiedDiagonal

/-!
# The isolated ramified Npc power charge

For a fixed-point-free odd-order action `t`, every vector is an action coboundary
`x = w + t • w`.  This file identifies the existing `NpcJet.powCharge` on that line:

`powCharge dat t x (orderOf t) = q w + dat.f w (t • w) + dat.m t w`.

Its exact polar contains the term `dat.f x y`.  A gauge change of the chosen factor-set section
adds an arbitrary normalized function of `x` to the charge.  Consequently the isolated charge
is not generically quadratic under `IsEquivariantFactorSet`; bilinearity of the chosen `f`
suffices, but is not part of the abstract boundary datum.

This is a routing result for the ramified Npc endpoint.  The generic proof must cancel the
section-dependent `f x y` term against the other Npc head blocks in the full diagonal, rather
than try to prove the omega2 charge quadratic in isolation.
-/

namespace GQ2.Dyadic.Instances.NpcRamifiedPowCharge

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.Dyadic
open GQ2.Dyadic.NpcJet
open GQ2.Dyadic.Certificates.MpcJet

variable {C V : Type} [Group C]
  [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V)
  (hdat : IsEquivariantFactorSet q dat)

/-- The charge obtained by conjugating the `C`-line through a slice element. -/
def conjugationCharge (t : C) (w : V) : ZMod 2 :=
  q w + dat.f w (t • w) + dat.m t w

/-- In characteristic two this is the usual action coboundary `t • w - w`. -/
def actionCoboundary (t : C) : V →+ V where
  toFun w := w + t • w
  map_zero' := by simp
  map_add' v w := by simp only [smul_add]; abel

private theorem polar_add_fun (Q R : V → ZMod 2) (v w : V) :
    polar (fun x ↦ Q x + R x) v w = polar Q v w + polar R v w := by
  simp only [polar]
  generalize Q (v + w) = a
  generalize Q v = b
  generalize Q w = c
  generalize R (v + w) = d
  generalize R v = e
  generalize R w = f
  revert a b c d e f
  decide

include hdat in
/-- Exact polarization of the conjugation model for the ramified power charge. -/
theorem polar_conjugationCharge (t : C) (v w : V) :
    polar (conjugationCharge (q := q) dat t) v w =
      polar q v w + dat.f (actionCoboundary t v) (actionCoboundary t w) +
        polar q w (t • v) := by
  rw [show conjugationCharge (q := q) dat t =
      fun x ↦ q x + (dat.f x (t • x) + dat.m t x) by
    funext x
    unfold conjugationCharge
    abel]
  rw [polar_add_fun]
  rw [NpcUnramifiedDiagonal.polar_factorSetGraph dat hdat]
  change polar q v w + (dat.f (v + t • v) (w + t • w) + polar q w (t • v)) =
    polar q v w + dat.f (v + t • v) (w + t • w) + polar q w (t • v)
  abel

include hdat in
/-- A positive constructor: bilinearity of the chosen factor set makes the isolated charge
quadratic.  The actual abstract boundary datum does not currently expose these hypotheses. -/
theorem isQuadratic_conjugationCharge_of_bilinear
    (hq : IsQuadraticFp2 q)
    (hfL : ∀ a b c : V, dat.f (a + b) c = dat.f a c + dat.f b c)
    (hfR : ∀ a b c : V, dat.f a (b + c) = dat.f a b + dat.f a c)
    (t : C) : IsQuadraticFp2 (conjugationCharge (q := q) dat t) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [conjugationCharge, hq.map_zero, hdat.f_zero_left, hdat.m_zero]
  · intro u v w
    rw [polar_conjugationCharge dat hdat, polar_conjugationCharge dat hdat,
      polar_conjugationCharge dat hdat]
    simp only [map_add, smul_add]
    rw [hfL]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel
  · intro u v w
    rw [polar_conjugationCharge dat hdat, polar_conjugationCharge dat hdat,
      polar_conjugationCharge dat hdat]
    simp only [map_add]
    rw [hfR]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel

include hdat in
theorem slice_inv_mul_cLine_mul_slice (hV2 : ∀ v : V, v + v = 0)
    (t : C) (w : V) :
    (sliceElt dat hdat w 0)⁻¹ * cLine dat hdat t * sliceElt dat hdat w 0 =
      elt dat hdat (w + t • w) t (conjugationCharge (q := q) dat t w) := by
  rw [sliceElt_inv dat hdat hV2, mul_assoc, cLine_mul_sliceElt dat hdat,
    sliceElt_def, elt_mul]
  simp only [zero_add, one_smul, one_mul, hdat.m_one, add_zero]
  unfold conjugationCharge
  congr 1
  abel

include hdat in
theorem powCharge_coboundary (hV2 : ∀ v : V, v + v = 0)
    (t : C) (htOdd : Odd (orderOf t))
    (htFpf : ∀ v : V, t • v = v → v = 0) (w : V) :
    powCharge dat t (w + t • w) (orderOf t) =
      conjugationCharge (q := q) dat t w := by
  let S := sliceElt dat hdat w 0
  let T := cLine dat hdat t
  let P := elt dat hdat (w + t • w) t 0
  let R := conjugationCharge (q := q) dat t w
  have hconj : S⁻¹ * T * S = WordCoh2.CentExt.incl
      (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R * P := by
    rw [show S⁻¹ * T * S = elt dat hdat (w + t • w) t R from
      slice_inv_mul_cLine_mul_slice dat hdat hV2 t w]
    dsimp [P]
    apply WordCoh2.CentExt.ext
    · change SectionEight.AffineTLift.Sd.mk (w + t • w) t =
        (1 : SectionEight.AffineTLift.Sd C V) *
          SectionEight.AffineTLift.Sd.mk (w + t • w) t
      rw [one_mul]
    · simp only [elt_fib, WordCoh2.CentExt.incl_mul_fib, add_zero]
  have hTpow : T ^ orderOf t = 1 := by
    change (nc3CLine dat hdat t) ^ orderOf t = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hconjpow : (S⁻¹ * T * S) ^ orderOf t = 1 := by
    change conjR T S ^ orderOf t = 1
    rw [← conjR_pow, hTpow]
    simp [conjR]
  have hRpow : WordCoh2.CentExt.incl
      (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R ^ orderOf t =
      WordCoh2.CentExt.incl
        (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R := by
    apply (NpcBridge.centExtEquiv dat hdat).injective
    rw [map_pow]
    change WordCoh.CentExt.incl (kappa0Cocycle dat hdat) R ^ orderOf t =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) R
    rw [centExt_incl_pow, nsmul_zmod2_odd htOdd]
  have hPpow : P ^ orderOf t =
      WordCoh2.CentExt.incl (SectionEight.AffineTLift.kappa0Cocycle dat hdat)
        (powCharge dat t (w + t • w) (orderOf t)) := by
    change elt dat hdat (w + t • w) t 0 ^ orderOf t = _
    rw [elt_pow_eq_sliceElt dat hdat (pow_orderOf_eq_one t)]
    · rfl
    · exact sum_pow_smul_orderOf_eq_zero htFpf (w + t • w)
  have hprod :
      (WordCoh2.CentExt.incl
        (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R * P) ^ orderOf t =
        WordCoh2.CentExt.incl
          (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R * P ^ orderOf t := by
    have hc : Commute
        (WordCoh2.CentExt.incl
          (SectionEight.AffineTLift.kappa0Cocycle dat hdat) R) P := by
      apply (NpcBridge.centExtEquiv dat hdat).injective
      exact (incl_commute R (NpcBridge.centExtEquiv dat hdat P)).eq
    rw [Commute.mul_pow hc, hRpow]
  rw [hconj, hprod, hPpow] at hconjpow
  have hfib := congrArg
    (WordCoh2.CentExt.fib
      (c := SectionEight.AffineTLift.kappa0Cocycle dat hdat)) hconjpow
  change R + powCharge dat t (w + t • w) (orderOf t) +
      (SectionEight.AffineTLift.kappa0Cocycle dat hdat).κ 1 1 = 0 at hfib
  rw [(SectionEight.AffineTLift.kappa0Cocycle dat hdat).norm] at hfib
  rw [add_zero] at hfib
  have hsolve : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact hsolve _ _ hfib

/-- `powCharge` restricted to the (surjective) ramified action-coboundary line. -/
def ramifiedPowCharge (t : C) (w : V) : ZMod 2 :=
  powCharge dat t (actionCoboundary t w) (orderOf t)

include hdat in
theorem ramifiedPowCharge_eq_conjugationCharge
    (hV2 : ∀ v : V, v + v = 0) (t : C) (htOdd : Odd (orderOf t))
    (htFpf : ∀ v : V, t • v = v → v = 0) :
    ramifiedPowCharge dat t = conjugationCharge (q := q) dat t := by
  funext w
  exact powCharge_coboundary dat hdat hV2 t htOdd htFpf w

include hdat in
/-- The exact polar formula directly on the existing `NpcJet.powCharge` specialization. -/
theorem polar_ramifiedPowCharge
    (hV2 : ∀ v : V, v + v = 0) (t : C) (htOdd : Odd (orderOf t))
    (htFpf : ∀ v : V, t • v = v → v = 0) (v w : V) :
    polar (ramifiedPowCharge dat t) v w =
      polar q v w + dat.f (actionCoboundary t v) (actionCoboundary t w) +
        polar q w (t • v) := by
  rw [ramifiedPowCharge_eq_conjugationCharge dat hdat hV2 t htOdd htFpf]
  exact polar_conjugationCharge dat hdat t v w

include hdat in
theorem isQuadratic_ramifiedPowCharge_of_bilinear
    (hq : IsQuadraticFp2 q)
    (hfL : ∀ a b c : V, dat.f (a + b) c = dat.f a c + dat.f b c)
    (hfR : ∀ a b c : V, dat.f a (b + c) = dat.f a b + dat.f a c)
    (hV2 : ∀ v : V, v + v = 0) (t : C) (htOdd : Odd (orderOf t))
    (htFpf : ∀ v : V, t • v = v → v = 0) :
    IsQuadraticFp2 (ramifiedPowCharge dat t) := by
  rw [ramifiedPowCharge_eq_conjugationCharge dat hdat hV2 t htOdd htFpf]
  exact isQuadratic_conjugationCharge_of_bilinear dat hdat hq hfL hfR t

/-! A gauge audit: the abstract factor-set axioms permit changing the section by an arbitrary
normalized function.  This makes the isolated charge acquire that arbitrary function on the
action-coboundary, so quadraticity cannot follow from those axioms alone. -/

def gaugeFactorSet (ell : V → ZMod 2) : FactorSet C V where
  f v w := dat.f v w + ell v + ell w + ell (v + w)
  m c v := dat.m c v + ell (c • v) + ell v

include hdat in
theorem gaugeFactorSet_equivariant (hV2 : ∀ v : V, v + v = 0)
    (ell : V → ZMod 2) (hell0 : ell 0 = 0) :
    IsEquivariantFactorSet q (gaugeFactorSet dat ell) := by
  constructor
  · intro v w x
    simp only [gaugeFactorSet]
    have hc := hdat.f_cocycle v w x
    rw [add_assoc v w x]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc
  · intro v
    simp only [gaugeFactorSet]
    rw [hV2, hell0, hdat.f_diag]
    linear_combination CharTwo.add_self_eq_zero (ell v)
  · intro v w
    simp only [gaugeFactorSet]
    rw [add_comm w v]
    have hp := hdat.f_polar v w
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hp
  · intro v
    simp only [gaugeFactorSet]
    rw [zero_add, hdat.f_zero_left, hell0]
    linear_combination CharTwo.add_self_eq_zero (ell v)
  · intro v
    simp only [gaugeFactorSet]
    rw [add_zero, hdat.f_zero_right, hell0]
    linear_combination CharTwo.add_self_eq_zero (ell v)
  · intro c v w
    simp only [gaugeFactorSet, smul_add]
    have hm := hdat.m_quad c v w
    linear_combination (norm := ring_nf) hm
  · intro c d v
    simp only [gaugeFactorSet, mul_smul]
    have hm := hdat.m_mul c d v
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hm
  · intro v
    simp only [gaugeFactorSet, one_smul, hdat.m_one]
    linear_combination CharTwo.add_self_eq_zero (ell v)

theorem conjugationCharge_gauge (ell : V → ZMod 2) (t : C) (w : V) :
    conjugationCharge (q := q) (gaugeFactorSet dat ell) t w =
      conjugationCharge (q := q) dat t w + ell (actionCoboundary t w) := by
  simp only [conjugationCharge, gaugeFactorSet]
  change _ = conjugationCharge (q := q) dat t w + ell (w + t • w)
  unfold conjugationCharge
  ring_nf
  simp [CharTwo.two_eq_zero]

end
end GQ2.Dyadic.Instances.NpcRamifiedPowCharge

/-! ## Axiom audit -/

#print axioms GQ2.Dyadic.Instances.NpcRamifiedPowCharge.powCharge_coboundary
#print axioms GQ2.Dyadic.Instances.NpcRamifiedPowCharge.polar_ramifiedPowCharge
#print axioms GQ2.Dyadic.Instances.NpcRamifiedPowCharge.isQuadratic_ramifiedPowCharge_of_bilinear
#print axioms GQ2.Dyadic.Instances.NpcRamifiedPowCharge.gaugeFactorSet_equivariant
#print axioms GQ2.Dyadic.Instances.NpcRamifiedPowCharge.conjugationCharge_gauge
