/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcRamifiedPowCharge
import GQ2.Dyadic.Instances.NpcUnramifiedProcyclic

/-!
# The honest ramified Npc diagonal

This file proves quadratic the diagonal left by the full-offset ramified Npc Hessian.  Put

```
a = (s ^ E(d.toZhat))⁻¹,  B = s ^ (2^r),  Phi(v) = B • (a • v - v).
```

Direct extension arithmetic first gives the exact normal form

```
f(v, a • v) + m_a(v) + m_(B⁻¹)(Phi(v)) + powCharge_u(Phi(v)).
```

The isolated power charge is not quadratic for an arbitrary factor-set section.  Fixed-point
freeness of the odd-order action `u` instead supplies the additive coordinate
`L = (1-u)⁻¹ ∘ Phi`.  In characteristic two, `Phi(v) = L(v) + u • L(v)`, so the exact
power-charge identity from `NpcRamifiedPowCharge` applies.  The two section-dependent
factor-set terms in the
total polar then cancel, leaving

```
polar q w (a • v) + polar q (L v) (L w) + polar q (L w) (u • L v).
```

This expression is bilinear.  Thus the full ramified diagonal is quadratic under precisely the
honest boundary hypotheses: quadratic `q`, exponent two on `V`, `alpha ≥ 2`, odd order of `u`,
and fixed-point-freeness of the `u`-action.  No bilinearity assumption on the chosen factor set
is used.
-/

namespace GQ2.Dyadic.Instances.NpcRamifiedDiagonal

noncomputable section

open GQ2 GQ2.QuadraticFp2
open GQ2.Dyadic GQ2.Dyadic.NpcJet GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V)
  (hdat : IsEquivariantFactorSet q dat)

@[simp] theorem ramifiedActionCoboundary_apply (u : C) (w : V) :
    NpcRamifiedPowCharge.actionCoboundary u w = w + u • w := rfl

/-- The additive boundary offset in the ramified normal cochain. -/
def ramifiedBoundaryHom (a b : C) : V →+ V where
  toFun v := b⁻¹⁻¹ • (a • v - v)
  map_zero' := by simp
  map_add' v w := by
    simp only [smul_add, sub_eq_add_neg, neg_add_rev]
    abel

@[simp] theorem ramifiedBoundaryHom_apply (a b : C) (v : V) :
    ramifiedBoundaryHom (V := V) a b v = b⁻¹⁻¹ • (a • v - v) := rfl

/-- The honest normal form before solving the `u-1` equation. -/
def npcRamifiedDiagonalChargeNF (a b u : C) (Phi : V →+ V) (v : V) : ZMod 2 :=
  dat.f v (a • v) + dat.m a v + dat.m b⁻¹ (Phi v) +
    NpcJet.powCharge dat u (Phi v) (orderOf u)

/-- Direct extension arithmetic identifies the W140 diagonal with its four-term charge normal
form. -/
theorem npcRamifiedDiagonal_eq_chargeNF
    (hV2 : ∀ v : V, v + v = 0) (s u : C) (E : Zhat → ℤ)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (d : EtaData) (v : V) :
    npcRamifiedDiagonal dat hdat s u E alpha r d v =
      npcRamifiedDiagonalChargeNF dat
        (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)) u
        (ramifiedBoundaryHom (V := V)
          (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))) v := by
  unfold npcRamifiedDiagonal npcRamifiedCoreElt npcRamifiedDiagonalChargeNF
  have hz : ((2 : ℤ) + 2 ^ alpha) = ((2 + 2 ^ alpha : ℕ) : ℤ) := by
    norm_num
  rw [hz, zpow_natCast, Certificates.hessSlice_pow_leading dat hdat hV2 halpha]
  rw [commR_eq_inv_mul_conjR, hessSlice_inv dat hdat hV2,
    NpcBridge.hessSlice_conj_hessLine]
  rw [NpcBridge.hessSlice_conj_hessLine]
  rw [hessSlice_inv dat hdat hV2]
  simp only [zero_add]
  rw [← NpcBridge.hessSlice_zero_eq_incl dat hdat (q v)]
  rw [← NpcBridge.hessSlice_zero_eq_incl dat hdat
    (NpcJet.powCharge dat u
      (((s ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • ((s ^ E d.toZhat)⁻¹ • v - v)) (orderOf u))]
  rw [hessSlice_mul dat hdat, hessSlice_mul dat hdat,
    hessSlice_mul dat hdat, hessSlice_mul dat hdat]
  simp only [zero_add, add_zero, ramifiedBoundaryHom_apply]
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_left (hV2 x)
  simp only [sub_eq_add_neg, hneg, inv_inv]
  have hBA (x : V) :
      (s ^ ((2 : ℤ) ^ r))⁻¹ •
          (s ^ ((2 : ℤ) ^ r) • ((s ^ E d.toZhat)⁻¹ • x + x)) =
        (s ^ E d.toZhat)⁻¹ • x + x := by
    rw [inv_smul_smul]
  rw [hBA]
  have hx : v + (s ^ E d.toZhat)⁻¹ • v =
      (s ^ E d.toZhat)⁻¹ • v + v := add_comm _ _
  rw [hx]
  rw [hV2, hdat.f_diag]
  simp only [hessSlice_fib, hdat.f_zero_left, hdat.f_zero_right, add_zero]
  generalize q v = qv
  generalize dat.f v ((s ^ E d.toZhat)⁻¹ • v) = fav
  generalize dat.m (s ^ E d.toZhat)⁻¹ v = mav
  generalize dat.m (s ^ ((2 : ℤ) ^ r))⁻¹
    (s ^ ((2 : ℤ) ^ r) • ((s ^ E d.toZhat)⁻¹ • v + v)) = mbv
  generalize NpcJet.powCharge dat u
    (s ^ ((2 : ℤ) ^ r) • ((s ^ E d.toZhat)⁻¹ • v + v)) (orderOf u) = pc
  generalize q ((s ^ E d.toZhat)⁻¹ • v + v) = qd
  revert qv fav mav mbv pc qd
  decide

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
/-- Polarization of the boundary `m`-term after an additive coordinate change. -/
theorem polar_m_comp (c : C) (Phi : V →+ V) (v w : V) :
    polar (fun x ↦ dat.m c (Phi x)) v w =
      dat.f (c • Phi v) (c • Phi w) + dat.f (Phi v) (Phi w) := by
  simp only [polar, map_add]
  have hm := hdat.m_quad c (Phi v) (Phi w)
  generalize dat.m c (Phi v + Phi w) = a at hm ⊢
  generalize dat.m c (Phi v) = b at hm ⊢
  generalize dat.m c (Phi w) = d at hm ⊢
  generalize dat.f (c • Phi v) (c • Phi w) = e at hm ⊢
  generalize dat.f (Phi v) (Phi w) = f at hm ⊢
  revert a b d e f
  decide

/-- The solved normal form: the exact power charge has been transported through an additive
inverse coordinate `L` of the ramified action coboundary. -/
def npcRamifiedDiagonalSolvedNF (a b u : C) (Phi L : V →+ V) (v : V) : ZMod 2 :=
  dat.f v (a • v) + dat.m a v + dat.m b⁻¹ (Phi v) +
    NpcRamifiedPowCharge.conjugationCharge (q := q) dat u (L v)

include hdat in
/-- The exact total polar.  Both section-dependent factor-set terms have cancelled. -/
theorem polar_npcRamifiedDiagonalSolvedNF
    (a b u : C) (Phi L : V →+ V)
    (hb : ∀ v : V, b⁻¹ • Phi v = v + a • v)
    (hL : ∀ v : V, Phi v = NpcRamifiedPowCharge.actionCoboundary u (L v))
    (v w : V) :
    polar (npcRamifiedDiagonalSolvedNF (q := q) dat a b u Phi L) v w =
      polar q w (a • v) + polar q (L v) (L w) + polar q (L w) (u • L v) := by
  unfold npcRamifiedDiagonalSolvedNF
  rw [show (fun x ↦ dat.f x (a • x) + dat.m a x + dat.m b⁻¹ (Phi x) +
        NpcRamifiedPowCharge.conjugationCharge (q := q) dat u (L x)) =
      fun x ↦ (dat.f x (a • x) + dat.m a x) +
        (dat.m b⁻¹ (Phi x) +
          NpcRamifiedPowCharge.conjugationCharge (q := q) dat u (L x)) by
    funext x
    abel]
  rw [polar_add_fun
    (fun x ↦ dat.f x (a • x) + dat.m a x)
    (fun x ↦ dat.m b⁻¹ (Phi x) +
      NpcRamifiedPowCharge.conjugationCharge (q := q) dat u (L x)) v w]
  rw [polar_add_fun
    (fun x ↦ dat.m b⁻¹ (Phi x))
    (fun x ↦ NpcRamifiedPowCharge.conjugationCharge (q := q) dat u (L x)) v w]
  rw [NpcUnramifiedDiagonal.polar_factorSetGraph dat hdat]
  rw [polar_m_comp dat hdat]
  rw [polar_comp (NpcRamifiedPowCharge.conjugationCharge (q := q) dat u) (⇑L)
    (fun x y ↦ map_add L x y)]
  rw [NpcRamifiedPowCharge.polar_conjugationCharge dat hdat]
  rw [hb v, hb w, ← hL v, ← hL w]
  generalize dat.f (v + a • v) (w + a • w) = f₁
  generalize polar q w (a • v) = p₁
  generalize dat.f (Phi v) (Phi w) = f₂
  generalize polar q (L v) (L w) = p₂
  generalize polar q (L w) (u • L v) = p₃
  revert f₁ p₁ f₂ p₂ p₃
  decide

include hdat in
/-- The solved normal form is quadratic without any bilinearity assumption on `dat.f`. -/
theorem isQuadratic_npcRamifiedDiagonalSolvedNF
    (hq : IsQuadraticFp2 q) (a b u : C) (Phi L : V →+ V)
    (hb : ∀ v : V, b⁻¹ • Phi v = v + a • v)
    (hL : ∀ v : V, Phi v = NpcRamifiedPowCharge.actionCoboundary u (L v)) :
    IsQuadraticFp2 (npcRamifiedDiagonalSolvedNF (q := q) dat a b u Phi L) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [npcRamifiedDiagonalSolvedNF, NpcRamifiedPowCharge.conjugationCharge,
      hq.map_zero, hdat.f_zero_left, hdat.m_zero]
  · intro x y z
    rw [polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL,
      polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL,
      polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL]
    simp only [smul_add, map_add]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel
  · intro x y z
    rw [polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL,
      polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL,
      polar_npcRamifiedDiagonalSolvedNF dat hdat a b u Phi L hb hL]
    simp only [map_add]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel

/-- The inverse `(1-u)⁻¹` coordinate applied to the concrete boundary offset. -/
def ramifiedChargeLift [Finite V] (u : C) (hVu : ∀ v : V, u • v = v → v = 0)
    (Phi : V →+ V) : V →+ V :=
  ((AddEquiv.ofBijective
      (NProcyclicUnram.oneSubHom (A := V) u)
      (NProcyclicUnram.oneSubHom_bijective hVu)).symm : V →+ V).comp Phi

theorem ramifiedChargeLift_spec [Finite V]
    (u : C) (hVu : ∀ v : V, u • v = v → v = 0)
    (Phi : V →+ V) (v : V) :
    ramifiedChargeLift u hVu Phi v - u • ramifiedChargeLift u hVu Phi v = Phi v :=
  (AddEquiv.ofBijective
    (NProcyclicUnram.oneSubHom (A := V) u)
    (NProcyclicUnram.oneSubHom_bijective hVu)).apply_symm_apply (Phi v)

theorem ramifiedChargeLift_coboundary [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (u : C)
    (hVu : ∀ v : V, u • v = v → v = 0) (Phi : V →+ V) (v : V) :
    Phi v = NpcRamifiedPowCharge.actionCoboundary u
      (ramifiedChargeLift u hVu Phi v) := by
  have hneg : -(u • ramifiedChargeLift u hVu Phi v) =
      u • ramifiedChargeLift u hVu Phi v :=
    neg_eq_of_add_eq_zero_left (hV2 _)
  rw [ramifiedActionCoboundary_apply, ← hneg, ← sub_eq_add_neg]
  exact (ramifiedChargeLift_spec u hVu Phi v).symm

theorem ramifiedBoundaryHom_inv_smul
    (hV2 : ∀ v : V, v + v = 0) (a b : C) (v : V) :
    b⁻¹ • ramifiedBoundaryHom (V := V) a b v = v + a • v := by
  rw [ramifiedBoundaryHom_apply, inv_inv, inv_smul_smul]
  have hneg : -v = v := neg_eq_of_add_eq_zero_left (hV2 v)
  simp only [sub_eq_add_neg, hneg]
  exact add_comm _ _

/-- The concrete W140 diagonal is the solved normal form. -/
theorem npcRamifiedDiagonal_eq_solvedNF [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (s u : C) (E : Zhat → ℤ)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (d : EtaData)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (v : V) :
    npcRamifiedDiagonal dat hdat s u E alpha r d v =
      npcRamifiedDiagonalSolvedNF (q := q) dat
        (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)) u
        (ramifiedBoundaryHom (V := V)
          (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)))
        (ramifiedChargeLift u hVu
          (ramifiedBoundaryHom (V := V)
            (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)))) v := by
  rw [npcRamifiedDiagonal_eq_chargeNF dat hdat hV2 s u E halpha d]
  unfold npcRamifiedDiagonalChargeNF npcRamifiedDiagonalSolvedNF
  rw [ramifiedChargeLift_coboundary hV2 u hVu
    (ramifiedBoundaryHom (V := V)
      (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))) v]
  rw [ramifiedActionCoboundary_apply]
  rw [NpcRamifiedPowCharge.powCharge_coboundary dat hdat hV2 u hu hVu]

include hdat in
/-- The full ramified Npc diagonal is quadratic under the honest boundary hypotheses. -/
theorem isQuadratic_npcRamifiedDiagonal [Finite V]
    (hq : IsQuadraticFp2 q) (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (E : Zhat → ℤ) {alpha r : ℕ} (halpha : 2 ≤ alpha) (d : EtaData)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0) :
    IsQuadraticFp2 (npcRamifiedDiagonal dat hdat s u E alpha r d) := by
  rw [show npcRamifiedDiagonal dat hdat s u E alpha r d =
      npcRamifiedDiagonalSolvedNF (q := q) dat
        (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)) u
        (ramifiedBoundaryHom (V := V)
          (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)))
        (ramifiedChargeLift u hVu
          (ramifiedBoundaryHom (V := V)
            (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)))) from
    funext (npcRamifiedDiagonal_eq_solvedNF dat hdat hV2 s u E halpha d hu hVu)]
  exact isQuadratic_npcRamifiedDiagonalSolvedNF dat hdat hq
    (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)) u
    (ramifiedBoundaryHom (V := V)
      (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r)))
    (ramifiedChargeLift u hVu
      (ramifiedBoundaryHom (V := V)
        (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))))
    (ramifiedBoundaryHom_inv_smul hV2 _ _)
    (ramifiedChargeLift_coboundary hV2 u hVu _)

/-! ## Axiom audit -/

#print axioms ramifiedBoundaryHom
#print axioms ramifiedActionCoboundary_apply
#print axioms ramifiedBoundaryHom_apply
#print axioms npcRamifiedDiagonalChargeNF
#print axioms npcRamifiedDiagonal_eq_chargeNF
#print axioms polar_m_comp
#print axioms npcRamifiedDiagonalSolvedNF
#print axioms polar_npcRamifiedDiagonalSolvedNF
#print axioms isQuadratic_npcRamifiedDiagonalSolvedNF
#print axioms ramifiedChargeLift
#print axioms ramifiedChargeLift_spec
#print axioms ramifiedChargeLift_coboundary
#print axioms ramifiedBoundaryHom_inv_smul
#print axioms npcRamifiedDiagonal_eq_solvedNF
#print axioms isQuadratic_npcRamifiedDiagonal

end
end GQ2.Dyadic.Instances.NpcRamifiedDiagonal
