/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian

/-!
# The honest unramified Npc diagonal

This file identifies and proves quadratic the opaque diagonal left by the full-offset
unramified Npc Hessian calculation.  If

```
A = s ^ E(d.toZhat),   B = s ^ (2^r),   y = Phi v,
```

and the normal cocycle equation is `v + A⁻¹ v = y + B⁻¹ y`, then the diagonal is

```
npcQ0_A(v) + q(Phi v) + npcQ0_B(Phi v).
```

The two `npcQ0` summands need not be quadratic separately.  Their graph-polarizations contain
the same factor-set term, however, and the normal cocycle equation makes those terms cancel.
Thus the full diagonal is quadratic from `q` alone.

It is tempting to identify this diagonal with the older `npcQ0 ∘ Mc`, where `Mc` is the
inverse of `lcOp`.  That is generally false: the honest normal-coordinate operator is
`Phi = (1 - B⁻¹)⁻¹ (1 - A⁻¹)`, whereas `Mc = lcOp⁻¹`; they agree only in special action
images.  The correct Gauss bridge instead composes the quadratic diagonal proved here with
an additive inverse to `Phi`.
-/

namespace GQ2.Dyadic.Instances.NpcUnramifiedDiagonal

noncomputable section

open GQ2 GQ2.QuadraticFp2
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

include hdat in
theorem polar_factorSetGraph (c : C) (v w : V) :
    polar (fun x ↦ dat.f x (c • x) + dat.m c x) v w =
      dat.f (v + c • v) (w + c • w) + polar q w (c • v) := by
  simp only [polar, smul_add]
  have hm := hdat.m_quad c v w
  have hp := hdat.f_polar w (c • v)
  have h1 := hdat.f_cocycle v w (c • v + c • w)
  have h2 := hdat.f_cocycle v (c • v) (w + c • w)
  have h3 := hdat.f_cocycle w (c • v) (c • w)
  have h4 := hdat.f_cocycle (c • v) w (c • w)
  simp only [polar] at hp
  abel_nf at h1 h2 h3 h4
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    h1 + h2 + h3 + h4 + hm + hp

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

def npcUnramifiedDiagonalNF (cA cB : C) (Phi : V →+ V) (v : V) : ZMod 2 :=
  (dat.f v (cA • v) + dat.m cA v) + q (Phi v) +
    (dat.f (Phi v) (cB • Phi v) + dat.m cB (Phi v))

include hdat in
theorem polar_npcUnramifiedDiagonalNF
    (cA cB : C) (Phi : V →+ V)
    (hPhi : ∀ v : V, v + cA • v = Phi v + cB • Phi v)
    (v w : V) :
    polar (npcUnramifiedDiagonalNF (q := q) dat cA cB Phi) v w =
      polar q w (cA • v) + polar q (Phi v) (Phi w) +
        polar q (Phi w) (cB • Phi v) := by
  unfold npcUnramifiedDiagonalNF
  rw [polar_add_fun, polar_add_fun]
  rw [polar_factorSetGraph dat hdat]
  rw [polar_comp q (⇑Phi) (fun a b ↦ map_add Phi a b)]
  rw [polar_comp
    (fun x ↦ dat.f x (cB • x) + dat.m cB x) (⇑Phi)
    (fun a b ↦ map_add Phi a b)]
  rw [polar_factorSetGraph dat hdat]
  rw [← hPhi v, ← hPhi w]
  generalize dat.f (v + cA • v) (w + cA • w) = a
  generalize polar q w (cA • v) = b
  generalize polar q (Phi v) (Phi w) = c
  generalize polar q (Phi w) (cB • Phi v) = d
  revert a b c d
  decide

include hdat in
theorem isQuadratic_npcUnramifiedDiagonalNF
    (hq : IsQuadraticFp2 q) (cA cB : C) (Phi : V →+ V)
    (hPhi : ∀ v : V, v + cA • v = Phi v + cB • Phi v) :
    IsQuadraticFp2 (npcUnramifiedDiagonalNF (q := q) dat cA cB Phi) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [npcUnramifiedDiagonalNF, hdat.f_zero_left, hdat.m_zero, hq.map_zero]
  · intro u v w
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    simp only [smul_add, map_add]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel
  · intro u v w
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    rw [polar_npcUnramifiedDiagonalNF dat hdat cA cB Phi hPhi]
    simp only [map_add]
    simp_rw [hq.polar_add_left, hq.polar_add_right]
    abel

/-- The full-offset diagonal is the sum of the head `npcQ0`, the boundary
`npcQ0`, and the intervening `q`-charge. -/
theorem npcUnramifiedDiagonal_eq_twoQ0
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hV2 : ∀ v : V, v + v = 0) (s : C) (E : Zhat → ℤ) (d : EtaData)
    (hA : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (Phi : V →+ V)
    (hPhi : ∀ v : V,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi v)
    (v : V) :
    npcUnramifiedDiagonal dat hdat s E alpha r d Phi v =
      NpcJet.npcQ0 dat s d.toPadic v + q (Phi v) +
        NpcJet.npcQ0 dat (s ^ (2 ^ r : ℤ)) 1 (Phi v) := by
  unfold npcUnramifiedDiagonal npcUnramifiedCoreElt
  have hz : ((2 : ℤ) + 2 ^ alpha) = ((2 + 2 ^ alpha : ℕ) : ℤ) := by
    norm_num
  rw [hz, zpow_natCast, Certificates.hessSlice_pow_leading dat hdat hV2 halpha]
  change (hessSlice dat hdat 0 (q v) *
      (commR (hessSlice dat hdat v 0) (hessLine dat hdat (s ^ E d.toZhat)) *
        ((conjR (hessSlice dat hdat (Phi v) 0)
          (hessLine dat hdat (s ^ (2 ^ r : ℤ))))⁻¹ *
            hessSlice dat hdat (Phi v) 0))).fib = _
  rw [commR_eq_inv_mul_conjR, hessSlice_inv dat hdat hV2,
    NpcBridge.hessSlice_conj_hessLine]
  rw [NpcBridge.hessSlice_conj_hessLine]
  rw [hessSlice_inv dat hdat hV2]
  simp only [zero_add]
  rw [hessSlice_mul dat hdat, hessSlice_mul dat hdat,
    hessSlice_mul dat hdat, hessSlice_mul dat hdat]
  simp only [zero_add, add_zero, hdat.f_zero_left, hessSlice_fib]
  rw [hA]
  simp only [NpcJet.npcQ0, etaHatZ_one, zpowHat_ofInt, zpow_one]
  have hsame :
      v + (s ^ᶻ etaHatZ d.toPadic)⁻¹ • v =
        (s ^ (2 ^ r : ℤ))⁻¹ • Phi v + Phi v := by
    rw [← hA]
    exact (hPhi v).trans (add_comm _ _)
  rw [hsame, hdat.f_diag]
  have hqsum : ∀ a b c : ZMod 2, c = a + b + (c + a + b) := by
    decide
  rw [show q ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v + Phi v) =
      q ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) + q (Phi v) +
        polar q ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) (Phi v) by
      exact hqsum _ _ _]
  have hqinv : ∀ (c : C) (x : V), q (c • x) = q x := by
    intro c x
    have hm := hdat.m_quad c x x
    rw [hV2 x, hdat.m_zero c, zero_add, hdat.f_diag, hdat.f_diag] at hm
    have hkey : ∀ a b z : ZMod 2, a + a = b + z → b = z := by
      decide
    exact hkey _ _ _ hm
  rw [hqinv]
  rw [show polar q ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) (Phi v) =
      dat.f ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) (Phi v) +
        dat.f (Phi v) ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) by
      exact (hdat.f_polar _ _).symm]
  generalize q v = a
  generalize dat.m (s ^ᶻ etaHatZ d.toPadic)⁻¹ v = b
  generalize dat.f v ((s ^ᶻ etaHatZ d.toPadic)⁻¹ • v) = c
  generalize dat.m (s ^ (2 ^ r : ℤ))⁻¹ (Phi v) = z
  generalize q (Phi v) = e
  generalize dat.f ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) (Phi v) = f
  generalize dat.f (Phi v) ((s ^ (2 ^ r : ℤ))⁻¹ • Phi v) = g
  revert a b c z e f g
  decide

theorem npcUnramifiedDiagonal_eq_nf
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hV2 : ∀ v : V, v + v = 0) (s : C) (E : Zhat → ℤ) (d : EtaData)
    (hA : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (Phi : V →+ V)
    (hPhi : ∀ v : V,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi v)
    (v : V) :
    npcUnramifiedDiagonal dat hdat s E alpha r d Phi v =
      npcUnramifiedDiagonalNF (q := q) dat
        (s ^ E d.toZhat)⁻¹ (s ^ (2 ^ r : ℤ))⁻¹ Phi v := by
  rw [npcUnramifiedDiagonal_eq_twoQ0 dat hdat hV2 s E d hA halpha Phi hPhi]
  unfold npcUnramifiedDiagonalNF NpcJet.npcQ0
  simp only [etaHatZ_one, zpowHat_ofInt, zpow_one]
  rw [hA]

theorem isQuadratic_npcUnramifiedDiagonal
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hq : IsQuadraticFp2 q)
    (hV2 : ∀ v : V, v + v = 0) (s : C) (E : Zhat → ℤ) (d : EtaData)
    (hA : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (Phi : V →+ V)
    (hPhi : ∀ v : V,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi v) :
    IsQuadraticFp2
      (npcUnramifiedDiagonal dat hdat s E alpha r d Phi) := by
  rw [show npcUnramifiedDiagonal dat hdat s E alpha r d Phi =
      npcUnramifiedDiagonalNF (q := q) dat
        (s ^ E d.toZhat)⁻¹ (s ^ (2 ^ r : ℤ))⁻¹ Phi from
    funext (npcUnramifiedDiagonal_eq_nf dat hdat hV2 s E d hA halpha Phi hPhi)]
  exact isQuadratic_npcUnramifiedDiagonalNF dat hdat hq _ _ Phi hPhi

theorem isQuadratic_npcUnramifiedDiagonal_comp
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hq : IsQuadraticFp2 q)
    (hV2 : ∀ v : V, v + v = 0) (s : C) (E : Zhat → ℤ) (d : EtaData)
    (hA : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic)
    {alpha r : ℕ} (halpha : 2 ≤ alpha) (Phi Psi : V →+ V)
    (hPhi : ∀ v : V,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi v) :
    IsQuadraticFp2
      (fun v ↦ npcUnramifiedDiagonal dat hdat s E alpha r d Phi (Psi v)) :=
  isQuadraticFp2_comp
    (npcUnramifiedDiagonal dat hdat s E alpha r d Phi)
    (isQuadratic_npcUnramifiedDiagonal dat hdat hq hV2 s E d hA halpha Phi hPhi)
    (⇑Psi) (fun a b ↦ map_add Psi a b) (map_zero Psi)

#print axioms polar_factorSetGraph
#print axioms npcUnramifiedDiagonalNF
#print axioms polar_npcUnramifiedDiagonalNF
#print axioms isQuadratic_npcUnramifiedDiagonalNF
#print axioms npcUnramifiedDiagonal_eq_twoQ0
#print axioms npcUnramifiedDiagonal_eq_nf
#print axioms isQuadratic_npcUnramifiedDiagonal
#print axioms isQuadratic_npcUnramifiedDiagonal_comp

end
end GQ2.Dyadic.Instances.NpcUnramifiedDiagonal
