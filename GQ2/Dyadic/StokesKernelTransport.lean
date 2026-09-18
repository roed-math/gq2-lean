/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Stokes transport using only kernels, ranges, and the pairing on cycles

Full Heisenberg equality is unnecessary for Stokes transport. Equal degree-one
kernels, inclusions of the old degree-one ranges in the new ones, and equality
of the pairings on cycles suffice. In the surjective case the range premises
follow from equal kernels by finiteness. No normal form or chosen basis is used.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

/-- Surjectivity survives a change of additive map with the same finite kernel. -/
theorem surjective_of_same_kernel
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Finite V] [Finite W]
    (f g : V →+ W) (hker : f.ker = g.ker) (hf : Function.Surjective f) :
    Function.Surjective g := by
  apply g.surjective_of_card_ker_le_div
  rw [← hker]
  have hcard : Nat.card V = Nat.card W * Nat.card f.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  rw [hcard, Nat.mul_comm (Nat.card W), Nat.mul_div_cancel]
  exact Nat.card_pos

/-- Transport Stokes duality without requiring equality on noncycles. -/
theorem stokesDuality_of_same_kernels_ranges_pairing
    {ι ρ C A : Type*} [Fintype ι] [Fintype ρ] [Group C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (c : ι → C) (w w' : ρ → FreeGroup ι)
    (hkerA : ∀ x : ι → A, heisD1 c w x = 0 ↔ heisD1 c w' x = 0)
    (hkerD : ∀ y : ι → ElemDual A, heisD1 c w y = 0 ↔ heisD1 c w' y = 0)
    (hrangeA : (heisD1 (A := A) c w).range ≤ (heisD1 (A := A) c w').range)
    (hrangeD : (heisD1 (A := ElemDual A) c w).range ≤
      (heisD1 (A := ElemDual A) c w').range)
    (hpair : ∀ (x : ι → A) (y : ι → ElemDual A),
      heisD1 c w x = 0 → heisD1 c w y = 0 →
      heisEta1 c w x y = heisEta1 c w' x y)
    (H : StokesDuality c w A) : StokesDuality c w' A := by
  refine
    { h0_inj := H.h0_inj
      h0_surj := ?_
      h1_inj := ?_
      h1_surj := ?_
      h2_inj := ?_
      h2_surj := H.h2_surj }
  · intro xi hxi
    apply H.h0_surj xi
    apply ElemDual.ext
    intro y
    obtain ⟨y', hy'⟩ := AddMonoidHom.mem_range.mp (hrangeD
      (AddMonoidHom.mem_range.mpr ⟨y, rfl⟩))
    have hz := DFunLike.congr_fun hxi y'
    change xi (heisD1 c w' y') = 0 at hz
    change xi (heisD1 c w y) = 0
    rwa [hy'] at hz
  · intro x hx ⟨xi, hxi⟩
    have hxw := (hkerA x).mpr hx
    apply H.pairing_vanish_left x hxw
    intro y hy
    rw [hpair x y hxw hy]
    have hz := DFunLike.congr_fun hxi y
    change xi (heisD1 c w' y) = heisEta1 c w' x y at hz
    rw [(hkerD y).mp hy, map_zero] at hz
    exact hz.symm
  · intro lam hlam
    obtain ⟨x, xi, hx, hsum⟩ := H.h1_surj lam hlam
    let delta : ElemDual (ι → ElemDual A) := lam - heisEta1 c w' x
    let d : (ι → ElemDual A) →+ (ρ → ElemDual A) := heisD1 c w'
    have hdelta : dualMap d.ker.subtype delta = 0 := by
      apply ElemDual.ext
      intro y
      have hy' : heisD1 c w' y.1 = 0 := AddMonoidHom.mem_ker.mp y.2
      have hy := (hkerD y.1).mpr hy'
      have hsumy := DFunLike.congr_fun hsum y.1
      change heisEta1 c w x y.1 + xi (heisD1 c w y.1) = lam y.1 at hsumy
      rw [hy, map_zero, add_zero, hpair x y.1 hx hy] at hsumy
      change lam y.1 - heisEta1 c w' x y.1 = 0
      exact sub_eq_zero.mpr hsumy.symm
    have hfactor := (dual_exact_pair (fun z : ρ → ElemDual A ↦ funext fun k ↦ (z k).add_self_eq_zero)
      d.ker.subtype d (AddSubgroup.range_subtype _) delta).mp hdelta
    obtain ⟨xi', hxi'⟩ := AddMonoidHom.mem_range.mp hfactor
    refine ⟨x, xi', (hkerA x).mp hx, ?_⟩
    change heisEta1 c w' x + dualMap d xi' = lam
    rw [hxi']
    dsimp only [delta]
    abel
  · intro v hv
    obtain ⟨x, hx⟩ := H.h2_inj v hv
    exact AddMonoidHom.mem_range.mp (hrangeA (AddMonoidHom.mem_range.mpr ⟨x, hx⟩))

/-- In the surjective case, matching kernels and cycle pairings suffice. -/
theorem stokesDuality_of_same_kernels_pairing_of_surjective
    {ι ρ C A : Type*} [Fintype ι] [Fintype ρ] [Group C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (c : ι → C) (w w' : ρ → FreeGroup ι)
    (hkerA : ∀ x : ι → A, heisD1 c w x = 0 ↔ heisD1 c w' x = 0)
    (hkerD : ∀ y : ι → ElemDual A, heisD1 c w y = 0 ↔ heisD1 c w' y = 0)
    (hsurjA : Function.Surjective (heisD1 (A := A) c w))
    (hsurjD : Function.Surjective (heisD1 (A := ElemDual A) c w))
    (hpair : ∀ (x : ι → A) (y : ι → ElemDual A),
      heisD1 c w x = 0 → heisD1 c w y = 0 →
      heisEta1 c w x y = heisEta1 c w' x y)
    (H : StokesDuality c w A) : StokesDuality c w' A := by
  have hA := surjective_of_same_kernel (heisD1 (A := A) c w) (heisD1 c w')
    (by ext x; exact hkerA x) hsurjA
  have hD := surjective_of_same_kernel (heisD1 (A := ElemDual A) c w) (heisD1 c w')
    (by ext y; exact hkerD y) hsurjD
  apply stokesDuality_of_same_kernels_ranges_pairing c w w' hkerA hkerD
  · rw [AddMonoidHom.range_eq_top.mpr hA]
    exact le_top
  · rw [AddMonoidHom.range_eq_top.mpr hD]
    exact le_top
  · exact hpair
  · exact H

/-- Stokes duality forces surjectivity when the dual coefficient has no invariants. -/
theorem StokesDuality.heisD1_surjective_of_dual_heisD0_injective
    {ι ρ C A : Type*} [Fintype ι] [Fintype ρ] [Group C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    {c : ι → C} {w : ρ → FreeGroup ι} (H : StokesDuality c w A)
    (hd0D : Function.Injective (heisD0 (A := ElemDual A) c)) :
    Function.Surjective (heisD1 (A := A) c w) := by
  intro v
  apply H.h2_inj v
  exact dualMap_surjective
    (fun z : ι → ElemDual A ↦ funext fun i ↦ (z i).add_self_eq_zero)
    _ hd0D (heisEta2 v)

#print axioms surjective_of_same_kernel
#print axioms stokesDuality_of_same_kernels_ranges_pairing
#print axioms stokesDuality_of_same_kernels_pairing_of_surjective
#print axioms StokesDuality.heisD1_surjective_of_dual_heisD0_injective

end
end GQ2.Dyadic
