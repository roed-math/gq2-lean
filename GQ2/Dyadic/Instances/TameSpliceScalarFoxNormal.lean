/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileSpliceSupply

/-!
# Scalar Fox normal form for the actual tame-splice sources

For exponent-two coefficients with trivial generator action, first jets are
ordinary additive exponent evaluations. The literal mod-two endpoint condition
therefore identifies the two relator rows, while the tame row is the tau
coordinate. This yields an all-cochain matrix identity and an explicit invertible
row reduction for both normalized/corrected pair and mobile splice words.

No relator-death hypothesis, chain-square identity, or equality of kernels is
used to infer the sigma column. The concrete endpoint theorems discharge all
syntactic input for the actual source words and their pinned resolvers.
-/

namespace GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates MarkedCore Words
open Multiplicative
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSplice Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcMobileNuSource Instances.MpcMobileSpliceSupply

private theorem free_word_trivial_action
    {X C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : X → C) (htriv : ∀ (i : X) (a : A), c i • a = a)
    (w : FreeGroup X) (a : A) : FreeGroup.lift c w • a = a := by
  induction w using FreeGroup.induction_on generalizing a with
  | one => simp
  | of i => simpa using htriv i a
  | inv_of w ih =>
      rw [map_inv]
      exact inv_smul_eq_iff.mpr (ih a).symm
  | mul u v ihu ihv => rw [map_mul, mul_smul, ihv, ihu]

private theorem scalar_jet_lift
    {X C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : X → C) (htriv : ∀ (i : X) (a : A), c i • a = a)
    (x : X → A) (lam : ElemDual A) (w : FreeGroup X) :
    lam ((FreeGroup.lift (heisGen c x 0) w).a) =
      Multiplicative.toAdd (FreeGroup.lift (fun i => Multiplicative.ofAdd (lam (x i))) w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => simp [heisGen]
  | inv_of w ih =>
      rw [map_inv, HeisLift.inv_a, heisWord_g,
        inv_smul_eq_iff.mpr (free_word_trivial_action c htriv (FreeGroup.of w) _).symm,
        map_neg, ih, map_inv, toAdd_inv]
  | mul u v ihu ihv =>
      rw [map_mul, HeisLift.mul_a, heisWord_g, free_word_trivial_action c htriv,
        map_add, ihu, ihv, map_mul, toAdd_mul]

/-- Trivial-action first jets see the literal total mod-two exponent vector.
This is a direct free-word calculation, not a chain-square or kernel argument. -/
theorem sum_scalarFox_eq_zero_of_endpoint
    {X rho C A : Type*} [Fintype X] [DecidableEq X] [Fintype rho]
    [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : X → C) (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (i : X) (a : A), c i • a=a)
    (w : rho → FreeGroup X) (hend : IsStokesEndpoint w) (x : X → A) :
    ∑ k, heisD1 c w x k = 0 := by
  by_contra hne
  obtain ⟨lam, hlam⟩ := elemDual_separates hA2 hne
  apply hlam
  rw [map_sum]
  simp only [heisD1_apply, scalar_jet_lift c htriv x lam]
  exact sum_toAdd_lift_eq_zero_of_endpoint hend
    (fun i => Multiplicative.ofAdd (lam (x i)))

/-- Both scalar rows are literally tau, on every cochain. No relator-death premise. -/
theorem scalarFox_rows_of_endpoint
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hqe : Even q)
    (R : PWord (Generator n))
    (hend : IsStokesEndpoint (fun k => heisToFree E E₂ (gammaFam n q R k)))
    (x : Generator n → A) :
    heisD1 ⇑t (fun k => heisToFree E E₂ (gammaFam n q R k)) x = ![x .tau, x .tau] := by
  let w := fun k => heisToFree E E₂ (gammaFam n q R k)
  have hsum := sum_scalarFox_eq_zero_of_endpoint ⇑t hA2 htriv w hend x
  have hzero : heisD1 ⇑t w x 0 = x .tau := by
    change (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ (tameRelW n q))).a = _
    rw [← heisEvalZ_eq_lift, heisA_tameRelW_unram t x 0 E E₂ hA2 (htriv .tau) hqe]
    exact inv_smul_eq_iff.mpr (htriv .sigma (x .tau)).symm
  have hone : heisD1 ⇑t w x 1 = x .tau := by
    apply add_left_cancel (a := x .tau)
    rw [← hzero, ← Fin.sum_univ_two, hsum, hzero, hA2]
  funext k
  fin_cases k
  · exact hzero
  · exact hone

/-- Subtract the first relator row from the second; the inverse adds it back. -/
def scalarRowElimination (A : Type*) [AddCommGroup A] : (Fin 2 → A) ≃+ (Fin 2 → A) where
  toFun v := ![v 0, v 1 - v 0]
  invFun v := ![v 0, v 1 + v 0]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

@[simp] theorem scalarRowElimination_diagonal {A : Type*} [AddCommGroup A] (a : A) :
    scalarRowElimination A ![a, a] = ![a, 0] := by
  ext i
  fin_cases i <;> simp [scalarRowElimination]

variable {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
  [AddCommGroup A] [DistribMulAction C A]

/-- Literal all-cochain scalar rows of the actual normalized/corrected pair splice.
The sigma and every wild column vanish; both tau entries are identity. -/
theorem pairSplice_scalar_rows
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a)
    (x : Generator (2+2*h) → A) :
    heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
      (4 * Monoid.exponent C)) x = ![x .tau, x .tau] := by
  have hN := fourMulExponent_ne_zero_and_even C
  apply scalarFox_rows_of_endpoint t _ _ hA2 htriv hqe _ ?_ x
  exact isStokesEndpoint_tameSplice
    (headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP hN.1 hN.2)
    (pinned_mCompact_endpoint hqe hN.1 hN.2)

/-- The pair scalar matrix is reduced by an explicit additive equivalence on relator rows. -/
theorem pairSplice_scalar_reducedFox
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a)
    (x : Generator (2+2*h) → A) :
    scalarRowElimination A
      (heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4 * Monoid.exponent C)) x) = ![x .tau, 0] := by
  rw [pairSplice_scalar_rows t halpha hq0 hqe j nuP hA2 htriv x,
    scalarRowElimination_diagonal]

/-- The arbitrary-unit mobile splice has exactly the same literal scalar matrix,
uniformly in both levels, charge and handle rank, including rank zero. -/
theorem mobileSplice_scalar_rows {r p : ℕ}
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a)
    (x : Generator (2+2*h) → A) :
    heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C)) x = ![x .tau, x .tau] := by
  have hN := fourMulExponent_ne_zero_and_even C
  apply scalarFox_rows_of_endpoint t _ _ hA2 htriv hqe _ ?_ x
  exact isStokesEndpoint_tameSplice
    (mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP hN.1 hN.2)
    (pinned_mCompact_endpoint hqe hN.1 hN.2)

/-- Explicit scalar row elimination for the actual mobile source, on all cochains. -/
theorem mobileSplice_scalar_reducedFox {r p : ℕ}
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a)
    (x : Generator (2+2*h) → A) :
    scalarRowElimination A
      (heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C)) x) = ![x .tau, 0] := by
  rw [mobileSplice_scalar_rows t halpha hq0 hqe eta nuP hA2 htriv x,
    scalarRowElimination_diagonal]

#print axioms sum_scalarFox_eq_zero_of_endpoint
#print axioms scalarFox_rows_of_endpoint
#print axioms scalarRowElimination
#print axioms scalarRowElimination_diagonal
#print axioms pairSplice_scalar_rows
#print axioms pairSplice_scalar_reducedFox
#print axioms mobileSplice_scalar_rows
#print axioms mobileSplice_scalar_reducedFox

end
end GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal

