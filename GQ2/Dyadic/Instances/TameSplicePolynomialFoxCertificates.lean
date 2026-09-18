/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceFoxCertificates
import GQ2.Dyadic.SigmaNormalFoxPolynomialInverse

/-!
# Full identity-pivot Fox records with literal inverse coefficients

The inverse of the unramified pivot is encoded in the original FoxCoeff grammar
as a finite sum of existing integer-power generator atoms. Its length is derived
from the finite action order, which is odd when the two-primary sigma action is
trivial; the ambient element is not assumed to have odd order.

The three original FoxRowOp steps scale the first row by S, subtract it from the
second, and scale the second by the explicit polynomial. The last scale carries
Id-S^-1 as its formal inverse and proves both inverse products. The concrete
pair/mobile producers have literal identity-pivot targets at tau and x2 and pin
the actual changed word and lift-level resolver in the FoxCertificate type.
-/

namespace GQ2.Dyadic.Instances.TameSplicePolynomialFoxCertificates
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words MarkedCore
open SigmaNormalFoxElimination SigmaNormalFoxPolynomialInverse
open Instances.TameSpliceFoxCertificates Instances.TameSpliceUnramifiedFoxRows
open Instances.EvenMHeadHandlePairSpliceSupply Instances.MpcMobileNuSource

/-- A literal finite sum of odd powers in the original coefficient grammar.
The sign is an integer exponent parameter, not an abstract inverse atom. -/
def oddPowerCoeff {n : ℕ} (g : Generator n) (sign : ℤ) : ℕ → FoxCoeff (TameSym n)
  | 0 => .zero
  | k+1 => .add (oddPowerCoeff g sign k)
      (.atom (.gen g (sign * ((2*k+1 : ℕ) : ℤ))))

variable {n : ℕ} {C A : Type} [Group C] [AddCommGroup A] [DistribMulAction C A]

theorem oddPowerCoeff_eval (t : Marking n C) (proj : AddMonoid.End A)
    (g : Generator n) (sign : ℤ) (k : ℕ) (a : A) :
    (oddPowerCoeff g sign k).eval (TameSym.toEnd t proj) a =
      ∑ j ∈ Finset.range k, ((t g)^sign)^(2*j+1) • a := by
  induction k with
  | zero => simp [oddPowerCoeff]
  | succ k ih =>
    rw [oddPowerCoeff, FoxCoeff.eval_add_apply, ih, Finset.sum_range_succ]
    simp only [FoxCoeff.eval_atom_apply, TameSym.toEnd_gen_apply,
      zpow_mul, zpow_natCast]

/-- The inverse-power polynomial is represented by generator-power atoms only. -/
theorem oddPowerCoeff_neg_one_eval (t : Marking n C) (proj : AddMonoid.End A)
    (g : Generator n) (k : ℕ) (a : A) :
    (oddPowerCoeff g (-1) k).eval (TameSym.toEnd t proj) a =
      oddInversePolynomial (t g) k a := by
  rw [oddPowerCoeff_eval, oddInversePolynomial_apply]
  simp

/-- The original formal coefficient for Id-S^-1. -/
def unramPivotCoeff (n : ℕ) : FoxCoeff (TameSym n) :=
  .add .one (.neg (.atom (.gen .sigma (-1))))

theorem unramPivotCoeff_eval (t : Marking n C) (proj : AddMonoid.End A) (a : A) :
    (unramPivotCoeff n).eval (TameSym.toEnd t proj) a = a-t.σ⁻¹ • a := by
  simp [unramPivotCoeff, sub_eq_add_neg]

variable [Finite C] [Finite A]

/-- The polynomial length is determined by the finite ACTION order, not ambient order. -/
def sigmaActionHalfPeriod (t : Marking n C) : ℕ :=
  orderOf (MulAction.toPermHom C A t.σ) / 2

theorem sigmaActionHalfPeriod_period (t : Marking n C)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a) (a : A) :
    t.σ^(2*sigmaActionHalfPeriod (A := A) t+1) • a=a := by
  have ho := odd_actionOrder_of_powOmega2_trivial t.σ hsigma2
  have hn : orderOf (MulAction.toPermHom C A t.σ) =
      2*sigmaActionHalfPeriod (A := A) t+1 := by
    have := Nat.odd_iff.mp ho
    dsimp [sigmaActionHalfPeriod]
    omega
  rw [← hn]
  exact pow_actionOrder_smul t.σ a

/-- Three original-format row operations: scale by S, subtract first row,
then apply the displayed inverse polynomial, carrying Id-S^-1 as its inverse. -/
def unramIdentityOps (n k : ℕ) : List (FoxRowOp (TameSym n)) :=
  [.scaleFst (.atom (.gen .sigma 1)) (.atom (.gen .sigma (-1))),
   .addSnd (.neg .one),
   .scaleSnd (oddPowerCoeff .sigma (-1) k) (unramPivotCoeff n)]

theorem unramIdentityOps_invertible
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a) :
    ∀ op ∈ unramIdentityOps n (sigmaActionHalfPeriod (A := A) t),
      op.Invertible (TameSym.splitEnd (A := A) t) := by
  intro op hop
  simp only [unramIdentityOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl
  · constructor
    · apply AddMonoidHom.ext
      intro a
      change (t.σ^(1:ℤ)) • ((t.σ^(-1:ℤ)) • a)=a
      simp
    · apply AddMonoidHom.ext
      intro a
      change (t.σ^(-1:ℤ)) • ((t.σ^(1:ℤ)) • a)=a
      simp
  · trivial
  · change _ * _ = 1 ∧ _ * _ = 1
    constructor <;> apply AddMonoidHom.ext <;> intro a
    · change (oddPowerCoeff .sigma (-1) _).eval (TameSym.toEnd t 1)
        ((unramPivotCoeff n).eval (TameSym.toEnd t 1) a)=a
      rw [unramPivotCoeff_eval, oddPowerCoeff_neg_one_eval]
      exact polynomial_sub_inv_smul t.σ _ hA2 hfpf
        (sigmaActionHalfPeriod_period t hsigma2) a
    · change (unramPivotCoeff n).eval (TameSym.toEnd t 1)
        ((oddPowerCoeff .sigma (-1) _).eval (TameSym.toEnd t 1) a)=a
      rw [unramPivotCoeff_eval, oddPowerCoeff_neg_one_eval]
      exact sub_inv_smul_polynomial t.σ _ hA2 hfpf
        (sigmaActionHalfPeriod_period t hsigma2) a

/-- Exact finite-polynomial replay on the complete triangular pair of rows. -/
theorem unramIdentityOps_replay
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a) (a b : A) :
    FoxRowOp.listHom (TameSym.splitEnd (A := A) t)
      (unramIdentityOps n (sigmaActionHalfPeriod (A := A) t))
      (t.σ⁻¹ • a, a+(b-t.σ⁻¹ • b)) = (a,b) := by
  simp only [unramIdentityOps, FoxRowOp.listHom_cons, FoxRowOp.listHom_nil,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, FoxRowOp.toHom_scaleFst_apply,
    FoxRowOp.toHom_addSnd_apply, FoxRowOp.toHom_scaleSnd_apply,
    FoxCoeff.eval_atom_apply, FoxCoeff.eval_neg_apply, FoxCoeff.eval_one_apply,
    TameSym.splitEnd, TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_one,
    smul_inv_smul]
  rw [show a+(b-t.σ⁻¹ • b)+(-a)=b-t.σ⁻¹ • b by abel,
    oddPowerCoeff_neg_one_eval, Marking.apply_sigma,
    polynomial_sub_inv_smul t.σ _ hA2 hfpf (sigmaActionHalfPeriod_period t hsigma2)]

private def certificateOfRows {q : ℕ}
    (t : Marking n C) (R : PWord (Generator n)) (j : Fin (n+1))
    (hA2 : ∀ a : A, a+a=0) (hfpf : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hrow : ∀ x, heisD1 (A := A) ⇑t
      (pinnedResolvedFamily n q R (4*Monoid.exponent C)) x =
      ![t.σ⁻¹ • x .tau, x .tau+(x (.wild j)-t.σ⁻¹ • x (.wild j))]) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW n q) R) where
  rowOps := unramIdentityOps n (sigmaActionHalfPeriod (A := A) t)
  colOps := []
  target := ⟨.single .tau, .single (.wild j)⟩
  rowOps_invertible := unramIdentityOps_invertible t hA2 hfpf hsigma2
  colOps_invertible := by simp
  verifies := by
    apply AddMonoidHom.ext
    intro x
    rw [foxApplyOps_apply, FoxColOp.listHom_nil, AddMonoidHom.id_apply,
      foxJacobian_pinned_apply t hA2, hrow, FoxNormalForm.toHom_apply,
      FoxRowNormalForm.single_toHom_apply, FoxRowNormalForm.single_toHom_apply]
    exact unramIdentityOps_replay t hA2 hfpf hsigma2 (x .tau) (x (.wild j))


/-- Full identity-pivot original Fox certificate of the actual pair splice,
with its inverse represented by a finite sum of existing generator-power atoms. -/
def pairSplice_FoxCertificate_unramified_identity
    {alpha h q : ℕ} [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) (4*Monoid.exponent C) l)=1) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)) :=
  certificateOfRows t _ (x2Idx h) hA2 hsigma hsigma2
    (pairSplice_unramified_rows t halpha hq0 hqe j nuP
      hA2 hwild htau hsigma hsigma2 hr)

/-- Full identity-pivot original Fox certificate of the actual mobile splice,
with its inverse represented by a finite sum of existing generator-power atoms. -/
def mobileSplice_FoxCertificate_unramified_identity {r p : ℕ}
    {alpha h q : ℕ} [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h)) (4*Monoid.exponent C) l)=1) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))) :=
  certificateOfRows t _ (x2Idx h) hA2 hsigma hsigma2
    (mobileSplice_unramified_rows t halpha hq0 hqe eta nuP
      hA2 hwild htau hsigma hsigma2 hr)

#print axioms oddPowerCoeff
#print axioms oddPowerCoeff_eval
#print axioms oddPowerCoeff_neg_one_eval
#print axioms unramPivotCoeff
#print axioms unramPivotCoeff_eval
#print axioms sigmaActionHalfPeriod
#print axioms sigmaActionHalfPeriod_period
#print axioms unramIdentityOps
#print axioms unramIdentityOps_invertible
#print axioms unramIdentityOps_replay
#print axioms pairSplice_FoxCertificate_unramified_identity
#print axioms mobileSplice_FoxCertificate_unramified_identity

end
end GQ2.Dyadic.Instances.TameSplicePolynomialFoxCertificates

