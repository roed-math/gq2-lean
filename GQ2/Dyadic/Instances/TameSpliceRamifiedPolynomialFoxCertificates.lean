/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSplicePolynomialFoxCertificates

/-!
# Full ramified identity-pivot Fox records with literal inverse polynomials

This extends the unramified original-format records to the ramified sector. The
first inverse is P(T)S, where P(T)=T+T^3+... and its length comes from the actual
odd tau action order. In particular, S is applied first: no commuting-head
assumption is made. A single formal sigma/tau transvection clears the tau column,
then two inverse-carrying formal row scales produce identity pivots at sigma/x2.

All coefficients use only the unchanged FoxCoeff constructors and integer-power
generator atoms. Both inverse products and the entire operation replay are
proved. The concrete records pin the actual pair/mobile source and lift-level
resolver, with all projected-action hypotheses retained and no relation-death
or assumed-matrix premise. These are arbitrary-rank records, not finite fixtures.
-/

namespace GQ2.Dyadic.Instances.TameSpliceRamifiedPolynomialFoxCertificates
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words MarkedCore
open SigmaNormalFoxPolynomialInverse SigmaRamifiedFoxElimination
open Instances.TameSpliceFoxCertificates Instances.TameSpliceRamifiedFoxNormal
open Instances.TameSplicePolynomialFoxCertificates
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSpliceSupply
open Instances.EvenMHeadHandlePairSplice
open Instances.MpcMobileNuSource Instances.MpcMobileSpliceSupply

variable {n : ℕ} {C A : Type} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- A literal tame norm sum in the unchanged formal coefficient grammar. -/
def normPowerCoeff {n : ℕ} (g : Generator n) : ℕ → FoxCoeff (TameSym n)
  | 0 => .zero
  | k+1 => .add (normPowerCoeff g k) (.atom (.gen g (k : ℤ)))

theorem normPowerCoeff_eval (t : Marking n C) (proj : AddMonoid.End A)
    (g : Generator n) (k : ℕ) (a : A) :
    (normPowerCoeff g k).eval (TameSym.toEnd t proj) a =
      ∑ j ∈ Finset.range k, (t g)^j • a := by
  induction k with
  | zero => simp [normPowerCoeff]
  | succ k ih =>
    rw [normPowerCoeff, FoxCoeff.eval_add_apply, ih, Finset.sum_range_succ]
    simp

/-- Formal U=S^-1(T-1). -/
def sigmaPivotCoeff (n : ℕ) : FoxCoeff (TameSym n) :=
  .comp (.atom (.gen .sigma (-1))) (.add (.atom (.gen .tau 1)) (.neg .one))

/-- Formal U^-1=P(T)S. Composition applies S FIRST. -/
def sigmaPivotInverseCoeff (n k : ℕ) : FoxCoeff (TameSym n) :=
  .comp (oddPowerCoeff .tau 1 k) (.atom (.gen .sigma 1))

/-- Formal D=-S^-1. -/
def wildPivotCoeff (n : ℕ) : FoxCoeff (TameSym n) :=
  .neg (.atom (.gen .sigma (-1)))

/-- Formal D^-1=-S. -/
def wildPivotInverseCoeff (n : ℕ) : FoxCoeff (TameSym n) :=
  .neg (.atom (.gen .sigma 1))

/-- Formal L=S^-1-N_q(T). -/
def tauColumnCoeff (n q : ℕ) : FoxCoeff (TameSym n) :=
  .add (.atom (.gen .sigma (-1))) (.neg (normPowerCoeff .tau q))

variable [Finite C] [Finite A]

/-- Half the odd order of the actual tau ACTION, not the ambient element. -/
def tauActionHalfPeriod (t : Marking n C) : ℕ :=
  orderOf (MulAction.toPermHom C A t.τ) / 2

theorem tauActionHalfPeriod_period (t : Marking n C)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) (a : A) :
    t.τ^(2*tauActionHalfPeriod (A := A) t+1) • a=a := by
  have ho := odd_actionOrder_of_powOmega2_trivial t.τ hodd
  have hn : orderOf (MulAction.toPermHom C A t.τ) =
      2*tauActionHalfPeriod (A := A) t+1 := by
    have := Nat.odd_iff.mp ho
    dsimp [tauActionHalfPeriod]
    omega
  rw [← hn]
  exact pow_actionOrder_smul t.τ a

private theorem oddPowerCoeff_tau_eval (t : Marking n C) (proj : AddMonoid.End A)
    (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) (a : A) :
    (oddPowerCoeff .tau 1 (tauActionHalfPeriod (A := A) t)).eval
      (TameSym.toEnd t proj) a = (tauSubOne t.τ hfpf).symm a := by
  apply (tauSubOne t.τ hfpf).injective
  rw [AddEquiv.apply_symm_apply, tauSubOne_apply]
  have hfpf' : ∀ a : A, t.τ⁻¹ • a=a → a=0 :=
    fun a ha => hfpf a (inv_smul_eq_iff.mp ha).symm
  have hp : ∀ a : A, (t.τ⁻¹)^(2*tauActionHalfPeriod (A := A) t+1) • a=a := by
    intro a
    rw [inv_pow]
    exact inv_smul_eq_iff.mpr (tauActionHalfPeriod_period t hodd a).symm
  have he : ∀ a : A,
      (oddPowerCoeff .tau 1 (tauActionHalfPeriod (A := A) t)).eval
        (TameSym.toEnd t proj) a =
      oddInversePolynomial t.τ⁻¹ (tauActionHalfPeriod (A := A) t) a := by
    intro a
    rw [oddPowerCoeff_eval, oddInversePolynomial_apply]
    simp
  rw [he]
  have hh := sub_inv_smul_polynomial t.τ⁻¹ _ hA2 hfpf' hp a
  simp only [inv_inv] at hh
  have hn (b : A) : -b=b := neg_eq_of_add_eq_zero_left (hA2 b)
  simpa only [sub_eq_add_neg, hn, add_comm] using hh

theorem ramifiedPivotCoeff_eval (t : Marking n C) (proj : AddMonoid.End A)
    (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) (a : A) :
    (sigmaPivotCoeff n).eval (TameSym.toEnd t proj) a = sigmaPivot t.σ t.τ hfpf a ∧
    (sigmaPivotInverseCoeff n (tauActionHalfPeriod (A := A) t)).eval
      (TameSym.toEnd t proj) a = (sigmaPivot t.σ t.τ hfpf).symm a ∧
    (wildPivotCoeff n).eval (TameSym.toEnd t proj) a = wildPivot t.σ a ∧
    (wildPivotInverseCoeff n).eval (TameSym.toEnd t proj) a =
      (wildPivot t.σ).symm a := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [sigmaPivotCoeff, sub_eq_add_neg]
  · simp only [sigmaPivotInverseCoeff, FoxCoeff.eval_comp_apply,
      FoxCoeff.eval_atom_apply, TameSym.toEnd_gen_apply, Marking.apply_sigma,
      zpow_one, oddPowerCoeff_tau_eval t proj hA2 hfpf hodd, sigmaPivot_symm_apply]
  · simp [wildPivotCoeff]
  · simp [wildPivotInverseCoeff, wildPivot_symm_apply]

omit [Finite C] [Finite A] in
theorem tauColumnCoeff_eval (t : Marking n C) (proj : AddMonoid.End A)
    (q : ℕ) (a : A) :
    (tauColumnCoeff n q).eval (TameSym.toEnd t proj) a =
      tauCoefficient t.σ t.τ q a := by
  simp [tauColumnCoeff, normPowerCoeff_eval, sub_eq_add_neg]

/-- Two row scalings, each carrying its literal formal inverse. -/
def ramifiedIdentityRowOps (n k : ℕ) : List (FoxRowOp (TameSym n)) :=
  [.scaleFst (sigmaPivotInverseCoeff n k) (sigmaPivotCoeff n),
   .scaleSnd (wildPivotInverseCoeff n) (wildPivotCoeff n)]

/-- Clear the tau column by replacing sigma with sigma-U^-1 L tau. -/
def ramifiedIdentityColOps (n q k : ℕ) : List (FoxColOp (Generator n) (TameSym n)) :=
  [.transvect .sigma .tau (.neg (.comp (sigmaPivotInverseCoeff n k) (tauColumnCoeff n q)))]

theorem ramifiedIdentityRowOps_invertible
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) :
    ∀ op ∈ ramifiedIdentityRowOps n (tauActionHalfPeriod (A := A) t),
      op.Invertible (TameSym.ramifiedEnd (A := A) t) := by
  intro op hop
  simp only [ramifiedIdentityRowOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · change _ * _ = 1 ∧ _ * _ = 1
    constructor <;> apply AddMonoidHom.ext <;> intro a
    · change (sigmaPivotInverseCoeff n _).eval (TameSym.toEnd t 0)
        ((sigmaPivotCoeff n).eval (TameSym.toEnd t 0) a)=a
      rw [(ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd a).1,
        (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.1]
      exact AddEquiv.symm_apply_apply _ _
    · change (sigmaPivotCoeff n).eval (TameSym.toEnd t 0)
        ((sigmaPivotInverseCoeff n _).eval (TameSym.toEnd t 0) a)=a
      rw [(ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd a).2.1,
        (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).1]
      exact AddEquiv.apply_symm_apply _ _
  · change _ * _ = 1 ∧ _ * _ = 1
    constructor <;> apply AddMonoidHom.ext <;> intro a
    · change (wildPivotInverseCoeff n).eval (TameSym.toEnd t 0)
        ((wildPivotCoeff n).eval (TameSym.toEnd t 0) a)=a
      rw [(ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd a).2.2.1,
        (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.2.2]
      exact AddEquiv.symm_apply_apply _ _
    · change (wildPivotCoeff n).eval (TameSym.toEnd t 0)
        ((wildPivotInverseCoeff n).eval (TameSym.toEnd t 0) a)=a
      rw [(ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd a).2.2.2,
        (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.2.1]
      exact AddEquiv.apply_symm_apply _ _

omit [Finite C] [Finite A] in
theorem ramifiedIdentityColOps_invertible (t : Marking n C) (q k : ℕ) :
    ∀ op ∈ ramifiedIdentityColOps n q k,
      op.Invertible (TameSym.ramifiedEnd (A := A) t) := by
  intro op hop
  simp only [ramifiedIdentityColOps, List.mem_singleton] at hop
  subst op
  intro heq
  cases heq

theorem ramifiedIdentityColOps_eval
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) (q : ℕ) (x : Generator n → A) :
    FoxColOp.listHom (TameSym.ramifiedEnd (A := A) t)
      (ramifiedIdentityColOps n q (tauActionHalfPeriod (A := A) t)) x =
      columnShear (sigmaPivot t.σ t.τ hfpf) (tauCoefficient t.σ t.τ q) x := by
  funext g
  simp only [ramifiedIdentityColOps, FoxColOp.listHom_cons, FoxColOp.listHom_nil,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, FoxColOp.toHom_transvect_apply]
  cases g with
  | sigma =>
    simp only [if_true, FoxCoeff.eval_neg_apply, FoxCoeff.eval_comp_apply,
      TameSym.ramifiedEnd, tauColumnCoeff_eval,
      (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.1, columnShear_sigma,
      sub_eq_add_neg]
  | tau => simp
  | wild i => simp

theorem ramifiedIdentityRowOps_replay
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) (a b : A) :
    FoxRowOp.listHom (TameSym.ramifiedEnd (A := A) t)
      (ramifiedIdentityRowOps n (tauActionHalfPeriod (A := A) t))
      (sigmaPivot t.σ t.τ hfpf a, wildPivot t.σ b) = (a,b) := by
  simp only [ramifiedIdentityRowOps, FoxRowOp.listHom_cons, FoxRowOp.listHom_nil,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, FoxRowOp.toHom_scaleFst_apply,
    FoxRowOp.toHom_scaleSnd_apply, TameSym.ramifiedEnd,
    (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.1,
    (ramifiedPivotCoeff_eval t 0 hA2 hfpf hodd _).2.2.2,
    AddEquiv.symm_apply_apply]

private def certificateOfRows {q : ℕ}
    (t : Marking n C) (R : PWord (Generator n)) (j : Fin (n+1))
    (hA2 : ∀ a : A, a+a=0) (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (hrow : ∀ x, heisD1 (A := A) ⇑t
      (pinnedResolvedFamily n q R (4*Monoid.exponent C)) x =
      ![sigmaPivot t.σ t.τ hfpf (x .sigma) + tauCoefficient t.σ t.τ q (x .tau),
        wildPivot t.σ (x (.wild j))]) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW n q) R) where
  rowOps := ramifiedIdentityRowOps n (tauActionHalfPeriod (A := A) t)
  colOps := ramifiedIdentityColOps n q (tauActionHalfPeriod (A := A) t)
  target := ⟨.single .sigma, .single (.wild j)⟩
  rowOps_invertible := ramifiedIdentityRowOps_invertible t hA2 hfpf hodd
  colOps_invertible := ramifiedIdentityColOps_invertible t q _
  verifies := by
    apply AddMonoidHom.ext
    intro x
    rw [foxApplyOps_apply, ramifiedIdentityColOps_eval t hA2 hfpf hodd,
      foxJacobian_pinned_apply t hA2, hrow, FoxNormalForm.toHom_apply,
      FoxRowNormalForm.single_toHom_apply, FoxRowNormalForm.single_toHom_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      columnShear_sigma, columnShear_tau, columnShear_wild,
      map_sub, AddEquiv.apply_symm_apply, sub_add_cancel]
    exact ramifiedIdentityRowOps_replay t hA2 hfpf hodd _ _

/-- Full identity-pivot original-format ramified certificate for an actual
splice. Its polynomial coefficients contain only existing generator atoms. -/
def tameSplice_FoxCertificate_ramified_identity
    {alpha h q : ℕ} {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a=pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q) (hq0 : q≠0) (hqe : Even q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C))) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice R (Words.MCompact.mCompactW alpha h))) :=
  certificateOfRows t _ (x2Idx h) hA2 hfpf hodd
    (fun x => (tameSplice_ramified_rows t pi hpi hsurj hA2 ht hq0 hqe hwild
      hfpf hodd R hspec hend x).trans (ramified_row_operators t q (x2Idx h) hfpf x))

/-- Concrete pair source, arbitrary handle rank, with literal sigma/x2 identity
pivots. No relator-death or unknown-matrix premise is added. -/
def pairSplice_FoxCertificate_ramified_identity
    {alpha h q : ℕ} {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
    (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)) :=
  tameSplice_FoxCertificate_ramified_identity t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)

/-- Concrete arbitrary-unit mobile source with literal sigma/x2 identity
pivots. All projected-action hypotheses of the genuine full row are retained. -/
def mobileSplice_FoxCertificate_ramified_identity {r p : ℕ}
    {alpha h q : ℕ} {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
    (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))) :=
  tameSplice_FoxCertificate_ramified_identity t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
    (mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)

#print axioms normPowerCoeff
#print axioms normPowerCoeff_eval
#print axioms sigmaPivotCoeff
#print axioms sigmaPivotInverseCoeff
#print axioms wildPivotCoeff
#print axioms wildPivotInverseCoeff
#print axioms tauColumnCoeff
#print axioms tauActionHalfPeriod
#print axioms tauActionHalfPeriod_period
#print axioms ramifiedPivotCoeff_eval
#print axioms tauColumnCoeff_eval
#print axioms ramifiedIdentityRowOps
#print axioms ramifiedIdentityColOps
#print axioms ramifiedIdentityRowOps_invertible
#print axioms ramifiedIdentityColOps_invertible
#print axioms ramifiedIdentityColOps_eval
#print axioms ramifiedIdentityRowOps_replay
#print axioms tameSplice_FoxCertificate_ramified_identity
#print axioms pairSplice_FoxCertificate_ramified_identity
#print axioms mobileSplice_FoxCertificate_ramified_identity

end
end GQ2.Dyadic.Instances.TameSpliceRamifiedPolynomialFoxCertificates
