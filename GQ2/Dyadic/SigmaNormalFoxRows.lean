/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalFoxElimination
import GQ2.Dyadic.Certificates.Mpc

/-!
# The explicit unramified Fox normal matrix

This specializes operator-valued row elimination to a finite unramified nontrivial action.
The first pivot is sigma inverse, the second is one minus sigma inverse, and the remaining
off-diagonal entry is the actual tau derivative of the word. A comparison on doubly-normal
cochains and the chain-square identity suffice to determine the full matrix, not just its
kernel. Both pivot inverses and all row operations are provided as additive equivalences.
-/

namespace GQ2.Dyadic.SigmaNormalFoxElimination
noncomputable section
open GQ2 GQ2.Dyadic GQ2.FoxH Count Certificates
open GQ2.Dyadic.Certificates.MProcyclic

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- The action of a group element, with its literal inverse action. -/
def actionEquiv (c : C) : A ≃+ A where
  toFun a := c • a
  invFun a := c⁻¹ • a
  left_inv a := inv_smul_smul c a
  right_inv a := smul_inv_smul c a
  map_add' a b := smul_add c a b

/-- The second pivot is invertible because the finite coefficient action has no fixed vectors. -/
def oneSubInvAction [Finite A] (sigma : C)
    (hfpf : ∀ a : A, sigma • a = a → a = 0) : A ≃+ A := by
  let d : A →+ A := AddMonoidHom.id A - (actionEquiv (A := A) sigma⁻¹).toAddMonoidHom
  have hsurj : Function.Surjective d := by
    intro b
    obtain ⟨a, ha⟩ := surjective_smul_sub_of_fixedPointFree
      (fun v hv ↦ hfpf v (inv_smul_eq_iff.mp hv).symm) (-b)
    change sigma⁻¹ • a - a = -b at ha
    refine ⟨a, ?_⟩
    change a - sigma⁻¹ • a = b
    calc
      a - sigma⁻¹ • a = -(sigma⁻¹ • a - a) := by abel
      _ = b := by rw [ha, neg_neg]
  exact AddEquiv.ofBijective d ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

@[simp] theorem oneSubInvAction_apply [Finite A] (sigma : C)
    (hfpf : ∀ a : A, sigma • a = a → a = 0) (a : A) :
    oneSubInvAction sigma hfpf a = a - sigma⁻¹ • a := rfl

/-- The sigma column is zero: it is precisely the image of the coboundary column, which
is onto the sigma slot because sigma minus one is invertible. -/
theorem sigma_column_zero [Finite A] {n : ℕ}
    (t : Marking n C) (d : (Generator n → A) →+ (Fin 2 → A))
    (htau : ∀ a : A, t.τ • a = a)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a = a)
    (hsigma : ∀ a : A, t.σ • a = a → a = 0)
    (hsquare : ∀ a : A, d (heisD0 ⇑t a) = 0) (b : A) :
    d (Pi.single .sigma b) = 0 := by
  obtain ⟨a, ha⟩ := surjective_smul_sub_of_fixedPointFree hsigma b
  have hcol : heisD0 ⇑t a = Pi.single .sigma b := by
    funext g
    cases g with
    | sigma => change t.σ • a - a = b; exact ha
    | tau => simp [heisD0_apply, htau]
    | wild i => simp [heisD0_apply, hwild]
  rw [← hcol]
  exact hsquare a

/-- An actual word's normalized first-jet identity gives an explicit reduced Fox matrix.
The conclusion is a matrix identity on ALL cochains, not only cocycles. -/
theorem heisD1_reduced_of_normal [Finite C] [Finite A] {n q : ℕ}
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (j : Fin (n+1))
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a=a)
    (hq : Even q) (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hres : ResolverLifts E (WordLift A C))
    (hsquare : ∀ a : A, heisD1 ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q R l))
      (heisD0 ⇑t a)=0)
    (hnormal : ∀ x : Generator n → A, x .sigma=0 → x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a = x (.wild j) - t.σ⁻¹ • x (.wild j))
    (x : Generator n → A) :
    let d := heisD1 (A := A) ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q R l))
    rowElimination (actionEquiv t.σ⁻¹) (oneSubInvAction t.σ hsigma)
      (tauColumn d) (d x) = ![x .tau, x (.wild j)] := by
  let d := heisD1 (A := A) ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q R l))
  apply reduced_rows_of_normal d (actionEquiv t.σ⁻¹) (oneSubInvAction t.σ hsigma) j
  · intro y
    change (FreeGroup.lift (heisGen ⇑t y 0) (heisToFree E E₂ (tameRelW n q))).a = _
    rw [← heisEvalZ_eq_lift]
    exact (heisEvalZ_a_eq_foxD hres ⇑t y 0 _).trans
      (foxD_tameRelW_unram t E E₂ hA₂ htau hq y)
  · exact sigma_column_zero t d htau hwild hsigma hsquare
  · intro y hys hyt
    change (FreeGroup.lift (heisGen ⇑t y 0) (heisToFree E E₂ R)).a = _
    rw [← heisEvalZ_eq_lift]
    exact hnormal y hys hyt

#print axioms actionEquiv
#print axioms oneSubInvAction
#print axioms sigma_column_zero
#print axioms heisD1_reduced_of_normal

end
end GQ2.Dyadic.SigmaNormalFoxElimination
