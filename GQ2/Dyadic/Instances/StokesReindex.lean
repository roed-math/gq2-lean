/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.StokesMiddleEquiv

/-!
# Stokes duality under alphabet equivalence

Relabeling the generators of a resolved free presentation transports its word complex and
Stokes ladder through additive equivalences in degree one.  Consequently Stokes duality is
invariant under every alphabet equivalence.  This is rank- and presentation-independent.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

/-- Reindex additive coordinates along an equivalence of alphabets. -/
def stokesReindex {iota kappa A : Type*} [AddCommGroup A]
    (e : iota ≃ kappa) : (iota → A) ≃+ (kappa → A) :=
  AddEquiv.arrowCongr e (AddEquiv.refl A)

@[simp] theorem stokesReindex_apply {iota kappa A : Type*} [AddCommGroup A]
    (e : iota ≃ kappa) (x : iota → A) (j : kappa) :
    stokesReindex e x j = x (e.symm j) := rfl

@[simp] theorem stokesReindex_symm_apply {iota kappa A : Type*} [AddCommGroup A]
    (e : iota ≃ kappa) (x : kappa → A) (i : iota) :
    (stokesReindex e).symm x i = x (e i) := rfl

/-- Contravariant transport of elementary duals along an additive equivalence. -/
def stokesElemDualCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : ElemDual A ≃+ ElemDual B where
  toFun := dualMap e.symm.toAddMonoidHom
  invFun := dualMap e.toAddMonoidHom
  left_inv lam := by
    apply ElemDual.ext
    intro a
    simp
  right_inv lam := by
    apply ElemDual.ext
    intro b
    simp
  map_add' lam mu := by
    apply ElemDual.ext
    intro b
    rfl

@[simp] theorem stokesElemDualCongr_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (lam : ElemDual A) (b : B) :
    stokesElemDualCongr e lam b = lam (e.symm b) := rfl

@[simp] theorem stokesElemDualCongr_symm_apply
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (lam : ElemDual B) (a : A) :
    (stokesElemDualCongr e).symm lam a = lam (e a) := rfl

/-- Heisenberg evaluation commutes with simultaneous relabeling of the word, marking, and
primal and dual offsets. -/
theorem lift_heisGen_freeGroupCongr
    {iota kappa C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (e : iota ≃ kappa) (c : kappa → C) (x : iota → A)
    (y : iota → ElemDual A) (r : FreeGroup iota) :
    FreeGroup.lift
        (heisGen c (stokesReindex e x) (stokesReindex e y))
        (FreeGroup.freeGroupCongr e r) =
      FreeGroup.lift (heisGen (fun i ↦ c (e i)) x y) r := by
  have H : (FreeGroup.lift
        (heisGen c (stokesReindex e x) (stokesReindex e y))).comp
        (FreeGroup.freeGroupCongr e).toMonoidHom =
      FreeGroup.lift (heisGen (fun i ↦ c (e i)) x y) := by
    apply FreeGroup.ext_hom
    intro i
    simp [heisGen]
  exact DFunLike.congr_fun H r

/-- Stokes duality is invariant under an arbitrary equivalence of generator alphabets. -/
theorem stokesDuality_freeGroupCongr_iff
    {iota kappa rho C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    [Fintype rho]
    (e : iota ≃ kappa) (c : kappa → C) (w : rho → FreeGroup iota) :
    StokesDuality (fun i ↦ c (e i)) w A ↔
      StokesDuality c (fun k ↦ FreeGroup.freeGroupCongr e (w k)) A := by
  let eX : (iota → A) ≃+ (kappa → A) := stokesReindex e
  let eD : (iota → ElemDual A) ≃+ (kappa → ElemDual A) := stokesReindex e
  let eY : ElemDual (iota → ElemDual A) ≃+ ElemDual (kappa → ElemDual A) :=
    stokesElemDualCongr eD
  apply stokesQuasiIso_iff_middle_addEquiv
    (heisD0 (A := A) (fun i ↦ c (e i)))
    (heisD1 (A := A) (fun i ↦ c (e i)) w)
    (heisD0 (A := A) c)
    (heisD1 (A := A) c (fun k ↦ FreeGroup.freeGroupCongr e (w k)))
    (dualMap (heisD1 (A := ElemDual A) (fun i ↦ c (e i)) w))
    (dualMap (heisD0 (A := ElemDual A) (fun i ↦ c (e i))))
    (dualMap (heisD1 (A := ElemDual A) c
      (fun k ↦ FreeGroup.freeGroupCongr e (w k))))
    (dualMap (heisD0 (A := ElemDual A) c))
    heisEta0
    (heisEta1 (A := A) (fun i ↦ c (e i)) w)
    heisEta2
    (heisEta1 (A := A) c (fun k ↦ FreeGroup.freeGroupCongr e (w k)))
    eX eY
  · intro a
    funext j
    change c j • a - a = c (e (e.symm j)) • a - a
    rw [e.apply_symm_apply]
  · intro x
    funext k
    simp only [heisD1_apply]
    exact congrArg HeisLift.a
      (lift_heisGen_freeGroupCongr e c x (0 : iota → ElemDual A) (w k))
  · intro lam
    apply ElemDual.ext
    intro y
    change lam (heisD1 (A := ElemDual A) c
        (fun k ↦ FreeGroup.freeGroupCongr e (w k)) y) =
      lam (heisD1 (A := ElemDual A) (fun i ↦ c (e i)) w ((stokesReindex e).symm y))
    congr 1
    funext k
    simp only [heisD1_apply]
    simpa using congrArg HeisLift.a
      (lift_heisGen_freeGroupCongr e c ((stokesReindex e).symm y)
        (0 : iota → ElemDual (ElemDual A)) (w k))
  · intro lam
    apply ElemDual.ext
    intro mu
    change lam ((stokesReindex e).symm
        (heisD0 (A := ElemDual A) c mu)) =
      lam (heisD0 (A := ElemDual A) (fun i ↦ c (e i)) mu)
    congr 1
  · intro x
    apply ElemDual.ext
    intro y
    simp only [heisEta1_apply]
    apply Finset.sum_congr rfl
    intro k _
    simpa [eX, eD, eY] using congrArg HeisLift.z
      (lift_heisGen_freeGroupCongr e c x ((stokesReindex e).symm y) (w k))

#print axioms stokesReindex
#print axioms stokesElemDualCongr
#print axioms lift_heisGen_freeGroupCongr
#print axioms stokesDuality_freeGroupCongr_iff

end

end GQ2.Dyadic
