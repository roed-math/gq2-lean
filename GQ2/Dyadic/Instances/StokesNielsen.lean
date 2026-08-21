/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.StokesReindex
import GQ2.Dyadic.Instances.StokesEndpointSubstitution

/-!
# Stokes duality under invertible free substitutions

An invertible substitution of free generators transports the primal and dual first jets by
additive equivalences.  Its substituted generator words may acquire central Heisenberg
coordinates, but their traced contribution is a mod-two exponent character and therefore
vanishes at a Stokes endpoint.  Hence Stokes duality is invariant under arbitrary Nielsen
changes, independently of rank, presentation, or dyadic branch.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH

/-- The lower marking induced by a free substitution. -/
def freeSubstMark {ι C : Type*} [Group C]
    (c : ι → C) (phi : ι → FreeGroup ι) : ι → C :=
  fun i ↦ FreeGroup.lift c (phi i)

/-- The primal first-jet coordinate change induced by a free substitution. -/
def freeSubstPrimal {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι) :
    (ι → A) →+ (ι → A) :=
  AddMonoidHom.mk'
    (fun x i ↦ (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (phi i)).a)
    (fun x y ↦ by
      funext i
      exact heisWord_a_add c x y (0 : ι → ElemDual A) (phi i))

/-- The dual first-jet coordinate change induced by a free substitution. -/
def freeSubstDual {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι) :
    (ι → ElemDual A) →+ (ι → ElemDual A) :=
  AddMonoidHom.mk'
    (fun y i ↦ (FreeGroup.lift (heisGen c (0 : ι → A) y) (phi i)).l)
    (fun y z ↦ by
      funext i
      exact heisWord_l_add c (0 : ι → A) y z (phi i))

@[simp] theorem freeSubstPrimal_apply {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι)
    (x : ι → A) (i : ι) :
    freeSubstPrimal c phi x i =
      (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (phi i)).a := rfl

@[simp] theorem freeSubstDual_apply {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι)
    (y : ι → ElemDual A) (i : ι) :
    freeSubstDual c phi y i =
      (FreeGroup.lift (heisGen c (0 : ι → A) y) (phi i)).l := rfl

/-- Evaluation after substitution is evaluation at the substituted marking. -/
theorem lift_lift_freeSubst {ι C : Type*} [Group C]
    (p : ι → C) (phi : ι → FreeGroup ι) (r : FreeGroup ι) :
    FreeGroup.lift p (FreeGroup.lift phi r) =
      FreeGroup.lift (fun i ↦ FreeGroup.lift p (phi i)) r := by
  have H : (FreeGroup.lift p).comp (FreeGroup.lift phi) =
      FreeGroup.lift (fun i ↦ FreeGroup.lift p (phi i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun H r

/-- The primal jet of a substituted generator word is the normalized primal coordinate. -/
theorem lift_heisGen_freeSubst_a {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι)
    (x : ι → A) (y : ι → ElemDual A) (i : ι) :
    (FreeGroup.lift (heisGen c x y) (phi i)).a = freeSubstPrimal c phi x i := by
  exact heisWord_a_indep c x y 0 (phi i)

/-- The dual jet of a substituted generator word is the normalized dual coordinate. -/
theorem lift_heisGen_freeSubst_l {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi : ι → FreeGroup ι)
    (x : ι → A) (y : ι → ElemDual A) (i : ι) :
    (FreeGroup.lift (heisGen c x y) (phi i)).l = freeSubstDual c phi y i := by
  exact heisWord_l_indep c x 0 y (phi i)

/-- Primal first jets compose contravariantly with free substitutions. -/
theorem freeSubstPrimal_comp {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi psi : ι → FreeGroup ι)
    (x : ι → A) (i : ι) :
    freeSubstPrimal (freeSubstMark c phi) psi (freeSubstPrimal c phi x) i =
      (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A))
        (FreeGroup.lift phi (psi i))).a := by
  let p : ι → HeisLift A C :=
    fun j ↦ FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (phi j)
  have hp : p = heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
      (0 : ι → ElemDual A) := by
    funext j
    apply HeisLift.ext
    · rfl
    · exact (heisWord_zero_dual c x (phi j)).1
    · exact (heisWord_zero_dual c x (phi j)).2
    · exact heisWord_g c x 0 (phi j)
  change (FreeGroup.lift
      (heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
        (0 : ι → ElemDual A)) (psi i)).a = _
  rw [← hp, ← lift_lift_freeSubst]

/-- Dual first jets compose contravariantly with free substitutions. -/
theorem freeSubstDual_comp {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi psi : ι → FreeGroup ι)
    (y : ι → ElemDual A) (i : ι) :
    freeSubstDual (freeSubstMark c phi) psi (freeSubstDual c phi y) i =
      (FreeGroup.lift (heisGen c (0 : ι → A) y)
        (FreeGroup.lift phi (psi i))).l := by
  let p : ι → HeisLift A C :=
    fun j ↦ FreeGroup.lift (heisGen c (0 : ι → A) y) (phi j)
  have hp : p = heisGen (freeSubstMark c phi) (0 : ι → A)
      (freeSubstDual c phi y) := by
    funext j
    ext
    · exact (heisWord_zero_prim c y (phi j)).1
    · rfl
    · exact (heisWord_zero_prim c y (phi j)).2
    · exact heisWord_g c 0 y (phi j)
  change (FreeGroup.lift
      (heisGen (freeSubstMark c phi) (0 : ι → A)
        (freeSubstDual c phi y)) (psi i)).l = _
  rw [← hp, ← lift_lift_freeSubst]

/-- Free substitution is exact on the zero-dual first-jet marking. -/
theorem lift_heisGen_zeroDual_freeSubst
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (x : ι → A) (r : FreeGroup ι) :
    FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (FreeGroup.lift phi r) =
      FreeGroup.lift
        (heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
          (0 : ι → ElemDual A)) r := by
  let p : ι → HeisLift A C :=
    fun j ↦ FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (phi j)
  have hp : p = heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
      (0 : ι → ElemDual A) := by
    funext j
    apply HeisLift.ext
    · rfl
    · exact (heisWord_zero_dual c x (phi j)).1
    · exact (heisWord_zero_dual c x (phi j)).2
    · exact heisWord_g c x 0 (phi j)
  rw [lift_lift_freeSubst]
  change FreeGroup.lift p r = _
  rw [hp]

/-- Free substitution is exact on the zero-primal first-jet marking. -/
theorem lift_heisGen_zeroPrimal_freeSubst
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (y : ι → ElemDual A)
    (r : FreeGroup ι) :
    FreeGroup.lift (heisGen c (0 : ι → A) y) (FreeGroup.lift phi r) =
      FreeGroup.lift
        (heisGen (freeSubstMark c phi) (0 : ι → A)
          (freeSubstDual c phi y)) r := by
  let p : ι → HeisLift A C :=
    fun j ↦ FreeGroup.lift (heisGen c (0 : ι → A) y) (phi j)
  have hp : p = heisGen (freeSubstMark c phi) (0 : ι → A)
      (freeSubstDual c phi y) := by
    funext j
    apply HeisLift.ext
    · exact (heisWord_zero_prim c y (phi j)).1
    · rfl
    · exact (heisWord_zero_prim c y (phi j)).2
    · exact heisWord_g c 0 y (phi j)
  rw [lift_lift_freeSubst]
  change FreeGroup.lift p r = _
  rw [hp]

/-- A coboundary first jet evaluates to conjugation by its coefficient. -/
theorem heisWord_d0_a
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (a : A) (r : FreeGroup ι) :
    (FreeGroup.lift
      (heisGen c (heisD0 c a) (0 : ι → ElemDual A)) r).a =
      FreeGroup.lift c r • a - a := by
  induction r using FreeGroup.induction_on with
  | C1 => simp
  | of i => simp [heisD0_apply, FreeGroup.lift_apply_of]
  | inv_of r ih =>
      rw [map_inv, HeisLift.inv_a, heisWord_g, ih, map_inv]
      simp only [smul_sub, inv_smul_smul, neg_sub]
  | mul r s ihr ihs =>
      rw [map_mul, HeisLift.mul_a, heisWord_g, ihr, ihs, map_mul]
      simp only [smul_sub, mul_smul]
      abel

/-- The substitution jet map carries coboundaries to coboundaries. -/
theorem freeSubstPrimal_heisD0
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (a : A) :
    freeSubstPrimal c phi (heisD0 c a) =
      heisD0 (freeSubstMark c phi) a := by
  funext i
  exact heisWord_d0_a c a (phi i)

/-- The dual substitution jet map carries dual coboundaries to coboundaries. -/
theorem freeSubstDual_heisD0
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (lam : ElemDual A) :
    freeSubstDual (A := A) c phi (heisD0 (A := ElemDual A) c lam) =
      heisD0 (A := ElemDual A) (freeSubstMark c phi) lam := by
  funext i
  change (FreeGroup.lift
      (heisGen c (0 : ι → A) (heisD0 (A := ElemDual A) c lam)) (phi i)).l = _
  rw [heisWord_l_eq_dual_a]
  exact heisWord_d0_a c lam (phi i)

/-- The dual jet is the primal substitution jet for the dual coefficient module. -/
theorem freeSubstDual_eq_primal
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (y : ι → ElemDual A) :
    freeSubstDual (A := A) c phi y =
      freeSubstPrimal (A := ElemDual A) c phi y := by
  funext i
  exact heisWord_l_eq_dual_a c 0 y (phi i)

/-- The first word differential after substitution is conjugate by the primal jet map. -/
theorem heisD1_freeSubst
    {ι rho C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (w : rho → FreeGroup ι) (phi : ι → FreeGroup ι)
    (x : ι → A) :
    heisD1 c (fun k ↦ FreeGroup.lift phi (w k)) x =
      heisD1 (freeSubstMark c phi) w (freeSubstPrimal c phi x) := by
  funext k
  exact congrArg HeisLift.a
    (lift_heisGen_zeroDual_freeSubst c phi x (w k))

/-- Mutually inverse free substitutions induce an additive equivalence on primal jets. -/
def freeSubstPrimalEquiv {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi psi : ι → FreeGroup ι)
    (hphi : ∀ i, FreeGroup.lift psi (phi i) = FreeGroup.of i)
    (hpsi : ∀ i, FreeGroup.lift phi (psi i) = FreeGroup.of i) :
    (ι → A) ≃+ (ι → A) where
  toFun := freeSubstPrimal c phi
  invFun := freeSubstPrimal (freeSubstMark c phi) psi
  left_inv x := by
    funext i
    rw [freeSubstPrimal_comp, hpsi]
    simp
  right_inv x := by
    funext i
    have hc : freeSubstMark (freeSubstMark c phi) psi = c := by
      funext j
      simp only [freeSubstMark]
      change FreeGroup.lift (fun i ↦ FreeGroup.lift c (phi i)) (psi j) = c j
      rw [← lift_lift_freeSubst, hpsi]
      simp
    have h := freeSubstPrimal_comp
      (freeSubstMark c phi) psi phi x i
    rw [hc] at h
    rw [h, hphi]
    simp
  map_add' := map_add (freeSubstPrimal c phi)

/-- Mutually inverse free substitutions induce an additive equivalence on dual jets. -/
def freeSubstDualEquiv {ι C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A] (c : ι → C) (phi psi : ι → FreeGroup ι)
    (hphi : ∀ i, FreeGroup.lift psi (phi i) = FreeGroup.of i)
    (hpsi : ∀ i, FreeGroup.lift phi (psi i) = FreeGroup.of i) :
    (ι → ElemDual A) ≃+ (ι → ElemDual A) where
  toFun := freeSubstDual c phi
  invFun := freeSubstDual (freeSubstMark c phi) psi
  left_inv y := by
    funext i
    rw [freeSubstDual_comp, hpsi]
    simp
  right_inv y := by
    funext i
    have hc : freeSubstMark (freeSubstMark c phi) psi = c := by
      funext j
      simp only [freeSubstMark]
      change FreeGroup.lift (fun i ↦ FreeGroup.lift c (phi i)) (psi j) = c j
      rw [← lift_lift_freeSubst, hpsi]
      simp
    have h := freeSubstDual_comp
      (freeSubstMark c phi) psi phi y i
    rw [hc] at h
    rw [h, hphi]
    simp
  map_add' := map_add (freeSubstDual c phi)

/-- A marking differs from its zero-central normalization by a central character. -/
theorem lift_central_normalization_z
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (p : ι → HeisLift A C) (r : FreeGroup ι) :
    (FreeGroup.lift p r).z =
      (FreeGroup.lift
        (fun i ↦ ⟨(p i).a, (p i).l, 0, (p i).g⟩ : ι → HeisLift A C) r).z +
      Multiplicative.toAdd
        (FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (p i).z) r) := by
  let q : ι → HeisLift A C := fun i ↦ ⟨(p i).a, (p i).l, 0, (p i).g⟩
  let eps : ι → Multiplicative (ZMod 2) :=
    fun i ↦ Multiplicative.ofAdd (p i).z
  let rhs : FreeGroup ι →* HeisLift A C := {
    toFun w := FreeGroup.lift q w * HeisLift.zcHom (FreeGroup.lift eps w)
    map_one' := by simp
    map_mul' u v := by
      simp only [map_mul]
      exact Commute.mul_mul_mul_comm
        (HeisLift.zcHom_comm (FreeGroup.lift eps u) (FreeGroup.lift q v)).symm _ _
  }
  have H : FreeGroup.lift p = rhs := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of]
    ext <;> simp [rhs, q, eps, HeisLift.zcHom, HeisLift.zc]
  rw [H]
  simp [rhs, q, eps, HeisLift.zcHom, HeisLift.zc, HeisLift.mul_z]

/-- The mixed coordinate after free substitution is the normalized mixed coordinate plus the
central exponent character of the substituted generator words. -/
theorem lift_heisGen_freeSubst_z
    {ι C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (c : ι → C) (phi : ι → FreeGroup ι) (x : ι → A)
    (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) (FreeGroup.lift phi r)).z =
      (FreeGroup.lift
        (heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
          (freeSubstDual c phi y)) r).z +
      Multiplicative.toAdd (FreeGroup.lift
        (fun i ↦ Multiplicative.ofAdd
          (FreeGroup.lift (heisGen c x y) (phi i)).z) r) := by
  let p : ι → HeisLift A C := fun i ↦ FreeGroup.lift (heisGen c x y) (phi i)
  have hnorm :
      (fun i ↦ ⟨(p i).a, (p i).l, 0, (p i).g⟩ : ι → HeisLift A C) =
        heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
          (freeSubstDual c phi y) := by
    funext i
    apply HeisLift.ext
    · exact lift_heisGen_freeSubst_a c phi x y i
    · exact lift_heisGen_freeSubst_l c phi x y i
    · rfl
    · exact heisWord_g c x y (phi i)
  rw [lift_lift_freeSubst]
  have H := lift_central_normalization_z p r
  rw [hnorm] at H
  exact H

/-- At a Stokes endpoint, the traced mixed coordinate is unchanged by central normalization
of the substituted generators. -/
theorem heisEta1_freeSubst
    {ι rho C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    [Fintype ι] [DecidableEq ι] [Fintype rho]
    (c : ι → C) (w : rho → FreeGroup ι) (phi : ι → FreeGroup ι)
    (hend : IsStokesEndpoint w) (x : ι → A) (y : ι → ElemDual A) :
    heisEta1 c (fun k ↦ FreeGroup.lift phi (w k)) x y =
      heisEta1 (freeSubstMark c phi) w
        (freeSubstPrimal c phi x) (freeSubstDual c phi y) := by
  let f : ι → Multiplicative (ZMod 2) := fun i ↦
    Multiplicative.ofAdd (FreeGroup.lift (heisGen c x y) (phi i)).z
  have hf : ∑ k, Multiplicative.toAdd (FreeGroup.lift f (w k)) = 0 :=
    sum_toAdd_lift_eq_zero_of_endpoint hend f
  simp only [heisEta1_apply]
  calc
    ∑ k, (FreeGroup.lift (heisGen c x y) (FreeGroup.lift phi (w k))).z =
        ∑ k, ((FreeGroup.lift
          (heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
            (freeSubstDual c phi y)) (w k)).z +
          Multiplicative.toAdd (FreeGroup.lift f (w k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact lift_heisGen_freeSubst_z c phi x y (w k)
    _ = (∑ k, (FreeGroup.lift
          (heisGen (freeSubstMark c phi) (freeSubstPrimal c phi x)
            (freeSubstDual c phi y)) (w k)).z) +
        ∑ k, Multiplicative.toAdd (FreeGroup.lift f (w k)) :=
      Finset.sum_add_distrib
    _ = _ := by rw [hf, add_zero]

/-- Stokes duality is invariant under an arbitrary invertible free-group substitution.

The first jets are transported by the substitution Jacobians.  Generator-wise central
normalization contributes a mod-two exponent character, whose traced value vanishes by the
endpoint condition. -/
theorem stokesDuality_freeSubst_iff
    {ι rho C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    [Fintype ι] [DecidableEq ι] [Fintype rho]
    (c : ι → C) (w : rho → FreeGroup ι) (phi psi : ι → FreeGroup ι)
    (hphi : ∀ i, FreeGroup.lift psi (phi i) = FreeGroup.of i)
    (hpsi : ∀ i, FreeGroup.lift phi (psi i) = FreeGroup.of i)
    (hend : IsStokesEndpoint w) :
    StokesDuality c (fun k ↦ FreeGroup.lift phi (w k)) A ↔
      StokesDuality (freeSubstMark c phi) w A := by
  let eX : (ι → A) ≃+ (ι → A) :=
    freeSubstPrimalEquiv c phi psi hphi hpsi
  let eD : (ι → ElemDual A) ≃+ (ι → ElemDual A) :=
    freeSubstPrimalEquiv (A := ElemDual A) c phi psi hphi hpsi
  let eY : ElemDual (ι → ElemDual A) ≃+ ElemDual (ι → ElemDual A) :=
    stokesElemDualCongr eD
  apply stokesQuasiIso_iff_middle_addEquiv
    (heisD0 (A := A) c)
    (heisD1 (A := A) c (fun k ↦ FreeGroup.lift phi (w k)))
    (heisD0 (A := A) (freeSubstMark c phi))
    (heisD1 (A := A) (freeSubstMark c phi) w)
    (dualMap (heisD1 (A := ElemDual A) c
      (fun k ↦ FreeGroup.lift phi (w k))))
    (dualMap (heisD0 (A := ElemDual A) c))
    (dualMap (heisD1 (A := ElemDual A) (freeSubstMark c phi) w))
    (dualMap (heisD0 (A := ElemDual A) (freeSubstMark c phi)))
    heisEta0
    (heisEta1 (A := A) c (fun k ↦ FreeGroup.lift phi (w k)))
    heisEta2
    (heisEta1 (A := A) (freeSubstMark c phi) w)
    eX eY
  · intro a
    exact (freeSubstPrimal_heisD0 c phi a).symm
  · intro x
    exact (heisD1_freeSubst c w phi x).symm
  · intro lam
    apply ElemDual.ext
    intro y
    change lam (heisD1 (A := ElemDual A) (freeSubstMark c phi) w y) =
      lam (heisD1 (A := ElemDual A) c
        (fun k ↦ FreeGroup.lift phi (w k)) (eD.symm y))
    congr 1
    rw [heisD1_freeSubst]
    exact congrArg (heisD1 (A := ElemDual A) (freeSubstMark c phi) w)
      (eD.apply_symm_apply y).symm
  · intro lam
    apply ElemDual.ext
    intro mu
    change lam (eD.symm (heisD0 (A := ElemDual A)
        (freeSubstMark c phi) mu)) =
      lam (heisD0 (A := ElemDual A) c mu)
    congr 1
    apply eD.injective
    rw [eD.apply_symm_apply]
    exact (freeSubstPrimal_heisD0 (A := ElemDual A) c phi mu).symm
  · intro x
    apply ElemDual.ext
    intro y
    change heisEta1 (A := A) (freeSubstMark c phi) w (eX x) y =
      heisEta1 (A := A) c (fun k ↦ FreeGroup.lift phi (w k)) x (eD.symm y)
    rw [heisEta1_freeSubst c w phi hend x (eD.symm y)]
    change heisEta1 (A := A) (freeSubstMark c phi) w
        (freeSubstPrimal c phi x) y =
      heisEta1 (A := A) (freeSubstMark c phi) w
        (freeSubstPrimal c phi x)
          (freeSubstDual c phi (eD.symm y))
    rw [freeSubstDual_eq_primal]
    exact congrArg
      (heisEta1 (A := A) (freeSubstMark c phi) w (freeSubstPrimal c phi x))
      (eD.apply_symm_apply y).symm

/-- Resolving a substituted profinite word is ordinary free substitution of the resolved
generator words. -/
theorem heisToFree_subst
    {X Y : Type*} (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (phi : X → PWord Y) (W : PWord X) :
    heisToFree E E₂ (PWord.subst phi W) =
      FreeGroup.lift (fun i ↦ heisToFree E E₂ (phi i)) (heisToFree E E₂ W) := by
  rw [heisToFree, PWord.evalZ_subst]
  exact evalZ_eq_lift_heisToFree
    (fun i ↦ PWord.evalZ FreeGroup.of E E₂ (phi i)) E E₂ W

/-- Resolved inverse word substitutions transport Stokes duality.  This is the direct bridge
from a syntactic Nielsen pair to the ordinary free-substitution theorem above. -/
theorem stokesDuality_heisToFree_subst_iff
    {ι rho C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    [Fintype ι] [DecidableEq ι] [Fintype rho]
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (c : ι → C) (W : rho → PWord ι) (phi psi : ι → PWord ι)
    (hphi : ∀ i, FreeGroup.lift (fun j ↦ heisToFree E E₂ (psi j))
      (heisToFree E E₂ (phi i)) = FreeGroup.of i)
    (hpsi : ∀ i, FreeGroup.lift (fun j ↦ heisToFree E E₂ (phi j))
      (heisToFree E E₂ (psi i)) = FreeGroup.of i)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (W k))) :
    StokesDuality c (fun k ↦ heisToFree E E₂ (PWord.subst phi (W k))) A ↔
      StokesDuality
        (freeSubstMark c (fun i ↦ heisToFree E E₂ (phi i)))
        (fun k ↦ heisToFree E E₂ (W k)) A := by
  have H := stokesDuality_freeSubst_iff (A := A) c
    (fun k ↦ heisToFree E E₂ (W k))
    (fun i ↦ heisToFree E E₂ (phi i))
    (fun i ↦ heisToFree E E₂ (psi i)) hphi hpsi hend
  simpa only [heisToFree_subst] using H

#print axioms stokesDuality_freeSubst_iff
#print axioms heisToFree_subst
#print axioms stokesDuality_heisToFree_subst_iff

#print axioms freeSubstMark
#print axioms freeSubstPrimal
#print axioms freeSubstDual
#print axioms lift_lift_freeSubst
#print axioms lift_heisGen_freeSubst_a
#print axioms lift_heisGen_freeSubst_l
#print axioms freeSubstPrimal_comp
#print axioms freeSubstDual_comp
#print axioms lift_heisGen_zeroDual_freeSubst
#print axioms lift_heisGen_zeroPrimal_freeSubst
#print axioms heisWord_d0_a
#print axioms freeSubstPrimal_heisD0
#print axioms freeSubstDual_heisD0
#print axioms freeSubstDual_eq_primal
#print axioms heisD1_freeSubst
#print axioms freeSubstPrimalEquiv
#print axioms freeSubstDualEquiv
#print axioms lift_central_normalization_z
#print axioms lift_heisGen_freeSubst_z
#print axioms heisEta1_freeSubst

end

end GQ2.Dyadic
