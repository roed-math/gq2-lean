/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LUniformHeisenbergResolver
import GQ2.Dyadic.Certificates.LFox
import GQ2.Dyadic.Certificates.Mpc
import GQ2.Roe.DualityAssembly

/-!
# The Roe complex is the uniform `L_sq` Stokes complex in degree one

This file records the word-level bridge needed to reuse the `q = 2`, `h = 0` Roe duality
theorem in the generic dyadic Stokes complex.  The old Roe development evaluates the intrinsic
`omega2`-word directly, whereas the generic development first replaces `omega2` by the fixed
integer `omega2Exp (4 * exponent C)`.  The uniform Heisenberg exponent theorem shows that these
are the same evaluation, simultaneously for every elementary coefficient module.

The remaining bridge to `StokesDuality` is homological algebra: reindex the four generator
coordinates and the two relator coordinates, and transport Roe's quasi-isomorphism across those
additive equivalences.  No further word identity is needed for the wild relator.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words.LSq Certificates.MProcyclic

/-- The constant uniform resolver really is a `ResolverLifts` witness for the full Heisenberg
lift, not merely for either of its first-jet projections. -/
theorem resolverLifts_uniformHeis
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0) :
    ResolverLifts
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (HeisLift A C) := by
  intro p
  rw [zpow_natCast]
  exact powOmega2_pow_eq p
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) p)
    (fourMulExponent_ne_zero_and_even C).1

/-- The generic Heisenberg generator marking at the `n = 1` adapter is the old Roe
`heisMarking`, generator for generator. -/
theorem heisGen_q2Offsets
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    heisGen (⇑(Marking.ofQ2 t)) (q2Offsets x) (q2Offsets y)
      = ⇑(Marking.ofQ2 (heisMarking t x y)) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | k + 2, h => exact absurd h (by omega)

/-- The four-coordinate adapter preserves the zero vector. -/
@[simp] theorem q2Offsets_zero {V : Type*} [Zero V] :
    q2Offsets (0 : Fin 4 → V) = (0 : Generator 1 → V) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | k + 2, h => exact absurd h (by omega)

/-- The four-generator adapter as an additive equivalence. -/
def q2OffsetsAddEquiv {A : Type*} [AddCommGroup A] :
    (Fin 4 → A) ≃+ (Generator 1 → A) where
  toFun := q2Offsets
  invFun := q2OffsetsInv
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv := q2Offsets_q2OffsetsInv
  map_add' x y := by
    funext g
    cases g with
    | sigma => rfl
    | tau => rfl
    | wild i =>
        obtain ⟨v, hv⟩ := i
        match v, hv with
        | 0, _ => rfl
        | 1, _ => rfl
        | k + 2, h => exact absurd h (by omega)

@[simp] theorem q2OffsetsAddEquiv_apply {A : Type*} [AddCommGroup A] (x : Fin 4 → A) :
    q2OffsetsAddEquiv x = q2Offsets x := by
  rfl

@[simp] theorem q2OffsetsAddEquiv_symm_apply {A : Type*} [AddCommGroup A]
    (x : Generator 1 → A) :
    q2OffsetsAddEquiv.symm x = q2OffsetsInv x := by
  rfl

/-- Identify the generic two-relator output family with Roe's ordered product. -/
def finTwoProdAddEquiv {A : Type*} [AddCommGroup A] : (Fin 2 → A) ≃+ A × A where
  toFun v := (v 0, v 1)
  invFun p := ![p.1, p.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl

@[simp] theorem finTwoProdAddEquiv_apply {A : Type*} [AddCommGroup A] (v : Fin 2 → A) :
    finTwoProdAddEquiv v = (v 0, v 1) := rfl

@[simp] theorem finTwoProdAddEquiv_symm_apply {A : Type*} [AddCommGroup A] (p : A × A) :
    finTwoProdAddEquiv.symm p = ![p.1, p.2] := rfl

/-- The degree-zero differential is unchanged by the four-generator adapter. -/
theorem heisD0_ofQ2_eq_q2Offsets_d0
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (a : A) :
    heisD0 (A := A) (⇑(Marking.ofQ2 t)) a = q2Offsets (FoxH.d0 t a) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | k + 2, h => exact absurd h (by omega)

/-- Projecting the tame Heisenberg value to its primal first jet gives the old Roe tame row. -/
theorem heisMarking_tameValue_a
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).tameValue.a = (FoxH.liftMarking t x).tameValue.u := by
  have h := Marking.map_tameValue (agHom (A := A) (C := C)) (heisMarking t x y)
  exact congrArg WordLift.u h.symm

/-- Projecting the intrinsic Roe wild value to its primal first jet gives the old Roe wild
row. -/
theorem heisMarking_wildValueR_a
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).wildValueR.a = (FoxH.liftMarking t x).wildValueR.u := by
  have h := Marking.map_wildValueR (agHom (A := A) (C := C)) (heisMarking t x y)
  exact congrArg WordLift.u h.symm

/-- The tame half of the same comparison.  It is independent of the resolver; at `q = 2` the
generic tame word is literally Roe's tame relator after the four-letter reindexing. -/
theorem heisEvalZ_tameRelW_one_two_eq_tameValue
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    heisEvalZ (⇑(Marking.ofQ2 t)) (q2Offsets x) (q2Offsets y) E E₂
        (Certificates.tameRelW 1 2)
      = (heisMarking t x y).tameValue := by
  rw [heisEvalZ, Certificates.tameRelW]
  simp only [PWord.evalZ_mul, PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_zpow,
    PWord.evalZ_gen]
  rw [heisGen_q2Offsets]
  rfl

/-- At the uniform exponent, the second-order evaluation of the base `L_sq` wild word is
exactly Roe's intrinsic wild value.  This is the central (not only first-derivative) regression
needed to identify both `d¹` and the middle Stokes pairing. -/
theorem heisEvalZ_lSqW_zero_eq_wildValueR
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    heisEvalZ (⇑(Marking.ofQ2 t)) (q2Offsets x) (q2Offsets y)
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (lSqW 0)
      = (heisMarking t x y).wildValueR := by
  rw [heisEvalZ, evalZ_eq_evalFin_of_resolverLifts
    (resolverLifts_uniformHeis hA₂), heisGen_q2Offsets]
  exact evalFin_lSqW_zero_eq_wildValueR (heisMarking t x y) _ _

/-- The degree-one differential of the uniform generic `L_sq` complex is Roe's `d¹_R`, with
the target pair written as a `Fin 2` family and the source reindexed by `q2Offsets`. -/
theorem heisD1_lSqFam_zero_two_uniform_q2Offsets
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) :
    heisD1 (⇑(Marking.ofQ2 t))
        (Certificates.LSqStokes.lSqFam 0 2
          (omega2Exp (4 * Monoid.exponent C)))
        (q2Offsets x)
      = ![(FoxH.d1FunR t x).1, (FoxH.d1FunR t x).2] := by
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑(Marking.ofQ2 t)) (q2Offsets x) 0)
        (heisToFree
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (Certificates.tameRelW 1 2))).a = (FoxH.liftMarking t x).tameValue.u
    rw [← heisEvalZ_eq_lift]
    change (heisEvalZ (⇑(Marking.ofQ2 t)) (q2Offsets x)
        (q2Offsets (0 : Fin 4 → ElemDual A))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (Certificates.tameRelW 1 2)).a = _
    rw [heisEvalZ_tameRelW_one_two_eq_tameValue, heisMarking_tameValue_a]
  · change
      (FreeGroup.lift (heisGen (⇑(Marking.ofQ2 t)) (q2Offsets x) 0)
        (heisToFree
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (lSqW 0))).a = (FoxH.liftMarking t x).wildValueR.u
    rw [← heisEvalZ_eq_lift]
    change (heisEvalZ (⇑(Marking.ofQ2 t)) (q2Offsets x)
        (q2Offsets (0 : Fin 4 → ElemDual A))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (lSqW 0)).a = _
    rw [heisEvalZ_lSqW_zero_eq_wildValueR hA₂, heisMarking_wildValueR_a]

/-- The middle map of the generic Stokes ladder is Roe's traced mixed pairing after the
four-generator adapter.  Unlike a first-row comparison, this includes the central Heisenberg
coordinate and is therefore strong enough to transport duality. -/
theorem heisEta1_lSqFam_zero_two_uniform_q2Offsets
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (t : _root_.GQ2.Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    heisEta1 (⇑(Marking.ofQ2 t))
        (Certificates.LSqStokes.lSqFam 0 2
          (omega2Exp (4 * Monoid.exponent C)))
        (q2Offsets x) (q2Offsets y)
      = mixedB_R t x y := by
  rw [heisEta1_apply, Fin.sum_univ_two, Certificates.LSqStokes.lSqFam_zero,
    Certificates.LSqStokes.lSqFam_one, ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift,
    heisEvalZ_tameRelW_one_two_eq_tameValue,
    heisEvalZ_lSqW_zero_eq_wildValueR hA₂]
  rfl

/-- **Bundled `h = 0`, `q = 2` Roe/Stokes ladder identification.**  The degree-zero map,
degree-one map, and middle duality map of the uniform generic word complex are respectively
Roe's `d0`, `d1FunR`, and `mixedB_R`, after only the explicit source/target coordinate adapters.
This formulation is independent of continuous cohomology and can feed either a direct
`StokesDuality` transport or the coefficient-local source comparison route. -/
theorem roeStokes_ladder_zero_two_uniform
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (t : _root_.GQ2.Marking C) :
    (∀ a : A, heisD0 (A := A) (⇑(Marking.ofQ2 t)) a = q2Offsets (FoxH.d0 t a)) ∧
      (∀ x : Fin 4 → A,
        heisD1 (⇑(Marking.ofQ2 t))
            (Certificates.LSqStokes.lSqFam 0 2
              (omega2Exp (4 * Monoid.exponent C))) (q2Offsets x)
          = ![(FoxH.d1FunR t x).1, (FoxH.d1FunR t x).2]) ∧
      (∀ (x : Fin 4 → A) (y : Fin 4 → ElemDual A),
        heisEta1 (⇑(Marking.ofQ2 t))
            (Certificates.LSqStokes.lSqFam 0 2
              (omega2Exp (4 * Monoid.exponent C)))
            (q2Offsets x) (q2Offsets y)
          = mixedB_R t x y) := by
  exact ⟨heisD0_ofQ2_eq_q2Offsets_d0 t,
    heisD1_lSqFam_zero_two_uniform_q2Offsets hA₂ t,
    heisEta1_lSqFam_zero_two_uniform_q2Offsets hA₂ t⟩

/-- **The source word complexes are additively chain-isomorphic.**  This is the explicit
three-term conjugacy needed by a quasi-isomorphism transport theorem: identity in degree zero,
`q2OffsetsAddEquiv` in degree one, and `finTwoProdAddEquiv` in degree two.  The third clause is
the middle ladder-map compatibility, included because it is the non-formal input to duality
transport. -/
theorem roeStokes_source_chain_equiv_zero_two_uniform
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (t : _root_.GQ2.Marking C) :
    (∀ a : A,
      q2OffsetsAddEquiv (FoxH.d0 t a) = heisD0 (A := A) (⇑(Marking.ofQ2 t)) a) ∧
      (∀ x : Fin 4 → A,
        finTwoProdAddEquiv
            (heisD1 (⇑(Marking.ofQ2 t))
              (Certificates.LSqStokes.lSqFam 0 2
                (omega2Exp (4 * Monoid.exponent C)))
              (q2OffsetsAddEquiv x))
          = FoxH.d1R t x) ∧
      (∀ (x : Fin 4 → A) (y : Fin 4 → ElemDual A),
        heisEta1 (⇑(Marking.ofQ2 t))
            (Certificates.LSqStokes.lSqFam 0 2
              (omega2Exp (4 * Monoid.exponent C)))
            (q2OffsetsAddEquiv x) (q2OffsetsAddEquiv y)
          = mixedB_R t x y) := by
  refine ⟨fun a ↦ by
      rw [q2OffsetsAddEquiv_apply]
      exact (heisD0_ofQ2_eq_q2Offsets_d0 t a).symm,
    ?_, fun x y ↦ by
      rw [q2OffsetsAddEquiv_apply, q2OffsetsAddEquiv_apply]
      exact heisEta1_lSqFam_zero_two_uniform_q2Offsets hA₂ t x y⟩
  intro x
  rw [q2OffsetsAddEquiv_apply]
  rw [heisD1_lSqFam_zero_two_uniform_q2Offsets hA₂]
  rfl

/-! ## Handle stabilization of the full Stokes middle map -/

/-- Restricting to the core does not change the tame second-order evaluation: the tame word
contains only `sigma` and `tau`.  This is the missing tame half needed to combine the existing
wild handle-stability theorem into a statement about `heisEta1`. -/
theorem heisEvalZ_tameRelW_coreRestrict
    {h q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
    (y : Generator (2 * h + 1) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    heisEvalZ ⇑t x y E E₂ (Certificates.tameRelW (2 * h + 1) q)
      = heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
          (LSq.coreRestrict h (ElemDual A) y) E E₂ (Certificates.tameRelW 1 q) := by
  rw [heisEvalZ, heisEvalZ, Certificates.tameRelW, Certificates.tameRelW]
  simp only [PWord.evalZ_mul, PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_zpow,
    PWord.evalZ_gen]
  rfl

/-- **Full middle-map handle decomposition, unramified class.**  The generic Stokes pairing at
`h` handles is the two-relator pairing at the `n = 1` core plus exactly `h` standard hyperbolic
planes.  The two displayed core terms are the tame and wild summands of the core `heisEta1`;
they are left expanded to avoid dependent casts between `Generator 1` and
`Generator (2 * 0 + 1)`.  Together with `foxDHom_lSq_eq_base_comp_unram`, this is the precise
chain-level statement needed for a direct-sum proof of Stokes duality from the Roe base case. -/
theorem heisEta1_lSqFam_handle_decomposition_unram
    {h q e : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
    (y : Generator (2 * h + 1) → ElemDual A) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) :
    heisEta1 ⇑t (Certificates.LSqStokes.lSqFam h q e) x y
      = (heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
            (LSq.coreRestrict h (ElemDual A) y) (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
            (Certificates.tameRelW 1 q)).z
        + (heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
            (LSq.coreRestrict h (ElemDual A) y) (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
            (lSqW 0)).z
        + ∑ j, (y (handleU j) (x (handleV j))
          + y (handleV j) (x (handleU j))) := by
  rw [Certificates.LSqStokes.heisEta1_lSqFam_apply (t := t) (x := x) (y := y)]
  rw [heisEvalZ_tameRelW_coreRestrict]
  rw [Certificates.LSqStokes.heisZ_lSq_handle_stable t x y
    (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) hA₂ hwild hτ rfl]
  abel

end

end GQ2.Dyadic
