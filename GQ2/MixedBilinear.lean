import GQ2.FoxHeisenberg

/-!
# Bilinearity of the traced mixed coordinate `mixedB`

The degree-one pairing `mixedB t x y = (heisMarking t x y).tameValue.z + (…).wildValue.z` is
**bilinear** in the offsets `(x, y)`.  Via `bridge_tame`/`bridge_wild` this reduces to bilinearity of
`(stokesEval c x y r).z` for an arbitrary free-group word `r`, which is an induction on `r` using the
`HeisLift` coordinate cocycle rules: the `.a`-coordinate depends only on `x`, the `.l`-coordinate only
on `y`, the `.g`-coordinate on neither, and the `.z`-coordinate is the bilinear cross-term
`Σ λ_left(a_right)`.

This is the general-offset toolkit consumed by the trivial-module Gram matrix (P-13f part i) and the
ramified mixed Hessian (P-13c).
-/

namespace GQ2.FoxH

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A] {n : ℕ}

/-- The `.a`-coordinate of a Stokes evaluation is independent of the dual offsets `y`. -/
theorem stokesEval_a_indep (c : Fin n → C) (x : Fin n → A) (y y' : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c x y r).a = (stokesEval c x y' r).a := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of]
  · rw [map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, stokesEval_g, stokesEval_g, ih]
  · rw [map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, stokesEval_g, stokesEval_g, ih1, ih2]

/-- The `.l`-coordinate of a Stokes evaluation is independent of the primal offsets `x`. -/
theorem stokesEval_l_indep (c : Fin n → C) (x x' : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c x y r).l = (stokesEval c x' y r).l := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of]
  · rw [map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_l, stokesEval_g, stokesEval_g, ih]
  · rw [map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_l, stokesEval_g, stokesEval_g, ih1, ih2]

/-- Canonical form of `stokesEval_a_indep` (dual offsets set to `0`). -/
theorem stokesEval_a_zero_dual (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) : (stokesEval c x y r).a = (stokesEval c x 0 r).a :=
  stokesEval_a_indep c x y 0 r

/-- Canonical form of `stokesEval_l_indep` (primal offsets set to `0`). -/
theorem stokesEval_l_zero_prim (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) : (stokesEval c x y r).l = (stokesEval c 0 y r).l :=
  stokesEval_l_indep c x 0 y r

/-- The `.a`-coordinate is additive in the primal offsets `x`. -/
theorem stokesEval_a_add (c : Fin n → C) (x x' : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c (x + x') y r).a = (stokesEval c x y r).a + (stokesEval c x' y r).a := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of, Pi.add_apply]
  · rw [map_inv, map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, HeisLift.inv_a,
      stokesEval_g, stokesEval_g, stokesEval_g, ih, smul_add, neg_add]
  · rw [map_mul, map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, HeisLift.mul_a,
      stokesEval_g, stokesEval_g, stokesEval_g, ih1, ih2, smul_add]
    abel

/-- The `.l`-coordinate is additive in the dual offsets `y`. -/
theorem stokesEval_l_add (c : Fin n → C) (x : Fin n → A) (y y' : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c x (y + y') r).l = (stokesEval c x y r).l + (stokesEval c x y' r).l := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of, Pi.add_apply]
  · rw [map_inv, map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_l, HeisLift.inv_l,
      stokesEval_g, stokesEval_g, stokesEval_g, ih, smul_add, neg_add]
  · rw [map_mul, map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_l, HeisLift.mul_l,
      stokesEval_g, stokesEval_g, stokesEval_g, ih1, ih2, smul_add]
    abel

/-- **`.z` is additive in the primal offsets `x`.** -/
theorem stokesEval_z_add_left (c : Fin n → C) (x x' : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c (x + x') y r).z = (stokesEval c x y r).z + (stokesEval c x' y r).z := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of]
  · simp only [map_inv, HeisLift.inv_z, stokesEval, FreeGroup.lift_apply_of, Pi.add_apply,
      map_add, zero_add]
  · simp only [map_mul, HeisLift.mul_z, stokesEval_g, stokesEval_l_zero_prim, stokesEval_a_add,
      smul_add, map_add, ih1, ih2]
    abel

/-- **`.z` is additive in the dual offsets `y`.** -/
theorem stokesEval_z_add_right (c : Fin n → C) (x : Fin n → A) (y y' : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) :
    (stokesEval c x (y + y') r).z = (stokesEval c x y r).z + (stokesEval c x y' r).z := by
  refine FreeGroup.induction_on r ?_ (fun i => ?_) (fun i ih => ?_) (fun r1 r2 ih1 ih2 => ?_)
  · simp
  · simp [stokesEval, FreeGroup.lift_apply_of]
  · simp only [map_inv, HeisLift.inv_z, stokesEval, FreeGroup.lift_apply_of, Pi.add_apply,
      ElemDual.add_apply, zero_add]
  · simp only [map_mul, HeisLift.mul_z, stokesEval_g, stokesEval_l_add, stokesEval_a_zero_dual,
      ElemDual.add_apply, ih1, ih2]
    abel

/-- **`mixedB` is additive in the primal offsets `x`.** -/
theorem mixedB_add_left [Finite A] [Finite C] (t : Marking C) (x x' : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    mixedB t (x + x') y = mixedB t x y + mixedB t x' y := by
  unfold mixedB
  rw [bridge_tame, bridge_wild, bridge_tame, bridge_wild, bridge_tame, bridge_wild,
    stokesEval_z_add_left, stokesEval_z_add_left]
  abel

/-- **`mixedB` is additive in the dual offsets `y`.** -/
theorem mixedB_add_right [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y y' : Fin 4 → ElemDual A) :
    mixedB t x (y + y') = mixedB t x y + mixedB t x y' := by
  unfold mixedB
  rw [bridge_tame, bridge_wild, bridge_tame, bridge_wild, bridge_tame, bridge_wild,
    stokesEval_z_add_right, stokesEval_z_add_right]
  abel

/-! ## The tame `.z` in closed form (trivial action)

For a trivial `C`-action, `fgTame = g₀⁻¹ g₁ g₀ g₁⁻²` evaluates (untwisted Heisenberg) to the
bilinear form below.  Crucially every term carries an index-`1` (`τ`) factor, so it **vanishes on the
split cocycles** `{x₁ = 0}` — i.e. the trivial-module degree-one pairing is carried entirely by the
wild relator, not the tame one. -/
theorem stokesEval_tame_z_trivial (htriv : ∀ (g : C) (a : A), g • a = a) (c : Fin 4 → C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (stokesEval c x y fgTame).z = y 1 (x 0) - y 0 (x 1) + y 1 (x 1) := by
  have hdtriv : ∀ (g : C) (lam : ElemDual A), g • lam = lam := fun g lam => by
    ext a; rw [ElemDual.smul_apply, htriv]
  simp only [fgTame, conjP, pow_two, map_mul, map_inv, stokesEval, FreeGroup.lift_apply_of,
    HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_a, HeisLift.mul_g, HeisLift.inv_z, HeisLift.inv_l,
    HeisLift.inv_a, HeisLift.inv_g, htriv, hdtriv, map_add, map_neg, ElemDual.add_apply,
    ElemDual.neg_apply]
  generalize (y 0) (x 0) = p
  generalize (y 0) (x 1) = q
  generalize (y 1) (x 0) = r
  generalize (y 1) (x 1) = s
  revert p q r s
  decide

/-- The tame `.z` (trivial action) vanishes on the split cocycles `x₁ = 0`, `y₁ = 0`. -/
theorem stokesEval_tame_z_trivial_cocycle (htriv : ∀ (g : C) (a : A), g • a = a) (c : Fin 4 → C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) (hx : x 1 = 0) (hy : y 1 = 0) :
    (stokesEval c x y fgTame).z = 0 := by
  rw [stokesEval_tame_z_trivial htriv, hx, hy]
  simp

end GQ2.FoxH
