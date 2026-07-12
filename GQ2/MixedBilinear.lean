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

/-- Conjugation by an `a=l`-slice element `g` (`g.a = g.l = 0`) fixes the central coordinate, even
when `g.z ≠ 0` and the base acts nontrivially: `(conjP p g).z = p.z`.  (The two `g.z` contributions
cancel in `ZMod 2`.)  Strengthens `conjP_z_of_slice` by dropping `g.z = 0` — needed because on
general offsets `g₀ = σ₂²` has `g₀.z = y₀(x₀) ≠ 0`. -/
theorem conjP_z_of_alzero (p g : HeisLift A C) (hga : g.a = 0) (hgl : g.l = 0) :
    (conjP p g).z = p.z := by
  simp only [conjP, HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g, HeisLift.inv_z,
    HeisLift.inv_l, HeisLift.inv_g, hga, hgl, smul_zero, neg_zero, map_zero,
    add_zero, zero_add, ElemDual.zero_apply]
  generalize g.z = a
  generalize p.z = b
  revert a b
  decide

/-! ## Wild `.z`, piece 1: the `x₁^σ = σ⁻¹x₁σ` factor (trivial action)

One factor of the wild relator `wildValue = h₀·u₁⁻¹·x₁^σ·c₀`.  Its central coordinate is the
**symplectic pairing of the σ- and x₁-slots**, `y₃(x₀) − y₀(x₃)` — the (0,3)/(3,0) Gram entries. -/
theorem heisMarking_x1sig_z_trivial {C : Type*} [Group C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] (htriv : ∀ (g : C) (a : V), g • a = a) (t : Marking C)
    (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (conjP (heisMarking t x y).x₁ (heisMarking t x y).σ).z = y 3 (x 0) - y 0 (x 3) := by
  have hdtriv : ∀ (g : C) (lam : ElemDual V), g • lam = lam := fun g lam => by
    ext a; rw [ElemDual.smul_apply, htriv]
  show (conjP (⟨x 3, y 3, 0, t.x₁⟩ : HeisLift V C) ⟨x 0, y 0, 0, t.σ⟩).z = _
  simp only [conjP, HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g,
    HeisLift.inv_z, HeisLift.inv_l, HeisLift.inv_g, htriv, hdtriv,
    ElemDual.add_apply, ElemDual.neg_apply]
  generalize y 3 (x 0) = a
  generalize y 0 (x 3) = b
  generalize y 0 (x 0) = d
  generalize y 3 (x 3) = e
  revert a b d e
  decide

/-- **Wild `.z`, piece 2: `c₀ = [d₀,z₀] ↦ 0` on cocycles.**  The symplectic commutator vanishes
because `d₀.a = d₀.l = 0` there (`liftMarking_d0_u = x₁ = 0`).  Same argument as `heisMarking_c0_z`,
with `x₁ = y₁ = 0` in place of x₀-support. -/
theorem heisMarking_c0_z_cocycle {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] [Finite V] (htriv : ∀ (g : C) (a : V), g • a = a)
    (hV₂ : ∀ v : V, v + v = 0) (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : x 1 = 0) (hy1 : y 1 = 0) :
    (heisMarking t x y).c0.z = 0 := by
  have hx0 : ∀ v : V, t.x₀ • v = v := fun v => htriv t.x₀ v
  have htau : ∀ v : V, t.τ • v = v := fun v => htriv t.τ v
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have htaud : ∀ l : ElemDual V, t.τ • l = l := fun l => HeisLift.smul_elemdual_trivial t.τ htau l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  set M := heisMarking t x y with hM
  have hd0a : M.d0.a = 0 := by rwa [heisMarking_d0_a t x y, liftMarking_d0_u t x hV₂ hx0 htau]
  have hd0l : M.d0.l = 0 := by rwa [heisMarking_d0_l t x y, liftMarking_d0_u t y hV₂d hx0d htaud]
  have hd0g := heisMarking_d0_g_smul t x y hx0 htau
  have hz0g := heisMarking_z0_g_smul t x y hx0
  have h := HeisLift.commP_z_of_trivial M.d0 M.z0 hd0g hz0g
  rwa [hd0l, ElemDual.zero_apply, hd0a, map_zero, add_zero] at h

/-- **Wild `.z`, piece 3: `h₀ ↦ y₂(x₂)` on cocycles** — the main term, giving the `(2,2)` Gram
entry.  Mirrors `heisMarking_h0_z` (the x₀-supported `↦ λ(c)`) with `x₁=y₁=0` in place of x₀-support:
the `d₀`-derived leaf coords still vanish (`liftMarking_d0_u = x₁ = 0`), the `ω₂` in `d₀.z` cancels
via the `dg·d₀` pair in char 2, and `g₀ = σ₂²` is `a=l`-slice (char-2 doubling) so
`conjP_z_of_alzero` handles its nonzero `.z`. -/
theorem heisMarking_h0_z_cocycle {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] [Finite V] (htriv : ∀ (g : C) (a : V), g • a = a)
    (hV₂ : ∀ v : V, v + v = 0) (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : x 1 = 0) (hy1 : y 1 = 0) :
    (heisMarking t x y).h0.z = y 2 (x 2) := by
  have hx0 : ∀ v : V, t.x₀ • v = v := fun v => htriv t.x₀ v
  have htau : ∀ v : V, t.τ • v = v := fun v => htriv t.τ v
  have hU : ∀ v : V, t.sigma2 • v = v := fun v => htriv t.sigma2 v
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have htaud : ∀ l : ElemDual V, t.τ • l = l := fun l => HeisLift.smul_elemdual_trivial t.τ htau l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  set M := heisMarking t x y with hM
  -- leaf coordinates
  have hd0a : M.d0.a = 0 := by rwa [heisMarking_d0_a t x y, liftMarking_d0_u t x hV₂ hx0 htau]
  have hd0l : M.d0.l = 0 := by rwa [heisMarking_d0_l t x y, liftMarking_d0_u t y hV₂d hx0d htaud]
  have hx0a : M.x₀.a = x 2 := rfl
  have hx0l : M.x₀.l = y 2 := rfl
  have hx0z : M.x₀.z = 0 := rfl
  -- `g₀ = σ₂²` is `a = l`-slice by char-2 doubling (its `.z` may be nonzero)
  have hsig2g : ∀ v : V, M.sigma2.g • v = v := heisMarking_sigma2_g_smul t x y hU
  have hg0a : M.g0.a = 0 := by
    show (M.sigma2 ^ 2).a = 0
    rw [pow_two, HeisLift.mul_a, hsig2g]; exact hV₂ _
  have hg0l : M.g0.l = 0 := by
    show (M.sigma2 ^ 2).l = 0
    rw [pow_two, HeisLift.mul_l, HeisLift.smul_elemdual_trivial M.sigma2.g hsig2g]; exact hV₂d _
  have hg0g : ∀ v : V, M.g0.g • v = v := heisMarking_g0_g_smul t x y hU
  have hd0g : ∀ v : V, M.d0.g • v = v := heisMarking_d0_g_smul t x y hx0 htau
  have hdgg : ∀ v : V, M.dg.g • v = v := heisMarking_dg_g_smul t x y hx0 htau
  -- derived φ / d₀² / hc coordinates
  have hφx0z : (conjP M.x₀ M.g0).z = 0 := (conjP_z_of_alzero _ _ hg0a hg0l).trans hx0z
  have hφx0l : (conjP M.x₀ M.g0).l = y 2 :=
    (HeisLift.conjP_l_of_gslice _ _ hg0l hg0g).trans hx0l
  have hdgz : M.dg.z = M.d0.z := conjP_z_of_alzero M.d0 M.g0 hg0a hg0l
  have hdga : M.dg.a = 0 := (HeisLift.conjP_a_of_gslice M.d0 M.g0 hg0a hg0g).trans hd0a
  have hd02a : (M.d0 ^ 2).a = 0 := by
    rw [pow_two, HeisLift.mul_a_of_trivial _ _ hd0g, hd0a, add_zero]
  have hd02z : (M.d0 ^ 2).z = 0 := by
    rw [pow_two, HeisLift.mul_z_of_trivial _ _ hd0g, hd0a, map_zero, add_zero,
      CharTwo.add_self_eq_zero]
  have hhca : M.hc.a = 0 := HeisLift.commP_a_of_trivial M.dg M.d0 hdgg hd0g
  have hhcz : M.hc.z = 0 := by
    have h := HeisLift.commP_z_of_trivial M.dg M.d0 hdgg hd0g
    rwa [hd0a, hdga, map_zero, map_zero, add_zero] at h
  -- base-trivialities of the accumulated products
  have hP1g : ∀ v : V, (conjP M.x₀ M.g0).g • v = v := HeisLift.conjP_g_trivial M.x₀ M.g0 hx0
  have hd02g : ∀ v : V, (M.d0 ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ hd0g hd0g v
  have hQ1g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.x₀ hP1g hx0 v
  have hQ2g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.dg hQ1g hdgg v
  have hQ3g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.d0 hQ2g hd0g v
  have hQ4g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ (M.d0 ^ 2) hQ3g hd02g v
  -- the class-two peel
  have e1 : (conjP M.x₀ M.g0 * M.x₀).z = y 2 (x 2) := by
    rw [HeisLift.mul_z_of_trivial _ _ hP1g, hφx0z, hx0z, hφx0l, hx0a, zero_add, zero_add]
  have e2 : (conjP M.x₀ M.g0 * M.x₀ * M.dg).z = y 2 (x 2) + M.d0.z := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ1g, e1, hdgz, hdga, map_zero, add_zero]
  have e3 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).z = y 2 (x 2) := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ2g, e2, hd0a, map_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have e4 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).z = y 2 (x 2) := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ3g, e3, hd02z, hd02a, map_zero, add_zero, add_zero]
  show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).z = y 2 (x 2)
  rw [HeisLift.mul_z_of_trivial _ _ hQ4g, e4, hhcz, hhca, map_zero, add_zero, add_zero]

/-- **Wild `.z` assembly on cocycles**: peeling `wildValue = h₀·u₁⁻¹·(x₁^σ)·c₀` keeps the sum of the
four factor `.z`'s plus one cross-term.  The `u₁.l`-terms — from `inv_z` (`u₁⁻¹.z = u₁.z + u₁.l(u₁.a)`)
and from the `(x₁^σ)`-cross (`(h₀u₁⁻¹).l = −u₁.l`) — **cancel** because `u₁.a = (x₁^σ).a = x₃` (both
are the same primal Fox derivative), leaving the opaque `u₁.z` (the ω₂ scalar) confined to the
`(3,3)` slot. -/
theorem heisMarking_wildValue_z_cocycle {C : Type*} [Group C] [Finite C] {V : Type*}
    [AddCommGroup V] [DistribMulAction C V] [Finite V] (htriv : ∀ (g : C) (a : V), g • a = a)
    (hV₂ : ∀ v : V, v + v = 0) (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : x 1 = 0) (hy1 : y 1 = 0) :
    (heisMarking t x y).wildValue.z = y 2 (x 2) + y 3 (x 0) - y 0 (x 3) + (heisMarking t x y).u1.z := by
  have hx0 : ∀ v : V, t.x₀ • v = v := fun v => htriv t.x₀ v
  have hx1act : ∀ v : V, t.x₁ • v = v := fun v => htriv t.x₁ v
  have htau : ∀ v : V, t.τ • v = v := fun v => htriv t.τ v
  have hU : ∀ v : V, t.sigma2 • v = v := fun v => htriv t.sigma2 v
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have htaud : ∀ l : ElemDual V, t.τ • l = l := fun l => HeisLift.smul_elemdual_trivial t.τ htau l
  have hUd : ∀ l : ElemDual V, t.sigma2 • l = l := fun l => HeisLift.smul_elemdual_trivial t.sigma2 hU l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  set M := heisMarking t x y with hM
  have hh0g : ∀ v : V, M.h0.g • v = v := heisMarking_h0_g_smul t x y hx0 htau hU
  have hu1g : ∀ v : V, M.u1.g • v = v := heisMarking_u1_g_smul t x y hx1act htau
  have hu1invg : ∀ v : V, M.u1⁻¹.g • v = v := fun v => HeisLift.inv_g_trivial M.u1 hu1g v
  have hx1sigg : ∀ v : V, (conjP M.x₁ M.σ).g • v = v := HeisLift.conjP_g_trivial M.x₁ M.σ hx1act
  have hh0z := heisMarking_h0_z_cocycle htriv hV₂ t x y hx1 hy1
  have hh0l : M.h0.l = 0 := by
    rw [heisMarking_h0_l t x y, liftMarking_h0_u t y hV₂d hx0d htaud hUd]
  have hu1a : M.u1.a = x 3 := by
    rw [heisMarking_u1_a t x y, liftMarking_u1_u t x hV₂ hx1act htau, hx1, add_zero]
  have hx1siga : (conjP M.x₁ M.σ).a = x 3 := by
    show (conjP (⟨x 3, y 3, 0, t.x₁⟩ : HeisLift V C) ⟨x 0, y 0, 0, t.σ⟩).a = x 3
    simp only [conjP, HeisLift.mul_a, HeisLift.mul_g, HeisLift.inv_a, HeisLift.inv_g, htriv]
    abel
  have hx1sigz := heisMarking_x1sig_z_trivial htriv t x y
  have hc0a : M.c0.a = 0 := (heisMarking_c0_a t x y).trans (liftMarking_c0_u t x hx0 htau hU)
  have hc0z := heisMarking_c0_z_cocycle htriv hV₂ t x y hx1 hy1
  have hu1invz : M.u1⁻¹.z = M.u1.z + M.u1.l (M.u1.a) := HeisLift.inv_z M.u1
  have hu1invl : M.u1⁻¹.l = -M.u1.l := HeisLift.inv_l_of_trivial M.u1 hu1g
  have hQ2g : ∀ v : V, (M.h0 * M.u1⁻¹).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.u1⁻¹ hh0g hu1invg v
  have hQ3g : ∀ v : V, (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ (conjP M.x₁ M.σ) hQ2g hx1sigg v
  have hQ2l : (M.h0 * M.u1⁻¹).l = -M.u1.l := by
    rw [HeisLift.mul_l, hh0l, zero_add, HeisLift.smul_elemdual_trivial M.h0.g hh0g, hu1invl]
  have e1 : (M.h0 * M.u1⁻¹).z = y 2 (x 2) + M.u1⁻¹.z := by
    rw [HeisLift.mul_z_of_trivial _ _ hh0g, hh0z, hh0l, ElemDual.zero_apply, add_zero]
  have e2 : (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).z
      = y 2 (x 2) + M.u1⁻¹.z + (y 3 (x 0) - y 0 (x 3)) + (-M.u1.l) (x 3) := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ2g, e1, hx1sigz, hQ2l, hx1siga]
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).z = _
  rw [HeisLift.mul_z_of_trivial _ _ hQ3g, e2, hc0z, hc0a, map_zero, add_zero, add_zero,
    hu1invz, hu1a]
  simp only [ElemDual.neg_apply]
  abel

/-- **The trivial-module degree-one pairing on cocycles**: `mixedB t x y = y₂(x₂) + y₃(x₀) − y₀(x₃) +
u₁.z`, the tame part vanishing (`stokesEval_tame_z_trivial_cocycle`) and the wild part from the peel.
The opaque `u₁.z` is the ω₂ scalar, confined to the `(3,3)` slot. -/
theorem mixedB_cocycle {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] [Finite V] (htriv : ∀ (g : C) (a : V), g • a = a)
    (hV₂ : ∀ v : V, v + v = 0) (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : x 1 = 0) (hy1 : y 1 = 0) :
    mixedB t x y = y 2 (x 2) + y 3 (x 0) - y 0 (x 3) + (heisMarking t x y).u1.z := by
  show (heisMarking t x y).tameValue.z + (heisMarking t x y).wildValue.z = _
  rw [bridge_tame, stokesEval_tame_z_trivial_cocycle htriv (markVec t) x y hx1 hy1,
    heisMarking_wildValue_z_cocycle htriv hV₂ t x y hx1 hy1, zero_add]

/-! ## `u₁.z` is confined to the `(3,3)` slot -/

/-- In the `l = 0` subgroup of `H(A)⋊C` the `.z` is additive, so a power keeps `l = 0, z = 0`. -/
theorem heisLift_pow_l_z_zero (w : HeisLift A C) (hl : w.l = 0) (hz : w.z = 0) (k : ℕ) :
    (w ^ k).l = 0 ∧ (w ^ k).z = 0 := by
  induction k with
  | zero => rw [pow_zero]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    exact ⟨by rw [HeisLift.mul_l, ih.1, hl, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih.2, hz, ih.1, ElemDual.zero_apply, add_zero, add_zero]⟩

/-- In the `a = 0` subgroup the `.z` is additive, so a power keeps `a = 0, z = 0`. -/
theorem heisLift_pow_a_z_zero (w : HeisLift A C) (ha : w.a = 0) (hz : w.z = 0) (k : ℕ) :
    (w ^ k).a = 0 ∧ (w ^ k).z = 0 := by
  induction k with
  | zero => rw [pow_zero]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    exact ⟨by rw [HeisLift.mul_a, ih.1, ha, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih.2, hz, ha, smul_zero, map_zero, add_zero, add_zero]⟩

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- `u₁.z = 0` when `y₃ = 0` (on cocycles): `u₁ = powOmega2(x₁τ)` and `x₁τ` has `l = 0, z = 0`, so
its powers do too. -/
theorem heisMarking_u1_z_of_y3_zero (htriv : ∀ (g : C) (a : V), g • a = a) (t : Marking C)
    (x : Fin 4 → V) (y : Fin 4 → ElemDual V) (hx1 : x 1 = 0) (hy1 : y 1 = 0) (hy3 : y 3 = 0) :
    (heisMarking t x y).u1.z = 0 := by
  have hdtriv : ∀ (g : C) (lam : ElemDual V), g • lam = lam := fun g lam => by
    ext a; rw [ElemDual.smul_apply, htriv]
  set w : HeisLift V C := (⟨x 3, y 3, 0, t.x₁⟩ : HeisLift V C) * ⟨x 1, y 1, 0, t.τ⟩ with hw
  have hwl : w.l = 0 := by
    rw [hw, HeisLift.mul_l]; show y 3 + t.x₁ • y 1 = 0
    rw [hdtriv t.x₁ (y 1), hy1, hy3, add_zero]
  have hwz : w.z = 0 := by
    rw [hw, HeisLift.mul_z]; show (0 : ZMod 2) + 0 + (y 3) (t.x₁ • x 1) = 0
    rw [htriv t.x₁ (x 1), hx1, map_zero, add_zero, add_zero]
  show (powOmega2 w).z = 0
  rw [powOmega2]
  exact (heisLift_pow_l_z_zero w hwl hwz _).2

/-- `u₁.z = 0` when `x₃ = 0` (on cocycles), dually. -/
theorem heisMarking_u1_z_of_x3_zero (htriv : ∀ (g : C) (a : V), g • a = a) (t : Marking C)
    (x : Fin 4 → V) (y : Fin 4 → ElemDual V) (hx1 : x 1 = 0) (hy1 : y 1 = 0) (hx3 : x 3 = 0) :
    (heisMarking t x y).u1.z = 0 := by
  set w : HeisLift V C := (⟨x 3, y 3, 0, t.x₁⟩ : HeisLift V C) * ⟨x 1, y 1, 0, t.τ⟩ with hw
  have hwa : w.a = 0 := by
    rw [hw, HeisLift.mul_a]; show x 3 + t.x₁ • x 1 = 0
    rw [htriv t.x₁ (x 1), hx1, hx3, add_zero]
  have hwz : w.z = 0 := by
    rw [hw, HeisLift.mul_z]; show (0 : ZMod 2) + 0 + (y 3) (t.x₁ • x 1) = 0
    rw [htriv t.x₁ (x 1), hx1, map_zero, add_zero, add_zero]
  show (powOmega2 w).z = 0
  rw [powOmega2]
  exact (heisLift_pow_a_z_zero w hwa hwz _).2

end GQ2.FoxH
