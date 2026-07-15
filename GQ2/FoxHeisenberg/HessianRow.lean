/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.FoxHeisenberg.WildRow

@[expose] public section

/-!
# Lemma 5.14 (mixed Hessian), normal forms, and the main duality

Split off from `GQ2.FoxHeisenberg`, building on `GQ2.FoxHeisenberg.WildRow`.  This file provides:

* **Lemma 5.14**, the mixed Hessian in the split case via `agHom`/`lgHom` naturality
  (`section HessianRow`), including the shared fixed-point-free surjectivity helper
  `surjective_smul_sub_of_fixedPointFree`;
* the Heisenberg **normal forms** (`section NormalForms`);
* the **main duality** conclusion (`section MainDuality`).

See `GQ2.FoxHeisenberg` for the umbrella module docstring.
-/

namespace GQ2

namespace FoxH

/-! ## Lemma 5.14: the mixed Hessian (split case) via `agHom`/`lgHom` naturality

The `.a` and `.l` coordinates of the Heisenberg-evaluated aux words come free from the `WordLift`
wild-row results: `agHom`/`lgHom` are homs pushing `heisMarking` to `liftMarking` (over `V`, resp.
`V^∨`), so `(heisMarking t x y).W.a = (liftMarking t x).W.u` and `.l = (liftMarking t y).W.u`.  On
the x₀-supported rep (`x₁ = x₃ = 0` slots) these vanish for every aux word, leaving a pure central
computation. -/

section HessianRow

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- The degree-one tuple supported on the `x₀`-slot (display (53)'s normal form). -/
def x0Supported (c : V) : Fin 4 → V := ![0, 0, c, 0]

omit [Finite C] [Finite V] in
private theorem heisMarking_map_agHom (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).map agHom = liftMarking t x := rfl

omit [Finite C] [Finite V] in
private theorem heisMarking_map_lgHom (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).map lgHom = liftMarking t y := rfl

/-- Naturality: the `.a` of an aux word at `heisMarking` is the `liftMarking` `.u` (via `agHom`);
`.l` is the dual `liftMarking` `.u` (via `lgHom`); `.g` agrees (both project the base). -/
theorem heisMarking_h0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.a = (liftMarking t x).h0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).h0 = (liftMarking t x).h0 by
    rw [← Marking.map_h0, heisMarking_map_agHom])

theorem heisMarking_h0_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.l = (liftMarking t y).h0.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).h0 = (liftMarking t y).h0 by
    rw [← Marking.map_h0, heisMarking_map_lgHom])

private theorem heisMarking_h0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.g = (liftMarking t x).h0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).h0 = (liftMarking t x).h0 by
    rw [← Marking.map_h0, heisMarking_map_agHom])

theorem heisMarking_d0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.a = (liftMarking t x).d0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).d0 = (liftMarking t x).d0 by
    rw [← Marking.map_d0, heisMarking_map_agHom])

theorem heisMarking_d0_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.l = (liftMarking t y).d0.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).d0 = (liftMarking t y).d0 by
    rw [← Marking.map_d0, heisMarking_map_lgHom])

private theorem heisMarking_d0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.g = (liftMarking t x).d0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).d0 = (liftMarking t x).d0 by
    rw [← Marking.map_d0, heisMarking_map_agHom])

theorem heisMarking_c0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).c0.a = (liftMarking t x).c0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).c0 = (liftMarking t x).c0 by
    rw [← Marking.map_c0, heisMarking_map_agHom])

private theorem heisMarking_c0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).c0.g = (liftMarking t x).c0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).c0 = (liftMarking t x).c0 by
    rw [← Marking.map_c0, heisMarking_map_agHom])

private theorem heisMarking_u1_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).u1.g = (liftMarking t x).u1.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).u1 = (liftMarking t x).u1 by
    rw [← Marking.map_u1, heisMarking_map_agHom])

private theorem heisMarking_sigma2_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.a = (liftMarking t x).sigma2.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).sigma2 = (liftMarking t x).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_agHom])

private theorem heisMarking_sigma2_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.l = (liftMarking t y).sigma2.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).sigma2 = (liftMarking t y).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_lgHom])

private theorem heisMarking_sigma2_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.g = (liftMarking t x).sigma2.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).sigma2 = (liftMarking t x).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_agHom])

omit [Finite C] [Finite V] in
/-- On the x₀-supported rep, `σ` (index 0) lands in the base slice, so `σ₂` and `g₀` are pure base
elements: their `.a`, `.l`, `.z` all vanish (via `secHom`-slice + the square for `z`). -/
theorem heisMarking_sigma2_u_zero (t : Marking C) (x : Fin 4 → V)
    (hx0 : x 0 = 0) : (liftMarking t x).sigma2.u = 0 :=
  WordLift.powOmega2_u_zero _ (show x 0 = 0 from hx0)

/-! ### Base-triviality of the Heisenberg aux words (transferred from `liftMarking`). -/

theorem heisMarking_sigma2_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hU : ∀ v : V, t.sigma2 • v = v) (v : V) : (heisMarking t x y).sigma2.g • v = v := by
  rw [heisMarking_sigma2_g_eq, liftMarking_sigma2_g]; exact hU v

theorem heisMarking_d0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).d0.g • v = v := by
  rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_smul t x hx0 htau v

theorem heisMarking_h0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (v : V) : (heisMarking t x y).h0.g • v = v := by
  rw [heisMarking_h0_g_eq]; exact liftMarking_h0_g_smul t x hx0 htau hU v

theorem heisMarking_u1_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).u1.g • v = v := by
  rw [heisMarking_u1_g_eq]; exact liftMarking_u1_g_smul t x hx1 htau v

theorem heisMarking_g0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hU : ∀ v : V, t.sigma2 • v = v) (v : V) : (heisMarking t x y).g0.g • v = v := by
  show ((heisMarking t x y).sigma2 ^ 2).g • v = v
  rw [pow_two, HeisLift.mul_g, mul_smul, heisMarking_sigma2_g_smul t x y hU,
    heisMarking_sigma2_g_smul t x y hU]

omit [Finite C] [Finite V] in
theorem heisMarking_z0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (v : V) : (heisMarking t x y).z0.g • v = v :=
  HeisLift.conjP_g_trivial (heisMarking t x y).x₀ (heisMarking t x y).sigma2 hx0 v

theorem heisMarking_dg_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).dg.g • v = v :=
  HeisLift.conjP_g_trivial (heisMarking t x y).d0 (heisMarking t x y).g0
    (heisMarking_d0_g_smul t x y hx0 htau) v

private theorem heisMarking_hc_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).hc.g • v = v :=
  HeisLift.commP_g_trivial (heisMarking t x y).dg (heisMarking t x y).d0
    (heisMarking_dg_g_smul t x y hx0 htau) (heisMarking_d0_g_smul t x y hx0 htau) v

private theorem heisMarking_c0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).c0.g • v = v :=
  HeisLift.commP_g_trivial (heisMarking t x y).d0 (heisMarking t x y).z0
    (heisMarking_d0_g_smul t x y hx0 htau) (heisMarking_z0_g_smul t x y hx0) v

/-! ### `g₀ = σ₂²` is a base-slice element on the x₀-supported rep (`a = l = z = 0`). -/

private theorem heisMarking_sigma2_a_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).sigma2.a = 0 := by
  rw [heisMarking_sigma2_a]; exact heisMarking_sigma2_u_zero t (x0Supported c) rfl

private theorem heisMarking_sigma2_l_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).sigma2.l = 0 := by
  rw [heisMarking_sigma2_l]; exact WordLift.powOmega2_u_zero _ rfl

private theorem heisMarking_g0_a_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.a = 0 := by
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).a = 0
  rw [pow_two, HeisLift.mul_a, heisMarking_sigma2_a_zero t c lam, smul_zero, add_zero]

private theorem heisMarking_g0_l_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.l = 0 := by
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).l = 0
  rw [pow_two, HeisLift.mul_l, heisMarking_sigma2_l_zero t c lam, smul_zero, add_zero]

private theorem heisMarking_g0_z_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.z = 0 := by
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).z = 0
  rw [pow_two, HeisLift.mul_z, heisMarking_sigma2_a_zero t c lam, smul_zero, map_zero, add_zero,
    CharTwo.add_self_eq_zero]

/-- **`h₀ ↦ λ(c)`** (Lemma 5.14, the `h₀`-shadow central contribution): on the x₀-supported rep the
central coordinate of the wild `h₀` word is `λ(c)`.  With `g₀` in the base slice, `φ = conj by g₀`
preserves all Heisenberg coordinates, so in the class-two peel
`h₀ = φ(x₀)·x₀·φ(d₀)·d₀·d₀²·[φ(d₀),d₀]`
every factor but the leading `φ(x₀)·x₀` cross-term vanishes (`d₀.a = d₀.l = 0`; the paired `z`'s
cancel in char 2), leaving `φ(x₀).l(x₀.a) = λ(c)`. -/
theorem heisMarking_h0_z (t : Marking C) (c : V) (lam : ElemDual V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).h0.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := HeisLift.smul_elemdual_trivial t.x₀ hx0
  have htaud : ∀ l : ElemDual V, t.τ • l = l := HeisLift.smul_elemdual_trivial t.τ htau
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => l.add_self_eq_zero
  -- leaf coordinates
  have hd0a : M.d0.a = 0 :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported c) hV₂ hx0 htau)
  have hd0l : M.d0.l = 0 :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported lam) hV₂d hx0d htaud)
  have hx0a : M.x₀.a = c := rfl
  have hx0l : M.x₀.l = lam := rfl
  have hx0z : M.x₀.z = 0 := rfl
  have hg0a : M.g0.a = 0 := heisMarking_g0_a_zero t c lam
  have hg0l : M.g0.l = 0 := heisMarking_g0_l_zero t c lam
  have hg0z : M.g0.z = 0 := heisMarking_g0_z_zero t c lam
  have hg0g : ∀ v : V, M.g0.g • v = v :=
    heisMarking_g0_g_smul t (x0Supported c) (x0Supported lam) hU
  have hd0g : ∀ v : V, M.d0.g • v = v :=
    heisMarking_d0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  have hdgg : ∀ v : V, M.dg.g • v = v :=
    heisMarking_dg_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  -- derived φ / d₀² / hc coordinates
  have hφx0z : (conjP M.x₀ M.g0).z = 0 :=
    (HeisLift.conjP_z_of_gslice _ _ hg0a hg0l hg0z hg0g).trans hx0z
  have hφx0l : (conjP M.x₀ M.g0).l = lam :=
    (HeisLift.conjP_l_of_gslice _ _ hg0l hg0g).trans hx0l
  have hdgz : M.dg.z = M.d0.z := HeisLift.conjP_z_of_gslice M.d0 M.g0 hg0a hg0l hg0z hg0g
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
  have e1 : (conjP M.x₀ M.g0 * M.x₀).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hP1g, hφx0z, hx0z, hφx0l, hx0a, zero_add, zero_add]
  have e2 : (conjP M.x₀ M.g0 * M.x₀ * M.dg).z = lam c + M.d0.z := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ1g, e1, hdgz, hdga, map_zero, add_zero]
  have e3 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ2g, e2, hd0a, map_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have e4 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ3g, e3, hd02z, hd02a, map_zero, add_zero, add_zero]
  show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ4g, e4, hhcz, hhca, map_zero, add_zero, add_zero]

omit [Finite C] [Finite V] in
/-- The 2-primary part of a base-slice element is base-slice: central coordinate vanishes. -/
theorem powOmega2_secHom_z (w : C) : (powOmega2 (secHom (A := V) w)).z = 0 := by
  rw [powOmega2, ← map_pow]; rfl

/-- **`[d₀,z₀] ↦ 0`** in the split case: `c₀`'s central coordinate vanishes since `d₀.a = d₀.l = 0`
(the paper's `P + 1 = 0` collapse for `T = 1`). -/
theorem heisMarking_c0_z (t : Marking C) (c : V) (lam : ElemDual V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).c0.z = 0 := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := HeisLift.smul_elemdual_trivial t.x₀ hx0
  have htaud : ∀ l : ElemDual V, t.τ • l = l := HeisLift.smul_elemdual_trivial t.τ htau
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => l.add_self_eq_zero
  have hd0a : M.d0.a = 0 :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported c) hV₂ hx0 htau)
  have hd0l : M.d0.l = 0 :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported lam) hV₂d hx0d htaud)
  have hd0g := heisMarking_d0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  have hz0g := heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  have h := HeisLift.commP_z_of_trivial M.d0 M.z0 hd0g hz0g
  rwa [hd0l, ElemDual.zero_apply, hd0a, map_zero, add_zero] at h

omit [Finite C] [Finite V] in
/-- `u₁` is a base-slice element on the x₀-rep, so its central coordinate vanishes. -/
theorem heisMarking_u1_z (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).u1.z = 0 := by
  show (powOmega2 ((heisMarking t (x0Supported c) (x0Supported lam)).x₁ *
    (heisMarking t (x0Supported c) (x0Supported lam)).τ)).z = 0
  rw [show (heisMarking t (x0Supported c) (x0Supported lam)).x₁ *
    (heisMarking t (x0Supported c) (x0Supported lam)).τ = secHom (t.x₁ * t.τ) from by
      rw [map_mul]; rfl]
  exact powOmega2_secHom_z _

omit [Finite C] [Finite V] in
/-- `x₁^σ` is a base-slice element on the x₀-rep, so its central coordinate vanishes. -/
theorem heisMarking_conjP_x1_sigma_z (t : Marking C) (c : V) (lam : ElemDual V) :
    (conjP (heisMarking t (x0Supported c) (x0Supported lam)).x₁
      (heisMarking t (x0Supported c) (x0Supported lam)).σ).z = 0 := by
  rw [show conjP (heisMarking t (x0Supported c) (x0Supported lam)).x₁
      (heisMarking t (x0Supported c) (x0Supported lam)).σ = secHom (conjP t.x₁ t.σ) from by
    simp only [conjP, map_mul, map_inv]; rfl]
  rfl

omit [Finite C] [Finite V] in
private theorem powOmega2_secHom_a (w : C) : (powOmega2 (secHom (A := V) w)).a = 0 := by
  rw [powOmega2, ← map_pow]; rfl

theorem heisMarking_u1_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).u1.a = (liftMarking t x).u1.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).u1 = (liftMarking t x).u1 by
    rw [← Marking.map_u1, heisMarking_map_agHom])

/-- **The split mixed pairing**, wild summand: `B_{ρ,A}(x₀-supported)` central coordinate is `λ(c)`.
Outer peel of `wildValue = h₀·u₁⁻¹·x₁^σ·c₀`: all four factors are trivially-based with vanishing
`.a` (naturality/base-slice), so `.z` is additive, and only `h₀.z = λ(c)` survives (`u₁⁻¹, x₁^σ, c₀`
have `.z = 0`). -/
theorem heisMarking_wildValue_z (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hh0g := heisMarking_h0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau hU
  have hu1g := heisMarking_u1_g_smul t (x0Supported c) (x0Supported lam) hx1 htau
  have hu1invg : ∀ v : V, M.u1⁻¹.g • v = v := fun v => HeisLift.inv_g_trivial M.u1 hu1g v
  have hx1sigg : ∀ v : V, (conjP M.x₁ M.σ).g • v = v := HeisLift.conjP_g_trivial M.x₁ M.σ hx1
  have hu1a : M.u1.a = 0 := by
    rw [show M.u1.a = (liftMarking t (x0Supported c)).u1.u from
        heisMarking_u1_a t (x0Supported c) (x0Supported lam),
      liftMarking_u1_u t (x0Supported c) hV₂ hx1 htau]
    simp [x0Supported]
  have hu1inva : M.u1⁻¹.a = 0 := by rw [HeisLift.inv_a_of_trivial M.u1 hu1g, hu1a, neg_zero]
  have hx1siga : (conjP M.x₁ M.σ).a = 0 := by
    rw [show conjP M.x₁ M.σ = secHom (conjP t.x₁ t.σ) from by
      simp only [conjP, map_mul, map_inv]; rfl]; rfl
  have hc0a : M.c0.a = 0 :=
    (heisMarking_c0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_c0_u t (x0Supported c) hx0 htau hU)
  have hh0z := heisMarking_h0_z t c lam hV₂ hx0 htau hU
  have hu1z := heisMarking_u1_z t c lam
  have hu1invz : M.u1⁻¹.z = 0 := by rw [HeisLift.inv_z, hu1z, hu1a, map_zero, add_zero]
  have hx1sigz := heisMarking_conjP_x1_sigma_z t c lam
  have hc0z := heisMarking_c0_z t c lam hV₂ hx0 htau
  have hQ2g : ∀ v : V, (M.h0 * M.u1⁻¹).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.u1⁻¹ hh0g hu1invg v
  have hQ3g : ∀ v : V, (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ (conjP M.x₁ M.σ) hQ2g hx1sigg v
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ3g, hc0z, hc0a, map_zero, add_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hQ2g, hx1sigz, hx1siga, map_zero, add_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hh0g, hh0z, hu1invz, hu1inva, map_zero, add_zero, add_zero]

/-! ### Ramified mixed Hessian: `U = σ₂` acts nontrivially

The ramified degree-one pairing `B(c,λ) = λ((1 + U + U⁻¹)c)`.  Two central contributions:
`h₀ ↦ λ(c)` (the shadow, with all `U²`-twisted cross-terms cancelling in char 2) and
`[d₀,z₀] ↦ λ(Uc) + λ(U⁻¹c)` (the symplectic commutator, now nonzero since `Dd₀ = c ≠ 0`).  Unlike
the split case `g₀ = σ₂²` is not `g`-slice, so the peel uses `conjP_*_of_slice` to track the
`U`-action. -/
omit [Finite C] in
/-- Fixed-point-freeness makes `σ − 1` surjective on a finite module: if `σ • v = v` forces
`v = 0` then `v ↦ σ • v − v` is injective (difference-telescope), hence surjective on the
finite `V`.  The canonical form of the hand-rolled `hsurj`/`hτsurj` derivations. -/
theorem surjective_smul_sub_of_fixedPointFree {σ : C} (hfpf : ∀ v : V, σ • v = v → v = 0) :
    Function.Surjective fun v : V => σ • v - v :=
  Finite.injective_iff_surjective.mp fun a b hab => sub_eq_zero.mp
    (hfpf (a - b) (by rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]; exact hab))

omit [Finite C] in
/-- Contragredient fixed-point-freeness: if `T = τ` has no nonzero fixed vector on the finite
module `V` (`V^T = 0`), then the same holds on the dual `V^∨`.  (`T − 1` injective ⟹ surjective on
finite `V`; the dual `T^∨ − 1` is then injective.)  Supplies the ramified `d₀.l = λ` computation. -/
theorem elemDual_fixedPointFree_of_fixedPointFree (t : Marking C)
    (htau : ∀ v : V, t.τ • v = v → v = 0) :
    ∀ lam : ElemDual V, t.τ • lam = lam → lam = 0 := by
  have hsurj : Function.Surjective (fun w : V => t.τ⁻¹ • w - w) :=
    surjective_smul_sub_of_fixedPointFree fun w hw => htau w (inv_smul_eq_iff.mp hw).symm
  intro lam hlam
  ext v
  obtain ⟨w, hw⟩ := hsurj v
  have hlw : lam (t.τ⁻¹ • w) = lam w := DFunLike.congr_fun hlam w
  show lam v = 0
  rw [← hw, map_sub, hlw, sub_self]

/-- **`h₀ ↦ λ(c)`** (ramified Lemma 5.14).  Unlike the split case, `g₀ = σ₂²` acts *nontrivially*
(`U²`), so the conjugation `φ = ·^{g₀}` shifts the `A`/`A^∨` coordinates by `U⁻²`; but every
Heisenberg base still acts trivially on `V` (the conjugation cancels `U²`), so the class-two peel is
a `mul_z_of_trivial` computation whose `U²`-twisted cross-terms cancel in char 2, leaving `λ(c)`. -/
theorem heisMarking_h0_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).h0.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  -- dual-side hypotheses
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := HeisLift.smul_elemdual_trivial t.x₀ hx0
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => l.add_self_eq_zero
  have htaud : ∀ l : ElemDual V, t.τ • l = l → l = 0 :=
    elemDual_fixedPointFree_of_fixedPointFree t htau
  have hToddd : ∀ l : ElemDual V, powOmega2 t.τ • l = l :=
    HeisLift.smul_elemdual_trivial (powOmega2 t.τ) hTodd
  -- `d₀` coordinates (ramified: `a = c`, `l = lam`, base trivial)
  have hD_a : M.d0.a = c :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported c) hV₂ hx0 htau hTodd)
  have hD_l : M.d0.l = lam :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported lam) hV₂d hx0d htaud hToddd)
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  -- `g₀` base-slice (`a = l = z = 0`, base `U²`)
  have hg0a : M.g0.a = 0 := heisMarking_g0_a_zero t c lam
  have hg0l : M.g0.l = 0 := heisMarking_g0_l_zero t c lam
  have hg0z : M.g0.z = 0 := heisMarking_g0_z_zero t c lam
  -- `x₀`
  have hX_a : M.x₀.a = c := rfl
  have hX_l : M.x₀.l = lam := rfl
  have hX_z : M.x₀.z = 0 := rfl
  have hX_g : ∀ v : V, M.x₀.g • v = v := hx0
  -- factor base-trivialities
  have hP_g : ∀ v : V, (conjP M.x₀ M.g0).g • v = v := HeisLift.conjP_g_trivial M.x₀ M.g0 hx0
  have hDg_g : ∀ v : V, M.dg.g • v = v := HeisLift.conjP_g_trivial M.d0 M.g0 hD_g
  -- factor `a/l/z` coordinates
  have hP_a : (conjP M.x₀ M.g0).a = M.g0.g⁻¹ • c := by
    rw [HeisLift.conjP_a_of_slice M.x₀ M.g0 hg0a, hX_a]
  have hP_l : (conjP M.x₀ M.g0).l = M.g0.g⁻¹ • lam := by
    rw [HeisLift.conjP_l_of_slice M.x₀ M.g0 hg0l, hX_l]
  have hP_z : (conjP M.x₀ M.g0).z = 0 := by
    rw [HeisLift.conjP_z_of_slice M.x₀ M.g0 hg0a hg0l hg0z, hX_z]
  have hDg_a : M.dg.a = M.g0.g⁻¹ • c := by
    show (conjP M.d0 M.g0).a = _; rw [HeisLift.conjP_a_of_slice M.d0 M.g0 hg0a, hD_a]
  have hDg_l : M.dg.l = M.g0.g⁻¹ • lam := by
    show (conjP M.d0 M.g0).l = _; rw [HeisLift.conjP_l_of_slice M.d0 M.g0 hg0l, hD_l]
  have hDg_z : M.dg.z = M.d0.z := by
    show (conjP M.d0 M.g0).z = _; rw [HeisLift.conjP_z_of_slice M.d0 M.g0 hg0a hg0l hg0z]
  -- `d₀²`
  have hD2_a : (M.d0 ^ 2).a = 0 := by
    rw [pow_two, HeisLift.mul_a_of_trivial _ _ hD_g, hD_a]; exact hV₂ c
  have hD2_l : (M.d0 ^ 2).l = 0 := by
    rw [pow_two, HeisLift.mul_l_of_trivial _ _ hD_g, hD_l]; exact hV₂d lam
  have hD2_z : (M.d0 ^ 2).z = lam c := by
    rw [pow_two, HeisLift.mul_z_of_trivial _ _ hD_g, hD_l, hD_a, CharTwo.add_self_eq_zero, zero_add]
  -- `[φ(d₀),d₀]`
  have hHc_a : M.hc.a = 0 := HeisLift.commP_a_of_trivial M.dg M.d0 hDg_g hD_g
  have hHc_z : M.hc.z = lam (M.g0.g • c) + lam (M.g0.g⁻¹ • c) := by
    show (commP M.dg M.d0).z = _
    rw [HeisLift.commP_z_of_trivial M.dg M.d0 hDg_g hD_g, hDg_l, hD_a, hD_l, hDg_a,
      ElemDual.smul_apply, inv_inv]
  -- prefix base-trivialities
  have hQ2g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hP_g hX_g v
  have hQ3g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ2g hDg_g v
  have hQ4g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ3g hD_g v
  have hD2g : ∀ v : V, (M.d0 ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ hD_g hD_g v
  have hQ5g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ4g hD2g v
  -- peel `h₀ = φ(x₀)·x₀·φ(d₀)·d₀·d₀²·[φ(d₀),d₀]`
  show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ5g, HeisLift.mul_z_of_trivial _ _ hQ4g,
    HeisLift.mul_z_of_trivial _ _ hQ3g, HeisLift.mul_z_of_trivial _ _ hQ2g,
    HeisLift.mul_z_of_trivial _ _ hP_g,
    HeisLift.mul_l_of_trivial _ _ hQ4g, HeisLift.mul_l_of_trivial _ _ hQ3g,
    HeisLift.mul_l_of_trivial _ _ hQ2g, HeisLift.mul_l_of_trivial _ _ hP_g,
    hP_z, hX_z, hDg_z, hD2_z, hHc_z, hP_l, hX_l, hDg_l, hD2_l, hHc_a, hX_a, hDg_a, hD_a, hD2_a]
  simp only [ElemDual.add_apply, ElemDual.smul_apply, inv_inv, smul_inv_smul, map_zero, add_zero,
    zero_add]
  generalize lam c = a
  generalize lam (M.g0.g • c) = b
  generalize lam (M.g0.g⁻¹ • c) = e
  generalize M.d0.z = δ
  revert a b e δ
  decide

/-- **`[d₀,z₀] ↦ λ(Uc) + λ(U⁻¹c)`** (ramified Lemma 5.14, `U = σ₂`).  On the x₀-rep `Dd₀ = c` and
`Dz₀ = U⁻¹c`; the Heisenberg commutator symplectic form `commP_z_of_trivial` gives
`[d₀,z₀].z = d₀.l(z₀.a) + z₀.l(d₀.a) = λ(U⁻¹c) + (U⁻¹λ)(c) = λ(U⁻¹c) + λ(Uc)`. -/
theorem heisMarking_c0_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).c0.z
      = lam (t.sigma2⁻¹ • c) + lam (t.sigma2 • c) := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := HeisLift.smul_elemdual_trivial t.x₀ hx0
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => l.add_self_eq_zero
  have htaud : ∀ l : ElemDual V, t.τ • l = l → l = 0 :=
    elemDual_fixedPointFree_of_fixedPointFree t htau
  have hToddd : ∀ l : ElemDual V, powOmega2 t.τ • l = l :=
    HeisLift.smul_elemdual_trivial (powOmega2 t.τ) hTodd
  have hD_a : M.d0.a = c :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported c) hV₂ hx0 htau hTodd)
  have hD_l : M.d0.l = lam :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported lam) hV₂d hx0d htaud hToddd)
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  have hsig_g : M.sigma2.g = t.sigma2 :=
    (heisMarking_sigma2_g_eq t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_sigma2_g t (x0Supported c))
  have hX_a : M.x₀.a = c := rfl
  have hX_l : M.x₀.l = lam := rfl
  have hz0a : M.z0.a = t.sigma2⁻¹ • c := by
    show (conjP M.x₀ M.sigma2).a = _
    rw [HeisLift.conjP_a_of_slice M.x₀ M.sigma2 (heisMarking_sigma2_a_zero t c lam), hX_a, hsig_g]
  have hz0l : M.z0.l = t.sigma2⁻¹ • lam := by
    show (conjP M.x₀ M.sigma2).l = _
    rw [HeisLift.conjP_l_of_slice M.x₀ M.sigma2 (heisMarking_sigma2_l_zero t c lam), hX_l, hsig_g]
  have hz0g : ∀ v : V, M.z0.g • v = v :=
    heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  show (commP M.d0 M.z0).z = _
  rw [HeisLift.commP_z_of_trivial M.d0 M.z0 hD_g hz0g, hD_l, hz0a, hz0l, hD_a,
    ElemDual.smul_apply, inv_inv]

/-- **The ramified mixed pairing, wild summand**: `wildValue.z = λ((1 + U + U⁻¹)c)`.  The peel
`wildValue = h₀·u₁⁻¹·(x₁^σ)·c₀`: `u₁⁻¹` and `x₁^σ` are pure `secHom` base elements
(`a = l = z = 0`),
so right-multiplication by them preserves `.z`; only `h₀.z = λ(c)` and `c₀.z = λ(Uc) + λ(U⁻¹c)`
survive. -/
theorem heisMarking_wildValue_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (_ : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z
      = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c) := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hh0z : M.h0.z = lam c := heisMarking_h0_z_ramified t c lam hV₂ hx0 htau hTodd
  have hc0z : M.c0.z = lam (t.sigma2⁻¹ • c) + lam (t.sigma2 • c) :=
    heisMarking_c0_z_ramified t c lam hV₂ hx0 htau hTodd
  -- base-trivialities for `c₀.a`
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  have hz0g : ∀ v : V, M.z0.g • v = v :=
    heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  have hc0a : M.c0.a = 0 := HeisLift.commP_a_of_trivial M.d0 M.z0 hD_g hz0g
  -- pure-base coordinates of `u₁` and `x₁^σ`
  have hu1a : M.u1.a = 0 := by
    show (powOmega2 (M.x₁ * M.τ)).a = 0
    rw [show M.x₁ * M.τ = secHom (t.x₁ * t.τ) from by rw [map_mul]; rfl]
    exact powOmega2_secHom_a _
  have hu1z : M.u1.z = 0 := heisMarking_u1_z t c lam
  have hu1inva : M.u1⁻¹.a = 0 := by rw [HeisLift.inv_a, hu1a, smul_zero, neg_zero]
  have hu1invz : M.u1⁻¹.z = 0 := by rw [HeisLift.inv_z, hu1a, map_zero, add_zero, hu1z]
  have hx1sa : (conjP M.x₁ M.σ).a = 0 := by
    rw [show conjP M.x₁ M.σ = secHom (conjP t.x₁ t.σ) from by
      simp only [conjP, map_mul, map_inv]; rfl]; rfl
  have hx1sz : (conjP M.x₁ M.σ).z = 0 := heisMarking_conjP_x1_sigma_z t c lam
  -- right-multiplication by a pure-base element preserves `.z`
  have hmulpure : ∀ (p q : HeisLift V C), q.a = 0 → q.z = 0 → (p * q).z = p.z :=
    fun p q hqa hqz => by rw [HeisLift.mul_z, hqa, smul_zero, map_zero, add_zero, hqz, add_zero]
  have hX4z : (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).z = M.h0.z := by
    rw [hmulpure _ _ hx1sa hx1sz, hmulpure _ _ hu1inva hu1invz]
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).z = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c)
  rw [HeisLift.mul_z, hc0a, smul_zero, map_zero, add_zero, hX4z, hh0z, hc0z, map_add, map_add]
  abel

end HessianRow

section NormalForms

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

omit [Finite C] in
/-- **The marked wild generators act trivially on a simple module** — the admissibility input the
normal-form and pairing lemmas below need.  This is the paper's Lemma 5.12 ("simple char-2 modules
are tame") applied to the normal 2-subgroup `L = ⟨⟨x₀, x₁⟩⟩`: `L` is normal (a normal closure) and
a 2-group (the `Pro2Core` clause `hcore`), and contains `x₀, x₁`. -/
theorem wild_acts_trivially (t : Marking C) [Finite V]
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) (hcore : t.Pro2Core) :
    (∀ v : V, t.x₀ • v = v) ∧ (∀ v : V, t.x₁ • v = v) := by
  have htriv := lemma_5_12 hV₂ hsimple (Subgroup.normalClosure {t.x₀, t.x₁})
    Subgroup.normalClosure_normal hcore
  exact ⟨htriv t.x₀ (Subgroup.subset_normalClosure (by simp)),
    htriv t.x₁ (Subgroup.subset_normalClosure (by simp))⟩

omit [Finite C] in
/-- **The tame row in the split case, closed form** (unconditional — needs only `T = 1` and char
2, no wild-core input): `L_t(x) = S⁻¹·x₁`.  This is the `x 1 = 0` half of `lemma_5_13_split`'s
`Z¹` description, and holds verbatim from the general tame row `d1Fun_tame` with `T = 1`. -/
theorem d1Fun_tame_split (t : Marking C) (ht : t.TameRel) (htau : ∀ v : V, t.τ • v = v)
    (hV₂ : ∀ v : V, v + v = 0) (x : Fin 4 → V) :
    (d1Fun t x).1 = t.σ⁻¹ • x 1 := by
  rw [d1Fun_tame t ht x, htau (x 0), htau (x 1), sub_self, zero_add, hV₂ (x 1), sub_zero]

omit [Finite C] in
/-- **The `B¹` coboundary shape when the wild generators act trivially** (the paper's `B¹` in
Lemma 5.13(i), with the trivial wild action made an explicit hypothesis — however it is obtained:
directly, or via the proved `lemma_5_12` from `Pro2Core`; see
`docs/orchestration/p13-normal-form-hypothesis-gap.md`).  Under `T = 1` and `x₀, x₁` acting trivially, every
coboundary `d⁰v` is supported on the `σ`-slot: `B¹ = {((S−1)v, 0, 0, 0)}`. -/
theorem b1w_split_shape (t : Marking C)
    (htau : ∀ v : V, t.τ • v = v) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (y : Fin 4 → V) :
    y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0] := by
  simp only [B1w, AddMonoidHom.mem_range]
  constructor <;> rintro ⟨v, rfl⟩ <;>
    exact ⟨v, funext fun i => by
      fin_cases i <;> simp only [d0, AddMonoidHom.mk'_apply, htau, hx0, hx1, sub_self]⟩

omit [Finite C] in
/-- On classes supported away from the `σ, τ` slots (`x 0 = x 1 = 0`, `y 0 = y 1 = 0`), the tame
relator value lies in the base slice `secHom '' C` (all its `σ, τ` inputs do), so its central
coordinate vanishes.  Hence the `mixedB` pairing on the `x₀`-supported normal forms is carried
entirely by the wild relator — the split/ramified Hessian is a pure wild-relator computation. -/
theorem heisMarking_tameValue_z_eq_zero (t : Marking C) (x : Fin 4 → V)
    (y : Fin 4 → ElemDual V) (hx0 : x 0 = 0) (hx1 : x 1 = 0) (hy0 : y 0 = 0) (hy1 : y 1 = 0) :
    (heisMarking t x y).tameValue.z = 0 := by
  have hσ : (heisMarking t x y).σ = secHom (A := V) t.σ := by
    simp only [heisMarking, secHom, hx0, hy0, MonoidHom.coe_mk, OneHom.coe_mk]
  have hτ : (heisMarking t x y).τ = secHom (A := V) t.τ := by
    simp only [heisMarking, secHom, hx1, hy1, MonoidHom.coe_mk, OneHom.coe_mk]
  have key : (heisMarking t x y).tameValue = secHom (A := V) t.tameValue := by
    simp only [Marking.tameValue, hσ, hτ, conjP, map_mul, map_inv, map_pow]
  rw [key]
  simp only [secHom, MonoidHom.coe_mk, OneHom.coe_mk]

/-- **Lemma 5.13, split case (i), cocycle shape**: if `T = 1` (trivial `τ`-action on a
nontrivial simple module), `Z¹ = {(a, 0, c, 0)}` and `B¹ = {((S−1)v, 0, 0, 0)}`.

Hypotheses (per `docs/orchestration/p13-normal-form-hypothesis-gap.md`): `hcore` supplies trivial wild action
(`wild_acts_trivially`); `hVS` is `V^S = 0`, i.e. `1 + S⁻¹` invertible — it excludes the trivial
module `𝔽₂` (where `1 + S⁻¹ = 0` and the `x 3 = 0` clause would fail; that module is handled
separately in `prop_5_15`).  `hU` is the σ-tameness (`σ₂ = U` acts trivially).  Both `hVS` and `hU`
are *derivable* in the split case — with `τ, x₀, x₁` acting trivially the `C`-action factors through
the cyclic `⟨σ̄⟩`, so a nontrivial simple `V` is a simple `𝔽₂[⟨σ⟩]`-module: `V^S = V^C = 0` and `σ`
has odd order (⇒ `σ₂ = 1`).  Those derivations need `t.Generates` and simple-cyclic rep theory, so
they are factored out as hypotheses here, keeping the normal-form proof pure finite-Fox calculus.
See `docs/orchestration/p13-normal-form-hypothesis-gap.md` §7.

Proved (the §5 proof layer): `B¹` half from `b1w_split_shape`; `Z¹` half from the tame row `d1Fun_tame_split`
(`= S⁻¹·x₁`) and the wild row `liftMarking_wildValue_u` (`= x₁ + (1+S⁻¹)·x₃`), with `x 1 = 0` from
`S⁻¹` injective and `x 3 = 0` from `hVS`. -/
theorem lemma_5_13_split (t : Marking C) (ht : t.TameRel) (_ : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) :
    (∀ x : Fin 4 → V, x ∈ Z1w (A := V) t ↔ x 1 = 0 ∧ x 3 = 0) ∧
    (∀ y : Fin 4 → V, y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0]) := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  refine ⟨fun x => ?_, fun y => b1w_split_shape t htau hx0 hx1 y⟩
  rw [Z1w, AddMonoidHom.mem_ker, show (d1 t) x = d1Fun t x from rfl, Prod.ext_iff]
  rw [d1Fun_tame_split t ht htau hV₂ x,
    show (d1Fun t x).2 = x 1 + x 3 + t.σ⁻¹ • x 3 from
      liftMarking_wildValue_u t x hV₂ hx0 hx1 htau hU]
  simp only [Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hx1z : x 1 = 0 := by rwa [inv_smul_eq_iff, smul_zero] at h1
    rw [hx1z, zero_add] at h2
    have h3 : t.σ⁻¹ • x 3 = x 3 :=
      (add_eq_zero_iff_neg_eq.mp h2).symm.trans (neg_eq_of_add_eq_zero_left (hV₂ (x 3)))
    exact ⟨hx1z, hVS _ (inv_smul_eq_iff.mp h3).symm⟩
  · rintro ⟨h1, h3⟩
    simp [h1, h3]

/-- **Lemma 5.13, ramified case (ii), unique normal form**: if `V^T = 0`, every degree-one
class has a unique representative supported on `x₀` (display (53)).

Hypothesis `hcore` supplies trivial wild action (`wild_acts_trivially`); the ramified condition
`V^T = 0` (`htau`) gives `1 + T` invertible.

**Hypothesis `hTodd`**: `τ`'s 2-primary part `powOmega2 t.τ` acts
trivially on `V`, i.e. `τ` acts with *odd* order on `V`.  This is the ramified analogue of the
split case's `hU : ∀ v, t.sigma2 • v = v` (`sigma2 = powOmega2 t.σ`), and is the arithmetic fact
that `τ = ` tame inertia is prime-to-2, so acts through an odd quotient on the `𝔽₂`-module `V`.
It is **required** (not implied by `V^T = 0`, which admits even-order fixed-point-free actions):
the wild-row aux offset `(powOmega2 p).u` is a geometric sum whose length is the `ω₂`-exponent,
and it collapses to `0` (via the `P = 0` norm ledger `WordLift.norm_eq_zero_of_fixedPointFree`)
exactly because the odd action-period divides that length.  Like `hU`/`hVS` in the split case,
this is factored out as an explicit hypothesis, supplied by the simple-factor analysis.
See `docs/orchestration/p13-normal-form-hypothesis-gap.md` for the counterexample and rationale.

**Signature note**: the trivial wild action is taken as hypotheses
`hx0`/`hx1` rather than derived from `(hsimple, hcore)` via `wild_acts_trivially` — so the lemma
applies to the contragredient dual `A∨` (whose wild-triviality transfers from `A`'s) without a
"dual of simple is simple" detour, mirroring the split-side `split_shapes_of_wild`.

No `hU` hypothesis is needed: the σ-tameness `∀ v, σ₂ • v = v` is *not derivable from
admissibility* (`S₃` on its 2-dim simple module and `C₅⋊C₄` on `𝔽₁₆`, markings `x₀=x₁=1`,
are admissible ramified counterexamples), and it is not needed: the `h₀`-row `x₂`-cancellation
happens in `g₀`-conjugate pairs (`liftMarking_h0_u_ramified`, via `conjP_u_of_base_trivial`). -/
theorem lemma_5_13_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    ∀ x ∈ Z1w (A := V) t, ∃! c : V, x - x0Supported c ∈ B1w (A := V) t := by
  -- `T − 1` is injective (`V^T = 0`) hence surjective on the finite space `V`.
  have hTsurj : Function.Surjective (fun w : V => t.τ • w - w) :=
    surjective_smul_sub_of_fixedPointFree htau
  intro x hx
  rw [Z1w, AddMonoidHom.mem_ker] at hx
  -- Wild row `S⁻¹·x₃ = 0` forces `x₃ = 0`.
  have hx3 : x 3 = 0 := by
    have hwild : (liftMarking t x).wildValue.u = 0 := congrArg Prod.snd hx
    rw [liftMarking_wildValue_u_ramified t x hV₂ hx0 hx1 htau hTodd] at hwild
    rw [← smul_inv_smul t.σ (x 3), hwild, smul_zero]
  -- `v = (T − 1)⁻¹ x₁`; subtracting `d⁰v` kills the `x₁`-slot.
  obtain ⟨v, hv⟩ := hTsurj (x 1)
  have hv2 : t.τ • v - v = x 1 := hv
  have hc0 : (x - d0 t v) 0 = x 0 - (t.σ • v - v) := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_zero]
  have hc1 : (x - d0 t v) 1 = 0 := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hv2, sub_self]
  have hxcob : d1Fun t (x - d0 t v) = 0 := by
    have hsub : d1 t (x - d0 t v) = d1 t x - d1 t (d0 t v) := (d1 t).map_sub x (d0 t v)
    rw [hx, show d1 t (d0 t v) = d1Fun t (d0 t v) from rfl, d1Fun_comp_d0 t ht hw v, sub_zero]
      at hsub
    exact hsub
  -- The reduced cocycle's tame row `σ⁻¹(T − 1)x'₀ = 0` forces `x'₀ = 0`, i.e. `x₀ = (S − 1)v`.
  have hx'0 : x 0 - (t.σ • v - v) = 0 := by
    have ht' : (d1Fun t (x - d0 t v)).1 = 0 := congrArg Prod.fst hxcob
    rw [d1Fun_tame t ht (x - d0 t v), hc0, hc1] at ht'
    simp only [smul_zero, add_zero, sub_zero] at ht'
    rw [sub_eq_zero] at ht'
    exact htau _ (by simpa only [smul_inv_smul] using congrArg (t.σ • ·) ht')
  have hx0v : x 0 = t.σ • v - v := sub_eq_zero.mp hx'0
  -- Hence `x − x0Supported(x₂) = d⁰v`, and `c = x₂` is the unique witness.
  have hcob : x - x0Supported (x 2) = d0 t v := by
    funext i
    fin_cases i <;> simp [Pi.sub_apply, x0Supported, d0, hx0, hx1, hx3, hx0v, ← hv2]
  refine ⟨x 2, ?_, fun c hc => ?_⟩
  · simp only [B1w, AddMonoidHom.mem_range]; exact ⟨v, hcob.symm⟩
  · simp only [B1w, AddMonoidHom.mem_range] at hc
    obtain ⟨w, hw'⟩ := hc
    have h := congrFun hw' 2
    have hcw : (0 : V) = x 2 - c := by simpa [d0, x0Supported, hx0, Pi.sub_apply] using h
    exact (sub_eq_zero.mp hcw.symm).symm

/-- **Lemma 5.13, pairing display (54), split case**: on `x₀`-supported representatives the
degree-one pairing is `(c, λ) ↦ λ(c)` when `T = 1`.

The proof uses the mixed Hessian ledger, Lemma 5.14 — `h₀ ↦ λ(c)` via
`classTwoIdentity` [needs `g₀ = σ₂²` trivial, i.e. `hU`], and the `[d₀,z₀]` term vanishes since
`P + 1 = 0` in char 2 for `T = 1`.  `hsimple`/`hcore` give the trivial wild action
(`wild_acts_trivially`); `hU` is the σ-tameness (derivable in split; see `lemma_5_13_split`). -/
theorem lemma_5_13_pairing_split (t : Marking C) (_ : t.TameRel) (_ : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V] (hcore : t.Pro2Core)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) (c : V) (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam) = lam c := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  show (heisMarking t (x0Supported c) (x0Supported lam)).tameValue.z
      + (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = lam c
  rw [heisMarking_tameValue_z_eq_zero t (x0Supported c) (x0Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValue_z t c lam hV₂ hx0 hx1 htau hU, zero_add]

/-- **Lemma 5.13, pairing display (54), ramified case**: when `V^T = 0` the pairing on
`x₀`-supported representatives is `(c, λ) ↦ λ((1 + U + U⁻¹)c)` for `U = S₂^ω`
(`Marking.sigma2`).

The tame relator's central coordinate vanishes on the x₀-supported rep
(`heisMarking_tameValue_z_eq_zero`), so the pairing is carried entirely by the wild relator
(`heisMarking_wildValue_z_ramified`): `h₀ ↦ λ(c)` (the shadow) plus the `[d₀,z₀]` symplectic term
`λ(Uc) + λ(U⁻¹c)` (nonzero here because `Dd₀ = c ≠ 0`, unlike the split `P + 1 = 0` collapse).

**Hypothesis `hTodd`** (added the §5 proof layer, mirroring the §5 proof layer's `lemma_5_13_ramified`): `τ`'s 2-primary part
acts trivially on `V` (tame inertia is prime-to-2), needed for the ramified `Dd₀ = c` via the
`P = 0` ledger.  Supplied per simple factor by the tame representation-theory proof.  The trivial wild action is taken as
hypotheses `hx0`/`hx1` (the Prop. 5.15 proof signature note on `lemma_5_13_ramified`). -/
theorem lemma_5_13_pairing_ramified (t : Marking C) (_ : t.TameRel) (_ : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (c : V)
    (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam)
      = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c) := by
  show (heisMarking t (x0Supported c) (x0Supported lam)).tameValue.z
      + (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = _
  rw [heisMarking_tameValue_z_eq_zero t (x0Supported c) (x0Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValue_z_ramified t c lam hV₂ hx0 hx1 htau hTodd, zero_add]

end NormalForms

section MainDuality

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/- **Prop. 5.15 lives in `GQ2/DualityAssembly.lean`.**  The proof
composes the dévissage strong induction `prop_5_15_of_simple` (`GQ2/DevissageInduction.lean`,
via `lemma_5_11`) with the simple case `selfDual_of_simple` (split/ramified dichotomy) — all of
which live in files importing *this* one, so proving it here would be an import cycle.  The
qualified name `GQ2.FoxH.prop_5_15` and the statement are unchanged. -/

/- **§§5.16–5.17 live in `GQ2/LocalLiftingDuality.lean`.**  `prop_5_16` (local
lifting duality) and its corollary `cor_5_17_card` live there so their proofs can invoke B6
(`GQ2.tateDuality`) and the `𝔽₂`-cup transport, which live in files that import *this* one —
proving them here would be an import cycle.  Both keep their `GQ2.FoxH.*` qualified names, so
downstream references are unaffected. -/

end MainDuality

end FoxH

end GQ2
