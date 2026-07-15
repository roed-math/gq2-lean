/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.FoxHeisenberg.Basic

@[expose] public section

/-!
# §5.2 definitions: the Heisenberg lift `H(A) ⋊ C` and the finite Stokes formula

Split off from `GQ2.FoxHeisenberg`, building on `GQ2.FoxHeisenberg.Basic`.  This file provides:

* the **Heisenberg lift group** `H(A) ⋊ C` (`HeisLift A C`) on `A × A^∨ × 𝔽₂ × C` with the §5.2
  multiplication `(a,λ,z)(a',λ',z') = (a+a', λ+λ', z+z'+λ(a'))` twisted by the diagonal
  `C`-action, and its API;
* the **mixed central coordinate** machinery (`section Mixed`);
* **Lemma 5.7**, the finite-word Stokes formula in its general free-group form (`stokesEval`,
  `expMod2`, and the proved tame exponent vector `expMod2_fgTame`).

See `GQ2.FoxHeisenberg` for the umbrella module docstring.
-/

namespace GQ2

namespace FoxH

/-! ## The Heisenberg lift group `H(A) ⋊ C`  (§5.2) -/

/-- `H(A) ⋊ C`: quadruples `(a, λ, z, g)` with the §5.2 multiplication
`(a,λ,z)(a',λ',z') = (a+a', λ+λ', z+z'+λ(a'))` twisted by the diagonal `C`-action.  The
central coordinate `z` is the carrier of the mixed derivatives. -/
@[ext] structure HeisLift (A C : Type*) [AddCommGroup A] where
  /-- The `A`-coordinate (the first derivative `D_u`). -/
  a : A
  /-- The dual coordinate (`D^∨_u`). -/
  l : ElemDual A
  /-- The central coordinate (`β_u`). -/
  z : ZMod 2
  /-- The base value in `C`. -/
  g : C

namespace HeisLift

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

noncomputable instance : One (HeisLift A C) := ⟨⟨0, 0, 0, 1⟩⟩
noncomputable instance : Mul (HeisLift A C) :=
  ⟨fun p q => ⟨p.a + p.g • q.a, p.l + p.g • q.l, p.z + q.z + p.l (p.g • q.a), p.g * q.g⟩⟩
noncomputable instance : Inv (HeisLift A C) :=
  ⟨fun p => ⟨-(p.g⁻¹ • p.a), -(p.g⁻¹ • p.l), p.z + p.l p.a, p.g⁻¹⟩⟩

omit [DistribMulAction C A] in
@[simp] theorem one_a : (1 : HeisLift A C).a = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_l : (1 : HeisLift A C).l = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_z : (1 : HeisLift A C).z = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_g : (1 : HeisLift A C).g = 1 := rfl

@[simp] theorem mul_a (p q : HeisLift A C) : (p * q).a = p.a + p.g • q.a := rfl
@[simp] theorem mul_l (p q : HeisLift A C) : (p * q).l = p.l + p.g • q.l := rfl
@[simp] theorem mul_z (p q : HeisLift A C) : (p * q).z = p.z + q.z + p.l (p.g • q.a) := rfl
@[simp] theorem mul_g (p q : HeisLift A C) : (p * q).g = p.g * q.g := rfl
@[simp] theorem inv_a (p : HeisLift A C) : p⁻¹.a = -(p.g⁻¹ • p.a) := rfl
@[simp] theorem inv_l (p : HeisLift A C) : p⁻¹.l = -(p.g⁻¹ • p.l) := rfl
@[simp] theorem inv_z (p : HeisLift A C) : p⁻¹.z = p.z + p.l p.a := rfl
@[simp] theorem inv_g (p : HeisLift A C) : p⁻¹.g = p.g⁻¹ := rfl

noncomputable instance : Group (HeisLift A C) where
  mul_assoc p q r := by
    ext
    · simp only [mul_a, mul_g, smul_add, mul_smul, add_assoc]
    · simp only [mul_l, mul_g, smul_add, mul_smul, add_assoc]
    · simp only [mul_z, mul_a, mul_l, mul_g, ElemDual.add_apply, ElemDual.smul_apply,
        map_add, smul_add, mul_smul, inv_smul_smul]
      ring
    · simp only [mul_g, mul_assoc]
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext
    · simp
    · simp only [mul_l, inv_l, inv_g, one_l, neg_add_cancel]
    · simp only [mul_z, inv_z, inv_l, inv_g, one_z, ElemDual.neg_apply,
        ElemDual.smul_apply, inv_inv, smul_inv_smul]
      linear_combination CharTwo.add_self_eq_zero p.z
    · simp

/-- `H(A) ⋊ C` is finite when `A` and `C` are (all four coordinates range over finite types). -/
instance [Finite A] [Finite C] : Finite (HeisLift A C) :=
  Finite.of_injective (fun p : HeisLift A C => (p.a, p.l, p.z, p.g)) fun p q h => by
    obtain ⟨pa, pl, pz, pg⟩ := p; obtain ⟨qa, ql, qz, qg⟩ := q; simpa using h

/-- The base projection `HeisLift A C →* C`. -/
def gHom : HeisLift A C →* C where
  toFun := HeisLift.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] private theorem gHom_apply (p : HeisLift A C) : gHom p = p.g := rfl

/-- The central element `⟨0, 0, w, 1⟩` (the paper's `z(w)`).  It is genuinely central. -/
noncomputable def zc (w : ZMod 2) : HeisLift A C := ⟨0, 0, w, 1⟩

omit [DistribMulAction C A] in
@[simp] theorem zc_z (w : ZMod 2) : (zc (A := A) (C := C) w).z = w := rfl

omit [DistribMulAction C A] in
@[simp] theorem zc_zero : zc (A := A) (C := C) (0 : ZMod 2) = 1 := rfl

private theorem mul_zc (p : HeisLift A C) (w : ZMod 2) : p * zc w = ⟨p.a, p.l, p.z + w, p.g⟩ := by
  ext <;> simp [zc]

@[simp] private theorem mul_zc_z (p : HeisLift A C) (w : ZMod 2) : (p * zc w).z = p.z + w := by
  rw [mul_zc]

/-- `zc` is additive in its argument: `z(u+v) = z(u)·z(v)`. -/
theorem zc_add (u v : ZMod 2) : zc (A := A) (C := C) (u + v) = zc u * zc v := by
  ext <;> simp [zc]

/-- `zc w` is central in `H(A) ⋊ C`. -/
theorem zc_comm (w : ZMod 2) (q : HeisLift A C) : zc w * q = q * zc w := by
  ext <;> simp [zc, add_comm]

/-- The central factor `z(·)` as a homomorphism `Multiplicative (ZMod 2) →* H(A) ⋊ C`. -/
noncomputable def zcHom : Multiplicative (ZMod 2) →* HeisLift A C where
  toFun w := zc (Multiplicative.toAdd w)
  map_one' := rfl
  map_mul' _ _ := zc_add _ _

@[simp] private theorem zcHom_apply (w : Multiplicative (ZMod 2)) :
    zcHom (A := A) (C := C) w = zc (Multiplicative.toAdd w) := rfl

/-- The image of `zcHom` is central. -/
theorem zcHom_comm (v : Multiplicative (ZMod 2)) (q : HeisLift A C) :
    zcHom v * q = q * zcHom v := zc_comm _ _

/-- **The conjugation computation** `p_a⁻¹ · ⟨0,λ,0,g⟩ · p_a = ⟨g·a − a, λ, λ(g·a), g⟩`, where
`p_a = ⟨a,0,0,1⟩`.  This is the algebraic heart of Lemma 5.7's left form: conjugating a
`g=1`-slot generator by the `A`-translation `p_a` shifts its `A`-coordinate by the coboundary
`g·a − a` and drops the central defect `λ(g·a)`. -/
theorem conj_gen (a : A) (lam : ElemDual A) (g : C) :
    (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * ⟨0, lam, 0, g⟩ * ⟨a, 0, 0, 1⟩
      = ⟨g • a - a, lam, lam (g • a), g⟩ := by
  have hinv : (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ = ⟨-a, 0, 0, 1⟩ := by ext <;> simp
  rw [hinv]
  ext
  · simp only [mul_a, mul_g, smul_zero, one_mul, add_zero]; abel
  · simp
  · simp
  · simp

/-- **The dual conjugation computation** `q_λ⁻¹ · ⟨a,0,0,g⟩ · q_λ = ⟨a, g·λ − λ, −λ(a), g⟩`, where
`q_λ = ⟨0,λ,0,1⟩`.  This is the algebraic heart of Lemma 5.7's right form: conjugating a
`g=1`-slot generator by the dual translation `q_λ` shifts its dual coordinate by the coboundary
`g·λ − λ` and records the central defect `−λ(a)`. -/
theorem conj_gen_r (a : A) (lam : ElemDual A) (g : C) :
    (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * ⟨a, 0, 0, g⟩ * ⟨0, lam, 0, 1⟩
      = ⟨a, g • lam - lam, -(lam a), g⟩ := by
  have hinv : (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ = ⟨0, -lam, 0, 1⟩ := by ext <;> simp
  rw [hinv]
  ext
  · simp
  · simp only [mul_l, mul_g, smul_zero, one_mul, add_zero]; abel_nf
  · simp
  · simp

/-- **The Heisenberg commutator central coordinate (symplectic `B`-form)**, in the `g = 1` fiber
`H(A) = A × A^∨ × 𝔽₂`.  For `p, q` with trivial base value, the central coordinate of the
commutator `[p,q] = p⁻¹q⁻¹pq` is the alternating pairing `p.l(q.a) + q.l(p.a)` (the sign is
absorbed in char 2).  This is the extraspecial/Heisenberg central kernel `B` of Lemma 5.14: it
supplies the `[d₀,z₀]` mixed contribution `λ(U⁻¹c) + (U^∨λ)(c) = λ((U⁻¹+U)c)`. -/
theorem commP_z_fiber (p q : HeisLift A C) (hp : p.g = 1) (hq : q.g = 1) :
    (commP p q).z = p.l (q.a) + q.l (p.a) := by
  simp only [commP, mul_z, mul_l, mul_g, inv_z, inv_a, inv_l, inv_g, hp, hq,
    inv_one, one_smul, mul_one, map_neg, ElemDual.add_apply, ElemDual.neg_apply]
  -- What remains is a linear identity over `ZMod 2` in the six atomic central values;
  -- generalise them and decide the `2⁶` cases.
  generalize p.z = a1; generalize q.z = a2; generalize p.l p.a = a3
  generalize q.l q.a = a4; generalize p.l q.a = a5; generalize q.l p.a = a6
  revert a1 a2 a3 a4 a5 a6; decide

/-! ### The trivially-based toolkit for the mixed Hessian (Lemma 5.14)

Mirror of the `WordLift` toolkit for the central coordinate.  On elements whose base `g` acts
trivially on the module, `.a` and `.l` are additive homs and `.z` follows the Heisenberg cocycle
`(p*q).z = p.z + q.z + p.l(q.a)`.  This drives the `h₀ ↦ λ(c)` / `[d₀,z₀] ↦ 0` central ledger. -/

/-- A `C`-element acting trivially on the module acts trivially on its `𝔽₂`-dual
(contragredient). -/
theorem smul_elemdual_trivial (g : C) (hg : ∀ a : A, g • a = a) (lam : ElemDual A) :
    g • lam = lam := by
  ext a
  rw [ElemDual.smul_apply, inv_smul_eq_iff.mpr (hg a).symm]

theorem mul_g_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (p * q).g • a = a := by rw [mul_g, mul_smul, hq, hp]

theorem inv_g_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) : p⁻¹.g • a = a :=
  inv_smul_eq_iff.mpr (hp a).symm

theorem conjP_g_trivial (p g : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) :
    (conjP p g).g • a = a := by
  rw [conjP, mul_g, mul_g, inv_g, mul_smul, mul_smul, hp, ← mul_smul, inv_mul_cancel, one_smul]

theorem commP_g_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (commP p q).g • a = a := by
  rw [commP]
  exact mul_g_trivial _ _ (mul_g_trivial _ _ (mul_g_trivial _ _ (inv_g_trivial p hp)
    (inv_g_trivial q hq)) hp) hq a

theorem mul_a_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).a = p.a + q.a := by rw [mul_a, hp]

theorem mul_l_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).l = p.l + q.l := by rw [mul_l, smul_elemdual_trivial _ hp]

theorem mul_z_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).z = p.z + q.z + p.l q.a := by rw [mul_z, hp]

theorem inv_a_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.a = -p.a := by
  rw [inv_a, inv_smul_eq_iff.mpr (hp p.a).symm]

theorem inv_l_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.l = -p.l := by
  rw [inv_l, smul_elemdual_trivial _ fun a => inv_smul_eq_iff.mpr (hp a).symm]

/-! Conjugation by a **g-slice** element `g` (`g.a = 0`, `g.l = 0`, `g.z = 0`) with trivially-acting
base preserves all three Heisenberg coordinates — it only conjugates the base.  This is `φ = conj by
g₀` in the `h₀`-shadow (`g₀ = σ₂²` lands in the base slice on the x₀-supported rep). -/

theorem conjP_a_of_gslice (p g : HeisLift A C) (hga : g.a = 0) (hgt : ∀ a : A, g.g • a = a) :
    (conjP p g).a = p.a := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hgt a).symm
  simp only [conjP, mul_a, mul_g, inv_a, inv_g, hga, smul_zero, neg_zero, add_zero, zero_add, hgi]

theorem conjP_l_of_gslice (p g : HeisLift A C) (hgl : g.l = 0) (hgt : ∀ a : A, g.g • a = a) :
    (conjP p g).l = p.l := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hgt a).symm
  simp only [conjP, mul_l, mul_g, inv_l, inv_g, hgl, smul_zero, neg_zero, add_zero, zero_add,
    smul_elemdual_trivial _ hgi]

theorem conjP_z_of_gslice (p g : HeisLift A C) (hga : g.a = 0) (hgl : g.l = 0) (hgz : g.z = 0)
    (hgt : ∀ a : A, g.g • a = a) : (conjP p g).z = p.z := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hgt a).symm
  simp only [conjP, mul_z, mul_l, mul_g, inv_z, inv_l, inv_g, hga, hgl, hgz,
    smul_zero, neg_zero, map_zero, add_zero, zero_add, ElemDual.zero_apply,
    smul_elemdual_trivial _ hgi]

/-- Conjugation by a **base-slice** element `g` (`g.a = 0`), whose base may act *nontrivially*:
`(conjP p g).a = g.g⁻¹ • p.a`.  Generalises `conjP_a_of_gslice` (drops the base-triviality; used in
the ramified Hessian where `g₀ = σ₂²` acts by `U²`). -/
theorem conjP_a_of_slice (p g : HeisLift A C) (hga : g.a = 0) :
    (conjP p g).a = g.g⁻¹ • p.a := by
  simp only [conjP, mul_a, mul_g, inv_a, inv_g, hga, smul_zero, neg_zero, add_zero, zero_add]

/-- Conjugation by a base-slice element `g` (`g.l = 0`): `(conjP p g).l = g.g⁻¹ • p.l` (dual). -/
theorem conjP_l_of_slice (p g : HeisLift A C) (hgl : g.l = 0) :
    (conjP p g).l = g.g⁻¹ • p.l := by
  simp only [conjP, mul_l, mul_g, inv_l, inv_g, hgl, smul_zero, neg_zero, add_zero, zero_add]

/-- Conjugation by a base-slice element `g` (`a = l = z = 0`) fixes the central coordinate, even
when the base `g.g` acts nontrivially: `(conjP p g).z = p.z`. -/
theorem conjP_z_of_slice (p g : HeisLift A C) (hga : g.a = 0) (hgl : g.l = 0) (hgz : g.z = 0) :
    (conjP p g).z = p.z := by
  simp only [conjP, mul_z, mul_l, mul_g, inv_z, inv_l, inv_g, hga, hgl, hgz,
    smul_zero, neg_zero, map_zero, add_zero, zero_add, ElemDual.zero_apply]

/-- The commutator symplectic `B`-form for **trivially-based** elements (not just the `g = 1`
fiber): `[p,q].z = p.l(q.a) + q.l(p.a)`.  Gives `c₀ = [d₀,z₀] ↦ 0` once `d₀.a = d₀.l = 0`. -/
theorem commP_z_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).z = p.l (q.a) + q.l (p.a) := by
  have hpi : ∀ a : A, p.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hp a).symm
  have hqi : ∀ a : A, q.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hq a).symm
  simp only [commP, mul_z, mul_l, mul_g, inv_z, inv_a, inv_l, inv_g, mul_smul, hp,
    hpi, hqi, smul_elemdual_trivial _ hpi, smul_elemdual_trivial _ hqi, map_neg,
    ElemDual.add_apply, ElemDual.neg_apply]
  generalize p.z = a1; generalize q.z = a2; generalize p.l p.a = a3
  generalize q.l q.a = a4; generalize p.l q.a = a5; generalize q.l p.a = a6
  revert a1 a2 a3 a4 a5 a6; decide

/-- The `A`-coordinate of a commutator of trivially-based elements vanishes (`.a` is additive). -/
theorem commP_a_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).a = 0 := by
  have hpi := inv_g_trivial p hp
  have hqi := inv_g_trivial q hq
  rw [commP, mul_a_of_trivial _ q (mul_g_trivial _ _ (mul_g_trivial _ _ hpi hqi) hp),
    mul_a_of_trivial _ p (mul_g_trivial _ _ hpi hqi), mul_a_of_trivial _ q⁻¹ hpi,
    inv_a_of_trivial p hp, inv_a_of_trivial q hq]
  abel

end HeisLift

section Mixed

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The Heisenberg-lifted marking over `t` with offsets `x` and dual offsets `y`. -/
noncomputable def heisMarking (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    Marking (HeisLift A C) :=
  ⟨⟨x 0, y 0, 0, t.σ⟩, ⟨x 1, y 1, 0, t.τ⟩, ⟨x 2, y 2, 0, t.x₀⟩, ⟨x 3, y 3, 0, t.x₁⟩⟩

/-- **`B_{ρ,A}`** (Prop 5.8): the *traced* mixed central coordinate — the sum of the central
coordinates of the two evaluated relators (not the central coordinate of their product). -/
noncomputable def mixedB (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) : ZMod 2 :=
  ((heisMarking t x y).tameValue).z + ((heisMarking t x y).wildValue).z

end Mixed

/-! ## Lemma 5.7: the finite-word Stokes formula (general form) -/

section Stokes

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A] {n : ℕ}

/-- Evaluation of an ordinary free-group word after the substitution
`gᵢ ↦ (xᵢ, yᵢ, 0; cᵢ) ∈ H(A) ⋊ C`  (Lemma 5.7). -/
noncomputable def stokesEval (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* HeisLift A C :=
  FreeGroup.lift fun i => ⟨x i, y i, 0, c i⟩

/-- The mod-2 total exponent `ε_i(r)` of the `i`-th generator in an ordinary word. -/
def expMod2 {n : ℕ} (i : Fin n) : FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = i then 1 else 0)

/-- The base coordinate of a Stokes evaluation is the underlying word value in `C`. -/
@[simp] theorem stokesEval_g (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) : (stokesEval c x y r).g = FreeGroup.lift c r := by
  have h : (HeisLift.gHom).comp (stokesEval c x y) = FreeGroup.lift c :=
    FreeGroup.ext_hom _ _ fun i => rfl
  exact DFunLike.congr_fun h r

/-- With zero `A`-offsets, the `A`- and central coordinates of a Stokes evaluation vanish (the
elements `⟨0, λ, 0, g⟩` form a subgroup on which the central defect is inert). -/
theorem stokesEval_zero (c : Fin n → C) (y : Fin n → ElemDual A) (r : FreeGroup (Fin n)) :
    (stokesEval c 0 y r).a = 0 ∧ (stokesEval c 0 y r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩ (fun i => ⟨by simp [stokesEval], by simp [stokesEval]⟩)
    (fun i ih => ?_) (fun x₁ x₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_a, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, map_zero, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_a, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₂.1, smul_zero, map_zero, add_zero, add_zero]⟩

/-! ### The conjugation model of the coboundary evaluation (Lemma 5.7, left form)

The generic coboundary substitution `x = d⁰a` factors, one generator at a time, as
`⟨cᵢa−a, yᵢ, 0, cᵢ⟩ = p_a⁻¹ · ⟨0, yᵢ, 0, cᵢ⟩ · p_a · z(yᵢ(cᵢa))`  (with `p_a = ⟨a,0,0,1⟩`).
Because `z(·)` is central, the per-generator central factors telescope into a single
`z(Σᵢ εᵢ(r)·yᵢ(cᵢa))`, and the conjugation commutes with word evaluation.  This makes
`stokesEval c (d⁰a) y = conjPa a ∘ stokesEval c 0 y  ·  z ∘ epsWord` an identity of homomorphisms,
which we prove by `FreeGroup.ext_hom` and then read off the `z`-coordinate. -/

/-- Conjugation `q ↦ p_a⁻¹ · q · p_a` by the `A`-translation `p_a = ⟨a,0,0,1⟩`, as a group hom. -/
noncomputable def conjPa (a : A) : HeisLift A C →* HeisLift A C where
  toFun q := (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨a, 0, 0, 1⟩
  map_one' := by group
  map_mul' q q' := by group

@[simp] private theorem conjPa_apply (a : A) (q : HeisLift A C) :
    conjPa a q = (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨a, 0, 0, 1⟩ := rfl

/-- The `z`-coordinate of `p_a⁻¹ · q · p_a` when `q` sits in the `g`-slice (`q.a = 0`, `q.z = 0`):
conjugation records the central defect `q.l (q.g · a)`. -/
theorem conjPa_z (a : A) (q : HeisLift A C) (ha : q.a = 0) (hz : q.z = 0) :
    (conjPa a q).z = q.l (q.g • a) := by
  obtain ⟨qa, ql, qz, qg⟩ := q
  subst ha; subst hz
  rw [conjPa_apply, HeisLift.conj_gen]

/-- The **central exponent word** `r ↦ ∏ᵢ z(εᵢ(r)·fᵢ)` for a mod-2 coefficient vector `f`,
packaged as a hom to `Multiplicative (ZMod 2)` so that `z ∘ freeExp f` is the telescoped
central factor of a Stokes evaluation. -/
noncomputable def freeExp (f : Fin n → ZMod 2) : FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (f i)

/-- The additive value of `freeExp f` is the ε-counting sum `Σᵢ εᵢ(r)·fᵢ` (mod 2): each generator
`i` contributes `fᵢ` once per occurrence, so mod 2 exactly `εᵢ(r)` times. -/
theorem freeExp_toAdd (f : Fin n → ZMod 2) (r : FreeGroup (Fin n)) :
    Multiplicative.toAdd (freeExp f r) = ∑ i, Multiplicative.toAdd (expMod2 i r) * f i := by
  refine FreeGroup.induction_on r ?_ ?_ ?_ ?_
  · simp [freeExp, expMod2]
  · intro k
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [freeExp, expMod2, FreeGroup.lift_apply_of]
    · intro i _ hik
      simp [expMod2, FreeGroup.lift_apply_of, if_neg (Ne.symm hik)]
  · intro k ih
    simp only [map_inv, toAdd_inv, CharTwo.neg_eq]
    exact ih
  · intro x1 x2 ih1 ih2
    simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib, ih1, ih2]

/-- The **central ε-word** of the left form: `r ↦ ∏ᵢ z(εᵢ(r)·yᵢ(cᵢa))`. -/
noncomputable def epsWord (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  freeExp (fun i => y i (c i • a))

/-- `epsWord`'s additive value is the ε-counting sum `Σᵢ εᵢ(r)·yᵢ(cᵢa)` (mod 2). -/
theorem epsWord_toAdd (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) (r : FreeGroup (Fin n)) :
    Multiplicative.toAdd (epsWord c a y r)
      = ∑ i, Multiplicative.toAdd (expMod2 i r) * (y i (c i • a)) :=
  freeExp_toAdd _ r

/-- The RHS conjugation model of `stokesEval c (d⁰a) y`: conjugate the `y`-only evaluation by
`p_a` and multiply by the telescoped central factor. -/
noncomputable def stokesRhs (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* HeisLift A C where
  toFun w := conjPa a (stokesEval c 0 y w) * HeisLift.zcHom (epsWord c a y w)
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul]
    exact Commute.mul_mul_mul_comm
      (HeisLift.zcHom_comm (epsWord c a y w) (conjPa a (stokesEval c 0 y w'))).symm _ _

/-- **The Lemma 5.7 factorization** (identity of homomorphisms): `stokesEval` at the coboundary
`d⁰a` equals `conjPa a` of the `y`-only evaluation, corrected by the central ε-word. -/
theorem stokesEval_eq_rhs (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    stokesEval c (fun i => c i • a - a) y = stokesRhs c a y := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  have hE : stokesEval c (fun i => c i • a - a) y (FreeGroup.of i)
      = ⟨c i • a - a, y i, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have hE0 : stokesEval c 0 y (FreeGroup.of i) = ⟨0, y i, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have heps : epsWord c a y (FreeGroup.of i) = Multiplicative.ofAdd (y i (c i • a)) := by
    simp [epsWord, freeExp, FreeGroup.lift_apply_of]
  show stokesEval c (fun i => c i • a - a) y (FreeGroup.of i)
      = conjPa a (stokesEval c 0 y (FreeGroup.of i))
        * HeisLift.zcHom (epsWord c a y (FreeGroup.of i))
  rw [hE, hE0, heps, conjPa_apply, HeisLift.conj_gen, HeisLift.zcHom_apply, toAdd_ofAdd,
    HeisLift.mul_zc, CharTwo.add_self_eq_zero]

/-- **Lemma 5.7, display (38)**: for a word `r` with trivial lower value, evaluating at the
generic coboundary `x = d⁰a = ((cᵢ−1)a)ᵢ` gives
`β_r(d⁰a, y) = ⟨a, L^{A^∨}_r(y)⟩ + Σᵢ εᵢ(r)·yᵢ(cᵢa)`. -/
theorem lemma_5_7_left (c : Fin n → C) (r : FreeGroup (Fin n))
    (hr : FreeGroup.lift c r = 1) (a : A) (y : Fin n → ElemDual A) :
    (stokesEval c (fun i => c i • a - a) y r).z
      = (stokesEval c 0 y r).l a
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (y i (c i • a)) := by
  rw [stokesEval_eq_rhs c a y]
  show (conjPa a (stokesEval c 0 y r) * HeisLift.zcHom (epsWord c a y r)).z = _
  rw [HeisLift.zcHom_apply, HeisLift.mul_zc_z, epsWord_toAdd]
  have hg : (stokesEval c 0 y r).g = 1 := by rw [stokesEval_g]; exact hr
  rw [conjPa_z a _ (stokesEval_zero c y r).1 (stokesEval_zero c y r).2, hg, one_smul]

/-! ### The dual conjugation model (Lemma 5.7, right form)

The dual coboundary substitution `y = d⁰λ` factors, one generator at a time, as
`⟨xᵢ, cᵢλ−λ, 0, cᵢ⟩ = q_λ⁻¹ · ⟨xᵢ, 0, 0, cᵢ⟩ · q_λ · z(λ(xᵢ))`  (with `q_λ = ⟨0,λ,0,1⟩`),
mirroring the left form with the roles of the `A`- and dual coordinates exchanged. -/

/-- Conjugation `q ↦ q_λ⁻¹ · q · q_λ` by the dual translation `q_λ = ⟨0,λ,0,1⟩`. -/
noncomputable def conjQlam (lam : ElemDual A) : HeisLift A C →* HeisLift A C where
  toFun q := (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨0, lam, 0, 1⟩
  map_one' := by group
  map_mul' q q' := by group

@[simp] private theorem conjQlam_apply (lam : ElemDual A) (q : HeisLift A C) :
    conjQlam lam q = (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨0, lam, 0, 1⟩ := rfl

/-- The `z`-coordinate of `q_λ⁻¹ · q · q_λ` when `q` sits in the `g`-slice (`q.l = 0`, `q.z = 0`):
conjugation records the central defect `λ(q.a)` (the sign is absorbed mod 2). -/
theorem conjQlam_z (lam : ElemDual A) (q : HeisLift A C) (hl : q.l = 0) (hz : q.z = 0) :
    (conjQlam lam q).z = lam q.a := by
  obtain ⟨qa, ql, qz, qg⟩ := q
  subst hl; subst hz
  rw [conjQlam_apply, HeisLift.conj_gen_r]
  exact CharTwo.neg_eq _

/-- With zero dual offsets, the dual- and central coordinates of a Stokes evaluation vanish. -/
theorem stokesEval_zero_r (c : Fin n → C) (x : Fin n → A) (r : FreeGroup (Fin n)) :
    (stokesEval c x 0 r).l = 0 ∧ (stokesEval c x 0 r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩ (fun i => ⟨by simp [stokesEval], by simp [stokesEval]⟩)
    (fun i ih => ?_) (fun x₁ x₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_l, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, ElemDual.zero_apply, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_l, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₁.1, ElemDual.zero_apply, add_zero, add_zero]⟩

/-- The RHS conjugation model of `stokesEval c x (d⁰λ)` (dual form). -/
noncomputable def stokesRhsR (c : Fin n → C) (lam : ElemDual A) (x : Fin n → A) :
    FreeGroup (Fin n) →* HeisLift A C where
  toFun w := conjQlam lam (stokesEval c x 0 w) * HeisLift.zcHom (freeExp (fun i => lam (x i)) w)
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul]
    exact Commute.mul_mul_mul_comm (HeisLift.zcHom_comm (freeExp (fun i => lam (x i)) w)
      (conjQlam lam (stokesEval c x 0 w'))).symm _ _

/-- **The Lemma 5.7 factorization** (dual form): `stokesEval` at the dual coboundary `d⁰λ` equals
`conjQlam lam` of the `x`-only evaluation, corrected by the central ε-word. -/
theorem stokesEval_eq_rhsR (c : Fin n → C) (lam : ElemDual A) (x : Fin n → A) :
    stokesEval c x (fun i => c i • lam - lam) = stokesRhsR c lam x := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  have hE : stokesEval c x (fun i => c i • lam - lam) (FreeGroup.of i)
      = ⟨x i, c i • lam - lam, 0, c i⟩ := by simp [stokesEval, FreeGroup.lift_apply_of]
  have hE0 : stokesEval c x 0 (FreeGroup.of i) = ⟨x i, 0, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have heps : freeExp (fun i => lam (x i)) (FreeGroup.of i) = Multiplicative.ofAdd (lam (x i)) := by
    simp [freeExp, FreeGroup.lift_apply_of]
  show stokesEval c x (fun i => c i • lam - lam) (FreeGroup.of i)
      = conjQlam lam (stokesEval c x 0 (FreeGroup.of i))
        * HeisLift.zcHom (freeExp (fun i => lam (x i)) (FreeGroup.of i))
  rw [hE, hE0, heps, conjQlam_apply, HeisLift.conj_gen_r, HeisLift.zcHom_apply, toAdd_ofAdd,
    HeisLift.mul_zc, neg_add_cancel]

/-- **Lemma 5.7, display (39)**: the dual-variable form,
`β_r(x, d⁰λ) = ⟨L^A_r(x), λ⟩ + Σᵢ εᵢ(r)·λ(xᵢ)`.  (The lower-value hypothesis `hr` is recorded for
symmetry with the left form; the dual central defect is `g`-independent, so it is not needed
here.) -/
theorem lemma_5_7_right (c : Fin n → C) (r : FreeGroup (Fin n))
    (_hr : FreeGroup.lift c r = 1) (x : Fin n → A) (lam : ElemDual A) :
    (stokesEval c x (fun i => c i • lam - lam) r).z
      = lam ((stokesEval c x 0 r).a)
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (lam (x i)) := by
  rw [stokesEval_eq_rhsR c lam x]
  show (conjQlam lam (stokesEval c x 0 r)
    * HeisLift.zcHom (freeExp (fun i => lam (x i)) r)).z = _
  rw [HeisLift.zcHom_apply, HeisLift.mul_zc_z, freeExp_toAdd,
    conjQlam_z lam _ (stokesEval_zero_r c x r).1 (stokesEval_zero_r c x r).2]

/-- The free-group tame word `τ^σ · (τ²)⁻¹` on four letters (for the exponent stress test). -/
def fgTame : FreeGroup (Fin 4) :=
  conjP (FreeGroup.of 1) (FreeGroup.of 0) * (FreeGroup.of 1 ^ 2)⁻¹

/-- **Stress test** (Prop 5.8's proof, exponent claim): the tame word's mod-2 exponent vector
is `(0, 1, 0, 0)` — odd total `τ`-exponent, even everything else. -/
theorem expMod2_fgTame :
    (fun i => Multiplicative.toAdd (expMod2 i fgTame)) = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
  · simp only [fgTame, expMod2, conjP, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    decide

end Stokes

end FoxH

end GQ2
