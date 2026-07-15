/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.CupProduct
public import GQ2.Statement
public import GQ2.Subdirect

@[expose] public section

/-!
# §5 definitions: the word complex `(30)/(31)` and the lift group `A ⋊ C`

The definition layer of the paper's §5 finite (candidate-side) cochain theory, split off from
`GQ2.FoxHeisenberg`.  For a finite lower target `C` and an elementary `𝔽₂[C]`-module `A` this file
provides:

* the **relator values** `Marking.tameValue = τ^σ (τ²)⁻¹` and
  `Marking.wildValue = h₀u₁⁻¹x₁^σc₀` (relations (5)/(6) as elements) with their naturality lemmas;
* the **lift group** `A ⋊ C` (`WordLift A C`) with the paper's convention
  `(u, g)(v, h) = (u + g•v, gh)`;
* the **finite word complex** (30)/(31): `d0`, `d1Fun`/`d1`, `Z1w/H0w/H1w/H2w`, and the proved
  tame-row stress test `d1Fun_tame`;
* the `𝔽₂`-dual `ElemDual A := A →+ ZMod 2` (the Tate-duality interface's def-synonym recipe) with its contragredient
  `C`-action, the shared helper `ElemDual.add_self_eq_zero`, and the evaluation pairing `dualEval`.

See `GQ2.FoxHeisenberg` for the umbrella module docstring.
-/

namespace GQ2

/-! ## Relations (5)/(6) as elements of any marked group -/

/-- The **tame relator value** `τ^σ · (τ²)⁻¹` at a marking (relation (5) as an element). -/
def Marking.tameValue {G : Type*} [Group G] (t : Marking G) : G :=
  conjP t.τ t.σ * (t.τ ^ 2)⁻¹

/-- The tame relator dies iff the tame relation holds. -/
@[simp] theorem Marking.tameValue_eq_one_iff {G : Type*} [Group G] (t : Marking G) :
    t.tameValue = 1 ↔ t.TameRel :=
  mul_inv_eq_one

/-- The **wild relator value** `h₀ · u₁⁻¹ · x₁^σ · c₀` at a marking (relation (6) as an
element; the `ω₂`-powers are `powOmega2`). -/
noncomputable def Marking.wildValue {G : Type*} [Group G] (t : Marking G) : G :=
  t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0

/-- The wild relator dies iff the wild relation holds. -/
@[simp] theorem Marking.wildValue_eq_one_iff {G : Type*} [Group G] (t : Marking G) :
    t.wildValue = 1 ↔ t.WildRel :=
  Iff.rfl

/-- **Naturality of the tame relator value** under a group homomorphism.  (No `ω₂`-power occurs
in the tame word, so no finiteness is needed.) -/
theorem Marking.map_tameValue {G H : Type*} [Group G] [Group H] (φ : G →* H) (t : Marking G) :
    (t.map φ).tameValue = φ t.tameValue := by
  simp only [tameValue, Marking.map_σ, Marking.map_τ, map_mul, map_inv, map_pow,
    Marking.map_conjP]

/-- **Naturality of the wild relator value** under a group homomorphism.  The `ω₂`-powers in the
wild word push through `φ` via `powOmega2_map`, which needs the source group finite. -/
theorem Marking.map_wildValue {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H)
    (t : Marking G) : (t.map φ).wildValue = φ t.wildValue := by
  simp only [wildValue, Marking.map_h0, Marking.map_u1, Marking.map_x₁, Marking.map_σ,
    Marking.map_c0, map_mul, map_inv, Marking.map_conjP]

namespace FoxH

/-! ## The lift group `A ⋊ C`  (paper convention `(u,g)(v,h) = (u + g•v, gh)`) -/

/-- The lift group `A ⋊ C` of §5: pairs `(u, g)` with the multiplication of Lemma 5.5's proof,
`(u, g)(v, h) = (u + g•v, gh)`. -/
@[ext] structure WordLift (A C : Type*) where
  /-- The `A`-offset of the lift. -/
  u : A
  /-- The base value in `C`. -/
  g : C

namespace WordLift

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

instance : One (WordLift A C) := ⟨⟨0, 1⟩⟩
instance : Mul (WordLift A C) := ⟨fun p q => ⟨p.u + p.g • q.u, p.g * q.g⟩⟩
instance : Inv (WordLift A C) := ⟨fun p => ⟨-(p.g⁻¹ • p.u), p.g⁻¹⟩⟩

omit [DistribMulAction C A] in
@[simp] theorem one_u : (1 : WordLift A C).u = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_g : (1 : WordLift A C).g = 1 := rfl

@[simp] theorem mul_u (p q : WordLift A C) : (p * q).u = p.u + p.g • q.u := rfl
@[simp] theorem mul_g (p q : WordLift A C) : (p * q).g = p.g * q.g := rfl
@[simp] theorem inv_u (p : WordLift A C) : p⁻¹.u = -(p.g⁻¹ • p.u) := rfl
@[simp] theorem inv_g (p : WordLift A C) : p⁻¹.g = p.g⁻¹ := rfl

instance : Group (WordLift A C) where
  mul_assoc p q r := by
    ext <;> simp only [mul_u, mul_g, smul_add, mul_smul, add_assoc, mul_assoc]
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- `WordLift A C ≃ A × C` (the underlying data), for the finiteness instance. -/
def equivProd : WordLift A C ≃ A × C where
  toFun p := (p.u, p.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite A] [Finite C] : Finite (WordLift A C) := Finite.of_equiv _ equivProd.symm

variable {A' : Type*} [AddCommGroup A'] [DistribMulAction C A']

/-- **Coefficient functoriality**: a `C`-equivariant `f : A →+ A'` induces a group homomorphism
`WordLift A C →* WordLift A' C` (the identity on the base `C`). -/
def map (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a) :
    WordLift A C →* WordLift A' C where
  toFun p := ⟨f p.u, p.g⟩
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp [hf]

@[simp] theorem map_u (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (p : WordLift A C) : (map f hf p).u = f p.u := rfl

@[simp] theorem map_g (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (p : WordLift A C) : (map f hf p).g = p.g := rfl

/-- The base embedding `C →* WordLift A C`, `g ↦ (0, g)` (the offset-zero lift). -/
def baseEmbed : C →* WordLift A C where
  toFun g := ⟨0, g⟩
  map_one' := rfl
  map_mul' g h := by ext <;> simp

@[simp] private theorem baseEmbed_apply (g : C) : (baseEmbed (A := A) g) = ⟨0, g⟩ := rfl

/-- Conjugating a base generator `(0, g)` by `(v, 1)` produces the coboundary offset
`(g • v − v, g)` — the shape of `d⁰`. -/
theorem conj_baseEmbed (v : A) (g : C) :
    (⟨v, 1⟩ : WordLift A C)⁻¹ * ⟨0, g⟩ * ⟨v, 1⟩ = ⟨g • v - v, g⟩ := by
  ext
  · simp only [mul_u, mul_g, inv_u, inv_g, inv_one, one_smul, smul_zero, one_mul, add_zero]
    abel
  · simp only [mul_g, inv_g, inv_one, one_mul, mul_one]

/-- The base coordinate of a power is the power of the base (`.g` is multiplicative). -/
@[simp] theorem pow_g (p : WordLift A C) (n : ℕ) : (p ^ n).g = p.g ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, mul_g, ih]

/-- **The norm-of-power (geometric sum) formula** — the source of the paper's "norm projector"
`P = 1 + T + ⋯ + Tᵉ⁻¹` in the finite Fox rules (Lemma 5.4/5.5).  The `A`-offset of `pⁿ` is the
partial norm `(1 + g + ⋯ + gⁿ⁻¹) • u` of the offset `u` under the base action `g`. -/
theorem pow_u (p : WordLift A C) (n : ℕ) :
    (p ^ n).u = ∑ i ∈ Finset.range n, p.g ^ i • p.u := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_u, ih, pow_g, Finset.sum_range_succ]

/-- **Norm collapse under a trivially-acting base** — the engine that flattens every `ω₂`-power in
the wild row once the wild inertia acts trivially.  If the base `p.g` acts trivially on the char-2
module `A`, the `A`-offset of the 2-primary part `p^{ω₂}` (`powOmega2`) is just `p.u`.

The `ω₂`-exponent `e = omega2Exp (orderOf p)` is *odd* exactly when `orderOf p` is even, which is
exactly when `p.u ≠ 0` (then `addOrderOf p.u = 2 ∣ orderOf p`); for odd `e` and a 2-torsion `p.u`,
`e • p.u = p.u`.  When `p.u = 0` both sides vanish, so the identity is uniform. -/
theorem powOmega2_u_of_trivial [Finite A] [Finite C] (hA₂ : ∀ a : A, a + a = 0)
    (p : WordLift A C) (hg : ∀ a : A, p.g • a = a) : (powOmega2 p).u = p.u := by
  have hpow : ∀ k : ℕ, (p ^ k).u = k • p.u := by
    intro k
    rw [pow_u]
    have hc : ∀ i, p.g ^ i • p.u = p.u := (MulAction.stabilizer C p.u).pow_mem (hg p.u)
    simp only [hc, Finset.sum_const, Finset.card_range]
  rw [powOmega2, hpow]
  by_cases hpu : p.u = 0
  · simp [hpu]
  · have h2 : addOrderOf p.u = 2 := addOrderOf_eq_prime ((two_nsmul p.u).trans (hA₂ p.u)) hpu
    have hN0 : orderOf p ≠ 0 := (orderOf_pos p).ne'
    have hdvd : (2 : ℕ) ∣ orderOf p :=
      h2 ▸ addOrderOf_dvd_of_nsmul_eq_zero (by rw [← hpow, pow_orderOf_eq_one, one_u])
    have hv : (orderOf p).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hN0 hdvd).ne'
    have hodd : Odd (omega2Exp (orderOf p)) :=
      Nat.odd_iff.mpr ((omega2Exp_modEq_one hN0 hv).of_dvd (dvd_pow_self 2 hv))
    obtain ⟨m, hm⟩ := hodd
    rw [hm, add_nsmul, mul_nsmul, two_nsmul, hA₂, nsmul_zero, zero_add, one_nsmul]

/-- If the base `p.g` acts trivially, so does the base of the 2-primary part `p^{ω₂}` (any power of
a trivially-acting element acts trivially).  Companion to `powOmega2_u_of_trivial` for the
`.g`-action, used to push offsets through the collapsed ω₂-powers in the wild row. -/
theorem powOmega2_g_smul_of_trivial (p : WordLift A C) (hg : ∀ a : A, p.g • a = a) (a : A) :
    (powOmega2 p).g • a = a := by
  rw [powOmega2, pow_g]
  exact (MulAction.stabilizer C a).pow_mem (hg a) _

/-- An offset-zero element stays offset-zero under the 2-primary part (its powers do). -/
theorem powOmega2_u_zero (p : WordLift A C) (hpu : p.u = 0) : (powOmega2 p).u = 0 := by
  rw [powOmega2, pow_u, hpu]; simp

/-- **The `P = 0` ledger, general form**: a partial norm `∑_{i<K} σⁱ • u` vanishes whenever
`σ` acts *fixed-point-freely* on `A` (`A^σ = 0`) and `σᴷ` fixes `u`.  The sum `S` is
`σ`-invariant — `σ·S = S + σᴷu − u = S` (telescope) — so `S ∈ A^σ = 0`.  (No char-2 needed.) -/
theorem sum_pow_smul_eq_zero {σ : C} (hfpf : ∀ a : A, σ • a = a → a = 0) {K : ℕ} {u : A}
    (hK : σ ^ K • u = u) : ∑ i ∈ Finset.range K, σ ^ i • u = 0 := by
  set S := ∑ i ∈ Finset.range K, σ ^ i • u with hS
  have e1 : ∑ i ∈ Finset.range (K + 1), σ ^ i • u = S + u := by
    rw [Finset.sum_range_succ, hK]
  have e2 : ∑ i ∈ Finset.range (K + 1), σ ^ i • u = σ • S + u := by
    rw [Finset.sum_range_succ', pow_zero, one_smul, hS, Finset.smul_sum]
    simp only [pow_succ', mul_smul]
  exact hfpf S (add_right_cancel (e1.symm.trans e2)).symm

/-- **The `P = 0` ledger** (ramified norm collapse, Lemma 5.13(ii)): when the base `σ` acts
*fixed-point-freely* on `A` (`A^σ = 0`), the norm projector `P = 1 + σ + ⋯ + σ^{n−1}`
(`n = orderOf σ`) annihilates every element.  The ramified analogue of `powOmega2_u_of_trivial`:
in the split case `σ` acts trivially and the ω₂-power collapses to its offset; here `σ` is
non-trivial (`A^T = 0`), so the geometric sum vanishes instead. -/
theorem norm_eq_zero_of_fixedPointFree [Finite C] (σ : C) (hfpf : ∀ a : A, σ • a = a → a = 0)
    (a : A) : ∑ i ∈ Finset.range (orderOf σ), σ ^ i • a = 0 :=
  sum_pow_smul_eq_zero hfpf (by rw [pow_orderOf_eq_one, one_smul])

/-- **The ω₂-collapse for a fixed-point-free odd-order base** (the ramified wild-row engine): if
the base `p.g` acts fixed-point-freely on `A` and its 2-primary part `powOmega2 p.g` acts
trivially (i.e. `p.g` acts with *odd* order), then the ω₂-power's offset vanishes,
`(powOmega2 p).u = 0`.  Proof: `(powOmega2 p).u = ∑_{i<ω₂Exp(ord p)} p.gⁱ • p.u` (`pow_u`);
its length `ω₂Exp(ord p)` is a multiple of the odd action-period, so
`(p.g)^{ω₂Exp(ord p)} = powOmega2 p.g` (finite-exponent independence `powOmega2_pow_eq`) fixes
`p.u`, and `sum_pow_smul_eq_zero` applies.  This is the ramified twin of
`powOmega2_u_of_trivial`, consuming the `hTodd` hypothesis of `lemma_5_13_ramified`. -/
theorem powOmega2_u_of_oddFixedPointFree [Finite A] [Finite C] (p : WordLift A C)
    (hfpf : ∀ a : A, p.g • a = a → a = 0) (hodd : ∀ a : A, powOmega2 p.g • a = a) :
    (powOmega2 p).u = 0 := by
  rw [powOmega2, pow_u]
  refine sum_pow_smul_eq_zero hfpf ?_
  have hdvd : orderOf p.g ∣ orderOf p := by
    apply orderOf_dvd_of_pow_eq_one; rw [← pow_g, pow_orderOf_eq_one]; rfl
  rw [powOmega2_pow_eq p.g hdvd (orderOf_pos p).ne']
  exact hodd p.u

/-- **Trivial left factor is `ω₂`-transparent**: if `g` acts trivially on `A`, then
`powOmega2 (g·h)`
acts the same as `powOmega2 h`.  (`ω₂` is natural through `MulAction.toPermHom C A`
(`powOmega2_map`), and a trivially-acting `g` maps to `1`.)  Lets the ramified aux-word bases
`x₁·τ`, `x₀·τ` inherit `hTodd`'s odd-order condition from `τ` alone. -/
theorem powOmega2_smul_of_trivial_mul [Finite C] (g h : C) (hg : ∀ a : A, g • a = a)
    (hh : ∀ a : A, powOmega2 h • a = a) (a : A) : powOmega2 (g * h) • a = a := by
  have hperm : MulAction.toPermHom C A g = 1 := by ext w; simpa using hg w
  have hnat := powOmega2_map (MulAction.toPermHom C A) (g * h)
  rw [map_mul, hperm, one_mul, ← powOmega2_map] at hnat
  simpa using (congrArg (fun e => e a) hnat).trans (hh a)

/-! ### `.u` as an additive homomorphism on the trivially-based subgroup

At a tame lower map every wild aux word evaluates to an element whose base `g` acts trivially on the
coefficient module.  On that subgroup `(p*q).u = p.u + q.u` and `p⁻¹.u = -p.u`, so `.u` is a group
hom into `(A, +)`.  Consequently conjugates keep the offset (`conjP p g).u = p.u`) and commutators
have zero offset (`commP p q).u = 0`) — the mechanised form of the paper's "the wild factors
`h₀, [d₀,z₀]` have zero first derivative". -/

theorem inv_g_trivial (p : WordLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) : p⁻¹.g • a = a :=
  inv_smul_eq_iff.mpr (hp a).symm

theorem mul_g_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (p * q).g • a = a := by rw [mul_g, mul_smul, hq, hp]

theorem mul_u_of_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).u = p.u + q.u := by rw [mul_u, hp]

theorem inv_u_of_trivial (p : WordLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.u = -p.u := by
  rw [inv_u, inv_smul_eq_iff.mpr (hp p.u).symm]

theorem conjP_u_of_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a)
    (hg : ∀ a : A, g.g • a = a) : (conjP p g).u = p.u := by
  rw [conjP, mul_u_of_trivial _ g (mul_g_trivial _ _ (inv_g_trivial g hg) hp),
    mul_u_of_trivial _ p (inv_g_trivial g hg), inv_u_of_trivial g hg]
  abel

/-- General conjugation offset with only the *conjugated* word's base trivial: the conjugator's
prefix survives as `g.g⁻¹ • ·`.  (The `x₂`-cancellation in the ramified `h₀`-row then happens in
`g₀`-conjugate *pairs* — `hU` is not needed.) -/
theorem conjP_u_of_base_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a) :
    (conjP p g).u = g.g⁻¹ • p.u := by
  rw [conjP, mul_u, mul_u, inv_u, mul_g, inv_g, mul_smul, hp g.u]
  abel

theorem commP_u_of_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).u = 0 := by
  have hpi := inv_g_trivial p hp
  have hqi := inv_g_trivial q hq
  rw [commP, mul_u_of_trivial _ q (mul_g_trivial _ _ (mul_g_trivial _ _ hpi hqi) hp),
    mul_u_of_trivial _ p (mul_g_trivial _ _ hpi hqi), mul_u_of_trivial _ q⁻¹ hpi,
    inv_u_of_trivial p hp, inv_u_of_trivial q hq]
  abel

/-- A conjugate of a trivially-based element is trivially-based (for any conjugator). -/
theorem conjP_g_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) :
    (conjP p g).g • a = a := by
  rw [conjP, mul_g, mul_g, inv_g, mul_smul, mul_smul, hp, ← mul_smul, inv_mul_cancel, one_smul]

/-- A commutator of two trivially-based elements is trivially-based. -/
theorem commP_g_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (commP p q).g • a = a := by
  rw [commP]
  exact mul_g_trivial _ _ (mul_g_trivial _ _ (mul_g_trivial _ _ (inv_g_trivial p hp)
    (inv_g_trivial q hq)) hp) hq a

end WordLift

/-! ## The word complex (30)/(31) -/

section WordComplex

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The lifted marking `((ρσ, a), (ρτ, b), (ρx₀, c), (ρx₁, d))` over `t` with offsets `x`. -/
def liftMarking (t : Marking C) (x : Fin 4 → A) : Marking (WordLift A C) :=
  ⟨⟨x 0, t.σ⟩, ⟨x 1, t.τ⟩, ⟨x 2, t.x₀⟩, ⟨x 3, t.x₁⟩⟩

/-- **`d⁰`** (display (31)): simultaneous infinitesimal conjugation,
`v ↦ ((S−1)v, (T−1)v, (X₀−1)v, (X₁−1)v)`. -/
def d0 (t : Marking C) : A →+ (Fin 4 → A) :=
  AddMonoidHom.mk' (fun v => ![t.σ • v - v, t.τ • v - v, t.x₀ • v - v, t.x₁ • v - v]) <| by
    intro v w
    funext i
    fin_cases i <;> simp [smul_add, sub_add_sub_comm]

/-- **`d¹`, function level** (display (30)): the pair of `A`-coordinates of the evaluated tame
and wild relators at the lifted marking — "the coefficient of `A` in the evaluated relators". -/
noncomputable def d1Fun (t : Marking C) (x : Fin 4 → A) : A × A :=
  ((liftMarking t x).tameValue.u, (liftMarking t x).wildValue.u)

/-- **`d¹` is additive in the lift variables** — the paper's "finite Fox rules" linearity
(§5.1/§5.2, displays (36)–(37)).  Proof by *functoriality*: evaluate the relators over the
coefficient module `A × A`, then push the value through the three `C`-equivariant maps
`fst, snd, fst + snd : A × A →+ A` (`Marking.map_tameValue`/`map_wildValue` +
`WordLift.map`); the `u`-coordinates give `d1Fun` at `x`, `y`, and `x + y` respectively.

(Requires `A`, `C` finite: the wild relator's `ω₂`-powers only push through coefficient maps in
finite groups — `powOmega2_map`.  This is the paper's finite-word setting.) -/
theorem d1Fun_add [Finite A] [Finite C] (t : Marking C) (x y : Fin 4 → A) :
    d1Fun t (x + y) = d1Fun t x + d1Fun t y := by
  -- Coefficient maps `A × A →+ A`, all `C`-equivariant since the action is diagonal.
  have hfst : ∀ (g : C) (a : A × A),
      (AddMonoidHom.fst A A) (g • a) = g • (AddMonoidHom.fst A A) a := fun _ _ => rfl
  have hsnd : ∀ (g : C) (a : A × A),
      (AddMonoidHom.snd A A) (g • a) = g • (AddMonoidHom.snd A A) a := fun _ _ => rfl
  have hsum : ∀ (g : C) (a : A × A), (AddMonoidHom.fst A A + AddMonoidHom.snd A A) (g • a)
      = g • (AddMonoidHom.fst A A + AddMonoidHom.snd A A) a := by
    intro g a
    show (g • a).1 + (g • a).2 = g • (a.1 + a.2)
    rw [Prod.smul_fst, Prod.smul_snd, smul_add]
  set φ1 := WordLift.map (C := C) (AddMonoidHom.fst A A) hfst with hφ1
  set φ2 := WordLift.map (C := C) (AddMonoidHom.snd A A) hsnd with hφ2
  set φs := WordLift.map (C := C) (AddMonoidHom.fst A A + AddMonoidHom.snd A A) hsum with hφs
  -- The paired lift over `A × A` recovers the single-variable lifts after pushing through the maps.
  have hL1 : (liftMarking t (fun i => (x i, y i))).map φ1 = liftMarking t x := rfl
  have hL2 : (liftMarking t (fun i => (x i, y i))).map φ2 = liftMarking t y := rfl
  have hLs : (liftMarking t (fun i => (x i, y i))).map φs = liftMarking t (x + y) := rfl
  -- Both relator coordinates read off the paired value via `fst`, `snd`, `fst + snd`.
  refine Prod.ext ?_ ?_
  · show (liftMarking t (x + y)).tameValue.u
        = (liftMarking t x).tameValue.u + (liftMarking t y).tameValue.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_tameValue, Marking.map_tameValue, Marking.map_tameValue,
      hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl
  · show (liftMarking t (x + y)).wildValue.u
        = (liftMarking t x).wildValue.u + (liftMarking t y).wildValue.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_wildValue, Marking.map_wildValue, Marking.map_wildValue,
      hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl

/-- **`d¹`** (display (30)), bundled on `d1Fun_add` (finite coefficients, per `d1Fun_add`). -/
noncomputable def d1 [Finite A] [Finite C] (t : Marking C) : (Fin 4 → A) →+ A × A :=
  AddMonoidHom.mk' (d1Fun t) (d1Fun_add t)

/-- **(30) is a complex**: `d¹ ∘ d⁰ = 0` when the marking satisfies the two relations.
Proof: `liftMarking t (d0 t v)` is `t` pushed through `g ↦ ⟨g•v − v, g⟩ = ⟨v,1⟩⁻¹⟨0,g⟩⟨v,1⟩`
(conjugation of the base embedding), so its relator values are conjugates of `t`'s — which are
`1` by the relations — hence have zero `A`-coordinate. -/
theorem d1Fun_comp_d0 [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (v : A) : d1Fun t (d0 t v) = 0 := by
  -- Conjugation by `⟨v,1⟩`, an inner automorphism, composed with the base embedding.
  let ψ : C →* WordLift A C :=
    (MulAut.conj (⟨v, 1⟩ : WordLift A C)).symm.toMonoidHom.comp WordLift.baseEmbed
  have hψ : ∀ g : C, ψ g = ⟨g • v - v, g⟩ := WordLift.conj_baseEmbed v
  -- The coboundary lift is `t` pushed through `ψ`.
  have hkey : liftMarking t (d0 t v) = t.map ψ := by
    simp only [liftMarking, Marking.map, hψ, Marking.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact WordLift.ext (by simp [d0]) rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (d0 t v)).tameValue.u = (0 : A × A).1
    rw [hkey, Marking.map_tameValue, (Marking.tameValue_eq_one_iff t).mpr ht, map_one]
    rfl
  · show (liftMarking t (d0 t v)).wildValue.u = (0 : A × A).2
    rw [hkey, Marking.map_wildValue, (Marking.wildValue_eq_one_iff t).mpr hw, map_one]
    rfl

/-- `H⁰_{A,ρ}(A) = ker d⁰` (the `t`-invariants). -/
def H0w (t : Marking C) : AddSubgroup A := (d0 (A := A) t).ker

/-- `Z¹_{A,ρ}(A) = ker d¹` (display (30)'s degree-one kernel). -/
noncomputable def Z1w [Finite A] [Finite C] (t : Marking C) : AddSubgroup (Fin 4 → A) :=
  (d1 (A := A) t).ker

/-- `B¹_{A,ρ}(A) = im d⁰`. -/
def B1w (t : Marking C) : AddSubgroup (Fin 4 → A) := (d0 (A := A) t).range

/-- `H¹_{A,ρ}(A)` (as in `GQ2/Cohomology.lean`: the `addSubgroupOf`-quotient is total — the
chain inclusion `B¹ ≤ Z¹` is `d1Fun_comp_d0`, needed only for lemmas). -/
noncomputable def H1w [Finite A] [Finite C] (t : Marking C) : Type _ :=
  Z1w (A := A) t ⧸ (B1w (A := A) t).addSubgroupOf (Z1w (A := A) t)

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H1w (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- The class of a degree-one cocycle in `H¹_{A,ρ}`. -/
noncomputable def h1wMk [Finite A] [Finite C] (t : Marking C) (x : Z1w (A := A) t) :
    H1w (A := A) t :=
  QuotientAddGroup.mk x

/-- `H²_{A,ρ}(A) = A² ⧸ im d¹`. -/
noncomputable def H2w [Finite A] [Finite C] (t : Marking C) : Type _ :=
  (A × A) ⧸ (d1 (A := A) t).range

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H2w (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- **The tame row of `d¹`, in closed form** — the general (pre-`𝔽₂`) form of display (34),
`D(τ^σ τ⁻²)(a, b) = S⁻¹(T−1)a + S⁻¹b − (1+T)b`, valid at a marking satisfying the tame
relation.  This is the Fox–Heisenberg design stress test: it pins the lift convention, the `conjP` direction,
and the (30)-encoding against the paper's own computation (Lemma 5.5's proof). -/
theorem d1Fun_tame (t : Marking C) (ht : t.TameRel) (x : Fin 4 → A) :
    (d1Fun t x).1
      = t.σ⁻¹ • (t.τ • x 0) - t.σ⁻¹ • x 0 + t.σ⁻¹ • x 1 - (x 1 + t.τ • x 1) := by
  have hel : t.σ⁻¹ * t.τ * t.σ = t.τ * t.τ := by
    rwa [Marking.TameRel, conjP, pow_two] at ht
  simp only [d1Fun, Marking.tameValue, liftMarking, conjP, pow_two, WordLift.mul_u,
    WordLift.mul_g, WordLift.inv_u, WordLift.inv_g]
  rw [hel, smul_neg, smul_inv_smul, mul_smul]
  abel

end WordComplex

/-! ## The `𝔽₂`-dual -/

/-- The `𝔽₂`-dual `A^∨ = Hom(A, 𝔽₂)`, as a def-synonym (a plain abbrev would pick up
Mathlib's codomain-action instances — the Tate-duality interface diamond). -/
def ElemDual (A : Type*) [AddCommGroup A] : Type _ := A →+ ZMod 2

namespace ElemDual

variable {A : Type*} [AddCommGroup A]

noncomputable instance : AddCommGroup (ElemDual A) :=
  inferInstanceAs (AddCommGroup (A →+ ZMod 2))

instance : FunLike (ElemDual A) A (ZMod 2) :=
  inferInstanceAs (FunLike (A →+ ZMod 2) A (ZMod 2))

instance : AddMonoidHomClass (ElemDual A) A (ZMod 2) :=
  inferInstanceAs (AddMonoidHomClass (A →+ ZMod 2) A (ZMod 2))

instance [Finite A] : Finite (ElemDual A) :=
  Finite.of_injective (fun f : ElemDual A => (⇑f : A → ZMod 2)) DFunLike.coe_injective

@[ext] theorem ext {lam mu : ElemDual A} (h : ∀ a, lam a = mu a) : lam = mu :=
  DFunLike.ext _ _ h

@[simp] theorem zero_apply (a : A) : (0 : ElemDual A) a = 0 := rfl
@[simp] theorem add_apply (lam mu : ElemDual A) (a : A) : (lam + mu) a = lam a + mu a := rfl
@[simp] theorem neg_apply (lam : ElemDual A) (a : A) : (-lam) a = -(lam a) := rfl
@[simp] theorem sub_apply (lam mu : ElemDual A) (a : A) : (lam - mu) a = lam a - mu a := rfl

/-- `ElemDual A` is elementary (2-torsion): every `𝔽₂`-dual functional kills itself.  The
canonical form of the ubiquitous `hV₂d`-style hypotheses; also applies to raw `A →+ ZMod 2`
maps (`ElemDual` is a def-synonym). -/
theorem add_self_eq_zero (lam : ElemDual A) : lam + lam = 0 :=
  ext fun a => CharTwo.add_self_eq_zero (lam a)

section Action

variable {C : Type*} [Group C] [DistribMulAction C A]

/-- The contragredient action `(g•λ)(a) = λ(g⁻¹•a)`. -/
noncomputable instance : DistribMulAction C (ElemDual A) where
  smul g lam :=
    ((lam : A →+ ZMod 2).comp (DistribSMul.toAddMonoidHom A (g⁻¹ : C)) : A →+ ZMod 2)
  one_smul lam := by
    ext a
    show lam ((1 : C)⁻¹ • a) = lam a
    rw [inv_one, one_smul]
  mul_smul g h lam := by
    ext a
    show lam ((g * h)⁻¹ • a) = lam (h⁻¹ • g⁻¹ • a)
    rw [mul_inv_rev, mul_smul]
  smul_zero g := by ext a; rfl
  smul_add g lam mu := by ext a; rfl

@[simp] theorem smul_apply (g : C) (lam : ElemDual A) (a : A) : (g • lam) a = lam (g⁻¹ • a) :=
  rfl

end Action

end ElemDual

/-- The evaluation pairing `A →+ A^∨ →+ 𝔽₂`, `(a, λ) ↦ λ(a)` (bundled for the cup-product API cup
products; equivariant into the trivial module by contragredience). -/
noncomputable def dualEval (A : Type*) [AddCommGroup A] : A →+ ElemDual A →+ ZMod 2 :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun lam : ElemDual A => lam a) fun _ _ => rfl)
    fun a b => by ext lam; exact lam.map_add a b

@[simp] theorem dualEval_apply {A : Type*} [AddCommGroup A] (a : A) (lam : ElemDual A) :
    dualEval A a lam = lam a := rfl

end FoxH

end GQ2
