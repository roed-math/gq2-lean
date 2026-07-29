/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Generic word blocks: orbit norms and the four-factor `𝓔`-block

Group-level (`[Group G]`, no profinite or presentation infrastructure) versions of the two
word compressions the dyadic **presentation simplification campaign** asks to prove once
rather than re-deriving inside every branch ledger:

* **Orbit norms** (campaign §7.2).  For `U z : G` and `m : ℕ`,
  `𝒩_{U,m}(z) = ∏_{j=1}^m z^{U^j}`, and the constant-size identity
  `𝒩_{U,m}(z) = (z^U U⁻¹)^m U^m` (`orbitNorm_eq`) replaces an `O(m)`-factor product by a
  four-atom word.  This is what makes the phase-4 exit rule ("no expanded `O(m)`-factor
  product may appear in the Lean-facing API unless the compiler proves its equivalence to a
  constant-size block") satisfiable for the procyclic `M_α` relator
  `E₂ = δ₂^U 𝒩_{U,m}(z)^{U^m}`.
* **The four-factor shadow block** (campaign §7.3).  `𝓔(g,h;δ₀,δ₁) = (δ₁^h δ₁ δ₀)^g δ₀`
  expands to `δ₁^{hg} δ₁^g δ₀^g δ₀` (`eBlock_eq`).  The expansion is pure conjugation algebra:
  **no commutativity of `g` and `h` is used**.  In the applications `g` and `h` are powers of
  `σ₂` (compact `M_α`: `g = h = σ₂^m`; procyclic: `g = σ₂^{p+sm}`, `h = σ₂^{sm}`), so
  `eBlock_pow` specializes the identity to a common base.
* **Hyperbolic handles** (campaign §7.1), `H_h = ∏_{j=1}^h [u_j, v_j]`, as the plain
  group-level product `handlesProd`; the certificate-transfer theorem itself is later work.

Each block comes with a naturality lemma under `MonoidHom`, so downstream evaluations of a
word in different regimes (free profinite generators, finite marked groups, jet lifts) are
one-line transports of each other — the `map_drWord` pattern of `GQ2/Roe/DRPresentation.lean`.

## Conventions

Campaign §3, which is the paper's convention throughout this repository:

* `x ^ g = g⁻¹ * x * g`      (`conjR`)
* `[x, y] = x⁻¹ * y⁻¹ * x * y`  (`commR`)

**Both differ from mathlib's.**  Mathlib's `MulAut.conj g` is `x ↦ g * x * g⁻¹` and its
`commutatorElement` is `⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹`, i.e. the *left*-handed
conventions.  The bridge to mathlib's bracket is `commR_eq_commutatorElement`:
`commR x y = ⁅x⁻¹, y⁻¹⁆`.

`conjR`/`commR` agree verbatim with `GQ2.conjP`/`GQ2.commP` of `GQ2/Words.lean`, which is
itself a Mathlib-only leaf; this file re-states them only to stay import-independent of the
`ℚ₂` stack (it imports nothing but Mathlib).  Deduplicating by importing `GQ2.Words` is a
mechanical follow-up if the dyadic branch ever wants it.
-/

namespace GQ2.Dyadic

open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

/-! ### Right conjugation `x ^ g = g⁻¹ x g` -/

/-- Right conjugation `x ^ g = g⁻¹ * x * g` (campaign §3 / paper convention; note this is the
opposite handedness from mathlib's `MulAut.conj`). -/
def conjR (x g : G) : G := g⁻¹ * x * g

@[simp] theorem conjR_one (x : G) : conjR x 1 = x := by simp [conjR]

@[simp] theorem one_conjR (g : G) : conjR (1 : G) g = 1 := by simp [conjR]

/-- Conjugation is a right action: `(x^h)^g = x^{hg}`. -/
theorem conjR_conjR (x h g : G) : conjR (conjR x h) g = conjR x (h * g) := by
  simp [conjR, mul_assoc]

/-- Conjugation is multiplicative in the conjugated element. -/
theorem conjR_mul (x y g : G) : conjR (x * y) g = conjR x g * conjR y g := by
  simp [conjR, mul_assoc]

@[simp] theorem conjR_inv (x g : G) : conjR x⁻¹ g = (conjR x g)⁻¹ := by
  simp [conjR, mul_assoc]

theorem conjR_pow (x g : G) (n : ℕ) : conjR (x ^ n) g = conjR x g ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, conjR_mul, ih, pow_succ]

/-- The rewrite driving the orbit-norm identity: `x^g · g⁻¹ = g⁻¹ · x`. -/
theorem conjR_mul_inv (x g : G) : conjR x g * g⁻¹ = g⁻¹ * x := by
  simp [conjR, mul_assoc]

/-- Conjugators that commute may be swapped. -/
theorem conjR_comm {g h : G} (x : G) (hgh : Commute g h) : conjR x (h * g) = conjR x (g * h) := by
  rw [hgh.eq]

/-- Naturality of `conjR`: every group hom transports the paper's conjugation. -/
theorem map_conjR (f : G →* H) (x g : G) : f (conjR x g) = conjR (f x) (f g) := by
  simp [conjR]

/-! ### The paper's commutator `[x, y] = x⁻¹ y⁻¹ x y` -/

/-- Commutator `[x, y] = x⁻¹ * y⁻¹ * x * y` (campaign §3 / paper convention).  Mathlib's
`⁅·,·⁆` is the other convention; see `commR_eq_commutatorElement`. -/
def commR (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- Bridge to mathlib's `commutatorElement`, which uses the opposite convention
`⁅g₁, g₂⁆ = g₁ g₂ g₁⁻¹ g₂⁻¹`. -/
theorem commR_eq_commutatorElement (x y : G) : commR x y = ⁅x⁻¹, y⁻¹⁆ := by
  simp [commR, commutatorElement_def]

@[simp] theorem commR_self (x : G) : commR x x = 1 := by simp [commR]

@[simp] theorem commR_one_left (y : G) : commR 1 y = 1 := by simp [commR]

@[simp] theorem commR_one_right (x : G) : commR x 1 = 1 := by simp [commR]

/-- `[x, y] = 1` exactly when `x` and `y` commute. -/
theorem commR_eq_one_iff {x y : G} : commR x y = 1 ↔ Commute x y := by
  rw [commR, Commute, SemiconjBy, mul_assoc, mul_assoc, inv_mul_eq_one, eq_inv_mul_iff_mul_eq]
  exact eq_comm

/-- A commutator is a conjugate quotient: `[x, y] = x⁻¹ · x^y`. -/
theorem commR_eq_inv_mul_conjR (x y : G) : commR x y = x⁻¹ * conjR x y := by
  simp [commR, conjR, mul_assoc]

theorem map_commR (f : G →* H) (x y : G) : f (commR x y) = commR (f x) (f y) := by
  simp [commR]

/-! ### Orbit norms (campaign §7.2) -/

/-- The **orbit norm** `𝒩_{U,m}(z) = ∏_{j=1}^m z^{U^j}`, the factors accumulating on the
right in increasing order of `j`.  Compressed to a constant-size word by `orbitNorm_eq`. -/
def orbitNorm (U z : G) : ℕ → G
  | 0 => 1
  | m + 1 => orbitNorm U z m * conjR z (U ^ (m + 1))

@[simp] theorem orbitNorm_zero (U z : G) : orbitNorm U z 0 = 1 := rfl

theorem orbitNorm_succ (U z : G) (m : ℕ) :
    orbitNorm U z (m + 1) = orbitNorm U z m * conjR z (U ^ (m + 1)) := rfl

@[simp] theorem orbitNorm_one (U z : G) : orbitNorm U z 1 = conjR z U := by
  simp [orbitNorm_succ]

/-- **Campaign §7.2, the constant-size orbit-norm identity**:
`𝒩_{U,m}(z) = (z^U U⁻¹)^m U^m`.

The `m`-fold product on the left collapses to a word of bounded length whose only
`m`-dependence is in two exponents. -/
theorem orbitNorm_eq (U z : G) (m : ℕ) : orbitNorm U z m = (conjR z U * U⁻¹) ^ m * U ^ m := by
  rw [conjR_mul_inv]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [orbitNorm_succ, ih, pow_succ (U⁻¹ * z) m, mul_assoc ((U⁻¹ * z) ^ m),
      mul_assoc ((U⁻¹ * z) ^ m)]
    congr 1
    simp only [conjR, pow_succ]
    group

/-- The base of the compressed orbit norm, spelled without `conjR`. -/
theorem orbitNorm_eq' (U z : G) (m : ℕ) : orbitNorm U z m = (U⁻¹ * z) ^ m * U ^ m := by
  rw [orbitNorm_eq, conjR_mul_inv]

/-- Naturality: orbit norms are computed in the image. -/
theorem map_orbitNorm (f : G →* H) (U z : G) (m : ℕ) :
    f (orbitNorm U z m) = orbitNorm (f U) (f z) m := by
  induction m with
  | zero => simp
  | succ m ih => rw [orbitNorm_succ, map_mul, ih, map_conjR, map_pow, orbitNorm_succ]

/-! ### The four-factor `𝓔`-block (campaign §7.3) -/

/-- The **four-factor shadow block** `𝓔(g, h; δ₀, δ₁) = (δ₁^h δ₁ δ₀)^g δ₀` (campaign §7.3). -/
def eBlock (g h d₀ d₁ : G) : G := conjR (conjR d₁ h * d₁ * d₀) g * d₀

/-- **Campaign §7.3, the `𝓔`-block expansion**:
`𝓔(g, h; δ₀, δ₁) = δ₁^{hg} δ₁^g δ₀^g δ₀`.

Pure conjugation algebra — no hypothesis relating `g` and `h` is needed, in particular no
commutativity, even though `g` and `h` are powers of `σ₂` in every application. -/
theorem eBlock_eq (g h d₀ d₁ : G) :
    eBlock g h d₀ d₁ = conjR d₁ (h * g) * conjR d₁ g * conjR d₀ g * d₀ := by
  simp only [eBlock, conjR_mul, conjR_conjR]

/-- The `𝓔`-block at commuting conjugators: the leading factor may be read as `δ₁^{gh}`. -/
theorem eBlock_eq_of_commute {g h : G} (d₀ d₁ : G) (hgh : Commute g h) :
    eBlock g h d₀ d₁ = conjR d₁ (g * h) * conjR d₁ g * conjR d₀ g * d₀ := by
  rw [eBlock_eq, conjR_comm _ hgh]

/-- The form used in the `M_α` branches, where both conjugators are powers of `σ₂`: with
`g = U^a`, `h = U^b` the leading factor is `δ₁^{U^{a+b}}`.  (Compact `M_α`: `a = b = m`;
procyclic: `a = p + sm`, `b = sm`.) -/
theorem eBlock_pow (U d₀ d₁ : G) (a b : ℕ) :
    eBlock (U ^ a) (U ^ b) d₀ d₁ =
      conjR d₁ (U ^ (a + b)) * conjR d₁ (U ^ a) * conjR d₀ (U ^ a) * d₀ := by
  rw [eBlock_eq, ← pow_add, Nat.add_comm b a]

theorem map_eBlock (f : G →* H) (g h d₀ d₁ : G) :
    f (eBlock g h d₀ d₁) = eBlock (f g) (f h) (f d₀) (f d₁) := by
  simp only [eBlock, map_mul, map_conjR]

/-! ### Hyperbolic handles (campaign §7.1) -/

/-- The **hyperbolic handle product** `H_h = ∏_{j=1}^h [u_j, v_j]`, with the paper's
commutator and the factors accumulating on the right in increasing order of `j`. -/
def handlesProd (u v : ℕ → G) : ℕ → G
  | 0 => 1
  | h + 1 => handlesProd u v h * commR (u (h + 1)) (v (h + 1))

@[simp] theorem handlesProd_zero (u v : ℕ → G) : handlesProd u v 0 = 1 := rfl

theorem handlesProd_succ (u v : ℕ → G) (h : ℕ) :
    handlesProd u v (h + 1) = handlesProd u v h * commR (u (h + 1)) (v (h + 1)) := rfl

@[simp] theorem handlesProd_one (u v : ℕ → G) : handlesProd u v 1 = commR (u 1) (v 1) := by
  simp [handlesProd_succ]

/-- Handles built from commuting pairs contribute nothing. -/
theorem handlesProd_eq_one (u v : ℕ → G) (h : ℕ) (huv : ∀ j, Commute (u j) (v j)) :
    handlesProd u v h = 1 := by
  induction h with
  | zero => rfl
  | succ h ih => rw [handlesProd_succ, ih, commR_eq_one_iff.2 (huv _), mul_one]

theorem map_handlesProd (f : G →* H) (u v : ℕ → G) (h : ℕ) :
    f (handlesProd u v h) = handlesProd (fun j ↦ f (u j)) (fun j ↦ f (v j)) h := by
  induction h with
  | zero => simp
  | succ h ih => rw [handlesProd_succ, map_mul, ih, map_commR, handlesProd_succ]

end GQ2.Dyadic
