import Mathlib

/-!
# The auxiliary words (1)–(3) and the admissibility predicate

This file makes the paper's presentation data completely concrete for **finite groups**,
which is all the surjection-count form of Theorem 1.2 ever needs (paper §2, App. A–B).

Conventions match the paper exactly:
* `x ^ g = g⁻¹ * x * g`                (`conjP`)
* `[x, y] = x⁻¹ * y⁻¹ * x * y`          (`commP`)
* `x ^ ω₂` = the 2-primary part of `x` (`powOmega2`)

`ω₂ ∈ ℤ̂` is the idempotent that is `1` on the 2-adic factor and `0` on every odd factor.
On a single element `x` of finite order `d = 2^a · m` (`m` odd), `x ^ ω₂` is the projection
of `x` to the 2-primary part of `⟨x⟩`, i.e. `x ^ e` for any integer `e ≡ 1 (mod 2^a)`,
`e ≡ 0 (mod m)`. We realise such an `e` concretely as `omega2Exp d`. Because
`orderOf x ∣ Monoid.exponent G`, using `orderOf x` per element agrees with a single global
integer exponent on the whole finite group, so this is faithful to the profinite `ω₂`.
-/

namespace GQ2

open scoped Classical

/-! ### The `ω₂` exponent -/

/-- A concrete nonnegative-integer representative of the profinite idempotent `ω₂` modulo `n`:
the unique `e ∈ [0, n)` with `e ≡ 1 (mod 2^{v₂ n})` and `e ≡ 0 (mod oddpart n)`.
Realised as `(oddpart n) ^ (2^{v₂ n - 1})` (Euler: `m^{φ(2^a)} ≡ 1 mod 2^a`, and it is
`≡ 0 mod m`). -/
def omega2Exp (n : ℕ) : ℕ :=
  let a := n.factorization 2
  if a = 0 then 0 else (n / 2 ^ a) ^ (2 ^ (a - 1)) % n

/-- `x ^ ω₂`: the 2-primary part of a finite-order element.
Noncomputable because it uses `orderOf`; a computable variant parametrized by an explicit
exponent (a multiple of `Monoid.exponent G`) is a follow-up for the App. B cross-check. -/
noncomputable def powOmega2 {G : Type*} [Monoid G] (x : G) : G := x ^ omega2Exp (orderOf x)

@[inherit_doc] scoped notation:max x "^ω₂" => powOmega2 x

/-! ### The paper's conventions for conjugation and commutator -/

/-- Right conjugation `x ^ g = g⁻¹ x g` (paper's convention). -/
def conjP {G : Type*} [Group G] (x g : G) : G := g⁻¹ * x * g

/-- Commutator `[x, y] = x⁻¹ y⁻¹ x y` (paper's convention). -/
def commP {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

@[inherit_doc] scoped notation:max x " ^c " g => conjP x g

/-! ### A marked generating tuple `(σ, τ, x₀, x₁)` -/

/-- A "marking": an ordered quadruple of group elements `(σ, τ, x₀, x₁)`. -/
structure Marking (G : Type*) where
  σ : G
  τ : G
  x₀ : G
  x₁ : G
deriving DecidableEq

namespace Marking

variable {G : Type*} [Group G] (t : Marking G)

-- The auxiliary words use `powOmega2`, hence are noncomputable.
noncomputable section

/-! The auxiliary words, transcribed from the machine-readable block (App. B) and eqs. (1)–(3).
```
sigma2 = sigma^ω₂            g0 = sigma2^2
u0 = (x0*tau)^ω₂             u1 = (x1*tau)^ω₂
d0 = u0*x0⁻¹                 z0 = x0^sigma2
c0 = [d0, z0]               dg = d0^g0
hcomm = [dg, d0]            h0 = (x0^g0)*x0*dg*d0*d0^2*hcomm
``` -/

/-- `σ₂ = σ ^ ω₂`. -/
def sigma2 : G := powOmega2 t.σ
/-- `u i = (xᵢ τ) ^ ω₂`, with `u 0` and `u 1` the two used in the paper. -/
def u (xi : G) : G := powOmega2 (xi * t.τ)
/-- `u₀ = (x₀ τ) ^ ω₂`. -/
def u0 : G := t.u t.x₀
/-- `u₁ = (x₁ τ) ^ ω₂`. -/
def u1 : G := t.u t.x₁
/-- `d₀ = u₀ x₀⁻¹`. -/
def d0 : G := t.u0 * t.x₀⁻¹
/-- `z₀ = x₀ ^ σ₂`. -/
def z0 : G := conjP t.x₀ t.sigma2
/-- `c₀ = [d₀, z₀]`. -/
def c0 : G := commP t.d0 t.z0
/-- `g₀ = σ₂²`. -/
def g0 : G := t.sigma2 ^ 2
/-- `d_g = d₀ ^ g₀`. -/
def dg : G := conjP t.d0 t.g0
/-- `h_c = [d_g, d₀]`. -/
def hc : G := commP t.dg t.d0
/-- `h₀ = (x₀ ^ g₀) · x₀ · d_g · d₀ · d₀² · h_c`.  (Note the bare `d₀` between `d_g` and `d₀²` —
paper eq. (3) and the App. B machine block agree on `dg*d0*d0^2`; it is what makes `h₀` an
instance of the class-two word `h_ϕ(X,D) = ϕ(X)·X·ϕ(D)·D·D²·[ϕ(D),D]` of paper Lemma 5.2.
A step-1 transcription dropped it; see `docs/erratum-h0-transcription.md`.) -/
def h0 : G := (conjP t.x₀ t.g0) * t.x₀ * t.dg * t.d0 * t.d0 ^ 2 * t.hc

/-! ### The two relations -/

/-- The tame relation `τ^σ = τ²`  (eq. 5). -/
def TameRel : Prop := conjP t.τ t.σ = t.τ ^ 2

/-- The wild relation `h₀ u₁⁻¹ x₁^σ c₀ = 1`  (eq. 6). -/
def WildRel : Prop := t.h0 * t.u1⁻¹ * (conjP t.x₁ t.σ) * t.c0 = 1

/-- The marking generates the whole group. -/
def Generates : Prop := Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} = ⊤

/-- The 2-core condition: the normal closure of `{x₀, x₁}` is a 2-group (paper Prop. 2.3:
equivalent to `x₀, x₁ ∈ O₂(G)`). -/
def Pro2Core : Prop := IsPGroup 2 (Subgroup.normalClosure {t.x₀, t.x₁})

/-- A marking is **admissible** if it generates, satisfies both relations, and its wild
generators have 2-group normal closure (paper §2, "admissible marked generating quadruple"). -/
def Admissible : Prop := t.Generates ∧ t.TameRel ∧ t.WildRel ∧ t.Pro2Core

end -- noncomputable section

end Marking

/-- The finite count `N(G)` of admissible markings — the right-hand side of the
surjection-count form of Theorem 1.2 (equals `|Sur(Γ_A, G)|`, paper Prop. 2.3).
Well-defined (finite) for any finite group since `Marking G ≃ G⁴`. -/
noncomputable def admissibleCount (G : Type*) [Group G] : ℕ :=
  Nat.card {t : Marking G // t.Admissible}

/-- In a 2-torsion additive group, an odd multiple is the identity — the module-side face of
"`ω₂ ≡ 0` on the odd part" (odd averaging with no division, cf.
`inflationVanishes_of_oddNormal` and `regular_summand_of_subgroup_summand`). -/
theorem odd_nsmul_eq_self {A : Type*} [AddCommGroup A] (htor : ∀ a : A, a + a = 0)
    {n : ℕ} (hn : Odd n) (x : A) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul', two_nsmul, htor, zero_add]

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (1) = ⟦eq-defwords⟧
  * eq. (3) = ⟦eq-defwords3⟧
  * Lemma 5.2 = ⟦lem-class2square⟧
  * Prop 2.3 = ⟦prop-epi-semantics⟧
  * Theorem 1.2 = ⟦thm-main⟧
-/
