/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Subdirect

@[expose] public section


/-!
# The Roe-candidate words, wild relation, and `admissibleCountR`  (Roe note §1)

Transcribes eqs. (1.1)–(1.2) and Definition 1.1 of the verification note
`paper/roe-presentation-verification.tex` (the "Roe note") for **finite groups**: the auxiliary
words of David Roe's candidate presentation

  `Γ_R = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^ω₂ · x₁² · [x₁, x₁^{σ₂}]⟩`

evaluated at a marking `t = (σ, τ, x₀, x₁)`, the Roe wild relation `Marking.WildRelR`, the
`R`-admissibility predicate `Marking.AdmissibleR`, and the count `admissibleCountR G` of
`R`-admissible markings — the Roe-candidate counterparts of `GQ2.Words`'
`Marking.WildRel`/`Admissible`/`admissibleCount`.

Conventions match the note (and the paper) exactly:
* `x ^ g = g⁻¹ * x * g`                (`conjP`)
* `[x, y] = x⁻¹ * y⁻¹ * x * y`          (`commP`)
* `x ^ ω₂` = the 2-primary part of `x` (`powOmega2`)

The note's eq. (1.1) ⟦eq:defwords⟧, verbatim:
```
\sigma_2=\sigma^{\omegaTwo},\qquad
a=(x_0^{-3}\tau)^{\omegaTwo},\qquad
y_1=x_1^{\sigma_2},\qquad
c=[x_1,y_1].
```
`σ₂` already exists (`Marking.sigma2`, shared with `Γ_A`); the note's `a`, `y₁`, `c` are named
`aR`, `y1R`, `cR` here.  The two relators, eq. (1.2) ⟦eq:relators⟧, verbatim:
```
\rt=(\tau^\sigma)^{-1}\tau^2,\qquad
\rR=(x_0^\sigma)^{-1}a\,x_1^2c.
```
`r_t` is the tame relator shared with `Γ_A` (`Marking.TameRel`/`tameValue`); only `r_R` is new.

Alongside the definitions this file supplies (plan rules 8–9, stress-test discipline):
* **naturality**: `Marking.map_aR/map_y1R/map_cR/map_wildValueR/map_wildRelR` for a finite
  source (mirroring `Marking.map_wildValue`; the full `map_admissibleR` clone is ticket R3);
* the **finite-exponent form** `wildValueExpR` (the two `ω₂`-powers — in `aR` and in `sigma2`
  inside `cR` — replaced by `(·)^e`) with the independence lemmas
  `wildValueExpR_eq_wildValueR(_of_dvd)` and the unconditional naturality `wildValueExpR_map`,
  mirroring `GQ2.FoxH.wildValueExp` (`GQ2/FoxHeisenberg/Traced.lean`);
* **stress tests**: the abelian collapse `Marking.wildValueR_comm`/`wildValueExpR_comm` and
  `decide`-checked concrete evaluations in `Multiplicative (ZMod 8)`
  (`wildValueExpR_zmod8`, `wildValueExpR_zmod8_cube`, `wildValueR_zmod8`) pinning the factor
  order, the `−3` exponent, the inverted first factor, and the `x₁²` of `r_R`.
-/

namespace GQ2

open scoped Classical

/-! ### The Roe auxiliary words and relator (note eqs. (1.1)–(1.2)) -/

namespace Marking

variable {G : Type*} [Group G] (t : Marking G)

-- The auxiliary words use `powOmega2`, hence are noncomputable.
noncomputable section

/-- `a = (x₀⁻³ τ)^ω₂` — note eq. (1.1) ⟦eq:defwords⟧, verbatim `a=(x_0^{-3}\tau)^{\omegaTwo}`.
Here `x₀⁻³ = (x₀³)⁻¹`.  (The `R` suffix avoids clashing with variables named `a`.) -/
def aR : G := powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ)

/-- `y₁ = x₁ ^ σ₂` — note eq. (1.1) ⟦eq:defwords⟧, verbatim `y_1=x_1^{\sigma_2}`, with
`σ₂ = σ^ω₂ = Marking.sigma2` (shared with `Γ_A`) and the conjugation convention
`x ^c g = g⁻¹xg`. -/
def y1R : G := conjP t.x₁ t.sigma2

/-- `c = [x₁, y₁]` — note eq. (1.1) ⟦eq:defwords⟧, verbatim `c=[x_1,y_1]`, with the commutator
convention `[x, y] = x⁻¹y⁻¹xy`. -/
def cR : G := commP t.x₁ t.y1R

/-- The **Roe wild relator value** `r_R` at a marking — note eq. (1.2) ⟦eq:relators⟧, verbatim
`\rR=(x_0^\sigma)^{-1}a\,x_1^2c`, i.e.

  `r_R = (x₀ ^c σ)⁻¹ · a · x₁² · c`   **in exactly this order**,

with `a = Marking.aR` and `c = Marking.cR`.  The `Γ_A` analogue is `Marking.wildValue`.  The two
`ω₂`-powers sit inside `aR` and inside `cR`'s `sigma2`; the finite-exponent form (for a concrete
integer representative of `ω₂`) is `wildValueExpR`. -/
def wildValueR : G := (conjP t.x₀ t.σ)⁻¹ * t.aR * t.x₁ ^ 2 * t.cR

/-- The **Roe wild relation** `r_R = 1` (note eq. (1.2) ⟦eq:relators⟧ / Definition 1.1
⟦def:GammaR⟧) — the Roe-candidate counterpart of `Marking.WildRel`. -/
def WildRelR : Prop := t.wildValueR = 1

/-- The Roe wild relator dies iff the Roe wild relation holds. -/
@[simp] theorem wildValueR_eq_one_iff : t.wildValueR = 1 ↔ t.WildRelR := Iff.rfl

/-- A marking is **`R`-admissible** if it generates, satisfies the tame relation and the Roe wild
relation, and its wild generators have 2-group normal closure — note Definition 1.1 ⟦def:GammaR⟧:
"the distinguished tuple generates the quotient, the two words in eq. (1.2) vanish, and the normal
closure of the images of `x₀, x₁` is a 2-group".  `Generates`, `TameRel` and `Pro2Core` are reused
verbatim from the `Γ_A` development (`GQ2.Words`); only the wild relation differs. -/
def AdmissibleR : Prop := t.Generates ∧ t.TameRel ∧ t.WildRelR ∧ t.Pro2Core

end -- noncomputable section

end Marking

/-- The finite count `N_R(G)` of `R`-admissible markings — the Roe-candidate analogue of
`GQ2.admissibleCount` and the right-hand side of the surjection-count semantics of the note's
Definition 1.1 ⟦def:GammaR⟧ (`|Sur(Γ_R, G)| = admissibleCountR G` is ticket R4's `prop_2_3_R`).
Well-defined (finite) for any finite group since `Marking G ≃ G⁴`. -/
noncomputable def admissibleCountR (G : Type*) [Group G] : ℕ :=
  Nat.card {t : Marking G // t.AdmissibleR}

/-! ### Naturality of the Roe words (mirroring `GQ2.Subdirect`)

The `ω₂`-powers push through a group homomorphism via `powOmega2_map`, which needs the source
finite — exactly as for the `Γ_A` word ledger.  The full admissibility-preservation statement
(`map_admissible` analogue) is ticket R3's, alongside `GammaR`/`AdmissibleLimit`. -/

namespace Marking

variable {G H : Type*} [Group G] [Group H]

section
variable [Finite G] (f : G →* H) (t : Marking G)

@[simp] lemma map_aR : (t.map f).aR = f t.aR := by
  simp only [aR, map_x₀, map_τ, ← map_pow, ← map_inv, ← map_mul]
  exact (powOmega2_map f _).symm

@[simp] lemma map_y1R : (t.map f).y1R = f t.y1R := by
  simp only [y1R, map_x₁, map_sigma2, map_conjP]

@[simp] lemma map_cR : (t.map f).cR = f t.cR := by
  simp only [cR, map_x₁, map_y1R, map_commP]

/-- **Naturality of the Roe wild relator value** under a group homomorphism (finite source) —
the `Γ_R` counterpart of `Marking.map_wildValue`. -/
theorem map_wildValueR : (t.map f).wildValueR = f t.wildValueR := by
  simp only [wildValueR, map_aR, map_cR, map_x₀, map_x₁, map_σ, map_conjP, map_mul, map_inv,
    map_pow]

/-- The Roe wild relation transfers along any group hom (of a finite source). -/
lemma map_wildRelR (h : t.WildRelR) : (t.map f).WildRelR := by
  show (t.map f).wildValueR = 1
  rw [map_wildValueR, (h : t.wildValueR = 1), map_one]

end

end Marking

/-! ### The finite-exponent form (mirroring `GQ2.FoxH.wildValueExp`, Traced.lean) -/

/-- The Roe wild relator word with the `ω₂`-powers replaced by an explicit integer exponent `e`
(the note's `ω₂` becomes `(·)^e` for a concrete `e = omega2Exp N`, a multiple of the relevant
orders).  Mirrors `Marking.wildValueR`'s ledger exactly; only `sigma2` and `aR` carry the
exponent — two `ω₂`-subwords, versus three (`sigma2`, `u0`, `u1`) for `Γ_A`'s `wildValueExp`. -/
def wildValueExpR {G : Type*} [Group G] (t : Marking G) (e : ℕ) : G :=
  let sigma2 := t.σ ^ e
  let aR := ((t.x₀ ^ 3)⁻¹ * t.τ) ^ e
  let y1R := conjP t.x₁ sigma2
  let cR := commP t.x₁ y1R
  (conjP t.x₀ t.σ)⁻¹ * aR * t.x₁ ^ 2 * cR

/-- `wildValueExpR` is natural in group homomorphisms — it uses only `mul`, `inv`, `pow`,
`conjP`, `commP` (no `ω₂`), so no finiteness is needed. -/
theorem wildValueExpR_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (t : Marking G) (e : ℕ) :
    φ (wildValueExpR t e) = wildValueExpR (t.map φ) e := by
  simp only [wildValueExpR, Marking.map_σ, Marking.map_τ, Marking.map_x₀, Marking.map_x₁,
    map_mul, map_inv, map_pow, Marking.map_conjP, Marking.map_commP]

/-- For finite `G`, `wildValueExpR` at `omega2Exp (Monoid.exponent G)` **is**
`Marking.wildValueR`: only `sigma2` and `aR` carry `ω₂`, and each such element's order divides
the exponent, so `powOmega2_pow_eq` rewrites the two `ω₂`-powers to the explicit
`omega2Exp`-power. -/
theorem wildValueExpR_eq_wildValueR {G : Type*} [Group G] [Finite G] (t : Marking G) :
    t.wildValueR = wildValueExpR t (omega2Exp (Monoid.exponent G)) := by
  have h : ∀ g : G, powOmega2 g = g ^ omega2Exp (Monoid.exponent G) := fun g =>
    (powOmega2_pow_eq g (Monoid.order_dvd_exponent g) Monoid.exponent_ne_zero_of_finite).symm
  simp only [Marking.wildValueR, Marking.aR, Marking.cR, Marking.y1R, Marking.sigma2,
    wildValueExpR, h]

/-- Divisibility form of `wildValueExpR_eq_wildValueR`:
`wildValueExpR t (omega2Exp N) = t.wildValueR` for **any** `N ≠ 0` that is a multiple of the two
`ω₂`-subword orders (`σ` and `x₀⁻³τ`) — the exact analogue of
`GQ2.FoxH.wildValueExp_eq_wildValue_of_dvd`, with one fewer hypothesis (no `u1`-subword). -/
theorem wildValueExpR_eq_wildValueR_of_dvd {G : Type*} [Group G] {N : ℕ} (hN : N ≠ 0)
    (t : Marking G) (h0 : orderOf t.σ ∣ N) (h1 : orderOf ((t.x₀ ^ 3)⁻¹ * t.τ) ∣ N) :
    t.wildValueR = wildValueExpR t (omega2Exp N) := by
  have hsig : powOmega2 t.σ = t.σ ^ omega2Exp N := (powOmega2_pow_eq t.σ h0 hN).symm
  have ha : powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ) = ((t.x₀ ^ 3)⁻¹ * t.τ) ^ omega2Exp N :=
    (powOmega2_pow_eq _ h1 hN).symm
  simp only [Marking.wildValueR, Marking.aR, Marking.cR, Marking.y1R, Marking.sigma2,
    wildValueExpR, hsig, ha]

/-! ### Stress tests (plan rule 9)

Cheap sanity lemmas shipped with the definitions, chosen to catch transcription slips in `r_R`
early (the `Γ_A` campaign's `h₀` erratum, `docs/erratum-h0-transcription.md`, was exactly such a
slip): the abelian collapse pins the conjugation/commutator conventions and the factor list; the
`ZMod 8` evaluations pin the signs and exponents numerically. -/

section StressTests

/-- In a commutative group the paper's conjugation collapses: `x ^c g = x`. -/
theorem conjP_eq_self {G : Type*} [CommGroup G] (x g : G) : conjP x g = x := by
  simp [conjP, mul_assoc, mul_comm x g]

/-- In a commutative group the paper's commutator collapses: `[x, y] = 1`. -/
theorem commP_eq_one {G : Type*} [CommGroup G] (x y : G) : commP x y = 1 := by
  simp [commP, mul_assoc]

/-- **Stress test (abelian collapse).**  In a commutative group the commutator `cR` dies and the
conjugations collapse, so the Roe wild relator reduces to `x₀⁻¹ · a · x₁²` — the abelianization
of note eq. (1.2), with exponent vector `(0, 1, −1−3, 2)` in `(σ, τ, x₀, x₁)` once `a` is
expanded at an odd `ω₂`-representative (cf. the note's Lemma 5.1 ⟦lem:stokes⟧ mod-2 vector
`(0,1,0,0)`). -/
theorem Marking.wildValueR_comm {G : Type*} [CommGroup G] (t : Marking G) :
    t.wildValueR = t.x₀⁻¹ * t.aR * t.x₁ ^ 2 := by
  simp only [Marking.wildValueR, Marking.cR, commP_eq_one, conjP_eq_self, mul_one]

/-- Abelian collapse of the finite-exponent form: `wildValueExpR` reduces to
`x₀⁻¹ · (x₀⁻³τ)^e · x₁²` in a commutative group. -/
theorem wildValueExpR_comm {G : Type*} [CommGroup G] (t : Marking G) (e : ℕ) :
    wildValueExpR t e = t.x₀⁻¹ * ((t.x₀ ^ 3)⁻¹ * t.τ) ^ e * t.x₁ ^ 2 := by
  simp only [wildValueExpR, commP_eq_one, conjP_eq_self, mul_one]

/-- A concrete test marking `(σ, τ, x₀, x₁) = (5, 1, 1, 1)` (additive notation) in
`Multiplicative (ZMod 8)`, for the `decide`-checked evaluations below. -/
def zmod8MarkingR : Marking (Multiplicative (ZMod 8)) :=
  ⟨Multiplicative.ofAdd 5, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩

/-- **Stress test (concrete evaluation, `e = 1`).**  Additively in `ZMod 8`:
`−x₀ + (−3·x₀ + τ)·1 + 2·x₁ = −1 − 2 + 2 = −1 ≡ 7`.  Pins the inverted first factor (un-inverted
`x₀^σ` would give `1`), the `−3` (a `+3` would give `5`), and the square `x₁²` (a bare `x₁` would
give `6`). -/
theorem wildValueExpR_zmod8 :
    wildValueExpR zmod8MarkingR 1 = Multiplicative.ofAdd (7 : ZMod 8) := by decide

/-- **Stress test (concrete evaluation, `e = 3`).**  Same marking at the odd exponent `3` (every
`ω₂`-representative is odd): `−1 + 3·(−2) + 2 = −5 ≡ 3 (mod 8)` — pins the placement of the
exponent on the `aR`-subword. -/
theorem wildValueExpR_zmod8_cube :
    wildValueExpR zmod8MarkingR 3 = Multiplicative.ofAdd (3 : ZMod 8) := by decide

/-- `omega2Exp 8 = 1`: on a group of exponent `8` (a 2-group) the concrete `ω₂`-representative is
`1`, i.e. `ω₂` acts as the identity — the elementwise face of "`ω₂ ≡ 1` on the 2-part". -/
theorem omega2Exp_eight : omega2Exp 8 = 1 := by
  have hfac : (8 : ℕ).factorization 2 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  norm_num [omega2Exp, hfac]

/-- **Stress test (the genuine `ω₂`-word, end-to-end).**  `Multiplicative (ZMod 8)` has exponent
dividing `8` and `omega2Exp 8 = 1`, so the noncomputable `wildValueR` itself agrees with the
`e = 1` evaluation above — exercising `wildValueExpR_eq_wildValueR_of_dvd` on a concrete
instance. -/
theorem wildValueR_zmod8 :
    zmod8MarkingR.wildValueR = Multiplicative.ofAdd (7 : ZMod 8) := by
  have h := wildValueExpR_eq_wildValueR_of_dvd (N := 8) (by norm_num) zmod8MarkingR
    (orderOf_dvd_iff_pow_eq_one.mpr (by decide)) (orderOf_dvd_iff_pow_eq_one.mpr (by decide))
  rw [h, omega2Exp_eight]
  exact wildValueExpR_zmod8

end StressTests

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.1) = ⟦eq:defwords⟧
  * eq. (1.2) = ⟦eq:relators⟧
  * Definition 1.1 = ⟦def:GammaR⟧
  * Lemma 5.1 = ⟦lem:stokes⟧
-/
