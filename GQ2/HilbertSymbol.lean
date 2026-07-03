import Mathlib

/-!
# B7′: the dyadic Hilbert symbol  (ticket T-07)

The paper's Lemma 3.5 evaluates the cup product
`H¹(ℚ₂, μ₂) × H¹(ℚ₂, μ₂) → H²(ℚ₂, μ₂) ≅ 𝔽₂` on the square-class basis via the *Hilbert symbol*
`(·,·)₂`.  This file provides that symbol elementarily and records the explicit dyadic formula as
the axiom **B7′**.

* `GQ2.HilbertSymbol.IsHilbertSolvable a b` — the ternary form `a X² + b Y² - Z²` has a nontrivial
  `ℚ₂`-zero.  `hilbertSymbol a b : ℤˣ` (`= {±1}`) is `1` on this locus, `-1` off it.  Defined with no
  cohomology, so the elementary identities below are *theorems*.
* `GQ2.HilbertSymbol.ε`, `GQ2.HilbertSymbol.ω : ℤ₂ˣ → 𝔽₂` — Serre's residue characters
  `ε(u) ≡ (u-1)/2`, `ω(u) ≡ (u²-1)/8 (mod 2)` (*A Course in Arithmetic*, Ch. II §3.3), computed
  through the reduction `ℤ₂ → ℤ/8`.  Both are homomorphisms on units (`ε_mul`, `ω_mul`).
* **Axiom `hilbertSymbol_dyadic`** = Serre CiA III §1.2 Theorem 1, `p = 2` case:
  `(2^α u, 2^β v)₂ = (-1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`.

Stress tests (theorems): symmetry `(a,b)=(b,a)`; `(a,-a)=1`; square-class invariance in one slot;
the ε/ω residue tables and their values on the unit `-1`; and (as a consequence of the axiom) the
square-class-basis value `(-1,-1)₂ = -1`, the nontrivial diagonal entry of the paper's initial cup
form `α² + βγ + γβ`.

Conventions: `ℚ_[2] = Padic 2`, `ℤ_[2] = PadicInt 2`, `𝔽₂ = ZMod 2`; the symbol is `ℤˣ = {±1}`-valued
via `signOf : 𝔽₂ → ℤˣ`, `0 ↦ 1`, `1 ↦ -1`.

The axiom is `[Classical.]` (a theorem of Mathlib-in-principle; axiomatized here at step 1). Per the
ticket rule it will be migrated to `GQ2/Foundations/Axioms.lean` by T-19.
-/

namespace GQ2.HilbertSymbol

open scoped Classical

/-! ## The Hilbert symbol via solvability of `z² = a x² + b y²` -/

/-- `IsHilbertSolvable a b`: the ternary quadratic form `a X² + b Y² - Z²` has a nontrivial zero
over `ℚ₂`, i.e. the Hilbert symbol `(a, b)₂` is `+1`.  (Serre, *A Course in Arithmetic*, III §1.1.) -/
def IsHilbertSolvable (a b : ℚ_[2]) : Prop :=
  ∃ x y z : ℚ_[2], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2

/-- `signOf x = (-1)^x ∈ ℤˣ = {±1}`. -/
def signOf (x : ZMod 2) : ℤˣ := if x = 0 then 1 else -1

/-- The (quadratic) **Hilbert symbol** `(a, b)₂ ∈ ℤˣ = {±1}` for `a, b ∈ ℚ₂ˣ`: `+1` iff
`a X² + b Y² = Z²` has a nontrivial solution, else `-1`. -/
noncomputable def hilbertSymbol (a b : ℚ_[2]ˣ) : ℤˣ :=
  if IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]) then 1 else -1

/-! ## Elementary identities (theorems, from the definition) -/

/-- The defining locus is symmetric: swap the roles of `X` and `Y`. -/
theorem isHilbertSolvable_comm (a b : ℚ_[2]) :
    IsHilbertSolvable a b ↔ IsHilbertSolvable b a := by
  constructor <;>
  · rintro ⟨x, y, z, hne, heq⟩
    exact ⟨y, x, z, by tauto, by rw [← heq]; ring⟩

/-- `a X² + (-a) Y² = Z²` has the nontrivial solution `(1, 1, 0)`. -/
theorem isHilbertSolvable_self_neg (a : ℚ_[2]) : IsHilbertSolvable a (-a) :=
  ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩

/-- Rescaling the first slot by a nonzero square does not change the locus (`X ↦ c X`). -/
theorem isHilbertSolvable_mul_sq_left (a b : ℚ_[2]) {c : ℚ_[2]} (hc : c ≠ 0) :
    IsHilbertSolvable (a * c ^ 2) b ↔ IsHilbertSolvable a b := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨c * x, y, z, ?_, by rw [← heq]; ring⟩
    rcases hne with h | h | h
    · exact Or.inl (mul_ne_zero hc h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x / c, y, z, ?_, by rw [← heq]; field_simp⟩
    rcases hne with h | h | h
    · exact Or.inl (div_ne_zero h hc)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Symmetry** of the Hilbert symbol: `(a, b)₂ = (b, a)₂`. -/
theorem hilbertSymbol_comm (a b : ℚ_[2]ˣ) : hilbertSymbol a b = hilbertSymbol b a := by
  rw [hilbertSymbol, hilbertSymbol]
  by_cases h : IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2])
  · rw [if_pos h, if_pos ((isHilbertSolvable_comm _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((isHilbertSolvable_comm _ _).mpr hc))]

/-- `(a, -a)₂ = 1`. -/
theorem hilbertSymbol_self_neg (a : ℚ_[2]ˣ) : hilbertSymbol a (-a) = 1 := by
  have h : IsHilbertSolvable (a : ℚ_[2]) ((-a : ℚ_[2]ˣ) : ℚ_[2]) := by
    rw [Units.val_neg]; exact isHilbertSolvable_self_neg _
  rw [hilbertSymbol, if_pos h]

/-- **Square-class invariance** in the first slot: `(a c², b)₂ = (a, b)₂`. -/
theorem hilbertSymbol_mul_sq_left (a b c : ℚ_[2]ˣ) :
    hilbertSymbol (a * c ^ 2) b = hilbertSymbol a b := by
  have hcoe : ((a * c ^ 2 : ℚ_[2]ˣ) : ℚ_[2]) = (a : ℚ_[2]) * (c : ℚ_[2]) ^ 2 := by
    push_cast; ring
  rw [hilbertSymbol, hilbertSymbol, hcoe]
  by_cases h : IsHilbertSolvable ((a : ℚ_[2]) * (c : ℚ_[2]) ^ 2) (b : ℚ_[2])
  · rw [if_pos h, if_pos ((isHilbertSolvable_mul_sq_left _ _ c.ne_zero).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((isHilbertSolvable_mul_sq_left _ _ c.ne_zero).mpr hc))]

/-! ## Serre's residue characters `ε` and `ω`  (CiA Ch. II §3.3)

`ε` and `ω` depend only on `u (mod 8)`, so they factor through the reduction `ℤ₂ → ℤ/8`.  We define
them by the literal formulas `(u-1)/2` and `(u²-1)/8` on the residue's canonical representative
`ZMod.val ∈ {0,…,7}` (both numerators are divisible by `2`, resp. `8`, on the odd residues). -/

/-- `ε` on residues: `(r - 1)/2 mod 2`, using the representative `r.val ∈ {0,…,7}`. -/
def epsResidue (r : ZMod 8) : ZMod 2 := ((r.val - 1) / 2 : ℕ)

/-- `ω` on residues: `(r² - 1)/8 mod 2`, using the representative `r.val ∈ {0,…,7}`. -/
def omegaResidue (r : ZMod 8) : ZMod 2 := ((r.val ^ 2 - 1) / 8 : ℕ)

/-- `ε(u) ≡ (u - 1)/2 (mod 2)` — Serre, *A Course in Arithmetic*, Ch. II §3.3. -/
noncomputable def ε (u : ℤ_[2]ˣ) : ZMod 2 := epsResidue (PadicInt.toZModPow 3 (u : ℤ_[2]))

/-- `ω(u) ≡ (u² - 1)/8 (mod 2)` — Serre, *A Course in Arithmetic*, Ch. II §3.3. -/
noncomputable def ω (u : ℤ_[2]ˣ) : ZMod 2 := omegaResidue (PadicInt.toZModPow 3 (u : ℤ_[2]))

/-- On the unit residues `{1,3,5,7} ⊂ ℤ/8`, `ε` is additive. -/
theorem epsResidue_mul_of_isUnit {r s : ZMod 8} (hr : IsUnit r) (hs : IsUnit s) :
    epsResidue (r * s) = epsResidue r + epsResidue s := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨s, rfl⟩ := hs
  revert r s
  decide

/-- On the unit residues `{1,3,5,7} ⊂ ℤ/8`, `ω` is additive. -/
theorem omegaResidue_mul_of_isUnit {r s : ZMod 8} (hr : IsUnit r) (hs : IsUnit s) :
    omegaResidue (r * s) = omegaResidue r + omegaResidue s := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨s, rfl⟩ := hs
  revert r s
  decide

/-- `ε` is a homomorphism `ℤ₂ˣ → 𝔽₂`: `ε(uv) = ε(u) + ε(v)`. -/
theorem ε_mul (u v : ℤ_[2]ˣ) : ε (u * v) = ε u + ε v := by
  simp only [ε, Units.val_mul, map_mul]
  exact epsResidue_mul_of_isUnit (u.isUnit.map _) (v.isUnit.map _)

/-- `ω` is a homomorphism `ℤ₂ˣ → 𝔽₂`: `ω(uv) = ω(u) + ω(v)`. -/
theorem ω_mul (u v : ℤ_[2]ˣ) : ω (u * v) = ω u + ω v := by
  simp only [ω, Units.val_mul, map_mul]
  exact omegaResidue_mul_of_isUnit (u.isUnit.map _) (v.isUnit.map _)

/-- The reduction of the unit `-1 ∈ ℤ₂ˣ` is `-1 ∈ ℤ/8`. -/
theorem toZModPow_neg_one : PadicInt.toZModPow 3 ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = -1 := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

/-- `ε(-1) = 1` (as `-1 ≡ 3 (mod 4)`); checks the `ℤ₂ˣ → 𝔽₂` reduction, not just the residue. -/
theorem ε_neg_one : ε (-1) = 1 := by
  rw [ε, toZModPow_neg_one]; decide

/-- `ω(-1) = 0` (as `-1 ≡ -1 (mod 8)`); checks the `ℤ₂ˣ → 𝔽₂` reduction, not just the residue. -/
theorem ω_neg_one : ω (-1) = 0 := by
  rw [ω, toZModPow_neg_one]; decide

/-- Residue table for `ε`: `ε ≡ 0` on `{1, 5}` (`≡ 1 mod 4`), `ε ≡ 1` on `{3, 7}` (`≡ 3 mod 4`). -/
theorem epsResidue_table :
    epsResidue 1 = 0 ∧ epsResidue 3 = 1 ∧ epsResidue 5 = 0 ∧ epsResidue 7 = 1 := by
  decide

/-- Residue table for `ω`: `ω ≡ 0` on `{1, 7}` (`≡ ±1 mod 8`), `ω ≡ 1` on `{3, 5}` (`≡ ±3 mod 8`). -/
theorem omegaResidue_table :
    omegaResidue 1 = 0 ∧ omegaResidue 3 = 1 ∧ omegaResidue 5 = 1 ∧ omegaResidue 7 = 0 := by
  decide

/-! ## The dyadic Hilbert symbol formula (axiom B7′) -/

/-- The unit `2 ∈ ℚ₂ˣ`. -/
noncomputable def unit2 : ℚ_[2]ˣ := Units.mk0 2 (by norm_num)

/-- The inclusion of units `ℤ₂ˣ → ℚ₂ˣ` induced by `ℤ₂ ↪ ℚ₂`. -/
noncomputable def unitCoe (u : ℤ_[2]ˣ) : ℚ_[2]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := 2)).toMonoidHom u

/-- **B7′ (dyadic Hilbert symbol), `[Classical.]`.**  Writing `a = 2^α u`, `b = 2^β v` with
`u, v ∈ ℤ₂ˣ`, the Hilbert symbol over `ℚ₂` is
`(a, b)₂ = (-1)^{ε(u) ε(v) + α ω(v) + β ω(u)}`.

Citation: **Serre, *A Course in Arithmetic*, GTM 7, Ch. III §1.2, Theorem 1** (the `p = 2` case),
with `ε, ω` the residue characters of Ch. II §3.3.  This is exactly the paper's Lemma 3.5 formula
for the cup product on `H¹(ℚ₂, μ₂)`.  Convention: `signOf` sends the `𝔽₂`-valued exponent to
`{±1} = ℤˣ`; every element of `ℚ₂ˣ` has the form `2^α u` (`α ∈ ℤ`, `u ∈ ℤ₂ˣ`), so this determines
the symbol on all of `ℚ₂ˣ × ℚ₂ˣ`. -/
axiom hilbertSymbol_dyadic (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u)

/-- Faithfulness check on B7′: the axiom reproduces the canonical value `(-1, -1)₂ = -1` — the one
nontrivial diagonal entry, which anchors the paper's initial cup form `α² + βγ + γβ`.  (Depends on
`hilbertSymbol_dyadic`, so this is an `example`, not part of the unconditional API.) -/
example : hilbertSymbol (unitCoe (-1)) (unitCoe (-1)) = -1 := by
  have h := hilbertSymbol_dyadic 0 0 (-1) (-1)
  rw [zpow_zero, one_mul] at h
  rw [h, ε_neg_one, ω_neg_one]
  decide

end GQ2.HilbertSymbol
