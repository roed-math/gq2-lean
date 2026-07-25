/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.DRPresentation
public import GQ2.FoxHeisenberg.Basic

@[expose] public section

/-!
# The χ-twisted crossed-derivation calculus for `r₂`  (Roe note §3.2, ⟦prop:orientation⟧)

**Skeleton (ticket R7; fills are R9/R11).**  Statements are final; proofs may be `sorry`.

Labute's characterization of the canonical Demushkin orientation ([Labute], Théorème 4; note
Prop. 3.3 ⟦prop:orientation⟧): for a character `χ` of the free pro-2 group, a **crossed
derivation** into the rank-one module `ℤ₂(χ)` satisfies

  `D(gh) = Dg + χ(g)·Dh`,   `D(g⁻¹) = −χ(g)⁻¹·Dg`,

and such derivations descend through the relation precisely when `D(r₂) = 0` for arbitrary
values of `Ds, Dx, Dy`.  The canonical orientation is the unique `χ` with this property.

## Realization: `WordLift ℤ₂ ℤ₂ˣ`

A pair (character value, derivation value) is a point of the lift group
`ℤ₂(χ) ⋊ ℤ₂ˣ = FoxH.WordLift ℤ_[2] ℤ_[2]ˣ` (`GQ2/FoxHeisenberg/Basic.lean:76`, with `A = ℤ₂`
a `C = ℤ₂ˣ`-module via unit multiplication — Mathlib's `Units` scalar action), whose
multiplication `(u, g)(v, h) = (u + g•v, gh)` *is* the crossed-derivation product rule and
whose inverse is the inverse rule.  Assigning the generators `s, x, y ↦ (Ds, S), (Dx, X),
(Dy, Y)` therefore extends (uniquely) to the free group, and the value of the extension on
`r₂` is literally `drWord ⟨Ds, S⟩ ⟨Dx, X⟩ ⟨Dy, Y⟩`: its `.u`-component is `D(r₂)` and its
`.g`-component is `χ(r₂)`.  "Every crossed derivation kills `r₂`, and `χ` kills `r₂`" is the
single equation

  `∀ Ds Dx Dy, drWord ⟨Ds, S⟩ ⟨Dx, X⟩ ⟨Dy, Y⟩ = 1`   (`IsLabuteOrientationDatum`).

## The four equations

Evaluating (`drWord_wordLift`) and collecting coefficients produces the note's
⟦eq:charrelation⟧/⟦eq:Cx⟧/⟦eq:Cs⟧/⟦eq:Cy⟧: the base component gives the character relation
`Y² = X⁴` (3.9), and the offset component is `csR·Ds + cxR·Dx + cyR·Dy` with the coefficient
functions below.  `cxR` is the note's (3.10) verbatim; `csR`/`cyR` are the **raw** (pre-descent)
forms, which reduce to the note's (3.11)/(3.12) after substituting `Y² = X⁴`
(`X⁻⁴(Y−1)² = (Y−1)²/Y²` and `X⁻⁴(Y−1) = Y⁻¹(1−Y⁻¹)`); the raw forms are what the word
evaluation literally produces, so they are the right statement-final normal forms here.

## Solution  ⟦eq:orientationvalues⟧

Branch `Y = X²` is excluded (`(X−1)(X²−X−1) = 0` with the second factor odd forces `X = 1`,
then `Cy = 2 ≠ 0`); on `Y = −X²` the system reduces to the cubic `X³ + 2X² + 1 = 0` with
`S·(X²+X+1) = −X³`, and `Cy` becomes automatic (`Cy = (X+1)(X³+2X²+1)/X⁷`).  The Hensel root
`X ≡ 5 (mod 16)`, `S ≡ 13 (mod 16)` and the induced `im χ_R = {±1}×(1+4ℤ₂)` are ticket R10/R11
content (`GQ2/Roe/OrientationRoot.lean`); the existence/uniqueness statements here consume the
root facts as *hypotheses* whose shapes match R10's planned `rootX_spec`/`Sval_spec` exactly,
so no import of the (parallel) R10 file is needed.

All numerics were independently re-derived and 2-adically checked in the R2 spike
(`docs/orchestration/roe-r2-spike.md` §2): symbolic descent system, branch exclusion,
`X ≡ 2997 (mod 2¹²)`, and `Cx = Cs = Cy = 0` exactly at the root.
-/

namespace GQ2

open FoxH

/-! ## The crossed-derivation evaluation of the atomic factors -/

/-- **Conjugation rule** (note §3.2, first display): in the lift group `ℤ₂(χ) ⋊ ℤ₂ˣ`,
`x^s` at the lifts `(Dx, X), (Ds, S)` has derivation component
`D(x^s) = S⁻¹·Dx + S⁻¹(X−1)·Ds`. -/
theorem conjP_wordLift (S X : ℤ_[2]ˣ) (Ds Dx : ℤ_[2]) :
    conjP (⟨Dx, X⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Ds, S⟩
      = ⟨(↑(S⁻¹) : ℤ_[2]) * Dx + (↑(S⁻¹) : ℤ_[2]) * ((↑X : ℤ_[2]) - 1) * Ds, conjP X S⟩ := by
  ext
  · simp only [conjP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
      Units.smul_def, smul_eq_mul, Units.val_mul]
    ring
  · rfl

/-- **Commutator rule** ⟦eq:commderivative⟧ (note (3.8)): for lifts with character values
`G, H`, `D[g,h] = G⁻¹(H⁻¹−1)·Dg + H⁻¹(1−G⁻¹)·Dh`. -/
theorem commP_wordLift (Gv Hv : ℤ_[2]ˣ) (Dg Dh : ℤ_[2]) :
    commP (⟨Dg, Gv⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dh, Hv⟩
      = ⟨(↑(Gv⁻¹) : ℤ_[2]) * ((↑(Hv⁻¹) : ℤ_[2]) - 1) * Dg
          + (↑(Hv⁻¹) : ℤ_[2]) * (1 - (↑(Gv⁻¹) : ℤ_[2])) * Dh, commP Gv Hv⟩ := by
  ext
  · simp only [commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
      Units.smul_def, smul_eq_mul, Units.val_mul]
    linear_combination ((Hv⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * Dh * Units.inv_mul Gv
  · rfl

/-! ## The three coefficient functions -/

/-- **The `Dx`-coefficient** of `D(r₂)` — note ⟦eq:Cx⟧ (3.10), verbatim:
`−(X⁻¹S⁻¹ + X⁻² + X⁻³ + X⁻⁴)`. -/
noncomputable def cxR (S X : ℤ_[2]ˣ) : ℤ_[2] :=
  -((↑(X⁻¹) : ℤ_[2]) * (↑(S⁻¹) : ℤ_[2]) + (↑(X⁻¹) : ℤ_[2]) ^ 2 + (↑(X⁻¹) : ℤ_[2]) ^ 3
    + (↑(X⁻¹) : ℤ_[2]) ^ 4)

/-- **The `Ds`-coefficient** of `D(r₂)` — note ⟦eq:Cs⟧ (3.11) in **raw** (pre-descent) form:
`S⁻¹·(−X⁻¹(X−1) + X⁻⁴(Y−1)²)`.  The note displays `(Y−1)²/Y²` for the second summand, which
is this expression after the character relation `Y² = X⁴` ⟦eq:charrelation⟧; the raw form is
what the word evaluation (`drWord_wordLift`) literally produces. -/
noncomputable def csR (S X Y : ℤ_[2]ˣ) : ℤ_[2] :=
  (↑(S⁻¹) : ℤ_[2]) * (-((↑(X⁻¹) : ℤ_[2]) * ((↑X : ℤ_[2]) - 1))
    + (↑(X⁻¹) : ℤ_[2]) ^ 4 * ((↑Y : ℤ_[2]) - 1) ^ 2)

/-- **The `Dy`-coefficient** of `D(r₂)` — note ⟦eq:Cy⟧ (3.12) in **raw** (pre-descent) form:
`X⁻⁴·((1+Y) + (Y−1)(S⁻¹−1))`.  The note displays the second summand as `Y⁻¹(1−Y⁻¹)(S⁻¹−1)`
(no `X⁻⁴`), which is this expression after `Y² = X⁴` ⟦eq:charrelation⟧. -/
noncomputable def cyR (S X Y : ℤ_[2]ˣ) : ℤ_[2] :=
  (↑(X⁻¹) : ℤ_[2]) ^ 4 * ((1 + (↑Y : ℤ_[2]))
    + ((↑Y : ℤ_[2]) - 1) * ((↑(S⁻¹) : ℤ_[2]) - 1))

/-! ## The `r₂`-evaluation identity -/

/-- **The `r₂`-evaluation identity** (note §3.2, "collecting the three free coefficients") —
the master computation from which ⟦eq:charrelation⟧/⟦eq:Cx⟧/⟦eq:Cs⟧/⟦eq:Cy⟧ are read off:
evaluating the Roe relator word at the crossed-derivation lifts
`s ↦ (Ds, S), x ↦ (Dx, X), y ↦ (Dy, Y)` in `ℤ₂(χ) ⋊ ℤ₂ˣ` gives derivation component
`csR·Ds + cxR·Dx + cyR·Dy` and character component `X⁻⁴Y²`.

Fill (R9): expand via `conjP_wordLift`/`commP_wordLift`, `WordLift.mul_u`/`pow_u`, then
`ring`; the base component is `drWord_comm` in `ℤ₂ˣ`. -/
theorem drWord_wordLift (S X Y : ℤ_[2]ˣ) (Ds Dx Dy : ℤ_[2]) :
    drWord (⟨Ds, S⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dx, X⟩ ⟨Dy, Y⟩
      = ⟨csR S X Y * Ds + cxR S X * Dx + cyR S X Y * Dy, (X ^ 4)⁻¹ * Y ^ 2⟩ := by
  sorry

/-! ## The Labute descent condition -/

/-- **The Labute descent condition on character values** ⟦prop:orientation⟧: `(S, X, Y)` is a
*Labute orientation datum* for the Roe relator if the lifted word dies for **every** choice of
derivation generator-values — equivalently (`isLabuteOrientationDatum_iff`): the character kills
`r₂` (base component, ⟦eq:charrelation⟧) and every crossed derivation into `ℤ₂(χ)` kills `r₂`
(offset component, ⟦eq:Cx⟧/⟦eq:Cs⟧/⟦eq:Cy⟧).  This is Labute's characterization of the descent
of crossed derivations through the relation ([Labute], Théorème 4; note Prop. 3.3). -/
def IsLabuteOrientationDatum (S X Y : ℤ_[2]ˣ) : Prop :=
  ∀ Ds Dx Dy : ℤ_[2],
    drWord (⟨Ds, S⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dx, X⟩ ⟨Dy, Y⟩ = 1

/-- **A Labute orientation of `D_R`** ⟦prop:orientation⟧: a character `χ : D_R → ℤ₂ˣ` whose
generator values form a Labute orientation datum.  (House style for `ℤ₂ˣ`-valued characters —
`MonoidHom` plus a separate continuity hypothesis where needed — follows
`DyadicOrientation.chiTwo` and `prop_3_8_classification`.)  The note's `χ_R` is the unique such
character (`isLabuteOrientation_ext`); its construction from the Hensel root is ticket R11. -/
def IsLabuteOrientation (χ : (DR : Type) →* ℤ_[2]ˣ) : Prop :=
  IsLabuteOrientationDatum (χ drS) (χ drX) (χ drY)

/-- **Extraction of the four equations** ⟦eq:charrelation⟧/⟦eq:Cx⟧/⟦eq:Cs⟧/⟦eq:Cy⟧: the
Labute descent condition holds iff the character relation `Y² = X⁴` holds and the three
coefficients vanish.

Fill (R9): rewrite by `drWord_wordLift`; forward direction plugs the three coordinate vectors
`(1,0,0), (0,1,0), (0,0,1)` into the derivation values; backward is linearity. -/
theorem isLabuteOrientationDatum_iff (S X Y : ℤ_[2]ˣ) :
    IsLabuteOrientationDatum S X Y ↔
      (Y ^ 2 = X ^ 4 ∧ cxR S X = 0 ∧ csR S X Y = 0 ∧ cyR S X Y = 0) := by
  sorry

/-! ## Existence and uniqueness of the solution  ⟦eq:orientationvalues⟧

The root facts are consumed as hypotheses whose shapes match ticket R10's planned
`GQ2/Roe/OrientationRoot.lean` interface (`rootX`/`rootX_spec`, `Sval`/`Sval_spec`,
uniqueness of the unit root) — see the R7 design memo §R10 for the name map. -/

/-- **Existence** ⟦eq:orientationvalues⟧: given a unit root `X` of `Z³ + 2Z² + 1` (R10's
`rootX_spec`), the unit `S` with `S·(X²+X+1) = −X³` (R10's `Sval_spec`; the denominator is a
unit, note ⟦eq:SfromX⟧), and `Y = −X²`, the triple `(S, X, Y)` is a Labute orientation datum.

Fill (R9, pure `ring`-level algebra from `isLabuteOrientationDatum_iff`): the character
relation is `(−X²)² = X⁴`; `Cx·(−S X⁴) = X³ + 2X² + 1 − (X³ + X² + X)·(1 + S⁻¹X⁻¹·…)`-style
clearing reduces `Cx = 0` to `Sval_spec`, `Cs = 0` to the cubic, and `Cy` to the identity
`Cy·X⁷ = (X+1)(X³+2X²+1)` (automatic; R2 spike §2.1). -/
theorem isLabuteOrientationDatum_of_root (X S Y : ℤ_[2]ˣ)
    (rootX_spec : (↑X : ℤ_[2]) ^ 3 + 2 * (↑X : ℤ_[2]) ^ 2 + 1 = 0)
    (Sval_spec : (↑S : ℤ_[2]) * ((↑X : ℤ_[2]) ^ 2 + (↑X : ℤ_[2]) + 1) = -(↑X : ℤ_[2]) ^ 3)
    (hY : (↑Y : ℤ_[2]) = -(↑X : ℤ_[2]) ^ 2) :
    IsLabuteOrientationDatum S X Y := by
  sorry

/-- **Solution extraction** ⟦eq:orientationvalues⟧: any Labute orientation datum satisfies
`Y = −X²`, the cubic `X³ + 2X² + 1 = 0`, and `S·(X²+X+1) = −X³` (the multiplicatively cleared
form of ⟦eq:SfromX⟧ `S = −X³/(X²+X+1)`).

Fill (R9/R10): via `isLabuteOrientationDatum_iff`.  `Y = ±X²` since `±1` are the only square
roots of `1` in `ℤ₂ˣ`; the branch `Y = X²` is **excluded** — clearing denominators in `Cs = 0`
gives `(X−1)(X²−X−1) = 0` with the second factor odd, so `X = 1`, and then `Cy = 2 ≠ 0`
(note Prop. 3.3, proof).  On `Y = −X²` the equation `Cs = 0` clears to the cubic. -/
theorem isLabuteOrientationDatum_solution {S X Y : ℤ_[2]ˣ}
    (h : IsLabuteOrientationDatum S X Y) :
    (↑X : ℤ_[2]) ^ 3 + 2 * (↑X : ℤ_[2]) ^ 2 + 1 = 0 ∧
      (↑Y : ℤ_[2]) = -(↑X : ℤ_[2]) ^ 2 ∧
      (↑S : ℤ_[2]) * ((↑X : ℤ_[2]) ^ 2 + (↑X : ℤ_[2]) + 1) = -(↑X : ℤ_[2]) ^ 3 := by
  sorry

/-- **Uniqueness of the datum**, relative to uniqueness of the unit root of the cubic (the
Hensel-uniqueness fact supplied by R10; consumed here as the hypothesis `rootX_unique`):
two Labute orientation data coincide.

Fill (R11): both satisfy `isLabuteOrientationDatum_solution`; `rootX_unique` forces `X = X'`,
then `Y = −X²` forces `Y = Y'` and `S·(X²+X+1) = −X³` forces `S = S'` (the factor `X²+X+1` is
odd, hence a unit, and `Units.ext` applies). -/
theorem isLabuteOrientationDatum_unique
    (rootX_unique : ∀ a b : ℤ_[2]ˣ,
      (↑a : ℤ_[2]) ^ 3 + 2 * (↑a : ℤ_[2]) ^ 2 + 1 = 0 →
      (↑b : ℤ_[2]) ^ 3 + 2 * (↑b : ℤ_[2]) ^ 2 + 1 = 0 → a = b)
    {S X Y S' X' Y' : ℤ_[2]ˣ}
    (h : IsLabuteOrientationDatum S X Y) (h' : IsLabuteOrientationDatum S' X' Y') :
    S = S' ∧ X = X' ∧ Y = Y' := by
  sorry

/-- **Uniqueness at the character level**: two Labute orientations of `D_R` agree — they agree
on the generators by `isLabuteOrientationDatum_unique`, hence everywhere by topological
generation of `D_R` by `s, x, y` (the generation lemma is ticket-R8 infrastructure; continuity
of both characters is required for the density argument). -/
theorem isLabuteOrientation_ext
    (rootX_unique : ∀ a b : ℤ_[2]ˣ,
      (↑a : ℤ_[2]) ^ 3 + 2 * (↑a : ℤ_[2]) ^ 2 + 1 = 0 →
      (↑b : ℤ_[2]) ^ 3 + 2 * (↑b : ℤ_[2]) ^ 2 + 1 = 0 → a = b)
    {χ χ' : (DR : Type) →* ℤ_[2]ˣ} (hχ : Continuous χ) (hχ' : Continuous χ')
    (h : IsLabuteOrientation χ) (h' : IsLabuteOrientation χ') : χ = χ' := by
  sorry

/-! ## Stress test -/

/-- **Stress test (the trivial character is not a Labute orientation datum)**: at
`(S, X, Y) = (1, 1, 1)` the derivation values `(0, 0, 1)` give `D(r₂) = 2 ≠ 0` — the
`y²`-factor contributes `(1 + Y)·Dy = 2` and everything else vanishes.  (This is the same
`Cy = 2` obstruction that kills the excluded branch at `X = 1`.) -/
theorem not_isLabuteOrientationDatum_one : ¬ IsLabuteOrientationDatum 1 1 1 := by
  intro h
  have h1 := congrArg WordLift.u (h 0 0 1)
  simp only [drWord, conjP, commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u,
    WordLift.inv_g, WordLift.one_u, WordLift.one_g, Units.smul_def, smul_eq_mul,
    Units.val_mul, pow_succ, pow_zero] at h1
  norm_num at h1

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Prop 3.3 = ⟦prop:orientation⟧
  * eq. (3.3)/(3.9) = ⟦eq:orientationvalues⟧/⟦eq:charrelation⟧
  * eq. (3.8) = ⟦eq:commderivative⟧
  * eq. (3.10)–(3.12) = ⟦eq:Cx⟧/⟦eq:Cs⟧/⟦eq:Cy⟧
  * eq. (3.13) = ⟦eq:SfromX⟧
-/
