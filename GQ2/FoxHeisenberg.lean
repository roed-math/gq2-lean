/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.FoxHeisenberg.Basic
public import GQ2.FoxHeisenberg.Heisenberg
public import GQ2.FoxHeisenberg.Traced
public import GQ2.FoxHeisenberg.WildRow
public import GQ2.FoxHeisenberg.HessianRow

@[expose] public section

/-!
# §5 statements: the two source-specific lifting theories

The paper's §5 sets up, for a finite *lower target* `C` and an elementary `𝔽₂[C]`-module `A`,
the two cochain theories that the §9 induction compares: the **finite word complex** (30) on the
candidate side, and continuous Galois cohomology on the local side.  This file is a thin
umbrella: the content now lives in the `GQ2/FoxHeisenberg/` sub-modules imported above
(`Basic`, `Heisenberg`, `Traced`, `WildRow`, `HessianRow`), which provide the definition layer
(the complex, the Heisenberg groups, the mixed central coordinate) and the **proved**
Lemmas/Propositions 5.6, 5.7, 5.8, 5.11, 5.12, 5.13, 5.15, 5.16 together with the
5.17-numerics wiring corollary.  The overview below documents the §5 encodings shared by all
the sub-modules.

## The §5 objects and their encodings

* **Coefficients.**  `A` is an "elementary `𝔽₂[C]`-module": `[AddCommGroup A]` +
  `[DistribMulAction C A]` + the hypothesis `hA₂ : ∀ a : A, a + a = 0` (+ `[Finite A]` where the
  paper says finite).  No `Module 𝔽₂` instances (the continuous-cohomology and Demushkin conventions); "dim"-statements are stated
  in `Nat.card` form (e.g. `2^{2 dim A + dim (A^∨)^C}` becomes `#A² · #(A^∨)^C`).
* **The lower map.**  The complex depends on `ρ : Γ ↠ C` only through the four marked values
  `ρ(σ), ρ(τ), ρ(x₀), ρ(x₁)`, i.e. through the pushed marking `univMarking.map ρ` — so the
  whole candidate-side theory is parametrized by a `t : Marking C` (`GQ2/Words.lean`), keeping
  §5 purely finite.  The relations enter as hypotheses `t.TameRel`, `t.WildRel` where the paper
  assumes `ρ` kills the relators.
* **Relator values.**  `Marking.tameValue = τ^σ (τ²)⁻¹` and `Marking.wildValue = h₀u₁⁻¹x₁^σc₀`
  (relations (5)/(6) as *elements*; `= 1 ↔ TameRel/WildRel` proved).  The `ω₂`-powers are
  `powOmega2` — by the profinite-exponentiation API's headline these compute the profinite `ω₂` in every finite group, and
  by `powOmega2_pow_eq` any integer representative modulo the relevant exponent agrees: that is
  exactly **Lemma 5.1** (finite-exponent independence), which is therefore *absorbed by the
  encoding* and not re-stated.
* **`A ⋊ C`** (`WordLift A C`): own structure with the paper's lift convention
  `(u, g)(v, h) = (u + g•v, gh)` (Lemma 5.5's proof display) — definitional, no
  `Multiplicative`-wrapped `SemidirectProduct` (avoids the Demushkin wrapper traps).
* **The word complex (30)/(31).**  `d0 t : A →+ (Fin 4 → A)` is (31) (indices `0,1,2,3` =
  `σ,τ,x₀,x₁`, matching `univMarking`); `d1Fun t x` is the pair of `A`-coordinates of the two
  relator values at the lifted marking `liftMarking t x` — the paper's "coefficient of `A` in
  the evaluated tame and wild relators", verbatim.  **Additivity of `d1Fun` is the paper's
  "finite Fox rules"**, proved as `d1Fun_add` (via the ledger of Lemma 5.4); the bundled
  `d1 t` is built on it, and `Z1w/H0w/H1w/H2w` follow the `ContCoh` shape
  (`H1 = Z1 ⧸ B1.addSubgroupOf Z1` — total definitions, no chain condition needed; the
  chain identity `d¹∘d⁰ = 0` under the relations is the separate proved `d1Fun_comp_d0`).
  The **proved** stress test `d1Fun_tame` computes the tame row in closed form — the general
  form of display (34), validating the convention stack (lift order, `conjP`, the `(u,g)(v,h)`
  rule) end-to-end.
* **`𝔽₂`-duals** (`ElemDual A := A →+ ZMod 2`): the Tate-duality interface's `MuDual` def-synonym recipe (own
  `FunLike`, contragredient action `(g•λ)(a) = λ(g⁻¹•a)`; a plain `abbrev` would collide with
  Mathlib's codomain-action instance).
* **`H(A) ⋊ C`** (`HeisLift A C`, §5.2): own structure on `A × A^∨ × 𝔽₂ × C` with the paper's
  multiplication `(a,λ,z)(a',λ',z') = (a+a', λ+λ', z+z'+λ(a'))` twisted by the diagonal
  `C`-action — again definitional.  `mixedB t x y` is the traced mixed central coordinate
  `B_{ρ,A} = β_t + β_w` of Prop 5.8 (the **sum** of the two words' `z`-coordinates, not the
  `z`-coordinate of their product).
* **Stokes** (Lemma 5.7): stated in the paper's general form — ordinary free group
  `FreeGroup (Fin n)` (Mathlib's, not profinite), evaluation `stokesEval` via `FreeGroup.lift`,
  mod-2 exponents `expMod2` via the lift to `Multiplicative (ZMod 2)`.  The tame relator's
  exponent vector `(0,1,0,0)` (Prop 5.8's proof) is **proved** here for the free-group tame
  word (`expMod2_fgTame`); the wild word's vector was the §5 proof layer content (it needs the integer-`ω₂`
  representative words) and is proved in the sub-modules.
* **Duality statements.**  5.15/5.16 are stated in `Nat.card` + pairing form; "perfect" is
  encoded as two-sided nondegeneracy (equivalent to perfectness for finite elementary groups,
  given the card clauses).  On the candidate side the descended `H¹×H¹`-pairing is carried
  *inside* the statement (`∃ P, descends mixedB ∧ nondegenerate`) — no descent-backed
  definitions.  On the local side the pairing is the *already-descended* cup product with the
  evaluation pairing `dualEval`, in the form used by `TateDuality`;
  `TateDuality` phrasing; the target-line certification is the clause `#H²(𝔽₂-trivial) = 2`.
  `IsSelfDual` packages the 5.15 conclusion; **Lemma 5.11** (dévissage) is stated as
  two-out-of-three for `IsSelfDual` along a short exact sequence of coefficient modules — the
  mapping cone `K(A)` of (49) is its *proof* device (the §5 proof layer), not statement content (flagged
  deviation).
* **Prop 5.10** (the Fox–Heisenberg chain map) is *not* packaged as a `HomologicalComplex`
  map: its degree-(0,2) components are the trivial `traceD0`/`traceD2` below, and its two
  chain identities (47)/(48) are — after unfolding the canonical identifications — exactly
  Prop 5.8's (41)/(42) with `L = d1Fun` on `A` resp. `A^∨`.  Statement content = 5.8 + 5.6;
  deviation flagged.

## Encoding deviations

* **Corollary 5.17's adjoint-boundary identity (58)** uses connecting maps
  `∂ : H¹(V) → H²(T)` in *both* theories (snake maps for the word complex, coefficient-SES
  connecting maps for `ContCoh`).  The numerical half is `cor_5_17_card`; the connecting-map
  formulation is kept in the downstream assembly where both complexes are available.
* Lemmas 5.2/5.3/5.4/5.14 are represented by the class-two identity, `h₀`-shadow, ledger, and
  Hessian calculations in the proof modules.  Lemma 5.1 is absorbed into the definitions above.

Conventions: `x ^ g = g⁻¹xg` (`conjP`), `[x,y] = x⁻¹y⁻¹xy` (`commP`), marking order
`(σ, τ, x₀, x₁)` = indices `0,1,2,3`.
-/
