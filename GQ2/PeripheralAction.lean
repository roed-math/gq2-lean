/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.MaxProP
public import GQ2.Zhat
public import GQ2.FreeProfinite
public import GQ2.Subdirect
public import GQ2.ZtwoPowering

@[expose] public section

/-!
# B8: the cyclotomic action on the peripheral generators (Lemma 3.6)

The paper's Lemma 3.6 records the **group-theoretic output** of the outer Galois action on the
geometric maximal pro-2 fundamental group `Δ = π₁^{pro-2}(ℙ¹_{ℚ̄} ∖ {0,1,∞})`: for the three
*peripheral inertia* generators `P, T` and `C := (PT)⁻¹`, each `u ∈ ℤ₂ˣ` in the image of the
cyclotomic character acts by a continuous automorphism `φ_u` sending every peripheral generator to a
**cyclotomic conjugate** `φ_u(P) = c_P⁻¹ · P^u · c_P`, etc.

## Faithfulness deviation

The *literal* statement quantifies the outer action `G_ℚ → Out(Δ)` on an étale/anabelian `π₁`, which
Mathlib has no types for.  We therefore state **exactly the group-theoretic conclusion**
(Lemma 3.6), on the concrete `Δ = maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))`:

* `Δ`, `P = of 0`, `T = of 1`, `C = (PT)⁻¹` — `GQ2.Delta`, `GQ2.deltaP/T/C`.
* the cyclotomic power `P^u` is `P ^ᶻ (ι u)` (`GQ2/Zhat.lean` ẑ-exponentiation), where
  `ι : ℤ₂ˣ → ℤ̂` is the **2-adic cyclotomic exponent embedding** — `ι(u)` is `≡ u` on the pro-2
  part and `≡ 0` on the odd part, so on the pro-2 group `Δ` it computes the `u`-th power.  `ι` is
  carried as *data* of the bundle (as `rec`/`inv` are for B5/B6), pinned by `hι_cont` (continuity),
  `hι_one : ι 1 = ω₂` (`GQ2.omega2`; the `u = 1` cyclotomic exponent is exactly the idempotent
  of the profinite-exponentiation API — on a pro-2 group `x ^ᶻ ω₂ = x`), and `hι_proj` (see below).

**Interface correction.**  Pinning `ι` by `hι_cont` + `hι_one` alone is too weak: without the
full condition "`ι(u) ≡ u` on the pro-2 part" (i.e. `ι(u) = u·ω₂`), `ι(u)`'s action on a pro-2
group is undetermined for `u ≠ 1`
(e.g. `ι ≡ ω₂` satisfies both pinnings), so Lemma 3.7's proof cannot extract the `u`-th power.
The projection `GQ2.zhatProjTwo : ℤ̂ → ℤ₂` (`ker = proPKernel 2 ℤ̂`) makes the intended pinning
expressible **without** any `ℤ̂`-ring structure, and `hι_proj` states exactly it:
`zhatProjTwo (ι u) = ofAdd u`.  Consequently, on every pro-2 group `x ^ᶻ ι u = zpowZtwo x u`
(`GQ2/ZtwoPowering.lean`'s `zpowHat_eq_zpowZtwo`) — the `u`-th 2-adic power, as Lemma 3.6 intends.
Consistency: `ι(u) := u·ω₂` (classically) satisfies all four pinnings; for `u = 1` the
compatibility of `hι_one` with `hι_proj` is the *proved* `GQ2.zhatProjTwo_omega2`
(`zhatProjTwo ω₂ = ofAdd 1`, `GQ2/AnabelianBridge.lean`).  Reviewers re-check Lemma 3.6 ⟹ this
(strengthened) bundle; the mathematical content is unchanged — the decomposition group acts on
inertia through the cyclotomic character, whose 2-adic component at `u` **is** `u`.

The axiom `GQ2.Foundations` `peripheralCyclotomicAction : PeripheralCyclotomicAction` asserts this
bundle exists.  **Reviewers check the implication** (Lemma 3.6 ⟹ this bundle), **not a `π₁`
formalization**.

Citation: **Stix [8], §3.3 ("Cusps and inertia subgroups") and Definition 37** — the decomposition
group of a rational cusp acts on the procyclic inertia group through the cyclotomic character (the
paper's exact citation `[8, Section 3.3 and Definition 37]`).  Classical origin: Deligne, MSRI 16
(1989).  Paper: Lemma 3.6.  `docs/literature-axioms.md` B8.
-/

open scoped Pointwise

namespace GQ2

/-! ## `Δ` and its peripheral generators -/

/-- **`Δ`** (paper §3): the maximal pro-2 quotient of the free profinite group on two generators —
the geometric maximal pro-2 fundamental group `π₁^{pro-2}(ℙ¹ ∖ {0,1,∞})`, presented
group-theoretically. -/
noncomputable abbrev Delta : ProfiniteGrp := maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))

/-- The peripheral generator `P` (image of the first free generator in `Δ`). -/
noncomputable def deltaP : Delta :=
  maxProPMk 2 (FreeProfiniteGroup (Fin 2)) (FreeProfiniteGroup.of 0)

/-- The peripheral generator `T` (image of the second free generator in `Δ`). -/
noncomputable def deltaT : Delta :=
  maxProPMk 2 (FreeProfiniteGroup (Fin 2)) (FreeProfiniteGroup.of 1)

/-- The third peripheral generator `C := (P·T)⁻¹` (so `P·T·C = 1`). -/
noncomputable def deltaC : Delta := (deltaP * deltaT)⁻¹

/-! ## The Lemma 3.6 bundle -/

/-- **Lemma 3.6 (B8), bundled.**  The cyclotomic action on the peripheral generators of
`Δ = maxPro2(F₂)`: a 2-adic cyclotomic exponent embedding `ι` and, for each `u ∈ ℤ₂ˣ`, a continuous
automorphism `aut u` of `Δ` sending each peripheral generator to the corresponding cyclotomic
conjugate.  See the module docstring for the faithfulness deviation (no `π₁`) and the pinning of
`ι`.  Conjugation convention `x ^ c = c⁻¹ x c` (`GQ2.conjP`, matching `GQ2/Words.lean`). -/
structure PeripheralCyclotomicAction where
  /-- The 2-adic cyclotomic exponent embedding `ℤ₂ˣ → ℤ̂` (`ι(u) ≡ u` on the pro-2 part, `≡ 0` on
  the odd part). -/
  ι : ℤ_[2]ˣ → Zhat
  /-- `ι` is continuous. -/
  hι_cont : Continuous ι
  /-- `ι(1) = ω₂`: the `u = 1` cyclotomic exponent is the idempotent of the profinite-exponentiation API (so `P ^ᶻ ι 1 = P` on
  the pro-2 group `Δ`). -/
  hι_one : ι 1 = omega2
  /-- **`ι(u) ≡ u` on the pro-2 part** (see the module docstring): the canonical
  projection `ℤ̂ → ℤ₂` sends `ι u` to `u`.  This is what makes `x ^ᶻ ι u` the `u`-th 2-adic power
  on every pro-2 group (`zpowHat_eq_zpowZtwo`). -/
  hι_proj : ∀ u : ℤ_[2]ˣ, zhatProjTwo (ι u) = Multiplicative.ofAdd ((u : ℤ_[2]))
  /-- The continuous automorphism `φ_u` of `Δ` induced by `u ∈ ℤ₂ˣ`. -/
  aut : ℤ_[2]ˣ → ContinuousMulEquiv Delta Delta
  /-- The conjugator `c_P(u)` for the generator `P`. -/
  cP : ℤ_[2]ˣ → Delta
  /-- The conjugator `c_T(u)` for the generator `T`. -/
  cT : ℤ_[2]ˣ → Delta
  /-- The conjugator `c_C(u)` for the generator `C`. -/
  cC : ℤ_[2]ˣ → Delta
  /-- `φ_u(P) = c_P⁻¹ · P^u · c_P`. -/
  hP : ∀ u : ℤ_[2]ˣ, aut u deltaP = conjP (deltaP ^ᶻ ι u) (cP u)
  /-- `φ_u(T) = c_T⁻¹ · T^u · c_T`. -/
  hT : ∀ u : ℤ_[2]ˣ, aut u deltaT = conjP (deltaT ^ᶻ ι u) (cT u)
  /-- `φ_u(C) = c_C⁻¹ · C^u · c_C`. -/
  hC : ∀ u : ℤ_[2]ˣ, aut u deltaC = conjP (deltaC ^ᶻ ι u) (cC u)

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 3.6 = ⟦lem-peripheralpower⟧ (= lemma 3.7 in current tex)
  * Lemma 3.7 = ⟦lem-squarerootHNN⟧ (= lemma 3.8 in current tex)
-/
