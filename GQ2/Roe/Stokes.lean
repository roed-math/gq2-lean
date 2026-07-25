/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Words
public import GQ2.FoxHeisenberg.Traced

@[expose] public section

/-!
# The `r_R` Stokes exponent vector (Roe note Lemma 5.1 ⟦lem:stokes⟧)

Transcribes Lemma 5.1 of the verification note `paper/roe-presentation-verification.tex` (the "Roe
note") for the Roe wild relator `r_R`: the mod-2 exponent-vector facts that feed the finite-word
Stokes endpoint of Lemma 5.7 / Proposition 5.8.  This is the Roe-candidate twin of the `Γ_A`
computation `GQ2.FoxH.expMod2_wildValueExp` (`GQ2/FoxHeisenberg/Traced.lean`); the machinery
(`expMod2`, `freeMarking`, `fgTame`, `expMod2_fgTame`) is reused verbatim from the Fox–Heisenberg
core, never re-proved.

The note's Lemma 5.1 ⟦lem:stokes⟧, verbatim:
```
Modulo \(2\), the exponent vectors of \(\rt\) and \(\rR\), in the ordered
basis \((\sigma,\tau,x_0,x_1)\), are both
\[
  (0,1,0,0).
\]
Their sum is zero.  Hence the trace
\[
  (u_{\mathrm t},u_{\mathrm w})\longmapsto
  u_{\mathrm t}+u_{\mathrm w}
\]
satisfies the endpoint condition of the finite-word Stokes formula
\cite[Lemma~5.7 and Proposition~5.8]{RT}.
```
and its proof, for `r_R`:
```
Choose any finite integer exponent representing \(\omegaTwo\) at the
finite level under consideration.  It is odd.  In \(\rR\), the first
factor contributes one \(x_0\) modulo \(2\), while
\((x_0^{-3}\tau)^{\omegaTwo}\) contributes one \(x_0\) and one \(\tau\).
The two \(x_0\)-contributions cancel.  The square \(x_1^2\) and the
commutator have zero exponent vector modulo \(2\).  Thus only the
\(\tau\)-coordinate remains.
```

This file supplies:
* **`expMod2_wildValueExpR`** — the *general-exponent* vector `(0, e, e+1, 0)` in basis
  `(σ, τ, x₀, x₁)` for the finite-word form `wildValueExpR freeMarking e` (the `Γ_A` twin
  `expMod2_wildValueExp` reads `(0, e, 0, e+1)`; the `Γ_R` word carries its `τ`/`x₀`-defect on
  `x₀` rather than `x₁`).  Mirrors `Traced.lean`'s `expMod2_wildValueExp` line-for-line:
  conjugations are `expMod2`-invariant and commutators vanish in the abelian target
  `Multiplicative (ZMod 2)`, so only `(x₀^σ)⁻¹` (one `x₀`) and `(x₀⁻³τ)^e` (`e·(−3) ≡ e` `x₀`'s
  and `e` `τ`'s) survive, while `x₁²` and `cR` die;
* **`expMod2_wildValueExpR_odd`** — the odd-`e` collapse to `(0, 1, 0, 0)`, matching
  `expMod2_fgTame`.  This is the exponent-vector input the `Γ_A` chain-map assembly consumes
  (cf. the `have hvec` inside `GQ2.FoxH.mixedB_wildRow`, `Traced.lean`); its hypothesis
  `(e : ZMod 2) = 1` is discharged at the wild-row exponent `e = omega2Exp (exponent (H(A)⋊C))` by
  the existing `GQ2.FoxH.omega2Exp_exponent_heis_cast`.  Ticket R25's `r_R` wild row of Prop 5.8
  feeds on this lemma;
* **`expMod2_tame_add_wildValueExpR_odd`** — the note's "Their sum is zero": at odd `e` the tame
  and Roe-wild ε-vectors are equal, so `ε(r_t) + ε(r_R) = 0` (the endpoint condition (40) for the
  `(1,1)` trace);
* **stress test** `expMod2_wildValueExpR_three` — the vector evaluated at `e = 3` (odd) by `decide`
  directly from the free word, pinning the `−3`, the inverted first factor, and the vanishing of
  `x₁²`/`cR`.
-/

namespace GQ2

namespace FoxH

/-- **The Roe wild word's mod-2 exponent vector is `(0, e, e+1, 0)`** in basis `(σ, τ, x₀, x₁)`
(the Roe twin of `expMod2_wildValueExp`, whose vector is `(0, e, 0, e+1)`) — Roe note Lemma 5.1
⟦lem:stokes⟧.  Because `expMod2` lands in the abelian `Multiplicative (ZMod 2)`, conjugations are
exponent-invariant and commutators vanish: in `wildValueExpR freeMarking e` the inverted first
factor `(x₀^σ)⁻¹` contributes one `x₀`, and `(x₀⁻³τ)^e` contributes `e·(−3) ≡ e` `x₀`'s and `e`
`τ`'s, while `x₁²` (even) and the commutator `cR` have zero vector.  Summing the two `x₀`-terms
gives `1 + e = e + 1`; only `τ` and `x₀` survive.  At the odd representatives of `ω₂` this is
`(0, 1, 0, 0)` (`expMod2_wildValueExpR_odd`), matching the tame vector `expMod2_fgTame` — so
condition (40) holds for the `(1,1)` trace and the Stokes corrections of Lemma 5.7 cancel in the
`r_R` row of Prop 5.8 (ticket R25). -/
theorem expMod2_wildValueExpR (e : ℕ) :
    (fun i => Multiplicative.toAdd (expMod2 i (wildValueExpR freeMarking e)))
      = ![0, (e : ZMod 2), (e : ZMod 2) + 1, 0] := by
  have hconj : ∀ (k : Fin 4) (a b : FreeGroup (Fin 4)), expMod2 k (conjP a b) = expMod2 k a := by
    intro k a b; simp only [conjP, map_mul, map_inv]; rw [mul_right_comm, inv_mul_cancel, one_mul]
  have hcomm : ∀ (k : Fin 4) (a b : FreeGroup (Fin 4)), expMod2 k (commP a b) = 1 := by
    intro k a b; simp only [commP, map_mul, map_inv]
    rw [mul_right_comm (expMod2 k a)⁻¹ (expMod2 k b)⁻¹ (expMod2 k a), inv_mul_cancel, one_mul,
      inv_mul_cancel]
  funext i
  simp only [wildValueExpR, freeMarking, map_mul, map_inv, map_pow, hconj, hcomm]
  fin_cases i <;>
    (simp only [expMod2, FreeGroup.lift_apply_of, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd,
      toAdd_one, Fin.isValue]; ring_nf; generalize (e : ZMod 2) = x; revert x; decide)

/-- **Odd-exponent collapse to `(0, 1, 0, 0)`** — Roe note Lemma 5.1 ⟦lem:stokes⟧: at any odd
exponent `e` (`(e : ZMod 2) = 1`; every finite integer representative of `ω₂` is odd) the Roe wild
word's mod-2 exponent vector is `(0, 1, 0, 0)`, matching the tame vector `expMod2_fgTame`.  This is
the `r_R`-side twin of the exponent-vector input the `Γ_A` chain-map assembly consumes (the
`have hvec` local inside `GQ2.FoxH.mixedB_wildRow`/`mixedB_wildRow_right`).  Ticket R25 discharges
the hypothesis at the wild-row exponent `e = omega2Exp (Monoid.exponent (HeisLift A C))` via
`omega2Exp_exponent_heis_cast`. -/
theorem expMod2_wildValueExpR_odd {e : ℕ} (he : (e : ZMod 2) = 1) :
    (fun i => Multiplicative.toAdd (expMod2 i (wildValueExpR freeMarking e))) = ![0, 1, 0, 0] := by
  rw [expMod2_wildValueExpR]
  funext i
  fin_cases i <;> simp only [he] <;> decide

/-- **The tame and Roe-wild ε-vectors sum to zero** — Roe note Lemma 5.1 ⟦lem:stokes⟧ ("Their sum
is zero"): at odd `e` both `ε(r_t)` (`expMod2_fgTame`) and `ε(r_R)` (`expMod2_wildValueExpR_odd`)
equal `(0, 1, 0, 0)`, so their sum vanishes in the char-2 target.  This is the endpoint condition
(40) making the trace `(u_t, u_w) ↦ u_t + u_w` valid for the `(1,1)` pairing: the two Stokes
ε-corrections `y_τ(τ·a)` of the tame and wild rows cancel in the `r_R` Prop 5.8 (ticket R25). -/
theorem expMod2_tame_add_wildValueExpR_odd {e : ℕ} (he : (e : ZMod 2) = 1) :
    (fun i => Multiplicative.toAdd (expMod2 i fgTame)
              + Multiplicative.toAdd (expMod2 i (wildValueExpR freeMarking e))) = 0 := by
  funext i
  have h1 : Multiplicative.toAdd (expMod2 i fgTame) = ![0, 1, 0, 0] i := congrFun expMod2_fgTame i
  have h2 : Multiplicative.toAdd (expMod2 i (wildValueExpR freeMarking e)) = ![0, 1, 0, 0] i :=
    congrFun (expMod2_wildValueExpR_odd he) i
  rw [h1, h2, Pi.zero_apply, CharTwo.add_self_eq_zero]

/-- **Stress test (concrete evaluation, `e = 3`).**  The Roe wild word's mod-2 exponent vector at
the odd exponent `3`, computed by `decide` directly from the free word: `(0, 1, 0, 0)`.  Pins the
inverted first factor and the `−3` (the `x₀`-terms `1 + 3·(−3) ≡ 1 + 1 = 0` cancel), the odd
`τ`-exponent `3 ≡ 1`, and the vanishing of `x₁²` and the commutator `cR` — catching a transcription
slip in `wildValueExpR` independently of `expMod2_wildValueExpR`. -/
theorem expMod2_wildValueExpR_three :
    (fun i => Multiplicative.toAdd (expMod2 i (wildValueExpR freeMarking 3))) = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
    (simp only [wildValueExpR, freeMarking, conjP, commP, expMod2, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, Fin.isValue]
     decide)

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 5.1 = ⟦lem:stokes⟧
  * eq. (1.2) `r_R` = ⟦eq:relators⟧  (transcribed in `GQ2.wildValueExpR`, `GQ2/Roe/Words.lean`)
  * Lemma 5.7 / Prop 5.8 endpoint = the finite-word Stokes formula fed by these vectors
-/
