/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Words
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

@[expose] public section

/-!
# Roe candidate: small-group numerical cross-check vs the June LMFDB-verified counts  (R5)

End-to-end transcription validation of the Roe wild relator `r_R` (`GQ2/Roe/Words.lean`, R1)
*before* the deep proofs (R7–R32) consume it.  The candidate presentation

  `Γ_R = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², r_R⟩`,   `r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}]`

was verified numerically against the LMFDB 2-adic-field database in June 2026 (archive
`~/claude/q2_galois_presentation`, `README.md`/`PROOF.md`/`data/`).  This file re-checks that the
**Lean transcription** of `r_R` reproduces the June surjection counts on small groups, catching any
R1 transcription slip (the `Γ_A` campaign's `h₀` erratum, `docs/erratum-h0-transcription.md`, was
exactly such a slip that a cross-check like this would have caught).

## Semantics

By the surjection-count form of the note's Definition 1.1 (⟦def:GammaR⟧; ticket R4's
`prop_2_3_R`), for a finite group `G`

  `admissibleCountR G = |Sur(Γ_R, G)|`  ( = #{ (σ,τ,x₀,x₁) generating `G`, tame, `r_R = 1`,
                                              `⟨⟨x₀,x₁⟩⟩` a 2-group } ).

The June archive counts the **opposite-handed** problem (`engine.py`/`verify_winner.py` use
`g^h = h g h⁻¹`, tame `s t s⁻¹ = t²`, wild via `conj(a,s) = s a s⁻¹`), whereas `GQ2.Roe.Words`
uses the paper's `conjP x g = g⁻¹ x g`.  The relabelling `σ ↦ σ⁻¹` is a bijection
archive-admissible ↔ Lean-admissible fixing `τ, x₀, x₁`, `Generates` and `Pro2Core`, so **the two
counts are identical**.

## Cross-check table  (VERDICT: MATCH on all five groups)

```
  G              admissibleCountR G  =  June |Sur(Γ_R, G)|   archive source
  ───────────────────────────────────────────────────────────────────────────────────────
  C₂                    7                     7              lmfdb_counts 2.2/2T1  (|Aut|·#fields = 1·7)
  C₄                   24                    24              2.4/4T1 (2·12);  engine.py recount
  C₂×C₂  (V₄)          42                    42              2.4/4T2 (6·7);   engine.py recount
  DihedralGroup 4 (D₄) 144                   144             final_validation.log 8T4;  engine.py recount
  QuaternionGroup 2(Q₈)144                   144             final_validation.log 8T5;  engine.py recount
```

The counts themselves are **not** `decide`-checked in Lean: `admissibleCountR` embeds the
noncomputable `powOmega2` (via `orderOf`) and the predicates `Generates` (`Subgroup.closure = ⊤`),
`Pro2Core` (`IsPGroup 2 (normalClosure …)`) carry no `Decidable` instances, so `Nat.card {…}` does
not reduce.  Instead the count is cross-checked *numerically* by

* `scripts/roe_sanity_counts.py` — an independent pure-Python brute force over `G⁴` using **exactly
  the Lean conventions** of `GQ2/Roe/Words.lean`, which also recomputes in the archive convention and
  asserts the two agree; and
* the archive's own `scripts/engine.py` + `verify_winner.py` (Sage), whose June recount for these
  five groups returns `7, 24, 42, 144, 144` — a four-way agreement (both brute forces, the June Sage
  engine, and `final_validation.log`).

What Lean pins here, machine-checked, are concrete evaluations of the transcribed `r_R` in each
group via R1's proven template (`wildValueExpR` + `wildValueExpR_eq_wildValueR_of_dvd` +
`omega2Exp_eight` + `decide`) — the anti-transcription-bug content.  Because R1's stress tests all
live in the *abelian* `Multiplicative (ZMod 8)` (where `conjP` collapses and `cR = 1`), the
nonabelian `DihedralGroup 4`/`DihedralGroup 8` pins below add genuinely new coverage: a nontrivial
conjugation `x₀^σ ≠ x₀`, noncommutative factor order, and — in `DihedralGroup 8` — a nontrivial
anomalous commutator `cR = [x₁, x₁^{σ₂}] = r 4 ≠ 1` (the `p = 2` term that replaces the NSW bracket;
it collapses in the "small" 2-groups `D₄`, `Q₈`, whose subgroups are all `⟨x₁⟩`-commuting).
-/

namespace GQ2

open DihedralGroup

/-! ### C₂ = `Multiplicative (ZMod 2)`  (June `|Sur(Γ_R, C₂)| = 7`)

Here `r_R` collapses to `τ` (every factor but `τ` cancels in a group of exponent 2), giving a
discriminating pair: the wild relation **fails** at `τ = 1` and **holds** at `τ = 0`. -/

/-- `(σ,τ,x₀,x₁) = (1,1,1,1)` in `Multiplicative (ZMod 2)` — a *non*-solution of `r_R = 1`. -/
def c2MarkingR : Marking (Multiplicative (ZMod 2)) :=
  ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩

/-- `(σ,τ,x₀,x₁) = (1,0,1,1)` in `Multiplicative (ZMod 2)` — a solution of `r_R = 1`
(`WildRelR` holds, `wildRelR_c2wit`). -/
def c2WitR : Marking (Multiplicative (ZMod 2)) :=
  ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩

theorem wildValueExpR_c2 : wildValueExpR c2MarkingR 1 = Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

theorem wildValueExpR_c2wit : wildValueExpR c2WitR 1 = Multiplicative.ofAdd (0 : ZMod 2) := by
  decide

/-- Genuine `wildValueR` (the noncomputable `ω₂`-word) at `c2WitR`, via
`wildValueExpR_eq_wildValueR_of_dvd` + `omega2Exp_eight` — exactly R1's `wildValueR_zmod8` route. -/
theorem wildValueR_c2wit : c2WitR.wildValueR = Multiplicative.ofAdd (0 : ZMod 2) := by
  have h := wildValueExpR_eq_wildValueR_of_dvd (N := 8) (by norm_num) c2WitR
    (orderOf_dvd_iff_pow_eq_one.mpr (by decide)) (orderOf_dvd_iff_pow_eq_one.mpr (by decide))
  rw [h, omega2Exp_eight]
  exact wildValueExpR_c2wit

/-- **A concrete solution of the Roe wild relation.**  `c2WitR` satisfies `WildRelR` — the wild
relation is genuinely satisfiable (not vacuously false), and `c2WitR` is in fact `R`-admissible
(it generates `C₂` via `σ`, and `⟨⟨x₀,x₁⟩⟩ = C₂` is a 2-group). -/
theorem wildRelR_c2wit : c2WitR.WildRelR := by
  show c2WitR.wildValueR = 1
  rw [wildValueR_c2wit]; rfl

/-! ### C₄ = `Multiplicative (ZMod 4)`  (June `|Sur(Γ_R, C₄)| = 24`)

The informative abelian pin: `−3 ≡ 1 (mod 4)` makes the `x₀`-exponent `−1 + (−3) = −4 ≡ 0`, and
`x₁²` survives, so `r_R` evaluates to `τ + 2·x₁`; at `(σ,τ,x₀,x₁) = (1,0,1,1)` this is `2`. -/

/-- `(σ,τ,x₀,x₁) = (1,0,1,1)` in `Multiplicative (ZMod 4)`. -/
def c4MarkingR : Marking (Multiplicative (ZMod 4)) :=
  ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩

theorem wildValueExpR_c4 : wildValueExpR c4MarkingR 1 = Multiplicative.ofAdd (2 : ZMod 4) := by
  decide

theorem wildValueR_c4 : c4MarkingR.wildValueR = Multiplicative.ofAdd (2 : ZMod 4) := by
  have h := wildValueExpR_eq_wildValueR_of_dvd (N := 8) (by norm_num) c4MarkingR
    (orderOf_dvd_iff_pow_eq_one.mpr (by decide)) (orderOf_dvd_iff_pow_eq_one.mpr (by decide))
  rw [h, omega2Exp_eight]
  exact wildValueExpR_c4

/-! ### C₂×C₂ = `Multiplicative (ZMod 2 × ZMod 2)`  (June `|Sur(Γ_R, V₄)| = 42`) -/

/-- `(σ,τ,x₀,x₁) = ((1,0),(1,1),(0,1),(1,0))` in `Multiplicative (ZMod 2 × ZMod 2)`; `r_R`
collapses to `τ = (1,1)`. -/
def v4MarkingR : Marking (Multiplicative (ZMod 2 × ZMod 2)) :=
  ⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 1),
   Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 0)⟩

theorem wildValueExpR_v4 :
    wildValueExpR v4MarkingR 1 = Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2) := by decide

/-! ### DihedralGroup 4 = D₄, order 8  (June `|Sur(Γ_R, D₄)| = 144`)

First nonabelian pin.  At `(σ,τ,x₀,x₁) = (r 1, r 0, sr 0, sr 1)` the conjugation is genuinely
nontrivial (`x₀^σ = (r 1)⁻¹ (sr 0)(r 1) = sr 2 ≠ sr 0`) and the four factors multiply
noncommutatively; the anomalous commutator still collapses (`cR = 1` in `D₄`). `r_R` evaluates to
`r 2`. -/

/-- `(σ,τ,x₀,x₁) = (r 1, r 0, sr 0, sr 1)` in `DihedralGroup 4`. -/
def d4MarkingR : Marking (DihedralGroup 4) := ⟨r 1, r 0, sr 0, sr 1⟩

theorem wildValueExpR_d4 : wildValueExpR d4MarkingR 1 = r 2 := by decide

theorem wildValueR_d4 : d4MarkingR.wildValueR = r 2 := by
  have h := wildValueExpR_eq_wildValueR_of_dvd (N := 8) (by norm_num) d4MarkingR
    (orderOf_dvd_iff_pow_eq_one.mpr (by decide)) (orderOf_dvd_iff_pow_eq_one.mpr (by decide))
  rw [h, omega2Exp_eight]
  exact wildValueExpR_d4

/-! ### DihedralGroup 8, order 16  (the anomalous commutator, end-to-end)

`D₄`/`Q₈` are too small to exercise `cR = [x₁, x₁^{σ₂}]` (every conjugate of `x₁` commutes with
`x₁`).  In the order-16 group `DihedralGroup 8` it is nontrivial: at
`(σ,τ,x₀,x₁) = (r 1, r 0, sr 0, sr 0)`, `x₁^{σ₂} = (r 1)⁻¹ (sr 0)(r 1) = sr 2`, so
`cR = [sr 0, sr 2] = r 4 ≠ 1`.  `r_R` evaluates to `r 2`. -/

/-- `(σ,τ,x₀,x₁) = (r 1, r 0, sr 0, sr 0)` in `DihedralGroup 8`. -/
def d8MarkingR : Marking (DihedralGroup 8) := ⟨r 1, r 0, sr 0, sr 0⟩

/-- **The anomalous commutator is nontrivial.**  In the faithful finite-exponent form
(`σ₂ = σ^1`, exact because `DihedralGroup 8` is a 2-group so `ω₂ = id`), the Roe-specific subword
`cR = [x₁, x₁^{σ₂}]` of `d8MarkingR` equals `r 4 ≠ 1`.  This is the transcription's realization of
the candidate's `p = 2` anomaly — the `(x₁, x₁^{σ₂})` term that replaces the NSW/Diekert bracket
undefined at `q = 2` (README, `PROOF.md`). -/
theorem cRExp_d8_ne_one :
    commP d8MarkingR.x₁ (conjP d8MarkingR.x₁ (d8MarkingR.σ ^ 1)) = r 4 := by decide

theorem wildValueExpR_d8 : wildValueExpR d8MarkingR 1 = r 2 := by decide

theorem wildValueR_d8 : d8MarkingR.wildValueR = r 2 := by
  have h := wildValueExpR_eq_wildValueR_of_dvd (N := 8) (by norm_num) d8MarkingR
    (orderOf_dvd_iff_pow_eq_one.mpr (by decide)) (orderOf_dvd_iff_pow_eq_one.mpr (by decide))
  rw [h, omega2Exp_eight]
  exact wildValueExpR_d8

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Definition 1.1 = ⟦def:GammaR⟧  (surjection-count semantics, R4 `prop_2_3_R`)
  * eq. (1.2)      = ⟦eq:relators⟧  (the wild relator `r_R` pinned here)

June archive: `~/claude/q2_galois_presentation` (README.md, PROOF.md, data/lmfdb_counts.json,
data/final_validation.log, scripts/engine.py, scripts/verify_winner.py).  Independent recount:
`scripts/roe_sanity_counts.py`.
-/
