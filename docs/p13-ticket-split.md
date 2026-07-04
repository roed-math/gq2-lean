# P-13 decomposition — parallelizable sub-tickets for §5 proofs

**Date**: 2026-07-04 · **Owner of split**: P-13 (Opus).  P-13 (§5 proofs) is decomposed into
independent sub-tickets so the remaining work can run in parallel.  The split-case machinery
(P-13a) is now a **proven, shared foundation** that the ramified and assembly tickets consume.

All code is in [`GQ2/FoxHeisenberg.lean`](../GQ2/FoxHeisenberg.lean).  Every sub-ticket keeps the
project rules: no new `axiom`s except where the **Ax** column says so; new theorems `#print axioms`
⊆ std-3 ∪ the ticket's Ax column.  Claim a sub-ticket by marking its board row ◐ before starting.

## Dependency graph

```
P-13a  engines + split §5.13         ══ DONE ══╗
  (wild-Fox 5.4/5.5, Stokes 5.6–5.10,          ║
   Hessian toolkit 5.14, lemma_5_13_split,     ║
   lemma_5_13_pairing_split)                   ║
                                               ╠══► P-13b  ramified normal form ─┐
                                               ╚══► P-13c  ramified Hessian ──────┤
                                                                                 ├─► P-13f  prop_5_15
P-13d  tameness rep-theory  ─────────────────────────────────────────────────────┤    (duality
P-13e  dévissage / lemma_5_11 ────────────────────────────────────────────────────┘     assembly)
                                                                                        │
P-13g  local duality / prop_5_16  ── independent (invokes existing axioms B6, B7) ────────┘
                                                                        (cor_5_17_card wiring
                                                                         already proved; consumes f + g)
```

**Runnable in parallel right now:** P-13b, P-13c, P-13e, P-13g.
**Done:** P-13a, **P-13d** (`GQ2/TameSimple.lean`, all std-3).
**Blocked until its deps land:** P-13f (needs b, c, e; d is in).

## What is already proven (P-13a — DONE)

The shared foundation, all std-3, committed on branch `cmdline-url-and-validation`:

* **Wild-Fox engine** (Lemma 5.4/5.5): `WordLift.pow_u` (norm), `powOmega2_u_of_trivial` /
  `powOmega2_g_smul_of_trivial` (norm collapse under trivial inertia), the `.u`-additivity toolkit
  on the trivially-based subgroup (`mul_u_of_trivial`, `conjP_u_of_trivial`, `commP_u_of_trivial`,
  base-closures), `liftMarking_sigma2_g` (σ₂ exponent reconciliation, Lemma 5.1).
* **Stokes / chain map** (5.6/5.7/5.8/5.10): the traced finite-word Stokes identities, `prop_5_8`
  both rows, `lemma_5_6`, class-two identity `classTwoCore`/`classTwoIdentity` (Lemma 5.2).
* **Split wild row** `liftMarking_wildValue_u = x₁ + (1+S⁻¹)·x₃`; `lemma_5_13_split` (Z¹/B¹).
* **Mixed-Hessian toolkit** (Lemma 5.14): `HeisLift` trivially-based central toolkit
  (`mul_z_of_trivial` cocycle, `commP_z_of_trivial`, `conjP_{a,l,z}_of_gslice`), `agHom`/`lgHom`
  naturality (`heisMarking_*_a/_l/_g_eq`), the base-triviality transfers, `heisMarking_h0_z`
  (`h₀ ↦ λ(c)`), `heisMarking_wildValue_z`; **`lemma_5_13_pairing_split`** (`B(c,λ) = λ(c)`).
* `lemma_5_12` (simple char-2 modules are tame) — proved, reused by P-13d.

## Sub-tickets

### P-13b — ramified normal form (`lemma_5_13_ramified`)
**Deps: P-13a.**  The `V^T = 0` (ramified) inertia case of Lemma 5.13.  Here τ acts *non*-trivially,
so `1 + T` is invertible and the norm projector `P = 0`; the wild row collapses to `L_w = S⁻¹·d`,
forcing `d = 0`.  Then subtract the coboundary of `v = (T−1)⁻¹b` to kill `b`, and the tame row
`S⁻¹(1+T)a = 0` forces `a = 0`; uniqueness from `(T−1)v = 0 ⇒ v = 0`.  Reuses the wild-Fox engine
but needs the **`P = 0` ledger** (the ω₂-norm of a fixed-point-free T vanishes) — the ramified
analogue of `powOmega2_u_of_trivial`, which is new.  Model O.  Ax: —.

### P-13c — ramified mixed Hessian (`lemma_5_13_pairing_ramified`)
**Deps: P-13a.**  The ramified degree-one pairing `B(c,λ) = λ((1 + U + U⁻¹)c)`, `U = σ₂`.  Two
central contributions (Lemma 5.14): `h₀ ↦ λ(c)` via the **same-image** branch of Lemma 5.2(i)
(`Dd₀ = Dx₀ = c` since `P+1 = 1`), and `[d₀,z₀] ↦ λ(Uc) + λ(U⁻¹c)` via the commutator symplectic
`commP_z_of_trivial` with `Dd₀ = c`, `Dz₀ = U⁻¹c`.  Unlike the split case `g₀ = σ₂²` is **not**
g-slice (U acts nontrivially), so `φ = conj by g₀` no longer preserves the Heisenberg coordinates —
the new work is tracking the `U`-action through the peel.  Reuses the whole Hessian toolkit
(`commP_z_of_trivial`, naturality).  Model O.  Ax: —.

### P-13d — tameness rep-theory (supplies `hU`/`hVS` to the assembly) — ☑ DONE
**Deps: `lemma_5_12` (done); `t.Generates`.  File: `GQ2/TameSimple.lean` (new leaf, all std-3).**
The split lemmas take σ-tameness as explicit hypotheses (`hU : σ₂ acts trivially`,
`hVS : V^S = 0`); this ticket **derives** them, so `prop_5_15` can supply them per simple factor.

**Realized approach — no finite-field theory needed.**  The originally-planned route (factor through
`𝔽₂[⟨σ⟩]`, a finite field, and use unit-order) is replaced by a direct central-fixed-point argument,
the exact analogue of `lemma_5_12` with *centrality* in place of *normality*:

* `actionCommutant g` / `actionCentre` — the sub**group**s of `C` commuting (in the action) with a
  fixed `g •`, resp. with the whole `C`-action.
* **`central_pow2_smul_trivial`** — a 2-power-order element `g` whose action is central acts
  trivially on a simple char-2 module.  Its fixed space `V^{⟨g⟩}` is `C`-stable (centrality) and
  nonzero (`IsPGroup.card_modEq_card_fixedPoints`, char 2), so simplicity ⟹ `= ⊤`.  Mirrors
  `lemma_5_12`.
* **`orderOf_powOmega2_dvd_two_pow`** / **`isPGroup_zpowers_powOmega2`** — `σ₂ = σ^{ω₂}` has 2-power
  order: the odd part of `orderOf σ` divides `ω₂` (`oddPart_dvd_omega2Exp`), so
  `(σ^{ω₂})^{2^{v₂}} = 1`, hence `⟨σ₂⟩` is a 2-group.
* **`central_of_commutes_sigma`** — with `τ, x₀, x₁` trivial (`htau` + `wild_acts_trivially`) and
  `t.Generates`, an element commuting with `σ`'s action is central: the commutant contains all four
  generators, so is `⊤`.  `σ` (trivially) and `σ₂ = σ^k` (as a power) both qualify.
* **`sigma2_smul_trivial`** = `hU`: `σ₂` central + 2-power order ⟹ trivial via
  `central_pow2_smul_trivial`.
* **`fixedPoints_sigma_eq_zero`** = `hVS`: `V^σ` is a `C`-submodule (`σ` central), so `⊥`/`⊤`; the
  nontriviality `hσ : ∃ v, σ•v ≠ v` kills `⊤`.  (`hσ` is the case selector: split-tame + `σ` fixed
  everywhere ⟹ trivial module, handled by P-13f(i); `σ` nontrivial ⟹ this lemma.)

Resolves the "simple ⟹ tame at σ" input flagged in `docs/p13-normal-form-hypothesis-gap.md` §7.
Model O.  Ax: —.  **Note for P-13b (ramified):** the analogous `hTodd` (T = τ odd-order on `V`) is
*not* central in general, so `central_pow2_smul_trivial` does not directly apply; that case needs its
own argument.

### P-13e — dévissage (`lemma_5_11`)
**Deps: none (independent, homological).**  Two-out-of-three for `IsSelfDual` along a short exact
sequence of elementary `𝔽₂[C]`-modules.  Proof device: the mapping cone `K(A)` of display (49) and
its degreewise SES (50), whose long exact cohomology sequence gives acyclicity at each extension
step (card clauses by Euler characteristic; pairing perfection by the five-lemma).  Needs
long-exact-sequence / snake infrastructure for the word-complex functors `Z1w`/`H1w`/`H2w` — not yet
in the repo, design-sensitive.  Model **F**.  Ax: —.

### P-13f — duality assembly (`prop_5_15`) — ◐ part (i) cards done
**Deps: P-13b, P-13c, P-13d, P-13e** (+ the done split lemmas).  Assembles the chain-map
quasi-isomorphism for every finite elementary module.  Three parts: (i) the **trivial module**
`A = 𝔽₂` — all lower actions trivial, `d¹ = (b,b)`, the explicit 3×3 Gram matrix / scalar
cup–Bockstein table (25) [self-contained, could be a leaf]; (ii) **nontrivial simple modules** via
Lemma 5.12 + all four Lemma 5.13 cases, using P-13d to supply the tameness hypotheses; (iii)
**general elementary modules** via P-13e dévissage along a composition series.  The last ticket to
close.  Model O.  Ax: —.

**Part (i) progress** (`GQ2/TrivialSelfDual.lean`, all std-3): the **card clauses** of
`IsSelfDual t A` are proven for any trivial `C`-action on a finite elementary-2 module `A`.  On the
trivial module `d⁰ = 0` and `d¹ x = (x₁, x₁)` (`d1_of_trivial`, from `d1Fun_tame` + the split wild
row in char 2), giving `Z¹ = {x | x₁=0} ≅ A³`, `H² = (A×A)/Δ ≅ A`; combined with the dual-cardinality
`#(A^∨)^C = #A^∨ = #A` (`card_fixedPts_elemDual_trivial`, via `AddCommGroup.zmodModule` +
`Basis.linearEquiv_dual`), this yields `#H²w = #A` and `#Z¹w = (#A)³` — clauses 1 and 2.  The
`trivialSelfDual : IsSelfDual t A` theorem discharges those two and `sorry`s **only** clause 3.
**Remaining (the substance):** the degree-one pairing = table (25).  Needs (a) `mixedB` on
general-offset cocycles — the repo's `.z`-coordinate toolkit (`heisMarking_*_z`) is currently proven
only for x₀-supported reps (split case); (b) `mixedB` bilinearity, to assemble the `3×3` Gram matrix
from basis pairs; (c) nonsingularity ⇒ perfection via `dualEval`.

### P-13g — local lifting duality (`prop_5_16`)
**Deps: none — runnable now.**  Local Tate duality with trivial mod-2 cyclotomic twist + local
Euler–Poincaré for `Q₂`.  **No axiom decision is needed**: B6 (`GQ2.tateDuality`,
`Foundations/Axioms.lean:271`) and B7 (`Foundations.absGalQ2_localEulerCharacteristic`,
`Foundations/Axioms.lean:171`) are *already* declared axioms in the frozen census of 12; the **Ax**
column is the budget permitting this leaf to invoke them.  Proof work: the card clauses from B7
(finite discrete `𝔽₂[C]`-module), and `#H²(𝔽₂)=2` + the three bijective cups from **B6 at `n=2`**
(`μ₂ ≅ 𝔽₂`), matched to the T-14 `dualEval` cup framework.  Only if the current B6/B7 *shape* turns
out insufficient mid-proof would that escalate to an explicit axiom-amendment decision (as B9/B11
were during P-15) — not currently expected.  Independent of b–f.  Note: the proved wiring
`cor_5_17_card` consumes both `prop_5_15` (P-13f) and `prop_5_16` (P-13g).  Model O.  Ax: **B6, B7**.

## Board rows (spliced into `docs/tickets.md`)

| ID | Title | Diff | Model | Deps | Ax | Status |
|---|---|---|---|---|---|---|
| P-13a | B: §5 wild-Fox + mixed-Hessian engines & split §5.13 | ⭐⭐⭐ | O | P-12 | — | ☑ 2026-07-04 |
| P-13b | B: §5.13 ramified normal form (`lemma_5_13_ramified`) | ⭐⭐⭐ | O | P-13a | — | ☐ |
| P-13c | B: §5.14 ramified mixed Hessian (`lemma_5_13_pairing_ramified`) | ⭐⭐⭐ | O | P-13a | — | ☐ |
| P-13d | B: §5 tameness rep-theory (central σ₂ ⇒ σ₂=1; V^σ simple ⇒ V^S=0) | ⭐⭐⭐ | O | 5.12 (done) | — | ☑ 2026-07-04 (Opus; `GQ2/TameSimple.lean`, all std-3) |
| P-13e | B: §5.11 dévissage (mapping-cone 2-of-3 for `IsSelfDual`) | ⭐⭐⭐ | F | — | — | ☐ |
| P-13f | B: §5.15 duality assembly (`prop_5_15`) | ⭐⭐⭐ | O | P-13b, P-13c, P-13d, P-13e | — | ☐ |
| P-13g | B: §5.16 local lifting duality (`prop_5_16`; invokes existing B6/B7) | ⭐⭐⭐ | O | — | B6, B7 | ☐ |
