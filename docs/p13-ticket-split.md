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

**Runnable in parallel right now:** P-13b, P-13c, P-13d, P-13e, P-13g (five agents).
**Blocked until its deps land:** P-13f (needs b, c, d, e).

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

### P-13d — tameness rep-theory (supplies `hU`/`hVS` to the assembly)
**Deps: `lemma_5_12` (done, in P-13a's file); needs `t.Generates`.**  Currently the split lemmas
take σ-tameness as explicit hypotheses (`hU : σ₂ acts trivially`, `hVS : V^S = 0`); this ticket
**derives** them, so `prop_5_15` can supply them per simple factor.  Argument: with `τ, x₀, x₁`
acting trivially (Pro2Core + Lemma 5.12) and `t.Generates`, the `C`-action on a simple `V` factors
through the cyclic `⟨σ̄⟩`, so `V` is a simple `𝔽₂[⟨σ⟩] = 𝔽₂[x]/(irreducible)`-module — a finite
field — on which `σ` acts as a unit of odd order (`2^d − 1`), whence `σ₂ = σ^{ω₂} = 1` and
`V^S = V^C = 0`.  Needs Mathlib's simple-module-over-PID / finite-field-unit-order theory.  This is
the "simple ⟹ tame at σ" input flagged in `docs/p13-normal-form-hypothesis-gap.md` §7.  Model O.
Ax: —.

### P-13e — dévissage (`lemma_5_11`)
**Deps: none (independent, homological).**  Two-out-of-three for `IsSelfDual` along a short exact
sequence of elementary `𝔽₂[C]`-modules.  Proof device: the mapping cone `K(A)` of display (49) and
its degreewise SES (50), whose long exact cohomology sequence gives acyclicity at each extension
step (card clauses by Euler characteristic; pairing perfection by the five-lemma).  Needs
long-exact-sequence / snake infrastructure for the word-complex functors `Z1w`/`H1w`/`H2w` — not yet
in the repo, design-sensitive.  Model **F**.  Ax: —.

### P-13f — duality assembly (`prop_5_15`)
**Deps: P-13b, P-13c, P-13d, P-13e** (+ the done split lemmas).  Assembles the chain-map
quasi-isomorphism for every finite elementary module.  Three parts: (i) the **trivial module**
`A = 𝔽₂` — all lower actions trivial, `d¹ = (b,b)`, the explicit 3×3 Gram matrix / scalar
cup–Bockstein table (25) [self-contained, could be a leaf]; (ii) **nontrivial simple modules** via
Lemma 5.12 + all four Lemma 5.13 cases, using P-13d to supply the tameness hypotheses; (iii)
**general elementary modules** via P-13e dévissage along a composition series.  The last ticket to
close.  Model O.  Ax: —.

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
| P-13d | B: §5 tameness rep-theory (simple-cyclic ⇒ σ₂=1, V^S=0) | ⭐⭐⭐ | O | 5.12 (done) | — | ☐ |
| P-13e | B: §5.11 dévissage (mapping-cone 2-of-3 for `IsSelfDual`) | ⭐⭐⭐ | F | — | — | ☐ |
| P-13f | B: §5.15 duality assembly (`prop_5_15`) | ⭐⭐⭐ | O | P-13b, P-13c, P-13d, P-13e | — | ☐ |
| P-13g | B: §5.16 local lifting duality (`prop_5_16`; invokes existing B6/B7) | ⭐⭐⭐ | O | — | B6, B7 | ☐ |
