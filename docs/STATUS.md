# Status ledger

Live record of every Lean declaration in the repo: **proved**, `sorry` (target stated, proof
deferred), or scaffold. Updated 2026-07-01. Build: Mathlib `v4.31.0`, `lake build` green
(all `sorry`s are intentional and reported as warnings).

## Proved (no `sorry`, no new axioms)

| declaration | file | paper ref | notes |
|---|---|---|---|
| `GQ2.Tame.conj_pow_iterate` | `Tame.lean` | Lemma 3.1 (aux) | `(sⁿ)⁻¹ t sⁿ = t^(2ⁿ)` by induction |
| `GQ2.Tame.tame_odd_order` | `Tame.lean` | **Lemma 3.1, first assertion** | in a tame quotient `t` has odd order — full proof |
| `GQ2.FiniteGroup.oddOrder_twoQuotient_split` | `FiniteGroupLemmas.lean` | **Lemma 9.2 core** | odd normal subgroup with 2-group quotient splits (Schur–Zassenhaus) |
| `GQ2.omega2Exp`, `GQ2.powOmega2`, `conjP`, `commP` | `Words.lean` | (1)–(3), App. A–B | definitions of `ω₂`-power, conjugation, commutator |
| `GQ2.Marking.*` (all auxiliary words + predicates) | `Words.lean` | (1)–(3), §2 | `sigma2,u,d0,z0,c0,g0,dg,hc,h0`, `TameRel/WildRel/Generates/Pro2Core/Admissible` |
| `GQ2.admissibleCount` | `Words.lean` | Prop. 2.3 (RHS of eq. 154) | the finite count `N(G)` |
| `GQ2.main_presentation` (**modulo** its two `sorry` inputs) | `Statement.lean` | **Theorem 1.2 wiring** | the top-level logic *is checked*: `reconstruction` + `main_surjection_count` ⟹ the iso |

## Stated with `sorry` (faithful target, proof deferred)

| declaration | file | paper ref | blocker (see foundations-audit.md) |
|---|---|---|---|
| `GQ2.main_surjection_count` | `Statement.lean` | **Theorem 1.2, eq. (154)** | the entire §§3–9 tower (Demushkin, local CFT, cup products, Gauss sums) |
| `GQ2.reconstruction` | `Reconstruction.lean` | **Lemma 2.5** | Hopfian property of top. f.g. profinite groups, packaged over `ProfiniteGrp` (grade F′) |
| `GQ2.FiniteGroup.coprime_fiber_product` | `FiniteGroupLemmas.lean` | Lemma 9.1 | Goursat-style argument (grade F — genuinely reachable next) |
| `GQ2.Tame.tame_semidirect` | `Tame.lean` | Lemma 3.1 (structure) | semidirect recognition (grade F/F′) |
| `GQ2.Tame.tame_normal_two_subgroup_central` | `Tame.lean` | Lemma 3.1 (last) | centrality of normal 2-subgroups (grade F) |

## Not yet stated (missing foundations — would need axioms/opaque stubs)

| object | why deferred |
|---|---|
| the literal presented profinite group `Γ_A` | needs `FreeProfiniteGroup (Fin 4)` + profinite presentations (absent from Mathlib & PRs) |
| `ℤ̂`, `ω₂` as a genuine profinite exponent | needs `ZHat` (absent). On finite quotients `GQ2.powOmega2` already suffices. |

## Next reachable targets (in priority order)

1. `coprime_fiber_product` (Lemma 9.1) — pure finite group theory, Goursat/order-counting.
2. `tame_normal_two_subgroup_central` (Lemma 3.1 last) — `[N, I] ≤ N ∩ I = 1` centralizing argument.
3. `tame_semidirect` (Lemma 3.1 structure) — assemble from `tame_odd_order` + a complement.
4. `reconstruction` (Lemma 2.5) — the big F′ item; build the profinite-Hopfian lemma on `ProfiniteGrp`.
5. A **computable** `powOmega2` variant + `#eval` cross-check of the relator against App. B.
