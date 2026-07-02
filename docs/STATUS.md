# Status ledger

Live record of every Lean declaration in the repo: **proved**, `sorry` (target stated, proof
deferred), or scaffold. Updated 2026-07-01. Build: Mathlib `v4.31.0`, `lake build` green
(all `sorry`s are intentional and reported as warnings).

## Proved (no `sorry`, no new axioms)

| declaration | file | paper ref | notes |
|---|---|---|---|
| `GQ2.Tame.conj_pow_iterate` | `Tame.lean` | Lemma 3.1 (aux) | `(sⁿ)⁻¹ t sⁿ = t^(2ⁿ)` by induction |
| `GQ2.Tame.tame_odd_order` | `Tame.lean` | **Lemma 3.1, first assertion** | in a tame quotient `t` has odd order — full proof |
| `GQ2.Tame.zpowers_sq_eq_of_odd` | `Tame.lean` | Lemma 3.1 (aux) | `⟨t²⟩ = ⟨t⟩` for odd-order `t` (squaring is an automorphism) |
| `GQ2.Tame.zpowers_normal_of_tame` | `Tame.lean` | **Lemma 3.1 (normality)** | `⟨t⟩` is normal in `⟨s,t⟩` — full proof (normalizer = ⊤) |
| `GQ2.Tame.tame_semidirect` | `Tame.lean` | **Lemma 3.1 (structure)** | `⟨t⟩` normal odd cyclic, `⟨s⟩` cyclic, `⟨t⟩ ⊔ ⟨s⟩ = ⊤` (the `C_e ⋊ C_n` shape) |
| `GQ2.Tame.tame_zpowers_disjoint` | `Tame.lean` | **Lemma 3.1 (⋊ disjointness)** | `⟨t⟩ ∩ ⟨s⟩ = ⊥` via `sⁿ=1` — full proof; completes the semidirect decomposition |
| `GQ2.Tame.tame_normal_two_subgroup_central` | `Tame.lean` | **Lemma 3.1 (last)** | every normal 2-subgroup is central (`⁅n,g⁆ ∈ N ⊓ ⟨t⟩ = ⊥`). **Lemma 3.1 now fully proved.** |
| `GQ2.FiniteGroup.oddOrder_twoQuotient_split` | `FiniteGroupLemmas.lean` | **Lemma 9.2 core** | odd normal subgroup with 2-group quotient splits (Schur–Zassenhaus) |
| `GQ2.FiniteGroup.coprime_fiber_product` | `FiniteGroupLemmas.lean` | **Lemma 9.1** | coprime-kernel subdirect product is the full fibre product (via Mathlib's Goursat) |
| `GQ2.omega2Exp`, `GQ2.powOmega2`, `conjP`, `commP` | `Words.lean` | (1)–(3), App. A–B | definitions of `ω₂`-power, conjugation, commutator |
| `GQ2.oddPart_dvd_omega2Exp` | `Omega2.lean` | ω₂ spec | odd part of `n` divides `omega2Exp n` (`ω₂ ≡ 0` on odd part) |
| `GQ2.omega2Exp_modEq_one` | `Omega2.lean` | ω₂ spec | `omega2Exp n ≡ 1 (mod 2^{v₂n})` (`ω₂ ≡ 1` on 2-part) — via Euler |
| `GQ2.omega2_appendixB` | `Omega2.lean` | **App. B** | cross-check: paper's `ω₂ = 40491355905 (mod 85667662080)` satisfies both defining congruences |
| `GQ2.Marking.*` (all auxiliary words + predicates) | `Words.lean` | (1)–(3), §2 | `sigma2,u,d0,z0,c0,g0,dg,hc,h0`, `TameRel/WildRel/Generates/Pro2Core/Admissible` |
| `GQ2.admissibleCount` | `Words.lean` | Prop. 2.3 (RHS of eq. 154) | the finite count `N(G)` |
| `GQ2.main_presentation` (**modulo** its two `sorry` inputs) | `Statement.lean` | **Theorem 1.2 wiring** | the top-level logic *is checked*: `reconstruction` + `main_surjection_count` ⟹ the iso |
| `GQ2.FreeProfiniteGroup` + `.of` + `.homEquiv` | `FreeProfinite.lean` | foundation | **free profinite group** (absent from Mathlib) built from `profiniteCompletion ∘ FreeGroup`, with universal property `(FreeProfiniteGroup X ⟶ P) ≃ (X → P)` |
| `GQ2.grpCatHomEquiv` | `FreeProfinite.lean` | foundation | `(GrpCat.of A ⟶ GrpCat.of P) ≃ (A →* P)` |

## Stated with `sorry` (faithful target, proof deferred)

| declaration | file | paper ref | blocker (see foundations-audit.md) |
|---|---|---|---|
| `GQ2.main_surjection_count` | `Statement.lean` | **Theorem 1.2, eq. (154)** | the entire §§3–9 tower (Demushkin, local CFT, cup products, Gauss sums) |
| `GQ2.reconstruction` | `Reconstruction.lean` | **Lemma 2.5** | Hopfian property of top. f.g. profinite groups, packaged over `ProfiniteGrp` (grade F′); Mathlib has no `Hopfian` — must be built |

## Not yet stated (missing foundations — would need axioms/opaque stubs)

| object | why deferred |
|---|---|
| the literal presented profinite group `Γ_A` | needs `FreeProfiniteGroup (Fin 4)` + profinite presentations (absent from Mathlib & PRs) |
| `ℤ̂`, `ω₂` as a genuine profinite exponent | needs `ZHat` (absent). On finite quotients `GQ2.powOmega2` already suffices. |

## Next reachable targets (in priority order)

1. `tame_zpowers_disjoint` (Lemma 3.1 ⋊) — finish the `sⁿ=1` argument (needs ℤ-exponent +
   `orderOf (mk s)` lemmas; proof plan is in the docstring). Completes Lemma 3.1 fully.
2. `tame_normal_two_subgroup_central` (Lemma 3.1 last) — `[N, I] ≤ N ∩ I = 1` centralizing argument.
3. `reconstruction` (Lemma 2.5) — the big F′ item; build the profinite-Hopfian lemma on
   `ProfiniteGrp` (Mathlib has `denseRange`/`lift`/`homEquiv` in `ProfiniteGrp.Completion` to build on).
4. `FreeProfiniteGroup.homEquiv_naturality` — the `of`-compatibility (`homEquiv f x = f (of x)`),
   making the universal property fully usable; then define `Γ_A` as a profinite presentation quotient.
5. `ℤ̂` as a topological **ring** + the `ω₂`-power action on profinite groups — the last foundation
   needed to state Theorem 1.2 literally (currently `main_surjection_count` sidesteps it).
6. A **computable** `powOmega2` variant + `#eval` cross-check of the relator against App. B.

## What this autonomous session added (2026-07-01)

Proved from scratch: `zpowers_sq_eq_of_odd`, `zpowers_normal_of_tame`, `tame_semidirect`
(Lemma 3.1 structure), `coprime_fiber_product` (Lemma 9.1), `oddPart_dvd_omega2Exp`,
`omega2Exp_modEq_one`, `omega2_appendixB` (App. B cross-check), and the **`FreeProfiniteGroup`**
foundation with its universal property. See `docs/SESSION-LOG.md`.
