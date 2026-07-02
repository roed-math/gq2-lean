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
| `GQ2.powOmega2_pow_eq` | `Omega2.lean` | ω₂ well-def | `x^(ω₂ via any multiple of orderOf x) = powOmega2 x` (CRT on the 2-part/odd-part specs) |
| `GQ2.powOmega2_map` | `Omega2.lean` | ω₂ naturality | `f (x^ω₂) = (f x)^ω₂` for every group hom `f` — the functorial characterization of the 2-primary projection |
| `GQ2.powOmega2_prod` | `Omega2.lean` | ω₂ on products | `powOmega2 (a,b) = (powOmega2 a, powOmega2 b)` (coordinatewise; enables Lemma 2.1) |
| `GQ2.Marking.map_*` (word ledger) | `Subdirect.lean` | §2 | each auxiliary word commutes with group homs (`(t.map f).w = f t.w`), via `powOmega2_map` |
| `GQ2.Marking.map_tameRel`, `map_wildRel` | `Subdirect.lean` | §2 | both relations transfer along any group hom |
| `GQ2.Marking.map_admissible` | `Subdirect.lean` | **Lemma 2.2** | admissibility pushes forward along a surjective quotient map (cofinality of admissible quotients) |
| `GQ2.Marking.prod_tameRel`, `prod_wildRel` | `Subdirect.lean` | **Lemma 2.1** | both relations transfer to subdirect products of markings (via the word-ledger + `powOmega2_prod`) |
| `GQ2.reconstruction_finite` | `Reconstruction.lean` | **Lemma 2.5 (finite core)** | for finite groups, equal surjection-counts to all finite groups ⟹ iso (mutual surjections + equal cardinality). The profinite case reduces to this level-by-level. |
| `GQ2.finite_continuousMonoidHom` | `Reconstruction.lean` | **Lemma 2.5 (input)** | for top. f.g. profinite `P` and finite discrete `H`, `Hom_cont(P,H)` is finite (a continuous hom is pinned down by its values on a topological generating set) |
| `GQ2.profinite_hopfian` | `Reconstruction.lean` | **Lemma 2.5 (Hopfian core)** | a continuous surjective endomorphism of a top. f.g. profinite group is injective — elementary counting proof (precomposition is an injective, hence surjective, self-map of the finite hom-set). Absent from Mathlib. |
| `GQ2.continuousMulEquivOfBijective` | `Reconstruction.lean` | helper | a bijective continuous group hom from a compact group to a Hausdorff group is a topological iso |
| `GQ2.reconstruction_of_equinum` (**modulo** `exists_contSurj_of_card_le`) | `Reconstruction.lean` | **Lemma 2.5 (faithful form)** | the full assembly is checked: from *equinumerosity* `ContSurj P H ≃ ContSurj Q H` (which forces finite counts via `P` f.g.), get `Q↠P` and `P↠Q`; composite `P→Q→P` is Hopfian ⟹ `f` injective ⟹ bijective ⟹ topological iso. Only the (standard) compactness assembly remains. |
| `GQ2.Marking.*` (all auxiliary words + predicates) | `Words.lean` | (1)–(3), §2 | `sigma2,u,d0,z0,c0,g0,dg,hc,h0`, `TameRel/WildRel/Generates/Pro2Core/Admissible` |
| `GQ2.admissibleCount` | `Words.lean` | Prop. 2.3 (RHS of eq. 154) | the finite count `N(G)` |
| `GQ2.main_presentation` (**modulo** its two `sorry` inputs) | `Statement.lean` | **Theorem 1.2 wiring** | the top-level logic *is checked*: `reconstruction` + `main_surjection_count` ⟹ the iso |
| `GQ2.FreeProfiniteGroup` + `.of` + `.homEquiv` | `FreeProfinite.lean` | foundation | **free profinite group** (absent from Mathlib) built from `profiniteCompletion ∘ FreeGroup`, with universal property `(FreeProfiniteGroup X ⟶ P) ≃ (X → P)` |
| `GQ2.grpCatHomEquiv` | `FreeProfinite.lean` | foundation | `(GrpCat.of A ⟶ GrpCat.of P) ≃ (A →* P)` |
| `GQ2.instTotallyDisconnectedSpace_quotient`, `GQ2.profiniteQuotient` | `ProfiniteQuotient.lean` | **foundation (profinite presentations)** | for `G` profinite and `N` closed normal, `G ⧸ N` is profinite (the missing `TotallyDisconnectedSpace` instance, via a clopen basis) — packaged as `profiniteQuotient : ProfiniteGrp`. The construction behind `Γ_A`. Absent from Mathlib. |
| `GQ2.FreeProfiniteGroup.homEquiv_apply` | `FreeProfinite.lean` | foundation | **naturality of the universal property**: `homEquiv X P f x = f (of x)` — `homEquiv` is genuinely "restrict to generators", making it usable for defining maps out of `FreeProfiniteGroup X` (and profinite presentations `Γ_A`) |

## Stated with `sorry` (faithful target, proof deferred)

| declaration | file | paper ref | blocker (see foundations-audit.md) |
|---|---|---|---|
| `GQ2.main_surjection_count` | `Statement.lean` | **Theorem 1.2, eq. (154)** | the entire §§3–9 tower (Demushkin, local CFT, cup products, Gauss sums) |
| `GQ2.exists_contSurj_of_card_le` | `Reconstruction.lean` | **Lemma 2.5 (compactness input)** | assemble `S↠R` from surjection-counts, given the *target* `R` has finite surjection sets (`hRfin`), via König on the cofiltered system of finite quotients of `R`. Standard profinite theory (Ribes–Zalesskiĭ); recipe + Mathlib lemmas in the docstring. `profinite_hopfian` and `reconstruction_of_equinum` are fully proved; this is the only remaining input to the latter. |
| `GQ2.reconstruction` (**⚠ FALSE as stated**) | `Reconstruction.lean` | **Lemma 2.5** | the `Nat.card`-equality hypothesis is too weak: `Nat.card` sends infinite sets to 0, so it fails to encode "equal *finite* counts". Counterexample `P=1`, `Q=(ℤ/2)^ℕ` satisfies the hypotheses but `P≇Q`. Left as `sorry` with a warning; the faithful form is `reconstruction_of_equinum` (equinumerosity). **Decision needed: amend the `hcount` hypothesis.** |

## Not yet stated (missing foundations — would need axioms/opaque stubs)

| object | why deferred |
|---|---|
| the literal presented profinite group `Γ_A` | foundations now in place: `FreeProfiniteGroup (Fin 4)` + `profiniteQuotient` (quotient by a closed normal subgroup). Remaining: express the relators as elements and take the closed normal closure, then `Γ_A := profiniteQuotient …`. |
| `ℤ̂`, `ω₂` as a genuine profinite exponent | needs `ZHat` (absent). On finite quotients `GQ2.powOmega2` already suffices. |

## Next reachable targets (in priority order)

1. `tame_zpowers_disjoint` (Lemma 3.1 ⋊) — finish the `sⁿ=1` argument (needs ℤ-exponent +
   `orderOf (mk s)` lemmas; proof plan is in the docstring). Completes Lemma 3.1 fully.
2. `tame_normal_two_subgroup_central` (Lemma 3.1 last) — `[N, I] ≤ N ∩ I = 1` centralizing argument.
3. `reconstruction` (Lemma 2.5) — the big F′ item; build the profinite-Hopfian lemma on
   `ProfiniteGrp` (Mathlib has `denseRange`/`lift`/`homEquiv` in `ProfiniteGrp.Completion` to build on).
4. ~~`FreeProfiniteGroup.homEquiv_naturality`~~ **done** (`homEquiv_apply`: `homEquiv f x = f (of x)`).
   Next: define `Γ_A` as a profinite presentation quotient (closed normal closure of the relators in
   `FreeProfiniteGroup (Fin 4)`), now that maps out of the free profinite group are usable.
5. `ℤ̂` as a topological **ring** + the `ω₂`-power action on profinite groups — the last foundation
   needed to state Theorem 1.2 literally (currently `main_surjection_count` sidesteps it).
6. A **computable** `powOmega2` variant + `#eval` cross-check of the relator against App. B.

## What this autonomous session added (2026-07-01)

Proved from scratch: `zpowers_sq_eq_of_odd`, `zpowers_normal_of_tame`, `tame_semidirect`
(Lemma 3.1 structure), `coprime_fiber_product` (Lemma 9.1), `oddPart_dvd_omega2Exp`,
`omega2Exp_modEq_one`, `omega2_appendixB` (App. B cross-check), and the **`FreeProfiniteGroup`**
foundation with its universal property. See `docs/SESSION-LOG.md`.
