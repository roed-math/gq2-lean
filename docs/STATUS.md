# Status ledger

Live record of every Lean declaration in the repo: **proved**, `sorry` (target stated, proof
deferred), or scaffold. Updated 2026-07-02. Build: Mathlib `v4.31.0`, `lake build` green
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
| `GQ2.omega2Exp_appendixB_value` | `Omega2.lean` | **App. B (exact)** | the computable `omega2Exp 85667662080 = 40491355905` **exactly** — the definition, not just a hard-coded residue, matches the paper (standard axioms: `v₂` bounds + kernel `Nat` arithmetic) |
| `GQ2.powOmega2_eq_one_of_odd`, `GQ2.powOmega2_eq_self_of_orderOf_two_pow` | `AppendixB.lean` | **App. A ledger** | how `ω₂` acts elementwise: `= 1` on odd-order, `= x` on `2`-power-order elements (Lemma 5.1 content) |
| `GQ2.markOmega2` + `markOmega2_eq_powOmega2` | `AppendixB.lean` | **App. B** | the *computable* `ω₂`-power `x ↦ x^40491355905`, proved `= powOmega2` for orders dividing `M` |
| `GQ2.Marking.markS3_admissible` | `AppendixB.lean` | **App. A/B (verification)** | a fully machine-checked admissible marking `(sr 0, r 1, 1, 1)` in `S₃`: both relations (`τ^σ=τ²` by `decide`; wild relator collapses), generation, and `Pro2Core` |
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
| `GQ2.reconstruction`, `GQ2.reconstruction_of_equinum` (**modulo** `exists_contSurj_of_card_le`) | `Reconstruction.lean` | **Lemma 2.5** | `reconstruction`: `P`, `Q` both top. f.g. profinite with equal `Nat.card` surjection counts ⟹ iso (finite generation of *both* makes the counts genuinely finite; reduces to the equinum form). `reconstruction_of_equinum`: the more general equinumerosity form (`ContSurj P H ≃ ContSurj Q H`, no separate `Q` f.g.). Assembly checked: `Q↠P`, `P↠Q`, composite Hopfian ⟹ iso. Only the (standard) compactness assembly remains. |
| `GQ2.Marking.*` (all auxiliary words + predicates) | `Words.lean` | (1)–(3), §2 | `sigma2,u,d0,z0,c0,g0,dg,hc,h0`, `TameRel/WildRel/Generates/Pro2Core/Admissible` |
| `GQ2.admissibleCount` | `Words.lean` | Prop. 2.3 (RHS of eq. 154) | the finite count `N(G)` |
| `GQ2.main_presentation` (**modulo** its two `sorry` inputs) | `Statement.lean` | **Theorem 1.2 wiring** | the top-level logic *is checked*: `reconstruction` + `main_surjection_count` ⟹ the iso |
| `GQ2.FreeProfiniteGroup` + `.of` + `.homEquiv` | `FreeProfinite.lean` | foundation | **free profinite group** (absent from Mathlib) built from `profiniteCompletion ∘ FreeGroup`, with universal property `(FreeProfiniteGroup X ⟶ P) ≃ (X → P)` |
| `GQ2.grpCatHomEquiv` | `FreeProfinite.lean` | foundation | `(GrpCat.of A ⟶ GrpCat.of P) ≃ (A →* P)` |
| `GQ2.instTotallyDisconnectedSpace_quotient`, `GQ2.profiniteQuotient` | `ProfiniteQuotient.lean` | **foundation (profinite presentations)** | for `G` profinite and `N` closed normal, `G ⧸ N` is profinite (the missing `TotallyDisconnectedSpace` instance, via a clopen basis) — packaged as `profiniteQuotient : ProfiniteGrp`. The construction behind `Γ_A`. Absent from Mathlib. |
| `GQ2.quotientMk`, `GQ2.quotientLift` (+ `quotientMk_surjective`, `quotientLift_quotientMk`) | `ProfiniteQuotient.lean` | foundation | the quotient as a categorical quotient of profinite groups: projection `G ↠ G ⧸ N` and its **universal property** (a continuous hom killing `N` factors uniquely through `G ⧸ N`) — the tool for defining maps *out of* `Γ_A` |
| `GQ2.profinitePresentation`, `GQ2.relatorSubgroup` | `ProfinitePresentation.lean` | **foundation (Γ_A shape)** | the profinite group presented by generators `X` and relators `rels`: `FreeProfiniteGroup X` modulo the closed normal closure of `rels`. `Γ_A` is this for `X = Fin 4` + the four relators (writing the literal relators still needs `ZHat`). |
| `GQ2.FreeProfiniteGroup.homEquiv_apply` | `FreeProfinite.lean` | foundation | **naturality of the universal property**: `homEquiv X P f x = f (of x)` — `homEquiv` is genuinely "restrict to generators", making it usable for defining maps out of `FreeProfiniteGroup X` (and profinite presentations `Γ_A`) |
| `GQ2.omega2Exp_modEq` | `Omega2.lean` | ω₂ coherence | **compatibility across levels**: `N ∣ M → omega2Exp M ≡ omega2Exp N (mod N)` (CRT on the two defining congruences); `powOmega2_pow_eq` is now its corollary |
| `GQ2.orderOf_mk_ofAdd_one`, `ofAdd_mem_iff_index_dvd`, `mk_ofAdd_eq_mk_ofAdd_iff` | `Zhat.lean` | foundation (T-06) | classes in `ℤ/H` are integers mod the index, with **no classification of subgroups of `ℤ`** (the generator's class has order = index) |
| `GQ2.completion_exists_level` | `Zhat.lean` | foundation (T-06) | **congruence neighborhoods are a basis** in any profinite completion: open `U ∋ γ` contains the full "agrees with `γ` at level `H₀`" class — the tool for evaluating continuous maps on completions |
| `GQ2.Zhat` + `Zhat.ofInt` (+ `ofInt_add`, `denseRange_ofInt`, `funext_ofInt`, `commute`) | `Zhat.lean` | **foundation: `ℤ̂` (T-06/U1)** | `ℤ̂ = lim ℤ/N` via Mathlib's `ProfiniteCompletion`; dense embedding of `ℤ`; extensionality-by-density; commutativity. Group structure only (ring deferred by design) |
| `GQ2.omega2` | `Zhat.lean` | **`ω₂ ∈ ℤ̂` (App. A/B, §1)** | the profinite idempotent, componentwise `(omega2Exp N)_N`; compatibility = `omega2Exp_modEq` |
| `GQ2.zpowHat` (`x ^ᶻ γ`) + `zpowHatHom`, `zpowHat_ofInt`, `zpowHat_mul`, `map_zpowHat` | `Zhat.lean` | **foundation: `ẑ`-exponentiation (T-06/U1)** | continuous extension of `n ↦ xⁿ` to `γ : ℤ̂` in any profinite group, via `ProfiniteCompletion.lift`; extends `ℤ`-powers; **naturality** `f (x ^ᶻ γ) = (f x) ^ᶻ γ` via `lift_unique` |
| `GQ2.zpowHat_omega2`, `GQ2.map_zpowHat_omega2` | `Zhat.lean` | **`ω₂` evaluation (T-06 headline)** | in finite quotients the profinite `ω₂` computes the paper's finite calculus: `f (x ^ᶻ ω₂) = powOmega2 (f x)` — ties `omega2` to the entire App. A/B word ledger |
| `GQ2.zpowHat_omega2_s3_rotation`, `..._s3_reflection` | `Zhat.lean` | App. A/B sanity | in `S₃`: `(r 1) ^ᶻ ω₂ = 1`, `(sr 0) ^ᶻ ω₂ = sr 0` — concrete profinite-to-finite cross-check |

## Stated with `sorry` (faithful target, proof deferred)

| declaration | file | paper ref | blocker (see foundations-audit.md) |
|---|---|---|---|
| `GQ2.main_surjection_count` | `Statement.lean` | **Theorem 1.2, eq. (154)** | the entire §§3–9 tower (Demushkin, local CFT, cup products, Gauss sums) |
| `GQ2.exists_contSurj_of_card_le` | `Reconstruction.lean` | **Lemma 2.5 (compactness input)** | assemble `S↠R` from surjection-counts, given the *target* `R` has finite surjection sets (`hRfin`), via König on the cofiltered system of finite quotients of `R`. Standard profinite theory (Ribes–Zalesskiĭ); recipe + Mathlib lemmas in the docstring. Its arithmetic heart is **proved** (`contSurj_quotient_nonempty_finite`: each `R/V` level is nonempty+finite); only the König/cone assembly is deferred. `profinite_hopfian` and `reconstruction_of_equinum` are fully proved; this is the only remaining input to the latter. |

## Not yet stated (missing foundations — would need axioms/opaque stubs)

| object | why deferred |
|---|---|
| the literal presented profinite group `Γ_A` | **unblocked** (ticket T-21): `ℤ̂`/`ω₂`/`^ᶻ` now exist (`Zhat.lean`), so the four relator words are writable in `FreeProfiniteGroup (Fin 4)` and `Γ_A := profinitePresentation (Fin 4) rels` is definable. Remaining work is just writing the words and the faithfulness stress test (image under a finite marking = the `Words.lean` words, via `map_zpowHat_omega2`). |
| ~~`ℤ̂`, `ω₂` as a genuine profinite exponent~~ | **done 2026-07-02** (`Zhat.lean`, ticket T-06): `Zhat`, `omega2`, `zpowHat` with naturality and finite-quotient evaluation. Ring structure on `ℤ̂` remains deliberately out of scope. |

## Next reachable targets (in priority order)

1. ~~Lemma 3.1 (`tame_*`)~~ **done** (see Proved table).
2. ~~`reconstruction` (Lemma 2.5)~~ **done**, modulo the standard compactness input
   `exists_contSurj_of_card_le` (recipe in its docstring).  The `Nat.card`-hypothesis form was
   repaired by adding topological finite generation of *both* `P` and `Q` (`hQfg`); the general
   equinumerosity form is `reconstruction_of_equinum`. `main_presentation` correspondingly now
   assumes `G_{ℚ₂}` is topologically f.g. (`hfgG`, a true but unformalized fact).
3. **`exists_contSurj_of_card_le`** — the one remaining sorry in `reconstruction_of_equinum`: König
   assembly of `S ↠ R` from finite level-sets over `OpenNormalSubgroup R` (`SemilatticeInf`, so
   cofiltered) via `nonempty_sections_of_finite_cofiltered_system`, then a cone through
   `isoLimittoFiniteQuotientFunctor R` + dense/compact image. Standard; the biggest remaining chunk.
4. ~~`homEquiv_naturality`~~ + ~~profinite quotient/presentation foundations~~ **done**
   (`homEquiv_apply`, `profiniteQuotient`, `profinitePresentation`, `relator_quotientMk_eq_one`).
5. ~~`ℤ̂` + the `ω₂`-power action on profinite groups~~ **done** as a topological *group* with
   `^ᶻ`-action (`Zhat.lean`, T-06; the ring structure was not needed for the relators). Next:
   **T-21** — write the four relator words literally and define
   `Γ_A := profinitePresentation (Fin 4) …`, stating Theorem 1.2 in its literal form.
6. ~~computable `ω₂` cross-check against App. B~~ **done** (`omega2Exp_appendixB_value`).

## What this autonomous session added (2026-07-01)

Proved from scratch: `zpowers_sq_eq_of_odd`, `zpowers_normal_of_tame`, `tame_semidirect`
(Lemma 3.1 structure), `coprime_fiber_product` (Lemma 9.1), `oddPart_dvd_omega2Exp`,
`omega2Exp_modEq_one`, `omega2_appendixB` (App. B cross-check), and the **`FreeProfiniteGroup`**
foundation with its universal property. See `docs/SESSION-LOG.md`.
