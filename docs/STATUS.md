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
| `GQ2.Marking.sigma2Hat … h0Hat`, `tameRelator`, `wildRelator` | `GammaA.lean` | **eqs. (1)–(3), (5), (6) profinitely (T-21)** | the auxiliary-word ledger and both relator words with genuine `ω₂ ∈ ℤ̂` exponents (`^ᶻ omega2`), on any marking of any profinite group |
| `GQ2.Marking.map_sigma2Hat … map_h0Hat`, `map_tameRelator_eq_one_iff`, `map_wildRelator_eq_one_iff` | `GammaA.lean` | **relations (5)/(6): profinite = finite (T-21 stress)** | through any continuous hom to a finite group the `^ᶻω₂`-ledger computes the `powOmega2`-ledger of `Words.lean`; killing the relator words ⟺ `TameRel`/`WildRel` — the two readings of the relations provably agree |
| `GQ2.FreeProfiniteGroup.homEquiv_symm_of`, `GQ2.Marking.toHom`, `GQ2.univMarking`, `univMarking_map_toHom` | `FreeProfinite.lean` / `GammaA.lean` | foundation | markings of profinite `P` ↔ continuous homs `F₄ ⟶ P`, with the round-trip (universal property is "evaluate at generators") |
| `GQ2.IsAdmissibleU`, `GQ2.NA`, **`GQ2.GammaA`** | `GammaA.lean` | **`Γ_A` (paper §2.1, eq. (7))** | the marked quotient construction, verbatim: `N_A` = intersection of all admissible open normal subgroups of `F₄` (= kernels of admissible finite quotients), `Γ_A = F₄ ⧸ N_A` via `profiniteQuotient`. The pro-2 side condition is part of admissibility, exactly as in the paper |
| `GQ2.NA_le_ker`, `GQ2.surjective_of_map_generates` | `GammaA.lean` | eq. (7) certificate | `N_A` is contained in the kernel of **every** admissible continuous hom to **any** finite group — our open-normal-subgroup encoding captures the paper's whole class `Q_A` |
| `GQ2.isAdmissible_markS3_toHom`, `GQ2.gammaA_surjective_s3` | `GammaA.lean` | §2.1 nonvacuity | the App-B `S₃` marking classifies an admissible quotient, and `Γ_A ↠ S₃` — the construction is machine-checkably nonvacuous |
| `GQ2.isOpen_stabilizer`, `isOpen_iInf_stabilizer`, `exists_openNormalSubgroup_smul_eq_self` | `DiscreteModule.lean` | **discrete modules (T-01/I1)** | the typeclass conventions for topological `G`-modules (no new structures), with the smoothness facts: open stabilizers, open action kernel (finite `M`), action factors through a finite quotient over profinite `G` |
| `GQ2.ContCoh.H0/C1/C2/dZero/dOne/dTwo/Z1/Z2/B1/B2/H1/H2` (+`H1mk`,`H2mk`, `AddCommGroup` instances) | `Cohomology.lean` | **continuous cohomology ≤ 2 (T-02/U2)** | inhomogeneous continuous cochains, Serre GC I §2.2 conventions; `Z = C ⊓ ker δ`; readable `mem_Z1_iff`/`mem_Z2_iff`; `δ∘δ = 0`; `B ≤ Z`. The coefficient system for B3/B6/B7/B9 |
| `GQ2.ContCoh.H0comap/Z1comap/Z2comap/H1comap/H2comap`, `res0/res1/res2` | `Cohomology.lean` | **functoriality (T-02)** | one pullback along a compatible pair (`π : G →ₜ* Q`, intertwining `f : N →+ M`) in degrees ≤ 2; restriction to subgroups as the `(inclusion, id)` case; inflation = the `DistribMulAction.compHom` recipe (docstring) |
| `GQ2.ContCoh.mem_Z1_iff_of_trivial`, `B1_eq_bot_of_trivial`, `H1equivZ1OfTrivial`, `H0_eq_top_of_trivial`, `Z1_apply_one` | `Cohomology.lean` | T-02 stress | trivial action: `H¹ ≃+ Z¹` = continuous "additive homs"; `H⁰ = ⊤`; cocycles vanish at `1` |
| `GQ2.ContCoh.mapCoeff0/1/2`, `inf0/1/2`, `Z1_apply_inv` | `Cohomology.lean` | **lemma layer (T-03)** | coefficient functoriality (`π = id`) and inflation (`f = id`, actions agree through `π`) as the two specializations of the `Hicomap` workhorse; `φ(g⁻¹) = −g⁻¹·φ(g)`. Finite-`G` comparison to Mathlib deferred (verification concern, needs a `Rep ℤ G` bridge) |
| `GQ2.ContCoh.cup11` (+`cup11_mk_mk`, `cup11_add_left/right`, `cup11_zero_left/right`) | `CupProduct.lean` | **cup product `(1,1)` (T-04)** | `H¹(G,M) →+ H¹(G,N) →+ H²(G,P)` rel. a `G`-pairing `μ`; the B3-critical one (nondegeneracy of `H¹ × H¹ → H²`). Full Leibniz descent in both variables; bilinear + `∪0=0` by construction |
| `GQ2.ContCoh.cup02`, `GQ2.ContCoh.cup20` | `CupProduct.lean` | **cup products `(0,2)`,`(2,0)` (T-04)** | `H⁰ →+ H² →+ H²` and `H² →+ H⁰ →+ H²` — the shapes B6 (local Tate duality) needs for `H^i × H^{2−i} → H²` |
| `GQ2.ContCoh.cup11_mapCoeff_target`, `postPairing` | `CupProduct.lean` | T-04 coefficient naturality | cup commutes with a target `G`-map: `cup(fP∘μ) = mapCoeff2 fP ∘ cup(μ)` |
| `GQ2.ContCoh.toContRep`, `toTopRep`, `toAction` | `CtsCohBridge.lean` | **bridge to Mathlib continuous cohomology** | a topological `G`-module `M` as a continuous `ℤ`-rep `g ↦ (m↦g•m)`, hence `TopRep ℤ G` and (directly) `Action (TopModuleCat ℤ) G` — the coefficient of Mathlib's `continuousCohomology` |
| `GQ2.ContCoh.invariantsEquivH0`, `GQ2.ContCoh.H0Equiv` | `CtsCohBridge.lean` | **degree-0 bridge** | `(invariants ℤ G).obj (toAction M) ≃+ H0 G M` (both `Mᴳ`, defeq predicates) and `(continuousCohomology ℤ G 0).obj (toAction M) ≃+ H0 G M` (via Mathlib's `continuousCohomologyZeroIso`). Our `H⁰` = Mathlib's continuous `H⁰` |

## Stated with `sorry` (faithful target, proof deferred)

| declaration | file | paper ref | blocker (see foundations-audit.md) |
|---|---|---|---|
| `GQ2.main_surjection_count` | `Statement.lean` | **Theorem 1.2, eq. (154)** | the entire §§3–9 tower (Demushkin, local CFT, cup products, Gauss sums) |
| `GQ2.exists_contSurj_of_card_le` | `Reconstruction.lean` | **Lemma 2.5 (compactness input)** | assemble `S↠R` from surjection-counts, given the *target* `R` has finite surjection sets (`hRfin`), via König on the cofiltered system of finite quotients of `R`. Standard profinite theory (Ribes–Zalesskiĭ); recipe + Mathlib lemmas in the docstring. Its arithmetic heart is **proved** (`contSurj_quotient_nonempty_finite`: each `R/V` level is nonempty+finite); only the König/cone assembly is deferred. `profinite_hopfian` and `reconstruction_of_equinum` are fully proved; this is the only remaining input to the latter. |
| `GQ2.main_presentation_literal` | `GammaA.lean` | **Theorem 1.2, literal form** | `Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)` against the honest eq.-(7) `Γ_A`. Route (fixed): `main_presentation` (proved) at `Γ_A` + Prop. 2.3 (`|Sur(Γ_A,G)| = admissibleCount G` — step 2, from `NA_le_ker` + the relator bridges + `Subdirect.lean`) + top. f.g. of `Γ_A` + `main_surjection_count` (the B1–B9 tower) |

## Not yet stated (missing foundations — would need axioms/opaque stubs)

| object | why deferred |
|---|---|
| ~~the literal presented profinite group `Γ_A`~~ | **done 2026-07-02** (`GammaA.lean`, ticket T-21): `GammaA` is the paper's eq.-(7) marked quotient (NOT the bare two-relator presentation — the pro-2 condition is part of the presentation data), with the `^ᶻω₂`-relator words and the profinite=finite bridges. Theorem 1.2 is stated literally (`main_presentation_literal`, sorried). |
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
5. ~~`ℤ̂` + the `ω₂`-power action~~ **done** (T-06); ~~literal `Γ_A` + literal Theorem 1.2~~
   **done** (T-21, `GammaA.lean`). Next: **Prop. 2.3** — `Nat.card (ContSurj GammaA G) =
   admissibleCount G` for finite `G` (step 2 entry point; ingredients ready: `NA_le_ker`,
   the relator bridges, `Subdirect.lean`, `quotientLift`), which discharges `hΓA` in
   `main_presentation` and reduces `main_presentation_literal` to `main_surjection_count`
   + top. f.g. of `Γ_A`.
6. ~~computable `ω₂` cross-check against App. B~~ **done** (`omega2Exp_appendixB_value`).

## What this autonomous session added (2026-07-01)

Proved from scratch: `zpowers_sq_eq_of_odd`, `zpowers_normal_of_tame`, `tame_semidirect`
(Lemma 3.1 structure), `coprime_fiber_product` (Lemma 9.1), `oddPart_dvd_omega2Exp`,
`omega2Exp_modEq_one`, `omega2_appendixB` (App. B cross-check), and the **`FreeProfiniteGroup`**
foundation with its universal property. See `docs/SESSION-LOG.md`.
