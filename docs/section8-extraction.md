# §8 statement extraction — design note (ticket P-16, F-draft half)

Companion to [`GQ2/SectionEight.lean`](../GQ2/SectionEight.lean): maps the §8 nodes
(paper pp. 38–44: Lemmas 8.2–8.7, Prop 8.8, Prop 8.9, displays (124)–(142)) to their Lean
encodings.  The heavier per-item rationale lives in the module docstring; this note is the
inventory + deviation ledger for P-20 review and for the O-half of P-16.

## Statement inventory

| Paper node | Lean name (`GQ2.SectionEight.*`) | Status | Notes |
|---|---|---|---|
| Lemma 8.2, candidate | `lemma_8_2_gammaA` | **proved** (std-3) | see O-half log below |
| Lemma 8.2, local | `lemma_8_2_local` | **proved** (std-3) | via `card_char_piBd`; `BoundaryMaps` hypothesis |
| Lemma 8.2, twisting clause | `scalarTwist`, `isBoundaryLift_scalarTwist` | **proved** | std-3 |
| Lemma 8.3 (eq. (124)) | `lemma_8_3` | sorried | generic source, `hscalar` hypothesis |
| Lemma 8.4 (eq. (125), Fourier inversion) | `lemma_8_4` | **proved** | axiom-free |
| Lemma 8.5 (eq. (126), constrained Gauss) | `lemma_8_5` | **proved** | std-3; `a_χ` as data-with-spec |
| Lemma 8.6 (radical edge, half-torsor) | `RadicalCoverData`, `NoDescent`, `lemma_8_6_gammaA`, `lemma_8_6_local` | sorried | consequence form, per source |
| Lemma 8.7 / Prop 8.8 ((131)–(135)) | **not stated** | — | proof-internal to (140); P-14 precedent (6.7/6.10/6.11) |
| Prop 8.9 ((136)–(142)) | `RecursionFrame`, `ClosedRecursion`, `prop_8_9` | sorried | boxed system; see deviations |

Supporting layer (all **proved**, std-3): `sign`/`sign_add`/`one_add_sign` (the `𝔽₂`-sign
calculus), `sum_sign_eq_zero` (character orthogonality — both (125)'s dual-side and (126)'s
group-side instances), `sum_dual_sign`, `finite_dual`, `add_self_fp2`; `CentralCover` +
`pullTarget` (the Lemma 8.3 pulled-back boundary-framed structure — the paper's "central
kernel in `ker(π̃, θ̃)`" holds by construction), `sq_eq_one_of_mem_ker`, `liftableCount`,
`exactImageCountOn` (totalized stratum count).

`SORRY_ALLOWLIST` entry: `GQ2/SectionEight.lean` (six sorries, removed by the O-half).

## Encoding decisions and deviations (flagged for P-20)

1. **Multiplied-out integer forms.**  All displays with divisions ((125), (126), (136),
   (139), (140)) are stated over `ℤ` with the denominators cleared, and (137) is stated
   additively (`Z = m + Σ` instead of `m = Z − Σ`) — no `ℕ`-subtraction, no rationals.
2. **`a_χ` in (126) is data-with-spec** (`B_Q(a_χ, x) = χ(Lx)`), not derived from
   nonsingularity: the identity needs only the spec (`prop_7_4`-`lam` house pattern), so
   `Nonsingular` does not appear in `lemma_8_5` at all.
3. **Liftability encodes obstruction-vanishing.**  "Scalar pushout vanishes" / "pullback
   cover splits" / "unobstructed" are all rendered as *existence of a continuous lift
   through the cover* (`liftableCount`, `mB`, `mJ`, `zBC`, `nPhase`, `MLifts.Central`).
   This is the paper's own torsor description and keeps the statement layer free of
   `H²`-plumbing.
4. **Lemma 8.6's edge class is operational.**  The `H¹(C, T^∨)`-valued edge of (128) is
   not constructed; "edge ≠ 0" is `NoDescent` — no normal complement to `p⁻¹(T)` missing
   `z` — which the paper's own descent clause makes equivalent.  The (127) variation
   formula and (128) cocycle are P-16-proof-internal.  Consequence: the descent *iff* of
   8.6 becomes definitional and is not separately stated.
5. **Lemma 8.6 is per-source** (`gammaA`/`local`): the paper's proof runs the variation
   functional against degree-one duality, which is B6 on the local side and §5
   (B7-backed 5.15/5.16) on the candidate side; a source-generic statement would need a
   duality hypothesis in cochain vocabulary — deliberately avoided at the statement layer.
6. **`D_R` is encoded by kernels** (`card_DR`): `Y`-normal subgroups `R' ≤ R` of relative
   index ≤ 2, `λ = 0 ↔ R' = R` — the `lemma_7_1_dual` encoding of invariant functionals.
   The scalar covers `p_λ` are `RecursionFrame` **data** (`scalarCover`), pinned by the
   equations they satisfy rather than by a `Y/ker λ`-construction; ditto the quotient
   targets `TB`/`TC` (pinned by `ker_piB`/`ker_piC` + head/decoration compatibility).
7. **(140)–(142) are folded and `∃`-quantified.**  (141) is substituted into (140)
   (`s_Γ(ζ) = 2n_{Γ,0}(ζ) − e_Γ(C)`; the (100)-into-(105) precedent), and (142) is the
   Lemma 8.3 partition at the phase covers (recoverable from `lemma_8_3`, not re-boxed).
   The phase family `(μ, G⁰, D_T, phase)` is **existentially quantified outside the
   source split** in `prop_8_9`, so one witness serves both sources — which is exactly
   what the §9 comparison consumes.  The paper's pinning (`μ = |B¹(V)||Z¹(T)|` via
   5.15/5.16, `G⁰` = Gauss sum of the Prop 7.4 form, family = `Δ_{χ,κ}`-covers of
   (133)/(134)) is the O-half's construction; if P-17 needs the pinned values, that is a
   reviewed statement addition.
8. **`2^d = |V|` in (140) is `|M|/|T|` in `ℕ`-division** (exact by `T ≤ M`); `2^{2dimM}`
   is `|M|²`, `z_R` is `|R|²·|D_R|` — all cards, no `dim` bookkeeping.

## O-half log

* **Lemma 8.3 torsor core proved 2026-07-03** (std-3): the mathematical heart of the
  eight-lift partition is done — the continuous-hom lifts of a fixed map through a central
  double cover `p` form a **torsor** under `Hom_cont(Γ, 𝔽₂)` acting by `scalarTwist`.
  Landed lemmas (in the `Twist` section, over `variable (C : CentralCover Y)`):
  `orderOf_z` (= 2), `z_pow_eq_iff` (`z^a = z^b ↔ a ≡ b [2]`), `p_z`/`p_z_pow`,
  `z_pow_central`, `eq_one_or_z_of_mem_ker` (`⟨z⟩ = {1, z}`), `p_comp_scalarTwist` (action
  stays in the fibre), `scalarTwist_left_injective` (**freeness**), `liftChar`/`liftChar_rep`/
  `liftChar_add` + `liftDiff`/`scalarTwist_liftDiff` (**transitivity**: any two lifts differ by
  a unique 𝔽₂-character), and the packaged **`fiberLiftEquiv`** :
  `Hom_cont(Γ,𝔽₂) ≃ {g // p∘g = p∘g₀}` (each fibre has exactly `|Hom|` lifts).  The transitivity
  character is built representation-first: `g' γ = g γ · z^{χ γ}`, `χ` additive by cancelling
  `g(γδ) = gγ·gδ` and reading off `z^a = z^b ⇒ a ≡ b [2]` — avoids a 4-way `if`-split.  This
  infrastructure is directly reused by 8.6 (the half-torsor) and 8.9's `(139)` half-count.
  `lemma_8_3` itself stays sorried: what remains is **scoped finite bookkeeping** — the two
  fibrations of `R = {g // (p∘g).range = J ∧ boundary-framed}` (by image → RHS via
  `Nat.card_sigma` + range-corestriction; by projection → `8·u^β` via `fiberLiftEquiv` + a
  base-lift section), needing a **`hfg` t.f.g. amendment** to finitize the `BoundaryLifts`/`Hom`
  sets (flagged; all §8 sources are t.f.g.).  Docstring on `lemma_8_3` records the plan.
* **Lemma 8.3 fully PROVED 2026-07-03** (std-3): `lemma_8_3` is now sorry-free.  The two
  fibrations of the master set `masterLifts = {g // (p∘g).range = J ∧ boundary-framed}`:
  **(B, projection → `8·u^β`)** `projB g` corestricts `p∘g` to `↥J`; each `projB`-fibre is the
  torsor `{g' // p∘g' = p∘g₀} ≃ Hom_cont(Γ,𝔽₂)` (`fiberLiftEquiv`), so
  `Nat.card masterLifts = ∑_f 8 = 8·|L|` via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`.
  **(A, image → RHS)** `imageMap g = g.range`; each fibre `{g // g.range = J'} ≃
  BoundaryLifts((pullTarget T).stratum J')` by `cmhCodRestrict`/`cmhInclude`, and
  `stratum_surj` makes `exactImageCountOn = exactImageCount` (`dif_pos`) on the sum set; the
  finsum-over-set is matched to the `Nat.card_sigma` output by `finsum_mem_coe_finset` +
  `Finset.sum_subtype`.  `hfg` (applied amendment) finitizes everything via
  `finite_continuousMonoidHom`/`finite_boundaryLifts`.  Lean gotchas that bit: (i) never `rw`
  the `range = J` equation into a hypothesis whose type mentions `masterLifts …J` or `↥J`
  (`J`-dependency motive failure) — rewrite the *goal*'s fresh membership; (ii) `(C.pCont.comp g)
  γ` needs `show`-normalizing to `C.p (g γ)`; (iii) `Equiv` round-trips are `Subtype.ext ×2 + ext
  γ + rfl` (the corestriction/inclusion compose to `rfl`); (iv) `g̃` (combining-tilde) is not a
  valid identifier — use `gt`.  Scaffolding reused (all std-3):
  the reusable pieces the two fibrations run on are proved and in place:
  the **corestriction layer** `cmhCodRestrict` / `cmhInclude` / **`cmhSubgroupEquiv`**
  (`Hom(Γ,↥S) ≃ {f : Hom(Γ,G) // ∀ x, f x ∈ S}` — Mathlib has no `ContinuousMonoidHom.codRestrict`),
  `CentralCover.pCont` (the cover map bundled continuous), the master set **`masterLifts`**
  (`R`, as a reducible `abbrev`), and **`stratum_surj`** (`J'.map C.p = J ⇒` the pullback
  `J'`-stratum surjects onto `H`, so `exactImageCountOn = exactImageCount` on the sum set).
  The `lemma_8_3` body now discharges the finiteness (`finite_continuousMonoidHom hfg` +
  `Subtype.finite`) and sorries only the two `Nat.card_sigma` fibrations.  **Lean gotcha
  recorded**: `masterLifts …J` and `↥J` both depend on `J`, so a naive `rw [range = J]` in a
  hypothesis fails the motive check — rewrite the *goal*'s fresh membership instead, or use the
  `cmhSubgroupEquiv` round-trip.  This is why the two fibrations, though mechanical, need care.
* **`lemma_8_2_gammaA` proved 2026-07-03** (std-3), *without* the `Π`-route sketched below —
  entirely over the P-04/P-05 layer: `charEquiv` (characters of `Γ_A` = characters of `F₄`
  killing `N_A`, the `push`/`descend` mechanics) ∘ `cmhEquivFun` (characters of `F₄` =
  generator values, via the universal property) ∘ `vecEquiv`, with the middle transport
  `ker_char_NA_le_iff` : *killing `N_A` ⟺ killing `τ`*.  Forward: `tameRelator_mem_NA`
  (P-04) + `𝔽₂`-arithmetic (`decide`).  Backward: `ker c` is admissible —
  `generates_univMarking_map` (generation), the `τ`-kill (tame), and the new
  **exponent-2 ledger** `Marking.wildRel_of_comm2` (the full `ω₂`-word ledger collapses in
  an exponent-2 abelian group: `σ₂ = σ`, `uᵢ = xᵢτ`, `d₀ = τ`, `g₀ = 1`, `h₀ = τ`, and (6)
  telescopes) — then `isAdmissibleU_iff_NA_le` (P-04).  Statement amendment (F-owner): the
  `𝔽₂`-topology binders are `[TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]`
  (FoxHeisenberg convention) — binding the topology on `Multiplicative (ZMod 2)` directly
  fights Mathlib's `Multiplicative`-transfer instance (`instCompactSpaceMultiplicative`
  wants the base).  Lean gotchas hit and recorded: keep `Equiv`-field proofs as named
  private lemmas (nested-`by` abstraction timeout, the P-05 gotcha again), and pass
  `homEquiv_symm_of`'s **explicit `P`-argument** — leaving it `_` makes the unifier solve
  `↥?P =?= 𝔽₂` through the `CompHausLike` coercion (whnf timeout).

* **`lemma_8_2_local` proved 2026-07-03** (std-3), exactly by the sketched `Π`-route, with
  the flagged **statement amendment** applied: hypotheses `(B : BoundaryMaps)` +
  `[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` (the `main_presentation`
  house pattern).  Pieces: `card_char_piBd` (`|Hom(Π,𝔽₂)| = 8` — peel `maxProPHomEquiv`
  (T-05) then the now-generic `charEquiv` at `relatorSubgroup {piRelator}`; the relator
  condition is vacuous by the exponent-2 ledger, `char_kills_piRelator`), and the
  `pro2F`-precomposition bijectivity (injective from `pro2F_surjective`; surjective by
  descending `pro2F` to `continuousMulEquivOfBijective ψ` on the canonical pro-2 quotient
  via `ker_pro2F` and factoring the character through `maxProPHomEquiv`).  A second
  amendment: the `𝔽₂`-topology **binders were removed everywhere** — `ZMod.instTopologicalSpace`
  / `ZMod.instDiscreteTopology` and their `Multiplicative`-transfers are global Mathlib
  instances, so the FoxHeisenberg-style binders create a two-instance conflict (this bit as
  an instance mismatch inside `char_kills_piRelator`).  Lean gotcha recorded: bind
  constructed `ContinuousMulEquiv`s with `set`, not `have` — `have` is opaque for data and
  kills the `rfl`-defeqs (`e (mk x) ≡ ψ (mk x) ≡ pro2F x`).  Infra generalized in passing:
  `charEquiv` now takes any normal subgroup of any topological group; `cmhEquivFun` any
  generator-index type.

## P-16d statement corrections (2026-07-05, caught by attempting the (137) proof)

1. **`RecursionFrame.zBC` re-encoded.**  The original datum was the cover-valued lift `g`
   itself; the boundary equation of the pulled-back target only constrains `p_λ ∘ g`, so
   each `λ`-compatible `B`-lift carries exactly `#Hom(Γ,𝔽₂)` cover lifts (the `z`-scalar
   twists) and the pair count overstates the paper's `Z_{Γ,λ}(B/C)` by the factor 8 —
   contradicting (139) as displayed.  Corrected datum: the `B`-level lift `m` with
   **existence** of a cover lift (matching `m_{Γ,λ}`'s `∃`-form and the paper's
   "compatible lifts … without imposing generation in B").
2. **`eq137`'s index set restricted to `J ↠ C`.**  The paper's (137) sums over proper
   strata *surjecting onto `C`*; the unrestricted sum would overcount by the
   `m_{Γ,λ}(J)` of `C`-missing strata (whose `Z`-slices are empty since the pair's
   `C`-component is onto).  Both `ClosedRecursion.eq137` and the derivation were updated.

## O-half work order (remaining)

> **2026-07-04: decomposed into board sub-tickets P-16a–d** — see `docs/p16-ticket-split.md`
> (P-16a = def-layer relocation + items (a)–(c) below; P-16b/c = the two 8.6 closes; P-16d =
> `prop_8_9`).  Claim a sub-ticket row before starting; the technical detail below remains the
> authoritative work order.
2. `lemma_8_3` — the eight-lift partition: `scalarTwist` freeness + `hscalar` + exact-image
   bucketing (`Subgroup.map` fibres).  **DONE (std-3).**
3. `lemma_8_6_*` — (128)-cocycle, (127) variation via 5.10 (candidate) / B6 (local),
   half-orbit count; `NoDescent ↔ [ε̄] ≠ 0` internally.
   **P-16a+P-16b DONE (2026-07-05)**: the engine (`GQ2/CentralObstruction.lean`, std-3) and
   the **local close** (`GQ2/RadicalEdgeLocal.lean`; `lemma_8_6_local` proved & spliced,
   std-3+B6+B7; statement amended with compactness + `hfg` per the 8.2/8.3 precedents).
   Design note: the count twists by `T`-valued cocycles and closes by a twist-involution
   flip (`two_mul_card_of_swap`) — items (a)/(d) below are realized in that simplified form;
   `lemma_8_6_gammaA` (P-16c) still consumes (d′) via 5.15/5.16 when P-13f lands.
   **PROGRESS (Opus, 2026-07-04): the combinatorial CORE is landed** — `two_mul_card_fiber`
   (before `section HalfTorsor`, std-3, sorry-free): a nonzero `𝔽₂`-linear functional on a
   finite `𝔽₂`-space has each fibre exactly half (`ℓ` surjective ⟹ `V` splits into two equal
   fibres over `ZMod 2` via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`).  This is the (127)
   half-count, and is **also** what `prop_8_9`'s `(139)` consumes.  **REMAINING for
   `lemma_8_6_local`** (the deep cohomological core, all B6-side / no P-13):
   (a) `MLifts D ρ` is a torsor under `Z¹(Γ, M, a_ρ)` — twisted 1-cocycles for the
   `ρ`-conjugation action `a_ρ : Γ → Aut M` (well-defined since `M` abelian); pick a basepoint
   (handle `MLifts = ∅` ⟹ both sides 0) to get `MLifts ≃ Z¹(Γ,M)`, a finite `𝔽₂`-space
   (`M` elementary-abelian);  (b) the obstruction `o : MLifts → H²(Γ,𝔽₂) ≅ 𝔽₂` (`f` lifts
   through `p : cover ↠ B` iff the pullback central `𝔽₂`-extension splits) — needs
   group-extension obstruction theory wired to `ContCoh.H2 AbsGalQ2 (ZMod 2)` (NOT in repo;
   ~150 ln new);  (c) `o(f₀·φ) = o(f₀) + ℓ(φ)` with `ℓ` the (127) linear functional built
   from the cover's quadratic form `q` (cup-product variation);  (d) `ℓ ≠ 0 ⟺ NoDescent`,
   via **B6's perfect (1,1) pairing** `H¹(Γ,M^∨) × H¹(Γ,M) → H²(Γ,𝔽₂)` (`MuDual`, `D.inv`);
   then `two_mul_card_fiber` closes it.  `lemma_8_6_gammaA` is the same with (d) via
   5.15/5.16 (P-13-gated).  Est ~500 ln + new obstruction infra; a focused multi-session build.
4. `prop_8_9` — assemble per the paper's proof: unrestricted `M`-stage (5.15/5.16 + 7.1),
   Frattini argument for the final `R`-stage torsor, `lemma_8_4` for (136), `lemma_8_5` +
   Prop 8.8 for (140); construct the shared witness `(μ, G⁰, D_T, phase)`.
   Axes: B6, B7, B9 per App. D.  (`eq139` reuses `two_mul_card_fiber`.)
