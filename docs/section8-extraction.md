# §8 statement extraction — design note (ticket P-16, F-draft half)

Companion to [`GQ2/SectionEight.lean`](../GQ2/SectionEight.lean): maps the §8 nodes
(paper pp. 38–44: Lemmas 8.2–8.7, Prop 8.8, Prop 8.9, displays (124)–(142)) to their Lean
encodings.  The heavier per-item rationale lives in the module docstring; this note is the
inventory + deviation ledger for P-20 review and for the O-half of P-16.

## Statement inventory

| Paper node | Lean name (`GQ2.SectionEight.*`) | Status | Notes |
|---|---|---|---|
| Lemma 8.2, candidate | `lemma_8_2_gammaA` | **proved** (std-3) | see O-half log below |
| Lemma 8.2, local | `lemma_8_2_local` | sorried | needs the `Π`-route |
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

## O-half work order (remaining)

1. `lemma_8_2_local` — factor through the pro-2 quotient: `BoundaryMaps`' `pro2F` has
   `ker = proPKernel 2` (T-05 universal property gives the factorization of any
   `𝔽₂`-character), then `Hom(Π, 𝔽₂) = 𝔽₂³` by the Prop 3.10 presentation (3 generators,
   relator `x₀^{σ²}x₀[x₁,σ]` with no mod-2 linear part — the same exponent-2 ledger
   collapse).  **Requires a statement amendment**: add a `BoundaryMaps` hypothesis (the
   bundle is what pins `pro2F`; without it the count is B4/B5-content outside the P-16 Ax
   budget).
2. `lemma_8_3` — the eight-lift partition: `scalarTwist` freeness + `hscalar` + exact-image
   bucketing (`Subgroup.map` fibres).
3. `lemma_8_6_*` — (128)-cocycle, (127) variation via 5.10 (candidate) / B6 (local),
   half-orbit count; `NoDescent ↔ [ε̄] ≠ 0` internally.
4. `prop_8_9` — assemble per the paper's proof: unrestricted `M`-stage (5.15/5.16 + 7.1),
   Frattini argument for the final `R`-stage torsor, `lemma_8_4` for (136), `lemma_8_5` +
   Prop 8.8 for (140); construct the shared witness `(μ, G⁰, D_T, phase)`.
   Axes: B6, B7, B9 per App. D.
