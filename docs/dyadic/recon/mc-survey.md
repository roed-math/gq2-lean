# MC-M / MC-N recon survey — rank-four marked automorphism lifting (2026-07-28)

Read-only survey of the repo at master `d0714a7`, taken at campaign setup. Seed material for
ticket MC1 (design memo). File:line anchors verified at survey time.

**Headline:** there is **no rank-four Lean code anywhere in the repo**. `M_α` / `N_α` exist only
in the draft (`docs/dyadic/refs/dyadic-presentations.tex`: cores `eq:Mpc-core`, `eq:Msign-core`
(superseded), `eq:Ncompact-core`, `eq:Npc-core`). Everything below is the rank-three template
to port.

## 1. The marked matching engine — `GQ2/Roe/MarkedMatching.lean` (1193 lines)

Architecture is rank-generic; **every concrete declaration is rank-three-hardwired** (`D0`/`DR`
are fixed types, not variables; `Fin 3` / `Fin 2` are literal).

| decl | line | role |
|---|---|---|
| `isProP_two_wordLift : IsProP 2 (WordLift ℤ_[2] ℤ_[2]ˣ)` | :163 | topologizes the crossed-derivation lift group `ℤ₂(χ) ⋊ ℤ₂ˣ` so `d0LiftHom` can land in it |
| `chiD0G : ContinuousMonoidHom (D0) ℤ_[2]ˣ` | :293 | group-level canonical orientation `= chiD0 ∘ abMk`; generator values `(−1, 1, (−3)⁻¹)` at :298–303 |
| `masterH (c : Fin 3 → ℤ_[2])` (private) | :307 | **master crossed derivations**: for each `c`, a hom `D₀ → WordLift` over `χ₀` with prescribed derivation values |
| `masterContract` (private) | :355 | contracts the three basis masters by `c` (product rule) |
| `masterMod2 : (D0) →* Multiplicative (Fin 3 → ZMod 2)` (private) | :406 | mod-2 reduction — the "generation engine" |
| `evalMatrix f : Matrix (Fin 3) (Fin 3) ℤ_[2]` (private) | :484 | `M i j = Dⱼ(f(genᵢ))` at `![drS, drX, drY]` |
| `isUnit_evalMatrix` (private) | :524 | mod-2 rows span 𝔽₂³ (via `mem_closure_image_gens`) ⇒ `det ∈ ℤ₂ˣ` (Nakayama) |
| **`isLabuteOrientation_comp_iso (f : D_R ≃ₜ* D₀)`** | :576 | **orientation functoriality**: `χ₀ ∘ f` is a Labute orientation of `D_R`, for *every* iso `f` |
| `pairMod2`, `coordMatrix f : Matrix (Fin 2) (Fin 2) ℤ_[2]`, `isUnit_coordMatrix` | :837, :873, ~:930 | the `(S̄₀, Ȳ₀)`-coordinate matrix of `(f(s), f(x))` and its invertibility |
| `unitsMod16`, `chiSqHom`, `etaYHom` (private) | :718, :670, :678 | the **τ₂-is-odd** mod-16 argument: `X² = (η²)^{τ₂}`, `X ≡ 5 (mod 16)` |
| `exists_correction f` (private) | :980 | solves `σᵢ·u + τᵢ·b = ν_R(genᵢ)` with `u ≡ 1 (mod 2)` |
| **`exists_matching_iso (hex : Nonempty (D_R ≃ₜ* D₀))`** | :1112 | **the keystone**: produces `F` with the three `sHom`-marking equations |
| `nuUrBar_symm_eq_sHom` | :1145 | the `prop_1_1` ↔ `sHom` density bridge |

Rank-genericity verdict: the *proof strategy* (masters → mod-2 span → invertible evaluation
matrix → solve → contract → pull back) is dimension-agnostic and ports to `Fin 4`; the *code*
is not parameterized over rank at all.

## 2. The rank-three route: classify on the abelianization, then lift

**(a) Classify** — `GQ2/AnabelianBridge/Classification.lean`
- Binder `ξ : ContinuousMulEquiv (topAbelianization D₀) (topAbelianization D₀)` at :151;
  `B : BDecomposition` at :73.
- **`SectionThree.prop_3_8_classification`** at :342: every continuous χ₀-preserving `ξ` of
  `B = D₀^ab` is `α_{u,b}` for a **unique** `(u,b) ∈ ℤ₂ˣ × ℤ₂` — rows `Ā ↦ (1, −2u, 0)`,
  `S̄ ↦ (0, u, 0)`, `Ȳ ↦ (0, b, 1)` in `B.e`-coordinates.
- Supporting row lemmas: `xi_S_row` :305, `xi_Y_row` :320, `chi_row_extract` :214,
  `eta_pow_mod4` :178, `xi_fixes_t` :161, `sBar` :76 / `sBar_injective` :91.
- The coordinate frame is `BDecomposition` (`GQ2/SectionThree.lean:422`):
  `D₀^ab ≅ Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])` — torsion × `S̄` × `Ȳ`. **This 3-coordinate
  frame is the single most rank-specific object in the whole route.**

**(b) Lift** — `GQ2/AnabelianBridge/Construction.lean` (1126 lines)
- `psiHom` :580 / `psiEquiv` :679 (the `Ψ_u` scaling automorphism, built from the peripheral
  identity), `thetaHom` :880 / `thetaEquiv` :929 (the shear `Θ_b`, paper (19)).
- **`SectionThree.prop_3_8_lift (u : ℤ_[2]ˣ) (b : ℤ_[2])`** at :1089: produces
  `Ψ : ContinuousMulEquiv D₀ D₀` realizing exactly the three classification rows. Proof is
  `(thetaEquiv b').trans (psiEquiv R u)` with `R := peripheralCyclotomicAction` (:1094).
  ⚠ This lift depends on **B8** (`peripheralCyclotomicAction`) because D₀'s scaling
  automorphism comes from the anabelian peripheral identity. The rank-four cores are *presented*
  groups, so their lifts should be built directly on the presentation (the D_R-style route),
  with no B8 dependence expected.

**(c) Where Labute enters** — `GQ2/Roe/MarkedPro2.lean`
- **Not an axiom.** `BLabHypothesis : Prop` is a plain `def` at :141 inside `section Draft`
  (:106–149): "Demushkin, rank 3, q = 2, surjective Labute orientation ⇒
  `Nonempty (ContinuousMulEquiv D_R D₀)`". Docstring :108–140 cites Labute Thms 4 & 8.
- Orientation predicate = descent characterization: `IsLabuteOrientationDatum (S X Y : ℤ_[2]ˣ)`
  at `GQ2/Roe/CrossedDerivation.lean:183`; `IsLabuteOrientation χ` at :192; unpacked to four
  scalar equations by `isLabuteOrientationDatum_iff` :201 (`Y² = X⁴ ∧ cxR = 0 ∧ csR = 0 ∧ cyR = 0`).
- **`markedPro2_R`** at `MarkedPro2.lean:163` takes `(R : LocalReciprocity)
  (hBLab : BLabHypothesis)` and produces the marked identification `G_{ℚ₂}(2) ≅ D_R` with
  `ν`-matching. Four-step proof :170–210: B-Lab iso → `exists_matching_iso` → `dr_topGen`
  density → `prop_1_1` composition.
- `nuDR` :87 (values `(1,0,0)`), `nuDR_surjective` :101. Consumers: `GQ2/Roe/Main.lean:232`, :565.

## 3. `GQ2/Roe/Labute/` — 8953 lines, **zero sorries**

```
Assembly.lean            281   Levelwise.lean          1570   SpanFoundation.lean  424
StageLemma.lean           85   TwoCentralTower.lean     928
StageLemma/ Congruence 500, Defect 414, DigitToolkit 341, CrossedDerivation 841,
            StageOne 857, StageTwo 385
GradedLie/  Magnus 971, SpanBase 572, SpanStep 437, SpanIdentities 312, SpanAssembly 35
```

The SL1/SL2 design gap noted in older project memory is **closed** —
`GradedLie/SpanAssembly.lean:22,29` (`span_free_r0_proof` / `span_free_r2_proof`) discharge the
span theorem. Repo-wide, all `sorry` word-matches in `GQ2/` are doc mentions; no code sorries.

**Assembly chain** (`Assembly.lean`): `drFinsetTopGen` :67, `d0FinsetTopGen` :79,
`exists_contSurj_of_levelwise_nonempty` :100 (thin wrapper over `GQ2/Reconstruction.lean`),
`finite_contSurj_quotient` :115, `sPR0_nonempty` :160 / `sPR2_nonempty` :164 (base `k₀=3` +
`stageStepR0/R2` upward + `sPR0_levelProj` downward), `nonempty_contSurj_levelQuot_r0` :174 /
`_r2` :201 (cofinality via `exists_twoCentralSeries_le`), `nonempty_contSurj_D0_DR` :228,
`nonempty_contSurj_DR_D0` :234, **`bLab : BLabHypothesis`** :249 — two epis +
`profinite_hopfian` + `continuousMulEquivOfBijective`. Docstring :49–51 records
`#print axioms bLab = [propext, Classical.choice, Quot.sound]` — **the Labute instance is
axiom-FREE**.

**Tower** (`TwoCentralTower.lean`): `twoCentralSeries G k` (1-based λ-series), `levelQuot G k`,
`zLayer G k`, `chiLevel χ k : Qₖ →* (ZMod 2^k)ˣ`, `exists_twoCentralSeries_le`,
`twoCentralSeries_units_le`. Commutator conventions documented at :46–60.

## 4. Reusable verbatim vs. rank-three-specific

**Reusable as-is (rank-generic, no edits):**
- All of `GQ2/Roe/Labute/TwoCentralTower.lean` — arbitrary topological/pro-2 `G`.
- `GQ2/Reconstruction.lean`'s König/Cantor assembly (`exists_contSurj_of_levelwise_nonempty`,
  `profinite_hopfian`, `finite_continuousMonoidHom`, `continuousMulEquivOfBijective`).
- `GQ2/Demushkin.lean` — `IsDemushkin p G` :109, `demushkinRank` :127, `demushkinQ` :224,
  `topAbelianization` :213, `IsDemushkin.card_H1_eq_pow` :168, `demushkinRank_eq_of_card` :183.
  Fully generic in `(p, G)`; rank 4 is just `card_H1 = 16`.
- `FoxH.WordLift` and `GQ2/Roe/CrossedDerivation.lean`'s `conjP_wordLift` :80 /
  `commP_wordLift` :91 — generic word-shape algebra.
- `SpanFoundation.lean`'s `map_dbarWordR0/R2` :46,52, `dbarWordR0_comm` :59, `freeProTwo` +
  universal property — generic in `G`.
- Most of `GradedLie/Magnus.lean` (971 lines, generic restricted-Lie / Zassenhaus machinery).
- `GQ2/Roe/CorrectionR.lean` — already stated for arbitrary `Fin 4`-indexed markings
  (`liftMarking_wildValueR_g` :221, `corrected_wildValueR` :231, `d1FunR_base_change` :247);
  Γ_R-side (rank-4 free group), not D_R-side. **Closest existing rank-four infrastructure.**

**Rank-three-specific — needs a rank-four analogue written fresh:**
- `BDecomposition` (`SectionThree.lean:422`): the 3-coordinate frame `ZMod 2 × ℤ₂ × ℤ₂`. `M_α`
  (`A²[A,B]C₀^{2^α}[C₀,D]`) and `N_α` (`x₀^{2+2^α}[x₀,x₁][σ,x₂]`) have *different* torsion
  structure from `A²S⁴[S,Y]`, so the 4-coordinate frames are genuinely new math, not a re-index.
- `prop_3_8_classification` and its row lemmas — the `(u,b) ∈ ℤ₂ˣ × ℤ₂` normal form. Rank four
  gives a larger parameter group (a block over `ℤ₂` plus units, not a scalar+shear pair).
- `prop_3_8_lift` plus `psiHom`/`psiEquiv`/`thetaHom`/`thetaEquiv` — explicit generator-word
  automorphism constructions (for the new cores: presentation-side, Nielsen-move style).
- `evalMatrix` / `isUnit_evalMatrix` — `Fin 3 × Fin 3`, with three explicit `masterMod2_d0A/S/Y`
  basis lemmas (:492,503,514) that become four.
- `coordMatrix` / `isUnit_coordMatrix` (:873) — `Fin 2 × Fin 2`, becomes larger.
- `IsLabuteOrientationDatum` — hardwired to `drWord` (three generators); the analogue is
  per-core.
- The `τ₂`-odd mod-16 argument (:705–796) — tied to `X ≡ 5 (mod 16)` and the specific relator.
- `Levelwise.lean` (1570 lines) — every levelwise set, χ-target `(−1, 1, η)`, and the `k₀ = 3`
  base-case witnesses in `Q₃` (order 2⁸) are relator-specific. Rank-four base cases live in a
  bigger `Q₃`. (Relevant only if the owner later orders a Labute-instance discharge campaign
  for the rank-four cores.)
- `GQ2/Roe/DRDemushkin.lean` — `drCharM (v : Fin 3 → ZMod 2)` :91, `card_H1_DR = 8` :209,
  `card_H2_DR = 2` :403, the nine explicit cup entries `drCup_ss … drCup_yy` :426–463,
  `demushkinRank_DR = 3` :506. The 3×3 Gram matrix becomes 4×4 (16 entries, per core, uniform
  in α).
- `GQ2/Roe/ChiR.lean` (243 lines) — `chiR` :120, `isLabuteOrientation_chiR` :134,
  `chiR_surjective` :160, numeric pins mod 16. Relator-specific.

## 5. Axiom dependencies

- **There is no Labute axiom and no Demushkin-classification axiom** in
  `GQ2/Foundations/Axioms.lean` (9 axioms; Labute appears only in the reference list; B3c's
  docstring bundles Labute Thm 4 case (2) values for the Galois-side χ₂ — not the
  classification theorem).
- `MarkedMatching.lean` depends on **B3c** transitively: `chiD0G` :293 → `chiD0`
  (`GQ2/PropOneOneAssembly.lean:182`) → `orientBundle := dyadicOrientation` (:178).
- `prop_3_8_lift` depends on **B8** `peripheralCyclotomicAction` (`Construction.lean:824,:1094`).
- `markedPro2_R` additionally takes `LocalReciprocity` as an explicit parameter.
- **`GQ2/Roe/Labute/**` uses zero axioms** — `Assembly.lean:49–51` states
  `#print axioms bLab = [propext, Classical.choice, Quot.sound]`. `Levelwise.lean:34–35` notes
  `chiD0pres` is built from the presentation because the Galois-side `chiD0G` is
  "census-forbidden in this lane".
- `GQ2/AxiomLedger.lean:128–133` records that the Labute classification "enters those capstones
  as an explicit binder, never as an axiom".

**Implication for MC-M/MC-N:** preserve the axiom-free-lane structure. Any rank-four
Demushkin-classification input should be a per-core `def …LabHypothesis : Prop` threaded as an
explicit binder (BLabHypothesis pattern), never an axiom, with the discharge route an owner
decision (gate G-Lab). MC-M/MC-N themselves (abelian classification + lifting on the *presented*
cores) are unconditional pro-2 group theory and never need that hypothesis.
