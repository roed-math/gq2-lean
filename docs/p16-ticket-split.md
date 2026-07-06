# P-16 decomposition — parallelizable sub-tickets for the §8 O-half

**Date**: 2026-07-04 · **Owner of split**: P-16 (Fable).  The P-16 F-draft and the first O-half
tranche are done (inventory below); the remaining three sorries have *heterogeneous gates*
(one un-gated, two behind P-13f), so the residue is decomposed for the parallel fleet, per the
P-13/P-15 precedent.

Project rules apply: no new `axiom`s; new theorems `#print axioms` ⊆ std-3 ∪ the sub-ticket's
**Ax** column; own files + one-line splices into `GQ2/SectionEight.lean`; **claim a sub-ticket
by marking its board row ◐ before starting**; do not `git checkout` co-owned files; parallel
sessions handle commits.

## Dependency graph

```
P-16a  central-obstruction engine ──────────┬──► P-16b  lemma_8_6_local  ─┐
  (def-layer relocation +                   │      (B6 side; un-gated)   │
   MLifts torsor / obstruction o /          │                            ├─► P-16d  prop_8_9
   affine variation)                        └──► P-16c  lemma_8_6_gammaA ┘     assembly
                                                   ▲  (candidate side)          ▲
P-13f  prop_5_15 (◐, needs P-13e) ─────────────────┴────────────────────────────┘
P-13g  prop_5_16 ── MATH COMPLETE: consume as `prop_5_16_bundle`
                    (`GQ2/LocalLiftingDuality.lean`, sorry-free, std-3+B6+B7)
```

**Runnable now:** P-16a (critical path), P-16d-skeleton (hypothesis-parameterized aux).
**Queued:** P-16b (behind a), P-16c (behind a + P-13f), P-16d-splice (behind b, c, P-13f).

## Upstream gate snapshot (2026-07-04)

* **5.16**: available NOW — `prop_5_16_bundle` has `prop_5_16`'s exact signature; import
  `GQ2.LocalLiftingDuality` (cycle-free: nothing imports `SectionEight` except the root).
  Do **not** wait for the `FoxHeisenberg.prop_5_16` splice (blocked on a statement relocation).
* **5.15**: P-13f ◐ — part (i) has one plumbing sorry; simples (ii) unblocked (5.13 quartet +
  P-13d in); dévissage (iii) = P-13e ◐.  This is the only true gate on P-16c/d.
* §7 block 7.1–7.4: **all proved** (`SectionSeven.lean` sorry-free).  6.21/6.22: **proved**
  (P-15i closed 6.21 with the restored `κ⁰_q` hypothesis — call sites supply `(dat, hdat)`).
* B6-side toolkit from P-13g, reusable: `GQ2/CupSymmetry.lean` (`cup11_comm`,
  `H0/H1/H2congr`), `dualAddEquiv : MuDual 2 A ≃+ ElemDual A` (G-equivariant from `hpair`),
  `bijective_cup` (discharges B6's one-sided-perfectness deviation).
* Axiom census is now **13** (P-13g's addition); sub-tickets here add none.

## What is already proven (P-16 parent, all std-3 unless noted)

Engines 8.4/8.5; scalar twisting; `lemma_8_2_gammaA`; `lemma_8_2_local` (amended:
`BoundaryMaps` + compactness; `pro2F`-transport, `card_char_piBd`); **`lemma_8_3`** (the
eight-lift partition (124): `fiberLiftEquiv` torsor core + two fibrations of `masterLifts` +
corestriction layer, `hfg` t.f.g. amendment); **`two_mul_card_fiber`** (the (127)/(139)
half-count core); generalized `charEquiv`/`cmhEquivFun`; file-wide `𝔽₂`-topology binder
cleanup.  Remaining sorries: `lemma_8_6_gammaA` (1385), `lemma_8_6_local` (1394),
`prop_8_9` (1584).

## Sub-tickets

### P-16a — central-obstruction engine (def-layer relocation + (a)/(b)/(c))
**Deps: none — un-gated.  Model F+O (design-sensitive: the ContCoh wiring).  Ax: ∅.**

1. **Def-layer relocation** (do FIRST; avoids the P-13g import-cycle trap).  Move
   `RadicalCoverData` (SectionEight:1305), `RadicalCoverData.NoDescent` (:1334), `MLifts`
   (:1370), `MLifts.Central` (:1375), **and `two_mul_card_fiber`** (generic, needed by b/c/d
   own-files) into a new lower file `GQ2/RadicalEdgeData.lean` (top-level `namespace GQ2`,
   `OrbitData` precedent — `docs/orbit-data-refactor.md`).  Imports = whatever the four defs'
   fields reference (inspect; the §8 proof engines are NOT needed).  `SectionEight` imports
   the new file.  Verified 2026-07-04: nothing outside `SectionEight.lean` uses these defs,
   so the move is mechanical and cycle-safe.
2. **The engine**, own file `GQ2/CentralObstruction.lean` (imports `RadicalEdgeData`,
   `CupSymmetry`, the `ContCoh` home), per the work order in
   `docs/section8-extraction.md` §"O-half work order" item 3:
   * (a) `MLifts D ρ` is a torsor under `Z¹(Γ, M, a_ρ)` (twisted 1-cocycles for the
     `ρ`-conjugation action; `M` abelian ⟹ well-defined).  Basepoint selection with the
     `MLifts = ∅ ⟹ both sides 0` branch; finiteness (`M` elementary-abelian).
   * (b) the obstruction `o : MLifts → H²(Γ, 𝔽₂) ≅ 𝔽₂`: `f` lifts through the central cover
     `p : cover ↠ B` iff the pulled-back central `𝔽₂`-extension splits — group-extension
     obstruction theory wired to `ContCoh.H2 AbsGalQ2 (ZMod 2)` (~150 ln, new).  **State the
     splitting ⟺ class-dies core reusably** (abstract continuous Γ, not `AbsGalQ2`-specific):
     `prop_8_9`'s Frattini R-stage (P-16d) is a prospective second consumer.  The abelian
     baby case is `Transgression.symm_cocycle_is_coboundary` — same shape, useful template.
   * (c) affine variation `o(f₀·φ) = o(f₀) + ℓ_q(φ)`, `ℓ_q` the (127) functional from the
     cover's quadratic form (cup-product variation, 5.10-side).
   Est ~350 ln.  Everything std-3 (B6 enters only in the b/c *consumers*).

**DONE (Fable, 2026-07-05)** — `GQ2/RadicalEdgeData.lean` (relocation incl. `CentralCover` +
`two_mul_card_fiber`) + `GQ2/CentralObstruction.lean` (~700 ln, all std-3, sorry-free).
**Design refinement (paper-faithful)**: the paper's Lemma 8.6 twists by **`T`-valued** crossed
cocycles (`q|_T = 0` is exactly why the (129) variation is *linear*), and since `T` has
exponent 2 every twist is an **involution** — the M-torsor/orbit machinery of the original
work-order sketch collapses to the flip lemma `two_mul_card_of_swap`.  Landed: `zsign` kernel
calculus, `mul_comm_z` (extraspecial commutator ledger from `hq` alone), `TComplement` +
`tComplement_nonempty`, the (128) edge (`edge`/`edgeQ`, `edge_spec/_mul/_add/_M_zero/_coset`),
`not_noDescent_of_edge_trivial` (descent construction), `TCocycle`/`twist`/`twist_twist`,
`ob` + `central_iff_ob_eq_zero` + lift-family independence, exact (129) `ob_twist` with
`f`-independent `varCoc`, and `half_count`.

### P-16b — `lemma_8_6_local` close
**Deps: P-16a (P-13g files already landed).  Model O.  Ax: B6.**
Step (d), local source: `ℓ_q ≠ 0 ⟺ NoDescent` via **B6's perfect (1,1) pairing**
(`tateDuality`, `MuDual`, `D.inv`), consuming P-13g's `dualAddEquiv` equivariance +
`bijective_cup` + `H*congr` transport; then `two_mul_card_fiber` gives the half-count.
One-line splice into `SectionEight.lemma_8_6_local`.

**DONE (Fable, 2026-07-05)** — `GQ2/RadicalEdgeLocal.lean`; `lemma_8_6_local` **proved &
spliced**, axioms = std-3 + B6 + **B7** (`card_H2_zmod2_eq_two`'s finiteness; Ax budget
updated accordingly).  Route: `exists_good_twist` in a deliberately *minimal context* — the
shifted edge `φ(γ)(s) := ε̄(ρ(γ))(γ⁻¹•s)` is an exact `Z¹(G_ℚ₂, MuDual 2 A_T)`-cocycle
(`A_T` = `Additive ↥T` with the `ρ`-conjugation action); `[φ] = 0` would give a constant
trivialization of the edge by `ρ`-surjectivity, hence descent (contradicting `NoDescent`);
B6 `perfect11` then yields `[w]` with nonzero pairing, and on the nose
`cup11Fun (muDualPairing) φ w = muNTwoEquiv.symm ∘ varCoc u_w`.  The count is closed by
P-16a's `half_count`.  **Statement amendment (documented)**: `lemma_8_6_local` gains
compactness instance binders + `hfg` (the B1-shaped t.f.g. input), per the
`lemma_8_2_local`/`lemma_8_3` precedents — needed to finitize `MLifts`
(`finite_continuousMonoidHom`).  Lean-lessons for P-16c/d: a local
`DistribMulAction _ (ZMod 2)` alongside compactness binders explodes μ₂-dual instance search
(hence the split into a minimal-context helper + a fat-context count); class-typed defs need
`@[reducible]`; `Quotient.out (c⁻¹)` needs a `(c⁻¹ : Bg ⧸ M)` ascription.

### P-16c — `lemma_8_6_gammaA` close
**Deps: P-16a, P-13f.  Model O.  Ax: B6, B7** *(plan finding: likely **∅** — see below)*.
~~Same (a)–(c) core; step (d′), candidate source: the variation runs through 5.15/5.16
(`prop_5_15` from P-13f; `prop_5_16_bundle` from `GQ2/LocalLiftingDuality.lean` — import it,
do not wait for the FoxHeisenberg splice).  Splice into `SectionEight.lemma_8_6_gammaA`.~~

**PLAN (Fable, 2026-07-05) — supersedes the sketch above.**  Scoping (Opus, on-board) was
right that this is *not* a mechanical port of P-16b: the engine `half_count` is source-generic
and needs exactly two `ContCoh`-facts about the source — `#H²(Γ_A,𝔽₂) = 2` and a `NoDescent`
⟹ nonzero-variation-class step — and neither `prop_5_15` (word complex) nor `prop_5_16`
(`AbsGalQ2`) supplies them directly.  **Correction to the sketch: `prop_5_16_bundle` is NOT
what the Γ_A side needs** (it was P-16b's tool, via `card_H2_zmod2_eq_two`); the Γ_A route is
`prop_5_15` + `trivialSelfDual` + a new *degree-≤2 comparison for the marked presentation* —
which is much cheaper than a full quasi-iso because the repo already has the whole
homs-out-of-Γ_A dictionary: `Marking.push`/`push_admissible`/`descend`/`descend_surjective`
(`Prop23.lean`), relator-death `tameRelator_mem_NA`/`wildRelator_mem_NA`, cofinality
`exists_isAdmissibleU_le` + directedness `isAdmissibleU_inf`, pro-2 tools
`isPGroup_normalClosure_image_inf` (`AdmissibleLimit.lean`), and `topGen_gammaA` (P-25).
Since both new facts are std-3-sourced, **the close is plausibly Ax = ∅** (under the B6,B7
budget).  Two new own-files; four phases, each independently landable & verifiable:

* **Phase 1 — degree-≤1 bridge** (`GQ2/WordCohBridge.lean`, ~350 ln): for the pushforward
  marking `t_ρ` of a finite quotient `q : Γ_A ↠ C` (admissible by `Marking.push_admissible`;
  `Generates` from surjectivity), continuous crossed cocycles ≃ word cocycles:
  `z1Equiv : {c : Γ_A → A // crossed, cont} ≃ Z1w t_ρ` — forward = evaluate at the 4 marked
  generators (injective by `topGen_gammaA` density + continuity); backward = a crossed cocycle
  is a hom to `WordLift A C` over `q`, produced by `Marking.descend` applied to the lifted
  marking (admissible: `liftMarking` relations ⟺ `d1 x = 0` via the §5.13 ledger; `Pro2Core`
  by central-2-extension; `Generates` by passing to the generated subgroup + include back).
  `B¹ ↔ B1w` is direct.  Corollary: `H¹(Γ_A, A) ≃+ H1w t_ρ`.
* **Phase 2 — Θ and `#H²(Γ_A,𝔽₂) ≤ 2`** (same file, ~350 ln): a continuous 2-cocycle
  `κ : Γ_A² → 𝔽₂` factors through a finite level (new small compactness lemma; cofinality
  upgrades the level to admissible).  Define `theta κ ∈ 𝔽₂² ⧸ im d1_triv` = the pair of
  relator-`z` values of a generator-lift into the finite-level `κ`-twisted central extension
  `C̃_κ`, well-defined mod `im d1_triv` (central-shift = `d1` at trivial coefficients) and
  level-independent (cofinality).  **`theta_injective`**: `theta κ = 0` ⟹ the shifted marking
  of `C̃_κ` is admissible ⟹ `Marking.descend` splits it over `Γ_A` ⟹ the splitting's
  `𝔽₂`-component is a continuous trivializer, `κ ∈ B²`.  Target size: `#(𝔽₂²/im d1_triv) = 2`
  from `trivialSelfDual` at the **trivial-group marking** (`#H2w(t, 𝔽₂) = 2`).  Hence
  `#H²(Γ_A,𝔽₂) ≤ 2`; equality follows from Phase 3's nonzero class — no separate surjectivity.
  (Reusable: Θ-injectivity is the degree-2 half of the presentation-comparison, Thm-4.2-ward.)
* **Phase 3 — the twist** (`GQ2/RadicalEdgeGammaA.lean`, ~450 ln): port
  `RadicalEdgeLocal.exists_good_twist`'s **generic prefix** verbatim for `Γ = GammaA` (the
  `act`/`φf`/`hφZ1`/`not_noDescent_of_edge_trivial` blocks use nothing about `AbsGalQ2`;
  default copy-adapt — do NOT churn the closed P-16b file).  Replace the B6 tail: bridge
  `[φf] ≠ 0` through Phase 1 (+ P-13g's `dualAddEquiv` for `MuDual 2 ↔ ElemDual`) to a nonzero
  `H1w`-class on the dual side; `prop_5_15` (at `A_T := Additive ↥D.T`, conjugation `C`-action,
  `hA₂ = D.helem`) gives the perfect pairing `P`, hence `w` with
  `mixedB t_ρ x_w y_φ ≠ 0`; pull `w` back to the `TCocycle` `u_w`.  **Crux (risk #1), the
  Θ–mixedB comparison**: `varCoc u_w` is pointwise the cup 2-cochain of `(φ, w)` (P-16b's
  `hbridge`, generic), and its `theta` is the relator-`z` **pair** of `heisMarking t_ρ x_w y_φ`
  (twisted extension = pushout of the `HeisLift` extension — a ledger identity).  ⚠ Convention
  trap, now pinned: `mixedB` is the **traced sum** `tame.z + wild.z`, while the `H2w`-class
  detector is the pair mod `im d1_triv = span{(1,0)}` (τ-column; forced by `#H2w = 2`), i.e.
  the **wild** coordinate alone — the sum functional does *not* kill `im d1_triv`.  They agree
  exactly on σ/τ-slot-free representatives (`heisMarking_tameValue_z_eq_zero` needs
  `x 0 = x 1 = 0`, `y 0 = y 1 = 0`).  Resolution: run the §5.13 normal-form apparatus
  (x₀-supported representatives, as `lemma_5_13_pairing_*` already does) so tame-`z` = 0 and
  `mixedB = wild-z = Θ-detector`; fallback if the normal forms fight: derive the wild-`z`
  functional's nondegeneracy directly from `IsSelfDual`'s clauses (the tame-`z` term is itself
  a lower-complexity pairing).  Conclusion: `theta [varCoc u_w] ≠ 0`, so by Θ-linearity
  `varCoc u_w` is not a continuous coboundary — `hvar` ✓, and `#H² = 2` ✓ (with Phase 2).
* **Phase 4 — assembly + splice** (~80 ln): `half_torsor_gammaA` — `Finite (MLifts D ρ)` from
  `topGen_gammaA` + `finite_continuousMonoidHom` (**no `hfg` amendment needed**, unlike the
  local side; `GammaA` is a `ProfiniteGrp`, compactness instances exist), then `half_count`.
  One-line splice into `SectionEight.lemma_8_6_gammaA` (claim the co-owned row first).  Gate:
  `lake build` + `check_axioms` (census 13) + `#print axioms` — expect **std-3 only**.

Risks: (R1, main) Phase 3's Θ–mixedB ledger identity + normal-form grind — bounded, all
tooling exists (`HeisLift`, `heisMarking_*_z` lemmas, `lemma_5_13` unique representatives);
(R2, low) the finite-level factorization lemma for continuous 2-cocycles (~60 ln compactness);
(R3, low) instance juggling for the conjugation module (P-16b's `letI` pattern reusable).
Estimated 3–4 focused sessions; Phases 1+2 are self-contained wins (the presentation-comparison
is reusable beyond §8).

**P-16c sub-sub-tickets (2026-07-05 decomposition; board rows P-16c1–c5).**  Phase↔row
mapping: c1 = Phase 1, c2 = Phase 2, c3+c4 = Phase 3 (the Θ–mixedB crux isolated in c4 so the
grind rows parallelize around the risk), c5 = Phase 4.  All rows Ax ∅ (expected).

```
P-16c1 (deg-≤1 bridge z1Equiv/h1Equiv + lifted-marking-admissibility helpers)   [startable now]
   ├──► P-16c2 (θ: finite-level relator evaluation + θ-injective ⟹ #H²(Γ_A,𝔽₂) ≤ 2)
   ├──► P-16c3 (twist: generic exists_good_twist prefix + prop_5_15 pairing ⟹ w, mixedB ≠ 0)
   │              [c2 ∥ c3 once c1 lands; c3 also needs P-16a ✓]
   c2 + c3 ──► P-16c4 (Θ–mixedB comparison ⟹ [varCoc u_w] ≠ 0)          [⭐⭐⭐ the risk row]
   │
   c2 + c4 ──► P-16c5 (half_torsor_gammaA + splice)  ──► unblocks P-16d3's gammaA instance
```

* **c1** is the shared root (both lanes) and needs nothing unlanded — the natural first session.
* **c2**'s θ-injectivity and **c1**'s `h1Equiv` are the reusable presentation-comparison halves
  (degree ≤ 2), wanted again Thm-4.2-ward — they are worth landing even independently of 8.6.
* **c4** carries the plan's single real risk (the traced-SUM vs WILD-z convention, resolution on
  §5.13 x₀-supported normal forms; fallback in the plan text above).
* **c5** is the sink: one-line splice + gate; expected `#print axioms` = std-3 only.

### P-16d — `prop_8_9` assembly (eqs. (136)–(142))
**Deps: P-16b, P-16c, P-13f (7.1 ✓ proved).  Model O.  Ax: B6, B7, B9.**
**Skeleton is runnable NOW** (the P-15f-against-P-15e pattern): own file
(`GQ2/ClosedRecursion.lean`), aux theorem `prop_8_9_aux` taking the two 8.6 conclusions (and,
until P-13f lands, `prop_5_15`'s statement) as explicit hypotheses; assemble per the paper's
proof — unrestricted `M`-stage (5.15/5.16 + 7.1), Frattini argument for the final `R`-stage
torsor (candidate reuse of P-16a(b)'s core), `lemma_8_4` for (136), `lemma_8_5` + Prop 8.8 for
(140), shared witness `(μ, G⁰, D_T, phase)`; `eq139` reuses `two_mul_card_fiber`.  Splice when
b/c/P-13f land.

**SKELETON LANDED (Fable, 2026-07-05).**  In tree, all std-3 sorry-free:

* `GQ2/FrattiniNongen.lean` — `frattiniLike_nongen` (Φ-nongeneration for finite 2-groups:
  proper subgroups sit under an index-2 coatom, whose `ℤ/2`-quotient swallows squares and
  commutators; consumes P-21's `coatom_normal_of_pGroup`/`coatom_index_of_pGroup`) and
  `eq_top_of_map_frattini_quotient_top` — the paper's (136) automatic-surjectivity of
  `R`-lifts (`J ⊔ R = ⊤` from the quotient image, elementwise Dedekind `K = (J ⊓ K) ⊔ R`
  via `Subgroup.mul_normal`, then nongeneration).
* `SectionEight.RecursionInputs` + `prop_8_9_aux` — the assembly step: **eq138 is proved**
  (direct `lemma_8_3` instantiation at each scalar cover, under `lemma_8_3`'s own side
  conditions `hfg`/`hscalar`, satisfied by both real sources); the other four displays are
  typed input-slots with their suppliers documented in the structure docstring.

**P-16d sub-sub-tickets (2026-07-05 decomposition; board rows P-16d1–d6).**  Items 1–2 of
the original work order are closed: `stageR136_of` (combinatorial core; residue → P-16d2)
and `partition137_of` (**(137) fully discharged in `prop_8_9_aux`**, after the two
documented statement corrections — `zBC` re-encoded to the `∃`-lift form, (137)'s sum
restricted to `J ↠ C`; see the deviation ledger in `docs/section8-extraction.md`).

```
P-16d1 (frame enrichment: per-λ RadicalCoverData + κ⁰_q/6.3 datum)
   ├──► P-16d3 (zBC↔MLifts bridge + half139) ◄── P-16c (gammaA 8.6) ◄── P-13f
   ├──► P-16d4 (state+prove 8.7, 8.8/(135))
   │        └──► P-16d5 (witness μ,G⁰,D_T,phase; needs 8.7's e-class)
   └──────────────┐
P-13f ─► P-16d2 (R-stage obstruction module for stageR136_of; local numerics via 5.16 ✓)
                  │
   d2 + d3 + d4 + d5 ──► P-16d6 (phase140 + final two-source splice)

P-16d6 sub-split (2026-07-06; reducer+engine layer DONE in GQ2/RecursionSplice.lean —
                  spec: docs/p16d6-concrete-spec.md; rows P-16d6a–e in docs/tickets.md):
   d6a ((136) R-stage: Enrichment extension + hsep_hom/hZcount/hE2) ──────────┐
   d6b ((140) μ-independence) ──► d6c ((140) Prop-8.8 core: hM/hphase/witness)┼──► d6e (assembly
   d6d ((139)/G_ℚ₂ via lemma_8_6_local ✓) ────────────────────────────────────┤     + prop_8_9
   P-16c (lemma_8_6_gammaA → (139)/Γ_A) ──────────────────────────────────────┘     splice)
```

* **d1** ☑ **DONE (Fable 2026-07-05)**: derived layer facts (`MB_*`/`TBsub_*`/`ker_piBC`/
  `piBC_surj`), `RecursionFrame.Enrichment` + `radData` (+ `Iff.rfl` NoDescent bridge),
  `mForm_of_qbar` in new `GQ2/FrameEnrichment.lean` (all std-3).  ⚠️ `prop_8_9` amended
  with `(En : RF.Enrichment)` — deviation ledger #3 in `docs/section8-extraction.md`.
* **d3** ☑ **DONE (Opus 2026-07-05)**: `GQ2/RadicalEdgeBridge.lean` (sorry-free, std-3) —
  `half139_of` (fibre `zBC` over `ρ`, sum) + `liftsOver_equiv`/`centralOver_equiv` (the
  `MLifts` transport).  Source-generic: `hlem86` (Lemma 8.6) + `hMcount` (5.15/5.16) enter as
  hypotheses, so **no P-13f needed in d3**; d6 plugs the source's 8.6 + the numerics.
* **d4** ☑ **DONE (Fable F-plan + Opus O-close, 2026-07-05)**: `GQ2/AffineTLift.lean`
  (sorry-free, all std-3, Ax ∅) — `descended_splitting` (6.21 via the descended-cover
  `ξ`-cocycle), `central_twist_iff`+`tcocycle_torsor_equiv`+`lemma_8_7_count` (the `μ`
  fibration), `prop_8_8_target` (6.22 shear), `exists_polar_inverse`; SectionEight exports
  `headBC`/`thetaBC`/`isBoundaryLift_of_over`.  Two review-flagged deviations (8.7
  cocycle-level, 8.8 target-side/6.22-`Δ`) in the ledger.  Plan: `docs/p16d4-plan.md`.
* **d5** ☑ **DONE (Opus 2026-07-05)**: `centralCoverOfCocycle` (the twisted product
  `𝔽₂ ×_δ C₀` as a `CentralCover`) + `phaseFamily` in `GQ2/AffineTLift.lean` (std-3).
  The shared witness `(μ, G⁰, D_T, phase)` is now fully constructible; its assembly +
  the `eq140` proof (μ source-independence = P-13f) is the d6 splice.
* **d6** is the sink: everything, plus P-16c/P-13f through the gammaA lane.

**Original work-order notes (superseded by the rows above, kept for the technical detail):**
1. `stageR136` — **combinatorial core DONE (Fable, 2026-07-05)**: `RecursionFrame.liftB`
   (the `π_B`-fibration map on boundary lifts) and **`stageR136_of`** (std-3) derive the
   full (136) display from an **obstruction-module datum**: `(W, o, e : D_R ≃ W^∨)` with
   `e 0 = 0`, `hmB` (the `λ`-pushout ↔ `λ`-cover-liftability count match), `hobs`
   (`o = 0` detects liftability to `Y`), `hfib` (liftable fibres have size `z_R`).
   Proof: `liftB`-fibration (`sigmaFiberEquiv` + per-fibre `hfib`/empty), `lemma_8_4` ✓
   Fourier, character-sum reindex along `e`.  **Sharpened residue** (what remains of item
   1): construct `(W, o, e)` for the concrete `R`-stage — the `R`-obstruction module with
   its `D_R`-duality (this is where "`R` elementary + `D_R = (R^∨)^C`" enters; note
   `RecursionFrame.DR` is a bare `Fintype`, so the linear structure must come with the
   datum, exactly as packaged) — plus `hfib` from the 5.15/5.16 `Z¹`-numerics and the
   boundary-pinned torsor count (the surjectivity half is `eq_top_of_map_frattini_quotient_top` ✓).
2. `partition137`: image-fibration of the `zBC` pair-count (masterLifts pattern from
   `lemma_8_3`'s proof).
3. `half139`: build `RadicalCoverData` from the frame at each nonzero `λ` (needs the §7.4
   square-form data on `M_B` — the `q`/`hq`/`hrad`/`hTzero` fields), bridge `zBC` to
   per-`f` `MLifts`-counts, consume `lemma_8_6_local` ✓ / `lemma_8_6_gammaA` (P-16c).
4. `phase140`: state + prove Lemma 8.7 (affine `T`-lifting) and Prop 8.8/(135)
   (completed-square), then the 8.5 ✓ + 6.21 ✓ chain.
5. Witness `(μ, G⁰, D_T, phase)`: `μ` from the 5.15/5.16 numerics (P-13f), `G⁰` from the
   proved `prop_7_4` Gauss form, `D_T`/`phase` from the (134) `Δ_{χ,κ}`-covers.
6. Final: apply `prop_8_9_aux` twice (both sources) inside `prop_8_9`; discharge the
   side-conditions from `lemma_8_2`-side data.

## Board rows (spliced into `docs/tickets.md`)

| ID | Title | Diff | Model | Deps | Ax | Status |
|---|---|---|---|---|---|---|
| P-16a | B: §8 central-obstruction engine (def-layer → `RadicalEdgeData`; MLifts torsor, obstruction `o`, affine variation) | ⭐⭐⭐ | F+O | — | ∅ | ☑ DONE (Fable 2026-07-05) |
| P-16b | B: `lemma_8_6_local` close ((d) via B6 + P-13g toolkit + `two_mul_card_fiber`) | ⭐⭐ | O | P-16a | B6, B7 | ☑ DONE (Fable 2026-07-05) |
| P-16c | B: `lemma_8_6_gammaA` close ((d′) via `prop_5_15` + `prop_5_16_bundle`) | ⭐⭐ | O | P-16a, P-13f | B6, B7 | ☐ |
| P-16d | B: `prop_8_9` assembly (136)–(142) (skeleton vs hypotheses now; splice on b/c/P-13f) | ⭐⭐⭐ | O | P-16b, P-16c, P-13f | B6, B7, B9 | ☐ |
