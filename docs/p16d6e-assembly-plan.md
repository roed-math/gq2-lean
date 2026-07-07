# P-16d6e — assembly plan and statement-amendment record (Fable 5, 2026-07-07)

The authoritative execution plan for closing `prop_8_9` (= P-16). Supersedes the scattered
d6e notes on the board where they conflict.

---

## 1. TWO REVIEWED STATEMENT ACTIONS on `prop_8_9`

### (A) The phase family becomes per-λ  ⚠ paper-faithfulness fix (Bug-3 of the c-lane family)

The paper's phase classes are `Δ_{χ,κ}` (p. 42, (134)) with `κ = κ_λ` **the scalar-pushout
class of the λ-cover** — the boxed (140) is a per-λ display whose phase covers depend on λ.
The Lean `ClosedRecursion`/`prop_8_9` as drafted fix ONE family `phase : DT → CentralCover
RF.YC` shared across all λ; with that reading, (140) at two zero-edge λ's with one family
forces `zBC`-l-independence — a fact the paper neither states nor uses (the master count
transfers the λ-dependence into the phase-sign aggregate; per-(χ,ρ) signs are NOT
λ-independent, e.g. the `Q_κ(0)`-term of (135) at `b = 0` is the lifting obstruction of ρ
through the λ-cover). Fix: `phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC`
in `ClosedRecursion`, `RecursionInputs`, `prop_8_9_aux`, `prop_8_9`, `prop_8_9_of`, and the
(proved) `count_eq_of_closedRecursion` (whose `hphase` becomes per-λ accordingly — its
consumer, the P-17h induction, gets the per-λ covers from the same ∃-elimination; the
strict-decrease bounds (p. 44) are per-cover and unaffected).

`DT` stays shared: the paper's `D = (T^∨)^C` is λ-free, and `TCharC (En.radData l h)`
depends on the datum only through `T := RF.TBsub` and `hT := RF.TBsub_normal` — the same
literal fields for every `l` — so the types are definitionally equal across λ (`rfl`).

### (B) Specialization to the block frame + relocation

`stageR136` is only provable against the concrete frame: `blockRObstructionData`/
`blockStageR136` (P-16d6a, by decision "NO `Enrichment` edit — build against
`blockFrameImpl`") realize the R-stage obstruction theory for `RF := blockFrameImpl T Blk
hE2` and nothing else; a bare `RecursionFrame` has no axioms tying `DR`/`zR`/`mB` to
obstruction theory, so general-RF (136) is not provable (the docstring's own "junk covers"
caveat, one stage down). The only intended consumer is SectionNine's inductive branch at
`blockFrame T Blk hE2 = blockFrameImpl T Blk hE2` (P-17c) with `En := blockEnrichment`
(P-17d3). So `prop_8_9` is restated at `RF := blockFrameImpl T Blk hE2` (gaining the `hE2`
hypothesis it needs anyway — `thm_4_2` already carries it) and **relocated** to the new
capstone leaf `GQ2/Prop89Close.lean` (SectionEight.lean cannot name `blockFrameImpl`, which
sits above it; precedent: the `thm_4_2` relocation, P-17a action 2). `SectionEight.lean`
keeps a comment-pointer; the sorried general-RF form is deleted (no code consumers exist —
P-17h is not yet written).

### Hypothesis ledger of the relocated `prop_8_9`

Kept hypothesis-side (with their dischargers recorded):

| hypothesis | discharged by |
|---|---|
| `hE2 : ∀ e : E, e ^ 2 = 1` | `thm_4_2`'s standing hypothesis (P-17a) |
| `hfgF` (t.f.g. of `G_ℚ₂`) | **B1** `absGalQ2_isTopologicallyFinitelyGenerated` — first consumption reserved to P-17i |
| `hheadA`, `hheadF` (head surjectivity) | P-17h/§9 boundary data (no proved lemma; standing open hypothesis of the induction design) |
| `hsimple` (`En.Vmod` a simple `YC`-module), `hfaith` (faithful), `hVne` (nontrivial) | P-17h from the block's chief-factor structure (`blockEnrichment`'s `V`) |
| ~~`hG0indep`~~ **RESHAPED by the P-16d6e4 design** (`docs/p16d6e4-gauss-design.md` §4): `(G0 : ℤ)` + `hGaussZA`/`hGaussZF` (the per-source `∑ᶠ sign(QZero) = #V·G0` residues, (l,ρ)-uniform) + `Nontrivial RF.YC` | P-16d6e4 layer (I) + P-16d6e4a (the (83)-evaluation) + the landed pinning (`prop_6_9_unramified`/`lemma_6_8`); expected `G0 = −2^m` unramified / `+2^m` ramified; `Nontrivial RF.YC` at P-17h from the block's nontrivial simple head |

`hfgA` is discharged internally (`gammaA_topologicallyFinitelyGenerated`, proved);
`hscalar` internally (`lemma_8_2_*`); `hRK`/`hR2` internally (`lemma_7_2` at
`π := T.piY`, `cH := F.alpha`). Conclusion gains `0 < Nat.card DT` (P-17i; free —
`0 ∈ TCharC D`).

Residues that stall may be promoted to this ledger with an open ticket; the current build
plan expects to **prove**: the per-source (140) residues (`hsep`, `hpartial`, `hZcard`,
`hGaussZ`, `hH2`, `κ_M`, `κ_I`) and the Γ_A (136) residues (`hZcount_A`, `hsep_hom_A`).

---

## 2. File layout

* **`GQ2/Phase140Assembly.lean`** (P-16d6e2, source-generic): `descDataOfEnrichment`
  (`Enrichment → DescData (En.radData l h)`; 1:1 fields, `ker_piBC` for `hkerC0`),
  `phaseChi` (the per-(l,h) family `ζ ↦ centralCoverOfCocycle (DeltaChi S Dsc hσ ζ) …`),
  the `hMobst`-derivation (master count `two_mul_card_centralImage` at
  `Δ := DeltaChi S Dsc hσ`, `sh := shChi S Dsc hσ hinvQ`, `hkey := keystone …`, composed
  with `sign_iotaB_pullCoc_eq_lift_sign` at the bundled `rho0`-hom), and
  **`phase140_from_residues`** — the `RecursionInputs.phase140`-shaped conclusion,
  parametric over `{hsep, hpartial, hZcard, hGaussZ, hH2, κ_M, κ_I}` per source.
* **`GQ2/Phase140Local.lean`** (P-16d6e3/4-local): the `AbsGalQ2` residues.
* **`GQ2/Phase140GammaA.lean`** (P-16d6e6/4-A): the `GammaA` residues.
* **`GQ2/RStageGammaA.lean`** (P-16d6e5): `hZcount_A`, `hsep_hom_A`, `stageR136_gammaA`.
* **`GQ2/Prop89Close.lean`** (P-16d6e7 capstone): relocated `prop_8_9`, witness assembly,
  the two `RecursionInputs`, splice.

## 3. Supply map (landed ✓ / lane)

| input | Γ_A | G_ℚ₂ |
|---|---|---|
| `stageR136` | P-16d6e5 (`blockStageR136` ✓ + hZcount_A/hsep_hom_A) | ✓ `stageR136_local` |
| `half139` | `lemma_8_6_gammaA` ✓ + `hMcountM_A` (P-16d6e6) via `half139_via_radData` ✓ | ✓ `half139_local` |
| `phase140` | P-16d6e2 ⊗ P-16d6e6 residues | P-16d6e2 ⊗ P-16d6e3/4 residues |
| `hfg` | ✓ `gammaA_topologicallyFinitelyGenerated` | hypothesis (B1) |
| `hscalar` | ✓ `lemma_8_2_gammaA` | ✓ `lemma_8_2_local` |
| `hhead` | hypothesis | hypothesis |
| `hH2` | P-16d6e6 (zero-edge variant needed; `card_H2_gammaA_eq_two` carries a `NoDescent` crutch) | ✓ `card_H2_zmod2_eq_two` |
| `κ_M` (#MLifts) | P-16d6e6 (d6d-analog via `prop_5_15`) | ✓ `hMcountM_local` |
| `κ_I` (#red_T-image) | P-16d6e6 | P-16d6e3 (note `κ_I = κ_M / μ₀` via `mlifts_card_eq_image_mul_tcocycle` — derive, don't re-count) |
| `μ` l-indep | ✓ `tcocycle_card_l_indep` (En-level, source-free) | same |
| `G0` l-indep | `hG0indep` hypothesis (ledger) | same |
| `hGaussZ` | P-16d6e4 (I) + P-16d6e4a | P-16d6e4 (I) + P-16d6e4a |

## 4. Honest gap list (deep lanes)

1. **`hGaussZ`** (P-16d6e4): `Σ_{c ∈ Z¹} sign(Q⁰(c)) = #V · gaussSum(q̄)` — the paper's
   (126)-step. Route: `Q⁰` is `B¹`-invariant (coboundary-shift of the graph pullback =
   `lemma_6_14`-style `B²`-difference) ⟹ sum over `Z¹` = `#B¹ ·` (sum over a transversal);
   then the transversal-Gauss = `gaussSum(q̄)` pinning. Re-read paper p. 41 before starting.
2. **Γ_A degree-2 word↔continuous bridge** (P-16d6e5/6): needed for `hsep_hom_A` and the
   zero-edge `hH2_A` nonzero class. `card_H2_gammaA_le_two` (continuous ≤ 2) is landed; the
   missing direction is producing a nonzero **continuous** class without the `NoDescent`
   crutch, plus the twisted `R`-coefficient separation. Fallback: promote `hsep_hom_A` (and
   `hH2_A`) to the hypothesis ledger and keep P-16d6e-A open.
