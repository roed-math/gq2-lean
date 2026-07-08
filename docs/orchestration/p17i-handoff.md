# P-17i handoff — the §9 master induction (`thm_4_2`)

**Ticket:** P-17i — prove `GQ2.thm_4_2` (Theorem 4.2, the boundary-framed exact-image
equality) by strong induction on the marked 2-kernel size.
**Deliverable:** fill the **one** `sorry` at [`GQ2/SectionNine.lean:1713`](../GQ2/SectionNine.lean).
**Companion (authoritative design):** [`docs/section9-extraction.md`](section9-extraction.md)
§"Work order → P-17i" (lines 277–306) and the sub-ticket DAG.
**Status as of 2026-07-08 (Fable 5):** the two easy induction lanes rest on finished
machinery; the hard lane is doubly gated (see the dependency table). Not yet claimed — mark
the P-17i row `◐` before starting.

---

## 1. TL;DR

`thm_4_2` is the sink of the whole development. Its proof is a **strong induction on
`Nat.card T.LY`** with three lanes:

| Lane | Trigger | Engine | Ready? |
|---|---|---|---|
| **Terminal** | `IsScalarStack T.LY` | `terminal_count_eq` | ✅ **fully ready** (sorry-free) |
| **M-stage** | block exists, `Blk.R = ⊥` | `mStage_partition` + `prop_5_15`/`prop_5_16_bundle` | ✅ **ready** (needs a small `R=⊥ ⟹ piB` iso transport + per-source `mult` discharge) |
| **R-stage** | block exists, `Blk.R ≠ ⊥` | `count_eq_of_closedRecursion` ← `prop_8_9` | ⛔ **gated** on `prop_8_9` (P-16d6) **and** `blockEnrichment` (P-17e) |

So you can build the induction scaffold + the terminal lane + the M-stage lane **now**; the
R-stage lane cannot close until `prop_8_9` and `blockEnrichment` are sorry-free. See §7 for
the recommended sequencing.

---

## 2. The goal

```lean
-- GQ2/SectionNine.lean:1709
theorem thm_4_2 (B : BoundaryMaps) (F : BoundaryFrame H E) {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  sorry
```

`exactImageCount b F T = Nat.card (BoundaryLifts b F T)` — the number of boundary-framed
continuous epimorphisms from the source into `Y` ([`BoundaryFrame.lean:358`](../GQ2/BoundaryFrame.lean)).
`B.bA` is the `Γ_A` source, `B.bF` is the `G_ℚ₂` source. The theorem says the two agree for
every marked target.

**Section context** (`variable`s already in scope at line 1709): `{H E : Type}` with the
`Group/CommGroup + TopologicalSpace + DiscreteTopology + Finite` bundle. **`hE2` is the P-17a
standing hypothesis** (decoration target elementary abelian 2) — *do not remove it*: the
θ-descent through the block (`lemma_7_3`) and the terminal odd-kill both require it.

**Instances you will need to thread.** `terminal_count_eq` (and hence `thm_4_2`) requires
`[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]`, and the R-stage lane also needs
the `GammaA` compact/t.d./topological-group instances (see `prop_8_9`'s binders). These are
**not** global instances in this repo (deliberately — see the `Half139Local`/`BoundaryMapsWitness`
precedent); add them as hypotheses/instance-binders on `thm_4_2` if the proof needs them, OR
confirm they are already discharged where `thm_4_2` is consumed (§10 consumes it only at
`E = 0`, P-18). Check what `terminal_count_eq` demands and mirror it.

---

## 3. Dependency status (verified 2026-07-08)

**SectionNine has exactly one `sorry`** (`grep -c sorry` = 1, at line 1713 = `thm_4_2`). Every
other §9 interface listed below is already sorry-free.

### Ready — use directly

| Interface | Location | Role |
|---|---|---|
| `terminal_count_eq` | `SectionNine.lean:962` | terminal lane (P-17b3 ☑, std-3) |
| `mStage_partition` | `SectionNine.lean:1411` | M-stage partition (P-17f ☑) |
| `count_eq_of_closedRecursion` | `SectionNine.lean:1595` | R-stage solver (P-17h ☑) |
| `blockFrame` / `blockFrameImpl` | `SectionNine.lean:1390` / `BlockFrameImpl.lean:28` | the concrete `RecursionFrame` (P-17c ☑) |
| `card_LB_lt` / `card_LC_lt` | `BlockFrameBounds.lean:146` / `:155` | B/C-stage IH bounds (P-17g ☑) |
| `card_stratum_LB_lt` / `card_stratum_LC_lt` | `BlockFrameBounds.lean:222` / `:271` | (148)/(153) stratum IH bounds (P-17g ☑) |
| `card_LB_mul` | `BlockFrameBounds.lean:140` | `|L_TB|·|R| = |L_Y|` (Lagrange) |
| `exists_minimalBlock` | `SectionSeven.lean:162` | produce `Blk` in the non-terminal case |
| `IsScalarStack` | `SectionSeven.lean:60` | the terminal-case predicate |
| `prop_5_15` | `DualityAssembly.lean:596` | `Z¹`/`H²` numerics ⟹ M-stage `mult` |
| `prop_5_16_bundle` | `LocalLiftingDuality.lean:515` | `mult` for the `G_ℚ₂` side |
| `lemma_8_2_gammaA`/`_local`, `lemma_8_3` | SectionEight | phase-count expansion (R-stage `hphase`) |
| **B1** `absGalQ2_isTopologicallyFinitelyGenerated` | `Foundations/Axioms.lean:121` | `hfg` for `G_ℚ₂` — **live axiom, in census** |
| `GammaA` t.f.g. | P-03 | `hfg` for `Γ_A` |

### Gated — the R-stage lane cannot close until these land

| Blocker | Location | Sorries | Owner / gating ticket |
|---|---|---|---|
| **`prop_8_9`** | `Prop89Close.lean:52` | 1 (`sorry` at :78) | P-16c/P-16d2/**P-16d6** — the `Γ_A` residue lane (`P-16d6e5/6/7`), **actively in flight** |
| **`blockEnrichment`** | `BlockEnrichment.lean:264` | 3 | via `kappa0_exists` = **P-17e** (e1/e2 ✅; e3/e4/e5 ◐) |

`prop_8_9` is the node that returns **both** `ClosedRecursion` witnesses that
`count_eq_of_closedRecursion` consumes. `blockEnrichment` is a required *input* to `prop_8_9`
(the `En` argument). So the R-stage lane needs both.

**Good news:** the P-16d6-coordination flagged in the design note is **already resolved** —
`prop_8_9`'s conclusion already carries `0 < Nat.card DT` (`Prop89Close.lean:75`), which
discharges the `hDT` hypothesis of `count_eq_of_closedRecursion`. No further statement touch-up
needed there.

---

## 4. The induction skeleton

The design note writes `induction n := Nat.card ↥T.LY using Nat.strong_induction_on
generalizing Y T`. **The single trickiest part of P-17i is setting this up correctly**,
because `Y` is a type variable carrying four instances (`Group/TopologicalSpace/
DiscreteTopology/Finite`) plus `T : MarkedTarget H E Y`, and all of them must be generalized so
the IH quantifies over *all* smaller targets, not just sub-targets of the fixed `T`.

Recommended robust idiom — strong induction on an explicit `ℕ` measure, everything after `n`
generalized:

```lean
theorem thm_4_2 (B : BoundaryMaps) (F : BoundaryFrame H E) {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  -- peel the measure so it can drive well-founded recursion
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (T.LY : Subgroup Y) = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing Y with
  | _ n IH =>
    -- IH : ∀ m, m < n → ∀ {Y'} [Group Y'] … (T' : MarkedTarget H E Y'),
    --        Nat.card T'.LY = m → exactImageCount B.bA F T' = exactImageCount B.bF F T'
    subst hn                       -- or keep hn and rewrite; either way the measure is `n`
    by_cases hstack : SectionSeven.IsScalarStack T.LY
    · -- LANE 1 (terminal)
      exact terminal_count_eq B F T hE2 hstack
    · obtain ⟨Blk⟩ := SectionSeven.exists_minimalBlock T.normal T.isPGroup_two hstack
      by_cases hR : Blk.R = ⊥
      · -- LANE 2 (M-stage): see §5.2
        sorry
      · -- LANE 3 (R-stage): see §5.3  ← gated on prop_8_9 + blockEnrichment
        sorry
```

Gotchas for the induction:
- `generalizing Y` must also generalize the instance arguments and `T`; if Lean complains,
  `revert` `T` and the instances explicitly before `induction`, or phrase the helper as
  `∀ n, ∀ {Y} [insts] (T : MarkedTarget H E Y), Nat.card T.LY = n → …` and induct on that.
- Keep `B`, `F`, `hE2`, and the `H`/`E` section data **fixed** (they don't vary in the
  recursion); only `Y`/`T`/measure move.
- Each IH application must supply a **strictly smaller** `Nat.card T'.LY`; those inequalities
  are exactly the `BlockFrameBounds.lean` lemmas.

---

## 5. Per-lane playbook

### 5.1 Terminal lane — ready

```lean
exact terminal_count_eq B F T hE2 hstack
```
`terminal_count_eq (B) (F) [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (T) hE2
(hstack : IsScalarStack T.LY) : exactImageCount B.bA F T = exactImageCount B.bF F T`. Done. The
only friction is threading the two `AbsGalQ2` topology instances (see §2).

### 5.2 M-stage lane (`Blk.R = ⊥`) — ready, modest work

Design note lines 285–290. The plan:
1. `RF := blockFrameImpl T Blk hE2`.
2. Apply `mStage_partition RF hfg b F hhead mult hmult` for **each** source `b ∈ {B.bA, B.bF}`:
   `mult * e(b, RF.TC) = ∑_{J ↠ C} exactImageCountOn b F RF.TB J`.
   - `hfg`: `Γ_A` t.f.g. (P-03) for `B.bA`; **B1** for `B.bF`.
   - `mult := 2^{2·dim M}`, discharged **per source** via `prop_5_15` / `prop_5_16_bundle`
     (design-note deviation 2 — the multiplicity is a hypothesis, both sources give the same
     `2^{2 dim M}`). This is the `hlem86`/`hMcount` house pattern (cf. P-16d3).
3. The `⊤`-stratum contributes `exactImageCountOn b F RF.TB ⊤ = e(b, RF.TB)`, and **`R = ⊥ ⟹
   piB` is an iso** ⟹ `e(b, RF.TB) = e(b, T)`. You must supply this transport lemma (or
   special-case `blockFrameImpl` at `R = ⊥`). `card_LB_mul` (`|L_TB|·|R| = |L_Y|`) gives
   `|L_TB| = |L_Y|` at `R = ⊥`, confirming `TB ≅ T`.
4. Proper strata (`J ≠ ⊤`, `J ↠ C`) have `Nat.card (…).LY < n` by `card_stratum_LB_lt` ⟹ agree
   by the IH; `e(·, RF.TC)` agrees by the IH via `card_LC_lt`.
5. With `mult` equal and every RHS term equal, cancel to get `e(B.bA, T) = e(B.bF, T)`.

No `prop_8_9`, no `blockEnrichment` — this lane is self-contained on finished machinery.

### 5.3 R-stage lane (`Blk.R ≠ ⊥`) — gated

Design note lines 291–300. The plan (do **not** start until §3's two blockers are sorry-free):
1. `RF := blockFrameImpl T Blk hE2`; `En := blockEnrichment T Blk hE2 F`.
2. Obtain the closed system:
   ```lean
   obtain ⟨μ, G0, DT, _, phase, hDT, h_A, h_F⟩ :=
     prop_8_9 B T Blk hE2 En F hfgF hheadA hheadF hsimple hfaith hVne G0₀ hGaussZA hGaussZF
   ```
   — `prop_8_9` needs a **long** hypothesis list: `hfgF` (B1), `hheadA`/`hheadF` (boundary head
   surjectivity), `[Nontrivial RF.YC]`, `hsimple`/`hfaith`/`hVne` (the block chief-factor
   structure — from `Blk.chief` + `Blk.nontrivial_action`), a `G0`, and `hGaussZA`/`hGaussZF`
   (the c3-G0 Gauss-`Z` residues, `gaussSum_qbar_l_indep_*`). Chase each from `Blk`/`En`/`F`.
3. Gather the four IH atoms:
   - `hTB` via `IH … (card_LB_lt hR)` (needs `Blk.R ≠ ⊥`);
   - `hTC` via `IH … card_LC_lt`;
   - `hpull` per `(l,h,J')`: `exactImageCountOn` on the pulled target — `dite`-split, surviving
     branch is `IH … (card_stratum_LB_lt hR …)`;
   - `hphase` per `(l,h,ζ)`: expand `RF.nPhase` via `lemma_8_3` at `phase l h ζ` over `TC`
     (side conditions `hfg`+`hscalar` from `lemma_8_2_*`), strata agree by `IH …
     (card_stratum_LC_lt …)`, cancel the `8`.
4. Close:
   ```lean
   exact count_eq_of_closedRecursion RF B.bA B.bF F μ G0 DT phase h_A h_F
     (Nat.pos_iff_ne_zero.mp hDT) hTB hTC hpull hphase
   ```

---

## 6. Interface reference (exact signatures)

`RecursionFrame` [`SectionEight.lean:1334`] — the two-stage frame. Key fields/derived defs:
`YB`,`YC` (the `Y⧸R`, `Y⧸K` quotients), `piB`,`piC`,`piBC`, `TB`,`TC` (the sub-targets),
`MB`,`TBsub` (the `K`/`(K∩S)R` images in `YB`), `DR` (scalar-character index, `Fintype`),
`zeroDR`, `scalarCover l h : CentralCover YB`; derived counts `zR`, `mB`, `mJ`, `mJOn`, `zBC`,
`nPhase`, and the fibration `liftB`.

`Enrichment` [`SectionEight.lean:1605`] — the block's quadratic/module decoration (`Vmod`,
`qbar`, `dat`/`hdat` from `kappa0_exists`, radical data). Built concretely by
`blockEnrichment` (P-17d, **3 sorries**).

`ClosedRecursion RF b F μ G0 DT phase : Prop` [`SectionEight.lean:1689`] — the boxed system:
`eq136` (top count), `eq137` (Z_{Γ,λ}(B/C) partition), `eq138` (eight-lift partition),
`eq139` (no-descent half-torsor), `eq140` (descent constrained-Gauss). `prop_8_9` produces two
of these (one per source, shared `μ,G0,DT,phase`).

`RecursionInputs` [`SectionEight.lean:1975`] — per-source input bundle (`stageR136`, `half139`,
`phase140`) that `prop_8_9_of` ([`RecursionSplice.lean:43`]) closes into `ClosedRecursion` (via
`prop_8_9_aux`, which supplies the derived `eq137`/`eq138`). This is the pattern `prop_8_9`'s
own proof (P-16d6) follows — **you do not build these in `thm_4_2`**; you consume `prop_8_9`.

`count_eq_of_closedRecursion` [`SectionNine.lean:1595`] — takes `RF`, two sources `b₁ b₂`, the
shared `(μ,G0,DT,phase)`, two `ClosedRecursion` witnesses, `hDT`, `hTB`, `hTC`, `hpull`,
`hphase`; concludes `exactImageCount b₁ F T = exactImageCount b₂ F T`. Pure arithmetic
(cancel `8`, `2·#DT`, `#DR`) — already proved; you just feed it.

`prop_8_9` [`Prop89Close.lean:52`] — see §5.3 for the argument list; **sorried** (P-16d6).
Returns `⟨μ, G0', DT, _, phase, (0 < #DT), ClosedRecursion …bA…, ClosedRecursion …bF…⟩`.

`MarkedTarget` [`BoundaryFrame.lean:303`]: fields `LY`, `normal`, `isPGroup_two`, `piY`,
`piY_surjective`, `ker_piY`, `thetaY`; derived `stratum J hJ : MarkedTarget H E ↥J`.

`BoundaryMaps` [`BoundaryFrame.lean:383`]: the `{tameA,pro2A,compatA,surjA}` + `{tameF,pro2F,
compatF,tameF_surjective,…,surjF}` bundle; derived `bA`, `bF` (the two sources).

`SectionSeven.MinimalBlock L` [`SectionSeven.lean:121`]: `S < P`, `K` with `K ⊔ S = P`,
`chief`, `nontrivial_action`; derived `R = Φ(K)`. Produced by `exists_minimalBlock`.

---

## 7. Recommended execution plan

**Two viable sequencings:**

- **(A) Wait for full closure, then assemble once.** Cleanest history. Block until *both*
  `prop_8_9` (P-16d6) and `blockEnrichment` (P-17e) are sorry-free, then write all three lanes
  and remove the sorry in one commit. Recommended if P-16d6/P-17e are close.

- **(B) Land the scaffold + lanes 1–2 now, stub lane 3.** De-risks the induction setup (the
  trickiest part) and the terminal/M-stage lanes immediately. The proof keeps **one** `sorry`
  (the R-stage branch), so `thm_4_2` stays on the `SORRY_ALLOWLIST` and the census is unchanged
  — but the hard measure/IH plumbing is validated and reviewed early. Then a small follow-up
  fills lane 3 once the gates clear. Recommended if P-16d6/P-17e are not imminent.

Either way, **the induction-setup step (§4) is the highest-risk, do-it-first item** — get the
`Nat.strong_induction_on generalizing Y T` IH shape compiling with the three `by_cases` branches
as `sorry` before touching any lane.

---

## 8. Gate & commit discipline

- **`GQ2/SectionNine.lean` is co-owned** (it holds many other agents' closed §9 lemmas). Never
  `git checkout`/revert it; edit only the `thm_4_2` proof body. Stage only your touched files.
- `SectionNine.lean` is on the `SORRY_ALLOWLIST` in `scripts/check_axioms.sh` (line 24). When
  you fully remove the `thm_4_2` sorry, **also remove `SectionNine.lean` from the allowlist** in
  the same commit (that is the "last sorry" convention).
- Axiom budget: `thm_4_2` will trace to **B1** (first real consumption of
  `absGalQ2_isTopologicallyFinitelyGenerated`) + B3c/B6/B7/B7′/B8/B9 transitively — all existing
  census axioms, **census stays 15**. Verify with `#print axioms thm_4_2`; expect no `sorryAx`
  once complete, no new axiom.
- Gate: `lake build GQ2.SectionNine` (+ `GQ2.Prop89Close`, `GQ2.BlockEnrichment` once those
  land) then `scripts/check_axioms.sh`.
- ⚠ Heavy concurrent activity on this repo — oleans get invalidated often. Rebuild the closure
  (`lake build GQ2.SectionNine`) in a quiet window and expect to retry; use `lake env lean
  GQ2/SectionNine.lean` for fast local typechecks once deps are built.

---

## 9. References

- [`docs/section9-extraction.md`](section9-extraction.md) — the authoritative design + work
  order + sub-ticket DAG (P-17b–i). Read §"P-17i" and the deviations list first.
- [`docs/p17e-kappa0-scoping.md`](p17e-kappa0-scoping.md) — the `kappa0_exists`/`blockEnrichment`
  gate (deviation 4, the Griess counterexample; why `hsimple`/`htame` were added).
- [`docs/p16d6e-assembly-plan.md`](p16d6e-assembly-plan.md) — the `prop_8_9` gate (the per-λ
  phase-family amendment feeding `eq140`).
- Paper `paper/A_Profinite_Presentation_for_G__Q_2.pdf`, §9 pp. 44–47 (Lemmas 9.1–9.4, displays
  (143)–(153), the Theorem 4.2 endgame).

---

*Handoff written 2026-07-08 (Fable 5). Verified against the tree at that time: SectionNine one
sorry (thm_4_2:1713); prop_8_9 sorried (Prop89Close:78) with `0 < Nat.card DT` already present;
blockEnrichment 3 sorries; terminal_count_eq / mStage_partition / count_eq_of_closedRecursion /
blockFrameImpl / BlockFrameBounds all sorry-free.*
