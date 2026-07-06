# P-16d6 — the Prop 8.9 two-source splice: status + the remaining blockers

**Ticket**: P-16d6 (`docs/p16-ticket-split.md`).  Prove `GQ2.SectionEight.prop_8_9`
(`SectionEight.lean:2143`, currently `sorry` at 2151): for both sources `B.bA` (`Γ_A = GammaA`) and
`B.bF` (`G_ℚ₂ = AbsGalQ2`), a shared witness `(μ, G0, DT, phase)` and `ClosedRecursion` each.
**Owner** Opus, 2026-07-06.

## Route

`prop_8_9_aux` (`SectionEight.lean:2002`, **proved**) turns a per-source `RecursionInputs` bundle
(`stageR136` + `half139` + `phase140`; `(137)`/`(138)` are discharged inside from `partition137_of`
+ `lemma_8_3`) into `ClosedRecursion`.  So `prop_8_9` = witness + two `RecursionInputs` + per-source
`hfg`/`hscalar`/`hhead`.

## Landed (this pass) — `GQ2/RecursionSplice.lean` (leaf, off co-owned `SectionEight.lean`)

* ✅ **`prop_8_9_of`** (std-3, sorry-free) — the splice **backbone**: reduces `prop_8_9`'s conclusion
  to the witness + two `RecursionInputs` + `hfg`/`hhead` per source, via `prop_8_9_aux` ×2.
  **`hscalar` discharged internally** (`lemma_8_2_gammaA` / `lemma_8_2_local`, both proved).
  Instance args `[CompactSpace/TotallyDisconnected/IsTopologicalGroup]` for `GammaA`/`AbsGalQ2`
  (these are per-decl instances, not global — `prop_8_9`'s section supplies them, so the final
  splice will too).
* ✅ **`half139_via_radData`** (std-3, sorry-free) — strips the P-16d3 bridge plumbing
  (`centralOver_equiv`/`liftsOver_equiv` over `En.radData l h`) off `half139`, reducing it (BOTH
  sources) to the two pure `MLifts`-level source facts for `ρ' = rhoPrime …`:
  `hlem86M : 2·#{central M-lifts} = #(M-lifts)` and `hMcountM : #(M-lifts) = |M_B|²`.

**`prop_8_9` is NOT closed** — it stays `sorry`; the three per-source inputs + the witness are
blocked (below).  The final splice `exact prop_8_9_of …` into `SectionEight.lean` is a trivial edit,
deferred until the inputs land.

## The four remaining inputs (discharge path + blocker)

| input | status | path / blocker |
|---|---|---|
| **`half139` ×2** | ◑ dischargeable modulo P-16c | `half139_via_radData` + **`lemma_8_6_local`** (✓ `G_ℚ₂`, `SectionEight.lean:1301`) / **`lemma_8_6_gammaA`** (✗ **sorry**, `SectionEight.lean:1288`, = P-16c) for `hlem86M`, + **`prop_5_16`/`prop_5_15`** (✓) for `hMcountM`.  **Only `Γ_A` is blocked, on P-16c.** |
| **`stageR136` ×2** | ✗ blocked (infra) | needs an **`RObstructionData` built from `En`** — which `Enrichment` does **not** carry (no cover-map family `coverMap_λ`, no `pair : D_Rmod →ₗ (R→+𝔽₂)`; this is the P-16d2 escalation).  Then `stageR136_ofRSepData` (P-16d2, ✓) closes it from `hsep_hom` + `hZcount` + `hE2`.  **Requires extending `Enrichment` (co-owned `SectionEight.lean` structure edit — owner sign-off) with the P-16d2 cover-map/pair fields, then constructing the datum + discharging the source residues `hsep_hom`/`hZcount` concretely.** |
| **`phase140` ×2** | ✗ blocked (assembly) | all ingredients **proved** — `lemma_8_7_count` (`AffineTLift.lean:717`), `lemma_8_5` (`SectionEight.lean:215`), `prop_8_8_target` (`AffineTLift.lean:534`), `exists_polar_inverse` (`AffineTLift.lean:573`), `lemma_6_21`/`lemma_6_22` (`SectionSix.lean:964`/`1011`), `cor_5_17_card` (✓) — but the **gluing into the (140) identity is not written**.  This is the hardest input: fibre `zBC ≃ {central M-lifts}` (`centralOver_equiv`) → `lemma_8_7_count` (μ-fibration over `V`) → `lemma_8_5` on `W = Z¹(V)` with Prop 8.8's `Δ` + `exists_polar_inverse`'s `a_{χ,κ}` + the `phaseFamily` covers, summed over lower exact-image maps, cor 5.17 for the Γ-level (135). |
| **witness `(μ, G0, DT, phase)`** | ✗ blocked (constructor) | no constructor from `En` exists.  `μ = Nat.card (TCocycle …)` (`lemma_8_7_count`); `G0 = gaussSum (E.qbar …)` (`SectionEight.lean:199`); `DT =` the `(T^∨)^C` scalar-dual index; `phase = phaseFamily (DeltaScalar E.dat γ δ a) …` (`AffineTLift.lean:841`/`528`/`769`).  Shared across both sources (source-independent), so built once from `En`. |

## Cross-ticket dependencies still open

* **P-16c** — `lemma_8_6_gammaA` is a `sorry` (`SectionEight.lean:1288`); blocks `half139` for `Γ_A`.
* **P-17d** — `blockEnrichment` is a `sorry` (`SectionNine.lean:572`); blocks the *concrete*
  instantiation of `prop_8_9` (§9 supplies `RF := blockFrame`, `En := blockEnrichment`), but not the
  abstract `prop_8_9` proof itself.

## To close `prop_8_9`

1. **witness** — write the `(μ, G0, DT, phase)` constructor from `En` (source-independent).
2. **`phase140`** — write the (140) assembly (the big one) as `RecursionFrame.phase140_of …`.
3. **`stageR136`** — extend `Enrichment` with the P-16d2 cover-map/pair fields (owner sign-off on the
   `SectionEight` structure edit), build the `RObstructionData`, discharge `hsep_hom`/`hZcount`.
4. **`half139`** — `half139_via_radData` + `lemma_8_6_local` (now) / `lemma_8_6_gammaA` (after P-16c).
5. Assemble the two `RecursionInputs`, call **`prop_8_9_of`**, and splice `exact …` into `prop_8_9`
   (trivial co-owned edit, done last).
