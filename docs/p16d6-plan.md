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
* ✅ **`phase140_ofPhaseData`** (std-3, sorry-free) — the **(140) reducer**, the `lemma_8_5`/8.7
  analog of `stageR136_of`: reduces the (140) display to the two-count phase datum `hfib : zBC = μ·M`
  (the μ-fibration) + `hgauss : 2|D_T|·M = |V|·e_Γ(C) + G0·Σ_ζ(2·nPhase(phase ζ) − e_Γ(C))`
  (`lemma_8_5` aggregated), by pure algebra (`linear_combination`).  So **all three displays
  (136)/(139)/(140) now have clean reducers**; only the concrete data remains.
* ✅ **`zBC_eq_sum_centralOver`** (std-3, sorry-free) — the **`zBC` fibration** `zBC = Σᶠ_ρ
  #CentralOver(ρ)` (extracted from `half139_of`), the shared first step of both (139) and (140).
  Discharges **level 1** of the phase-module's `hfib`: `zBC = Σ_ρ #CentralOver = Σ_ρ μ·M_ρ = μ·M`.
* ✅ **`central_card_eq_reductions_mul_tcocycle`** (std-3, sorry-free) — **`hfib` level 2**, the
  per-ρ **μ-partition** at the `MLifts` level: `#{central M-lifts of ρ} = M_ρ · #Z¹(T)`, where
  `M_ρ = #(achievable central `T`-reductions)`.  Proof: corestrict `redT` to its finite range,
  `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`, each fibre `= #Z¹(T)` by `lemma_8_7_count` (via
  `subtypeSubtypeEquivSubtypeInter`), sum the constant.  The fibre-bundle-with-central-basepoint
  count — done.
* ✅ **`centralOver_card_eq_reductions_mul_tcocycle`** (std-3, sorry-free) — the same in bridge
  vocabulary, transported through `centralOver_equiv`: `#CentralOver(ρ) = M_ρ · #Z¹(T)` for
  `ρ' = rhoPrime …`.
* ✅ **`zBC_eq_mu_mul_reductionCount`** (std-3, sorry-free) — **the (140) `hfib` datum**, reduced
  to μ-independence: summing the per-ρ partition over the `C`-image and factoring out `μ` gives
  `zBC = μ · (Σ_ρ M_ρ)` from the single hypothesis `hμ : ∀ ρ, #Z¹(T)_{ρ'} = μ`.  This IS the
  `hfib` argument of `phase140_ofPhaseData`.

### The phase-module core that remains (the deep O-half)

**`hfib` is now fully reduced** to μ-independence (`zBC_eq_mu_mul_reductionCount`).  With the
whole reducer layer complete, closing (140) needs (for the concrete frame, descent case
`Descent (En.radData l h)`):

* **μ-independence** `hμ : ∀ ρ, #(TCocycle D ρ') = μ` — the source **5.15/5.16** fact that the
  crossed `Z¹_{Γ,ρ}(T)` count is the same for every lower map `ρ` (the ρ-twisted conjugation
  actions on `T` all give the same cohomology count).  Genuinely a source input — the
  `redT`-fibre count `#Z¹(T)` is `ρ`-dependent a priori.
* **`hgauss`** — `lemma_8_5` on `W =` the `V`-lift space, `Q = En.qbar`, `a_χ` from
  `exists_polar_inverse`, plus the phase-cover↔character reindex `Σ_χ sign(…) = Σ_ζ(2·nPhase − e)`
  — the same `Δ`/`phase` that **defines the witness** `(μ,G0,DT,phase)`.  Here `M = Σ_ρ M_ρ` (the
  reduction count of `zBC_eq_mu_mul_reductionCount`) is the constrained quadratic count and
  `#{central-liftable T-reductions} = N(κ_ρ,ε_ρ)` is the (135)/Prop 8.8 identity.

`hgauss` + the witness are one build (source/concrete-coupled); μ-independence is a source fact.
These are the genuinely deep O-half (not clean reducers) — a dedicated `(140) phase-module` pass.
The (140) chain is now **`phase140` ⟸ `hμ` + `hgauss` + witness**, all three isolated.

**`prop_8_9` is NOT closed** — it stays `sorry`; the three per-source inputs + the witness are
blocked (below).  The final splice `exact prop_8_9_of …` into `SectionEight.lean` is a trivial edit,
deferred until the inputs land.

## The four remaining inputs (discharge path + blocker)

| input | status | path / blocker |
|---|---|---|
| **`half139` ×2** | ◑ dischargeable modulo P-16c | `half139_via_radData` + **`lemma_8_6_local`** (✓ `G_ℚ₂`, `SectionEight.lean:1301`) / **`lemma_8_6_gammaA`** (✗ **sorry**, `SectionEight.lean:1288`, = P-16c) for `hlem86M`, + **`prop_5_16`/`prop_5_15`** (✓) for `hMcountM`.  **Only `Γ_A` is blocked, on P-16c.** |
| **`stageR136` ×2** | ✗ blocked (infra) | needs an **`RObstructionData` built from `En`** — which `Enrichment` does **not** carry (no cover-map family `coverMap_λ`, no `pair : D_Rmod →ₗ (R→+𝔽₂)`; this is the P-16d2 escalation).  Then `stageR136_ofRSepData` (P-16d2, ✓) closes it from `hsep_hom` + `hZcount` + `hE2`.  **Requires extending `Enrichment` (co-owned `SectionEight.lean` structure edit — owner sign-off) with the P-16d2 cover-map/pair fields, then constructing the datum + discharging the source residues `hsep_hom`/`hZcount` concretely.** |
| **`phase140` ×2** | ◑ **reducer landed** (`phase140_ofPhaseData`); residual = the two counts | the top-level (140) algebra is **done** — residual is the phase datum `M`/`hfib`/`hgauss` for the concrete frame: **`hfib`** the μ-fibration `zBC = μ·M` (`zBC`-fibration `RadicalEdgeBridge.lean:117` → `centralOver_equiv` → `lemma_8_7_count` over `redT`), and **`hgauss`** the `lemma_8_5` count on the `V`-descent with `Q = En.qbar`, `a_χ` from `exists_polar_inverse`, `Δ`/phase covers from Prop 8.8 (`prop_8_8_target` ✓) / `phaseFamily`.  All ingredients proved; this is the "(140) phase-module" — the largest remaining piece, coupled to the witness. |
| **witness `(μ, G0, DT, phase)`** | ✗ blocked (constructor) | no constructor from `En` exists.  `μ = Nat.card (TCocycle …)` (`lemma_8_7_count`); `G0 = gaussSum (E.qbar …)` (`SectionEight.lean:199`); `DT =` the `(T^∨)^C` scalar-dual index; `phase = phaseFamily (DeltaScalar E.dat γ δ a) …` (`AffineTLift.lean:841`/`528`/`769`).  Shared across both sources (source-independent), so built once from `En`. |

## Cross-ticket dependencies still open

* **P-16c** — `lemma_8_6_gammaA` is a `sorry` (`SectionEight.lean:1288`); blocks `half139` for `Γ_A`.
* **P-17d** — `blockEnrichment` is a `sorry` (`SectionNine.lean:572`); blocks the *concrete*
  instantiation of `prop_8_9` (§9 supplies `RF := blockFrame`, `En := blockEnrichment`), but not the
  abstract `prop_8_9` proof itself.

## `phase140` is a P-16d2-scale build: the "(140) phase-module"

Confirmed by tracing `lemma_8_5` (`SectionEight.lean:215`, the (140) Gauss engine, **proved** — the
analog of `lemma_8_4` for (136)) and `lemma_8_7_count` (`AffineTLift.lean:717`, **proved**): closing
`phase140` is not a thin reducer but a module comparable to the (136) obstruction module (P-16d2).
The (140) identity
`2·|D_T|·zBC = μ·(|V|·e_Γ(C) + G0·Σ_ζ (2·nPhase(phase ζ) − e_Γ(C)))` unfolds as a **4-level count**:

1. `zBC = Σ_ρ #CentralOver(ρ)` — the `zBC`-fibration over the `C`-image `ρ` (reuse the `hfib` step
   inside `half139_of`, `RadicalEdgeBridge.lean:117`) → `#{central M-lifts}` (`centralOver_equiv`).
2. `#{central M-lifts} = μ · #{central-liftable T-reductions}` — the `lemma_8_7_count` `μ`-fibration
   over `redT` (`μ = #(TCocycle D ρ)`, constant on the `V`-coordinate by `central_twist_iff`).
3. `#{central-liftable T-reductions} = N(κ_ρ, ε_ρ)` — the constrained quadratic count of `lemma_8_5`
   with `W =` the `V`-lift space, `Q = En.qbar`, `L` the descent, `a_χ` from `exists_polar_inverse`;
   the "central-liftable" ⟺ `Q(x)=ε ∧ Lx=κ` identity is the (135)/Prop 8.8 content
   (`prop_8_8_target` ✓, `lemma_6_21`/`6_22` ✓).
4. `Σ_χ sign(χκ+ε+Q(a_χ)) = Σ_ζ (2·nPhase(phase ζ) − e_Γ(C))` — the sign↔count reindex over the
   phase covers `phase = phaseFamily (DeltaScalar …)`, matching characters `χ ∈ V^∨` to the `D_T`
   index (the same `Δ`/`phase`/`μ`/`G0` that the **witness** defines — so `phase140` and the witness
   are one build).

**Recommended**: promote this to its own P-16d2-style sub-ticket ("(140) phase-module"): design the
`PhaseData` interface (the (140) analog of `RObstructionData`), prove `phase140_ofPhaseData` via
`lemma_8_5` + `lemma_8_7_count` + the fibration, and construct the witness `(μ,G0,DT,phase)` inside
it.  This is the single largest remaining §8 piece.

## Note — `hfg` and the B1 accounting

`hfgA` (`GammaA` t.f.g.) is a **proved** theorem (`FinitelyGenerated.lean:84`); `hfgF` (`AbsGalQ2`
t.f.g.) is **axiom B1** (`absGalQ2_isTopologicallyFinitelyGenerated`).  The board reserves B1's
*first consumption* for **P-17i** (the §9 master induction), so `prop_8_9_of` keeps `hfg` as
hypotheses rather than discharging `hfgF` (which would pull B1 into `prop_8_9`'s footprint) — an
axiom-accounting decision for the owner at splice time.  (`hhead` is `F`-dependent, so genuinely a
hypothesis.)

## To close `prop_8_9`

1. **witness** — write the `(μ, G0, DT, phase)` constructor from `En` (source-independent).
2. **`phase140`** — write the (140) assembly (the big one) as `RecursionFrame.phase140_of …`.
3. **`stageR136`** — extend `Enrichment` with the P-16d2 cover-map/pair fields (owner sign-off on the
   `SectionEight` structure edit), build the `RObstructionData`, discharge `hsep_hom`/`hZcount`.
4. **`half139`** — `half139_via_radData` + `lemma_8_6_local` (now) / `lemma_8_6_gammaA` (after P-16c).
5. Assemble the two `RecursionInputs`, call **`prop_8_9_of`**, and splice `exact …` into `prop_8_9`
   (trivial co-owned edit, done last).
