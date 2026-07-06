# P-16d6 — concrete-pass spec: the exact remaining obligations for `prop_8_9`

**Status (2026-07-06).**  The abstract reducer layer + the (140) engine discharge are **complete**
(all std-3, sorry-free, in `GQ2/RecursionSplice.lean`).  This doc is the handoff for the remaining
**concrete Prop-8.8 / source pass** — the exact hypotheses to discharge, with their `En`
instantiation, so `prop_8_9` (`SectionEight.lean:2143`, `sorry`) can be closed.

The final proof is `exact prop_8_9_of …` (co-owned `SectionEight.lean`, trivial edit, done last),
fed two `RecursionInputs` bundles (one per source `B.bA`/`B.bF`) + one shared witness.  Each
`RecursionInputs` is `⟨stageR136, half139, phase140⟩`; the three reducers below produce those fields
verbatim (conclusions already verified to match the field RHSs).

---

## 1. The witness `(μ, G0, DT, phase)` — shared, source-independent, from `En`

Build once from `En : RF.Enrichment` (frame-level, so shared across `bA`/`bF`):

| component | recipe | obligation |
|---|---|---|
| ~~`DT := Module.Dual (ZMod 2) En.Vmod` (`= V^∨`)~~ **CORRECTED (Fable 2026-07-06, P-16d6c ⚠ Bug 2): `DT := (T^∨)^C` = `fixedPts C (ElemDual T_B-model)`, dim r — the paper's phase index `D` with (140)-prefactor `2^{r+1} = 2·#D`; `Efp ≅ D^∨`** | `hDT : Nat.card (Efp^∨) = Nat.card DT` via finite double-duality | `Fintype DT` from finiteness of `T_B` ✓ |
| `G0 := gaussSum (En.qbar l₀ h₀)` | so `hG0 : gaussSum Q = G0` is **`rfl`** (with `Q := En.qbar l h`) | **`l`-independence**: `gaussSum (qbar l h)` constant in `l` (Arf invariant of the nonsingular `qbar`; all `qbar l h` share it — source 5.15/5.16 / §6 Gauss-sum content) |
| `μ := Nat.card (TCocycle (En.radData l₀ h₀) …)` | the `T`-cocycle count | **`l`-independence** + the `hμ` below |
| `phase := phaseFamily (fun ζ => DeltaScalar (En.dat l h) γ_ζ δ_ζ a_ζ) hcoc hl hr` | `AffineTLift.phaseFamily` / `centralCoverOfCocycle` | **DeltaScalar is a normalized 2-cocycle** (`hcoc`/`hl`/`hr`) — the deep phase-cover content; `γ_ζ`/`δ_ζ`/`a_ζ` are the per-character edge-killing shear of `prop_8_8_target` |

The `phase` construction is coupled to `hphase` (§2): the `Δ = DeltaScalar …` used here must be the
one in `hphase`'s sign-sum.  So the witness `phase` and `phase140`'s `hphase` are **one build**.

---

## 2. `phase140` — via `phase140_of_nonsingular` (engine done; 3 deep facts remain)

`RecursionInputs.phase140 := fun l h _hN => phase140_of_nonsingular RF b F μ G0 DT phase l h
  (En.radData l h) rfl hC_l Dsc_l htriv hfg Lin hLin (En.qbar l h) (En.hquad l h) (En.hns l h)
  κ ε (hμ l h) (hM l h) hDT (enrichment_card_Vmod RF En) rfl (hphase l h)`

with `W := En.Vmod`, `Q := En.qbar l h`, `D := En.radData l h` (`hD := rfl`).  Engine data
**already discharged**: `hquad`/`hns` (En fields), `a_χ = polarInverseL …` (internal), `hWV`
(`enrichment_card_Vmod`), `hG0`/`hDT` (`rfl`).  **Residual (per `l`, `h`, the descent case):**

* **`Lin : En.Vmod →ₗ[ZMod 2] Efp`, `hLin` (surjective), `κ`, `ε`** — the C-image linear map and
  the per-`ρ` constraint data `(κ_ρ, ε_ρ)`.  `Efp` = the `C`-stage image space; `Lin` = the
  descent-to-`C` map.  From the concrete `scalarCover`/`piBC` structure.
* **`hM l h`** — **⚠ SHAPE CORRECTED (Fable 2026-07-06, P-16d6c ⚠ Bug 1)**: as originally written
  (`#(central red_T image) = N(κρ, ερ)`) this is **unsatisfiable** — the LHS is a positive multiple
  of `#B¹_{Γ,ρ}(V) = #V` (free `B¹`-translation by `M_B`-conjugation), the RHS `≤ #W = #V` strictly.
  The true statement (and the c1s-repaired engine hypothesis) is
  `… = Nat.card W * Nat.card {x : En.Vmod // Lin x = κ ρ ∧ En.qbar l h x = ε ρ}`, with the
  `phase140_of_*` conclusions' `μ`-slot correspondingly `#W·μ` (paper (132): `μ = |B¹(V)|·|Z¹(T)|`).
  Content unchanged otherwise: the scalar-cover square relation (`En.q`/`En.hq`),
  `lemma_6_21`/`6_22`, `prop_8_8_target` (✓).  **The deep group-theory↔quadratic bridge.**
  See `docs/p16d6c-handoff.md` §⚠ + §c1 (authoritative).
* **`hphase l h : (∑ᶠ χ : V^∨, ∑ ρ, sign (χ (κ ρ) + ε ρ + En.qbar l h (polarInverseL … χ)))
  = ∑ᶠ ζ : DT, (2 * nPhase (phase ζ) − exactImageCount b F RF.TC)`** — **the character↔phase-cover
  reindex**: matches `V^∨`-characters to the `D_T`-indexed phase covers, `sign(…) = 2·nPhase − e`.
  Couples to the witness `phase`/`Δ` (§1).  **Prop 8.8 content.**
* **`hμ l h : ∀ ρ, Nat.card (TCocycle (En.radData l h) (rhoPrime …ρ)) = μ`** — **μ-independence**:
  the crossed `Z¹_{Γ,ρ}(T)` count is `ρ`-independent (the `ρ`-twisted conjugation actions on `T`
  all give the same count).  **Source 5.15/5.16.**  Needs `[Fintype (BoundaryLifts b F RF.TC)]`
  (from `hfg`).

`κ`/`ε`/`Lin`/`hLin` are concrete C-descent data; `hM`/`hphase` are Prop 8.8; `hμ` is source.

---

## 3. `stageR136` — via `stageR136_ofRSepData`  (SUPERSEDED — see `docs/p16d6a-handoff.md`)

> **UPDATE 2026-07-06:** this section's "blocked on the co-owned `Enrichment` R-stage extension"
> framing is **obsolete**.  The `RObstructionData` (`Dobs`) is built directly against the concrete
> `blockFrameImpl` (P-17c ✓) with **no `Enrichment` edit** — it is **DONE** as
> `blockRObstructionData` in `GQ2/BlockRStage.lean` (std-3), wired to (136) by `blockStageR136`.
> Only the source residues `hsep_hom`/`hZcount` (+ `htriv`/`hcard`/`hfg`, `hE2` free) remain, and
> they are supplied per-Γ at the P-16d6e assembly (Γ-specific 5.15/5.16 counts).  The authoritative,
> current spec for `stageR136` is **`docs/p16d6a-handoff.md`**; the paragraph below is kept for
> the residue statements only.

`RecursionInputs.stageR136 := stageR136_ofRSepData RF Dobs htriv hcard hfg hE2 hsep_hom hZcount`

**Blocker (infra):** needs `Dobs : RObstructionData RF`, which `Enrichment` **does not** carry.
`RObstructionData` (extends `RCoverData`) needs the **R-stage** cover-map family + the `D_R`
obstruction pairing `pair : D_Rmod →ₗ (R → 𝔽₂)` — the analog of `q`/`descend`/`qbar` but for the
`R = ker π_B` stage, which the current `Enrichment` (M_B/V side only) lacks.

**Action:** extend `Enrichment` (co-owned `SectionEight.lean` structure — **owner sign-off**) with
the R-stage fields (mirroring `q`/`hq`/`descend`/`qbar`/`hns` for `R`), then build `Dobs` from them.
Residues once `Dobs` exists: `hsep_hom` (the `(R^∨)^C`-separation, `obs g = 0 ⟹ ∃ hom lift` — the
concrete R+C-action property, **not** abstractly derivable), `hZcount` (`#RCocycle = z_R`, from
5.15/5.16), `hE2 : ∀ e:E, e² = 1` (from `lemma_7_3`), `hcard : #H²(Γ,𝔽₂) = 2`.

---

## 4. `half139` — via `half139_via_radData` (dischargeable modulo P-16c)

`RecursionInputs.half139 := fun l h _hN => half139_via_radData RF b F En l h hfg
  (hlem86M l h) (hMcountM l h)`

**Residual:**
* `hlem86M l h : ∀ ρ, 2 * #{central M-lifts of rhoPrime …ρ} = #(M-lifts …)` — the source
  **Lemma 8.6** half-torsor count.  **`G_ℚ₂`: `lemma_8_6_local` ✓** (`SectionEight.lean:1301`).
  **`Γ_A`: `lemma_8_6_gammaA` ✗ = P-16c** (`SectionEight.lean:1288`, `sorry`).
* `hMcountM l h : ∀ ρ, #(M-lifts of rhoPrime …ρ) = |M_B|²` — the `2^{2·dim}` M-lift count, from
  **`prop_5_16`/`prop_5_15` ✓**.

**Only `Γ_A` is blocked, on P-16c.**  `G_ℚ₂`'s `half139` is dischargeable now.

---

## 5. Recommended order for the concrete pass

1. **μ-independence `hμ`** (source 5.15/5.16) — self-contained; unblocks the `hfib` half of (140).
2. **`hM` + `Lin`/`κ`/`ε`** (Prop 8.8 count) — the group-theory↔quadratic bridge; the largest piece.
3. **`hphase` + the witness `phase`/`Δ`** (Prop 8.8 reindex) — one coupled build; needs the
   DeltaScalar 2-cocycle proofs + `prop_8_8_target`'s per-character shear.
4. **`G0`/`μ` `l`-independence** (Arf / source) — completes the witness.
5. **`half139` for `G_ℚ₂`** (`lemma_8_6_local` + 5.15/5.16) — quick; `Γ_A` waits on P-16c.
6. **`stageR136`**: land the `Enrichment` R-stage extension (owner sign-off), build `Dobs`,
   discharge `hsep_hom`/`hZcount`/`hE2`.
7. **Assemble** the two `RecursionInputs`, `exact prop_8_9_of …` into `SectionEight.lean`.

## Landed reducers this pass (all in `GQ2/RecursionSplice.lean`, std-3 sorry-free)

`prop_8_9_of` · `half139_via_radData` · `zBC_eq_sum_centralOver` ·
`central_card_eq_reductions_mul_tcocycle` · `centralOver_card_eq_reductions_mul_tcocycle` ·
`zBC_eq_mu_mul_reductionCount` · `phase140_ofPhaseData` · `lemma_8_5_aggregated` ·
`phase140_of_gaussCorrespondence` · `polarInverseL` (+`_spec`) · `phase140_of_nonsingular` ·
`enrichment_card_Vmod`.
