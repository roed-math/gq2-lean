# P-16d6e4aA-P* family handoff — the endgame of the Gauss-`Z` lane

**Scope**: the parallel work map P-16d6e4aA-P1…P5 (board rows 103–108 of `docs/tickets.md`),
whose completion closes the **last two live `sorry` tokens in the library**:

* `GQ2/GaussZFinalGammaA.lean:1252` — `zeroCount_qDouble_ramified_of_faithful`
  (the isotypic-pack count; **P3**, in flight);
* `GQ2/ThmFourTwo.lean:290` — the `⟨G0, hGaussZA, hGaussZF⟩`-obtain inside the `thm_4_2`
  strong induction (**P4→P5**, the reshaped route below).

Everything else on `SORRY_ALLOWLIST` (`GammaA`, `FoxHeisenberg`, `SectionSeven`) is
comment-mentions/transitive-`sorryAx` commentary — no live proof obligations.  Close cascade
(§7): P3 ∧ (P4d+P4e+P5) ⟹ `thm_4_2` sorryAx-free ⟹ `main_surjection_count'` (§10) sorryAx-free
⟹ the whole formalization at std-3 + the frozen 15-axiom census.

**Read-first per ticket**: P4's verdict `docs/p16d6e4aA-p4-tame-package.md` (it CHANGED the
family's architecture — §2 below); P4d/P4e execution guide `docs/p16d6e4aA-p4d-handoff.md`;
P3's design `docs/p16d6e4aA-pack-design.md` (P2's deliverable) and the A-4 prep
`docs/p16d6e4aA-a4-prep.md`.

## 1. Status at a glance (2026-07-08)

| Ticket | What | Status |
|---|---|---|
| P1 | Maschke/odd-order complements | ⚠ **DOWNGRADED — do not start** unless P3's étale route stalls (pack-design §2/§8: isotypic components are vector spaces over étale field factors of `𝔽₂[X]/(X^d−1)`; freeness is automatic) |
| P2 | pack design doc | ✅ **CLOSED** (`docs/p16d6e4aA-pack-design.md`; verdicts: pack FEASIBLE 600–1000 ln, pack-free arf-route REFUTED, P1 unnecessary) |
| P3 | the isotypic pack → count discharge | ◐ **IN FLIGHT (owned by a parallel agent — do not touch `GaussZFinalGammaA.lean`)**.  Landed: inc-1/2 (conjugation calculus; operator Frobenius + kernel stability), inc-3a (`exists_single_isotype`), inc-3b-i (`exists_isotypic_equiv : V ≃+ (Fin s → AdjoinRoot P)` with root-equivariance).  Next: 3b-ii (pack-interface layer: `zpowers t`-action on `Wt`, `he`, `hWt2`, `hWtsimple`), §4 (`f` even via self-reciprocity), §5 (`U^{2^a}=1` centrality + descent count), then the splice into `zeroCount_qDouble_ramified_of_faithful` |
| P4 | the c3-G0 package | ✅ **CLOSED — RESHAPE VERDICT** (`docs/p16d6e4aA-p4-tame-package.md`): the frozen `TamePackage{Unram,Ram}`/hpack shape is **refuted** (not block-derivable); replaced by the head-inflation architecture (§2) |
| P4b | reshape substrate | ✅ **LANDED** — `GQ2/BlockHeadDat.lean` (`blockEnrichmentD` + the faithful head quotient; all key decls std-3 exactly) |
| P4c | local twins | ✅ **LANDED** — `GQ2/GaussZFinalD.lean` (`gaussZResidueD_local_{unramified,ramified}`, hpack-free/hfaith-free; axiom footprints = the baseline twins', no sorryAx) |
| P4d | `Γ_A` twins | ☐ **OPEN, parallel-ready** — `docs/p16d6e4aA-p4d-handoff.md` (fresh-session-sized; independent of P3 except one interface name, §5) |
| P4e | the obtain | ☐ after P4d (small: `by_cases` + A-4.6b; skeleton in the P4d handoff §P4e) |
| P5 | ThmFourTwo swap | ☐ **RESCOPED by the reshape** (§4) — after P4e (and P3 for the delisting cascade) |

## 2. THE ARCHITECTURE CHANGE (P4's verdict — read before doing anything)

The original plan had P4 derive per-block `TamePackageUnram/Ram` witnesses (per-lift
factorizations `ρ.1.1 = c ∘ tameA` in `RF.YC` + `hfaith`) and P5 close the obtain with
`gaussZ_obtain_of_tamePackage`.  **This is impossible**: the boundary equation's θ-component
pins `θ_C(ρ(x₀-class)) = ψ̄(piX0)` while any tame factorization forces it `= 1`, and `thm_4_2`
quantifies over all frames; `hfaith` at `RF.YC` is likewise false whenever `K < L_Y` (`L_C`
acts trivially on the simple module).  The paper never claims either — its §6 runs over the
faithful tame image `H_V` (p. 25).

**The replacement (head-inflation)**: the boundary equation's *head* component IS the tame
factorization — `TC.piY ∘ ρ.1.1 = F.alpha ∘ B.tameA/tameF` for every lift of both sources,
`rfl`-deep (`boundaryLift_head_{gammaA,local}`).  So the enrichment's κ⁰ datum is made
*definitionally* head-inflated (`blockEnrichmentD`: `dat := (blockDatHV).reindexHom
blockProjF`, with `blockDatHV` built by the landed `kappa0_exists_tame` at the **faithful head
quotient** `HVq := H ⧸ headActKer` where `hfaith` is true by construction), and every
`QZero`/`Q0loc` evaluation transports down `reindexHom` to `C := HVq` at the **fixed**
surjection `mk' ∘ F.alpha`.  All package fields dissolve; the G0-obtain becomes
hypothesis-free; the un/ramified dichotomy is a `by_cases` on the head-level
`F.alpha tameTau`-action (ρ- and source-uniform).

**Consequences**: `TamePackageUnram/Ram` + `gaussZ_obtain_of_tamePackage*`
(GaussZFinalGammaA §A-4.6a) are **superseded** — they stay landed and true but are
unwitnessable; P5 must NOT build on them.  The consumed enrichment changes from
`blockEnrichment` to `blockEnrichmentD` (same `Vmod`/action/form fields via record-update —
only `dat`/`hdat` differ).

## 3. The landed substrate — what a consumer gets (all in `GQ2.SectionNine`)

From `GQ2/BlockHeadDat.lean` (P4b, everything std-3 exactly):

* `headEquiv : Y⧸L_Y ≃* H`, `headAct` (the `H`-action on `V = Additive (↥Blk.P ⧸ S.subgroupOf P)`),
  `blockPiCH : Y⧸K →* H` (= `(blockFrame T Blk hE2).TC.piY`, `blockPiCH_eq_TC_piY` is `rfl`),
  `blockPiCH_compat : c • v = blockPiCH c • v`;
* `headActKer`, `HVq T Blk := H ⧸ headActKer` (abbrev), `hvAct`, **`hvAct_faithful`**,
  `blockProjF : Y⧸K →* HVq` + `_surjective` + `_compat`;
* the tame pair `hvSigma/hvTau` (classes of `α σ`/`α τ`) + `hv_gen` (generation) + `hv_rel`
  (tame relation), transports `hv_inv`/`hv_simple`;
* `blockDatHV` (+ `_spec`) — the `HVq`-level κ⁰ datum (no sorryAx: P-17e5's
  `kappa0_exists_tame` is landed);
* **`blockEnrichmentD T Blk hE2 F : (blockFrame T Blk hE2).Enrichment`** with
  `blockEnrichmentD_dat_eq` = `rfl`;
* `boundaryLift_head_{gammaA,local}` — `congrArg Prod.fst (ρ.2 γ)`.

From `GQ2/GaussZFinalD.lean` (P4c):

* `Q0loc_reindexHom_hom` — the `MonoidHom`-level `Q0loc` reindex transport (std-3);
* `gaussZResidueD_local_{unramified,ramified}` — the local `hGaussZF` twins at
  `blockEnrichmentD`; hypotheses: `hsimple/hVne/hnt` (the `EnD`-typed shapes ThmFourTwo's lane
  already derives), `m/hm/hcard`, and the head-level dichotomy
  `(hunram/hram : letI …; ∀/∃ v, F.alpha tameTau • v (=/≠) v)` under `headAct`;
  ramified additionally `(R : LocalReciprocity)` + `(horient : TameUnitOrientation R B.tameF)`.
  Axioms: unram std-3+{B6,B7}; ram std-3+{B6,B7,B9,B11a,B11b,B12,B13} — exactly the baseline.

## 4. What remains, in order

1. **P4d** (parallel-ready NOW): `gaussZResidueD_gammaA_{unramified,ramified}` in a NEW leaf
   (`GQ2/GaussZGammaAD.lean`, say) — the A-4.5d/e seam replayed at `HVq`.  Full execution map,
   statement shapes, and the banked gotcha list: `docs/p16d6e4aA-p4d-handoff.md`.  The one new
   mathematical ingredient is a 3-line `kappa0Cocycle`-reindex identity moved through A-3's
   `relZPair_comap` machinery; peels (A-4.2/3c/4b), packs (A-4.5c, `tau_fixed_eq_zero_of_gen`),
   counts (`prop_6_9_unramified` — usable DIRECTLY at `HVq` since `hfaith` is true there) are
   all banked and generic in `C`.  **Correction to the P4d handoff**: the ramified twin should
   *cite* `zeroCount_qDouble_ramified_of_faithful` (the sorried theorem) — that adds NO sorry
   token to the new leaf, so **no `SORRY_ALLOWLIST` entry is needed**; the `sorryAx` flows
   transitively and disappears when P3 lands.
2. **P4e**: `gaussZ_obtain_blockD` — `obtain ⟨m, hm, hcard⟩ :=
   exists_one_le_card_eq_two_pow_of_nonsingular …` (A-4.6b, from `En.hns` + `hVne`), then
   `by_cases` on the head dichotomy; unram branch → the two `−2^m` twins, ram branch
   (`push_neg`) → the two `+2^m` twins with `R := localReciprocity`,
   `horient := TameOrientationWitness.tameFHom_tameUnitOrientation` (global witnesses,
   sanctioned census).  Conclusion shape = exactly the ThmFourTwo obtain.
3. **P5** (co-owned edit to `ThmFourTwo.lean` — coordinate on the board before starting):
   in the R-stage lane (:241-376), swap `SectionNine.blockEnrichment T Blk hE2 F` →
   `SectionNine.blockEnrichmentD T Blk hE2 F` at the obtain AND the `prop_8_9` call
   (`prop_8_9` is En-generic; `hsimple`/`hVne`/`hnt` derive from `blockHsimple`/`blockHnt`
   exactly as today — `Vmod`/`actV` are kept verbatim by the record-update), import the P4d/e
   leaf (DAG: it sits above BlockEnrichment + GaussZFinal — no cycle with ThmFourTwo), and
   close the sorry with `gaussZ_obtain_blockD`.
4. **The close cascade** (P5's second half, needs P3): delist `GaussZFinalGammaA` and
   `ThmFourTwo` from `SORRY_ALLOWLIST` (scripts/check_axioms.sh); re-audit
   `#print axioms GQ2.thm_4_2` (expected: std-3 + the sanctioned B-census, no sorryAx) and
   `main_surjection_count'`; board-close P4d/e → P4 → e4aA → e4a → e4 → the P-16 tree, and
   flag P-17i's row (the `thm_4_2` sorry is this same obtain).

## 5. Coordination & interfaces

* **File ownership**: `GaussZFinalGammaA.lean` is P3's (one surgical edit pending — do not
  touch); `ThmFourTwo.lean` is P5's moment (announce on the board row before editing);
  everything else in this family lands in NEW leaves + `GQ2.lean` registration.
* **The single P3↔P4d touch point**: the ramified count interface.  P3 discharges
  `zeroCount_qDouble_ramified_of_faithful` in place (GaussZFinalGammaA:1241 — stated at
  abstract faithful `(C, V)`, so it serves the `HVq`-route identically).  P4d cites that same
  theorem — do NOT fork or restate it.
* **P1 stays dormant** unless P3 reports the étale route stalled (then revive per its row).

## 6. Discipline (unchanged, family-wide)

Census frozen at **15** (`scripts/check_axioms.sh` — must stay all-pass); no new `axiom`s
without explicit user approval; `GQ2/Foundations/Axioms.lean` frozen; every landed leaf std-3
(+ the sanctioned B-budget where inherited); stage only session-touched files (never
`git add -A`); the frozen §6.17/6.18 signatures are co-owned (P-20 cross-flag for amendments).
Gate: `lake env lean <file>` per edit → `lake build` → `./scripts/check_axioms.sh` → pathspec
commit → board row update (swarm may sweep staged files: re-read `docs/tickets.md` before
editing it, and verify your hunks are in HEAD after any concurrent commit).

Recurring Lean gotchas for this family (paid for twice now — P4b/P4c; full list on the P4
board row and in the P4d handoff): pin `continuous_of_discreteTopology (f := …)`; shadow the
global `QuotientGroup.instTopologicalSpace` at raw `Y ⧸ Blk.K` spellings with frame-valued
cover-`letI`s; re-key `letI`s across the `EnD.Vmod`/`(EnD.descData l h).Vmod`/raw-`Additive`
spelling cells; never hand-write mixed-spelling `H1`/finsum types (convert pinned values to
the `Z¹⧸B¹` side with `rw [← hpinned]`); qualify `SectionEight.sign`; wrap
`QuotientGroup.lift_mk' _ _ _` in `show … from` when the expected type needs unfolding.

## 7. Definition of done

`grep -rn "^\s*sorry" GQ2/ | wc -l` → 0; `lake build` green; `check_axioms` all-pass with
`SORRY_ALLOWLIST` reduced by `GaussZFinalGammaA` + `ThmFourTwo`;
`#print axioms GQ2.thm_4_2` = std-3 + {B5, B6, B7, B9, B10′, B11a, B11b, B12, B13}-subset of
the sanctioned census, **no `sorryAx`**; board rows P-16d6e4aA-P1…P5 closed and the e4aA →
… → P-16 cascade marked.
