# B12 discharge — ticket board  (prove `kummerClassK_surjective`, census 15 → 14)

**Status (2026-07-09): B12-0 ☑ done — B12-1 ∥ B12-2 are ready to start** (independent lanes;
B12-3 after both; B12-4 gated on explicit user census approval + quiet tree).  The 2026-07-09
refactor is landed and accounted for in the B12-0 findings: dedup `2ce8bc8` (touched none of
the six port targets) and subdirectory regrouping `c6a2293` (only adjacent rename:
`ShapiroDeepness.lean` → `Shapiro/Deepness.lean`).  The census stays frozen at 15 until
**B12-4 un-freezes it by explicit user approval** (this axiom-removal initiative).

Route, ingredient inventory, and risk analysis: [`b12-proof-plan.md`](b12-proof-plan.md)
(§ numbers below refer to it).  Conventions as on the parent board [`tickets.md`](tickets.md) —
**Model**: **F** = Fable (design-heavy), **O** = Opus (well-specified), **F→O** = Fable design
then Opus close.  **Gates for every ticket**: own-file `lake build`; `lean_verify` = exactly
`{propext, Classical.choice, Quot.sound}` on every new declaration (the whole proof is
B-axiom-free); `scripts/check_axioms.sh` (census stays **15** until B12-4); stage only your own
files and print the staged set before committing.  All development happens in the single new
file `GQ2/KummerSurjectivity.lean` (imports `GQ2.EvensKahn` + Mathlib **only** — it must stay
upstream of `Foundations/Axioms.lean` for the zero-churn flip; verified safe: `EvensKahn`
imports only `Mathlib + CupProduct + Kummer + Demushkin`).

| # | St | Model | Ticket | Est. | Deps |
|---|----|-------|--------|------|------|
| B12-0 | ☑ 07-09 | O | Post-dedup recon: ingredients, Mathlib names, import DAG | ½ | — |
| B12-1 | ☑ 07-09 | O | Hom/kernel layer + `kummerClassK_one` port | 1 | B12-0 ☑ |
| B12-2 | ☑ 07-09 | O | Krull bridge: open index-2 kernel ⇒ quadratic subextension (in `KummerKrullBridge.lean`) | 1 | B12-0 ☑ |
| B12-3 | ⬜ | O | Downstream ports + capstone `kummerClassK_surjective'` | 1–1½ | B12-1 ∧ B12-2 |
| B12-4 | ⬜ | O | Census-flip commit (user approval + quiet tree) | ½ | B12-3 |

Est. in lane-sessions (~½–1 day each).  **B12-1 ∥ B12-2** are independent lanes.
Total remaining ≈ **3–5 lane-sessions** (the ×2 Mathlib-gap buffer is retired — see B12-0.3).

---

## B12-0 — post-dedup recon  ☑ done 2026-07-09

**Go/no-go: GO — the port list stands in full (all six).**  Findings:

1. **Ingredient homes: all unchanged.**  `kummerClassK` `EvensKahn.lean:448` ·
   `mem_Z1_iff_of_trivial` `Cohomology.lean:346` · `exists_sqrt_generator`
   `QuadraticAdjoin.lean:94` (+ `mem_bot_iff_mem` :80,
   `fixingSubgroup_subgroupOf_eq_stabilizer` :292) · `finrank_extendScalars_eq_two`
   `InvolutionVanish.lean:68` (+ `index_extendScalars_fixingSubgroup` :52) ·
   `kcf_root_indep'` `HilbertLedger.lean:113` · `kummerClassK_one` `HilbertLedger.lean:176` ·
   the axiom `Foundations/Axioms.lean:571`.
2. **Import DAG unchanged** — `QuadraticAdjoin → HilbertLedger → Foundations.Axioms`;
   `InvolutionVanish → Shapiro.Deepness + QuadraticAdjoin`.  Dedup `2ce8bc8` consolidated ten
   duplicate groups in *other* files (17-file stat checked); none of the six port targets moved
   or gained an upstream home ⇒ **B12-3's private-port section stands as written**.
3. **Both Mathlib lemmas EXIST — B12-2's design fork is resolved; the finite-level-descent
   fallback is retired.**  Pinned (against mathlib `ec410d2`):
   - `InfiniteGalois.fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k)) [IsGalois k K] :
     (IntermediateField.fixedField H).fixingSubgroup = H.1` —
     `Mathlib/FieldTheory/Galois/Infinite.lean:145`.
   - `InfiniteGalois.isOpen_iff_finite (L : IntermediateField k K) [IsGalois k K] :
     IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L` — ibid. :240.
     **Carrier form** — mind the `Set`-coercion shape when rewriting.
   - Support: `InfiniteGalois.fixedField_fixingSubgroup` (ibid. :84 — already exercised at
     `DeepCount.lean:64`, so the `IsGalois ℚ_[2] ℚ̄₂` instance is known to resolve),
     `InfiniteGalois.fixingSubgroup_isClosed` (:63),
     `IntermediateField.fixingSubgroup_isOpen` (`KrullTopology.lean:173`).
   - Glue, pinned: `Subgroup.isClosed_of_isOpen` (`Topology/Algebra/OpenSubgroup.lean:273`),
     `IsOpen.isOpenMap_subtype_val` (`Topology/Constructions.lean:392`),
     `Subgroup.subgroupOf_map_subtype` (`Algebra/Group/Subgroup/Basic.lean`; backup:
     `comap_map_eq_self_of_injective`).
   - Shape check: `GaloisGroup K` is a **reducible abbrev** of
     `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` (`Kummer.lean:50`) — exactly the
     `Gal(K̄/K)` shape the `InfiniteGalois` lemmas expect; no transport needed.
   - The §4-I2 chicken-egg (`finrank_extendScalars_eq_two` *consumes*
     `[FiniteDimensional ℚ_[2] L]`) resolves cleanly: `H′` open ⇒ closed
     (`Subgroup.isClosed_of_isOpen`) ⇒ package as `ClosedSubgroup` ⇒
     `fixingSubgroup_fixedField` turns `H′`-openness into `L.fixingSubgroup`-openness ⇒
     `isOpen_iff_finite.mp` ⇒ `FiniteDimensional ℚ_[2] L`.
4. **Atlas regeneration** (for B12-4 step 4):
   `lake exe atlas graph-data -o atlas-graph.json && python3 scripts/atlas_audit.py
   atlas-graph.json` (`docs/atlas.md`; never commit the json — it is gitignored).

## B12-1 — hom/kernel layer  ☑ done 2026-07-09 (commit `c8fb255`)

Delivered in `GQ2/KummerSurjectivity.lean` (imports `GQ2.EvensKahn` only), all std-3,
`lake build GQ2.KummerSurjectivity` green (8591 jobs), guard all-pass (census 15):

- **`H1mk_surjective` already existed** (`Cohomology.lean:223`, `QuotientAddGroup.mk'_surjective`)
  — referenced, not re-proved.
- `zHom (z) : ↥k.fixingSubgroup →* Multiplicative (ZMod 2)`, `g ↦ ofAdd (z.1 g)` (`map_one'` via
  `Z1_apply_one`, `map_mul'` via `mem_Z1_iff_of_trivial` + `ofAdd_add`); `zHom_apply` simp lemma.
- `mem_zHom_ker : g ∈ (zHom k z).ker ↔ z.1 g = 0` (`ofAdd_eq_one`).
- `zHom_ker_isOpen` (preimage of `{0}` under the continuous cocycle; `isOpen_discrete`).
- `zHom_surjective (hz : z.1 ≠ 0)` → `zHom_index_ker : (zHom k z).ker.index = 2`
  (`Subgroup.index_ker` + `MonoidHom.range_eq_top_of_surjective` + `topEquiv`; `decide` on
  `Nat.card (Multiplicative (ZMod 2)) = 2`).
- `eq_of_zero_set : (∀ g, f g = 0 ↔ f' g = 0) → f = f'` — the `𝔽₂` reconnect for B12-3.
- `kummerClassK_one` — direct port (not via the heavy `kummerClassK_mul`): `sqrtCl 1 = ±1`,
  Galois-fixed, so the cocycle is `0` and `H1mk 0 = 0`.

*Interface for B12-3*: feed `zHom_ker_isOpen`/`zHom_index_ker` into B12-2's `H`; reconnect via
`mem_zHom_ker` + `eq_of_zero_set`; `z = 0` branch uses `kummerClassK_one`.

## B12-2 — the Krull bridge  (O, 1 session)  ☑ DONE 2026-07-09 (commit `d802ae7`)

**Landed** as `GQ2.KummerSurjectivity.exists_quadratic_of_open_index_two` in its own upstream leaf
**`GQ2/KummerKrullBridge.lean`** (imports `GQ2.EvensKahn` + Mathlib; std-3; sorry-free;
`check_axioms` green, census 15).  Developed as a separate leaf rather than in the shared
`KummerSurjectivity.lean` so the B12-1 ∥ B12-2 lanes merge cleanly (two agents creating one new
file = whole-file conflict); fold back in the §3 consolidation pass if desired.

**Ports absorbed here (private):** the extendScalars trio — `finiteDimensional_extendScalars`,
`index_extendScalars_fixingSubgroup`, `finrank_extendScalars_eq_two` (B12-2's finrank output needs
them).  **⇒ B12-3's remaining ports are only** `exists_sqrt_generator` (+ `mem_bot_iff_mem`),
`fixingSubgroup_subgroupOf_eq_stabilizer`, `kcf_root_indep'`.

**B12-3 wiring:** `import GQ2.KummerKrullBridge` into `KummerSurjectivity.lean` (this also pulls
the leaf into the build cone — GQ2.lean registration was intentionally deferred to avoid a second
concurrent GQ2.lean touch) and call `exists_quadratic_of_open_index_two` at `H := zHom.ker`.

Input `H ≤ k.fixingSubgroup` open of index 2; output (§4-I2)

```lean
∃ (L : IntermediateField ℚ_[2] ℚ̄₂) (hkL : k ≤ L), FiniteDimensional ℚ_[2] L ∧
  (L.fixingSubgroup).subgroupOf k.fixingSubgroup = H ∧
  Module.finrank ↥k ↥(IntermediateField.extendScalars hkL) = 2
```

Route (every joint now has a pinned name, B12-0.3): `H' := H.map k.fixingSubgroup.subtype`,
open in the ambient group (`IntermediateField.fixingSubgroup_isOpen` for `k` fin-dim +
`IsOpen.isOpenMap_subtype_val`), hence closed (`Subgroup.isClosed_of_isOpen`);
`L := IntermediateField.fixedField H'` — **stay in the ambient `Kummer.GaloisGroup ℚ_[2]`
throughout, never transport to `Gal(ℚ̄₂/↥k)`**; `k ≤ L` elementary;
`L.fixingSubgroup = H'` by `InfiniteGalois.fixingSubgroup_fixedField` at the `ClosedSubgroup`
packaging; `FiniteDimensional ℚ_[2] L` by rewriting `H'`-openness through that equality into
`InfiniteGalois.isOpen_iff_finite` (carrier form); descend to `subgroupOf`-form by
`Subgroup.subgroupOf_map_subtype`; conclude `finrank = 2` by the (ported)
`finrank_extendScalars_eq_two` at the transported index.

*Model note*: **O** (was F→O) — the design fork this ticket was carrying is resolved by
B12-0.3: both correspondence lemmas exist, the chicken-egg has a named resolution, and the
route above is fully specified.  Escalate to F only if the reducible-abbrev/`IsGalois`
instance glue misbehaves at `Gal(ℚ̄₂/ℚ₂)` or the `ClosedSubgroup`/`subgroupOf` round-trips
fight back for more than ~half a session.

## B12-3 — ports + capstone  (O, 1–1½ sessions)

- Private ports (**confirmed alive by B12-0.2, all six**): `exists_sqrt_generator`,
  `mem_bot_iff_mem`, `fixingSubgroup_subgroupOf_eq_stabilizer`,
  `finrank_extendScalars_eq_two`, `index_extendScalars_fixingSubgroup`, `kcf_root_indep'` —
  verbatim-modulo-namespace; if one secretly uses a `HilbertLedger`-only helper, inline it
  (all are field-theoretic, §5).
- Capstone `theorem kummerClassK_surjective' (k) [FiniteDimensional ℚ_[2] k] :
  Function.Surjective (kummerClassK k)` — assembly per §1: obtain `z`; `z = 0` → `⟨1, …⟩`;
  else B12-2 at `zHom.ker`, `exists_sqrt_generator`, kernels identified via
  `fixingSubgroup_subgroupOf_eq_stabilizer` + `kcf_root_indep'` (`(sqrtCl d)² = d = δ²`),
  `hom_eq_of_ker_eq`, `congrArg`.
- `lean_verify GQ2.KummerSurjectivity.kummerClassK_surjective'` = std-3 exactly; commit the
  file (own-files-only discipline).  `GQ2.lean` registration: same commit **iff** no concurrent
  `GQ2.lean` churn is in flight; otherwise defer to B12-4 and say so in the commit message.

*Model note*: O — transplantation plus an assembly whose every joint is named above.  Escalate
to F only on port drift that changes a statement (then re-tension against the originals).

## B12-4 — census-flip commit  (O, ½ session + coordination; **user-approval gate**)

The B11/`dyadicNormCriterion` precedent (axiom → same-name theorem, zero consumer churn — the
consumers `DeepCount.lean` / `DimClose.lean` keep the name `GQ2.kummerClassK_surjective`
through their existing `Foundations.Axioms` import).  One commit, landed on a **quiet tree**
(no other lanes mid-flight), after explicit user sign-off on the census change:

1. `Foundations/Axioms.lean`: add `import GQ2.KummerSurjectivity`; replace the `axiom` with
   `theorem kummerClassK_surjective … := KummerSurjectivity.kummerClassK_surjective' k`;
   keep the docstring, marked **discharged 2026-07 (B12 board)**; update the header's census
   prose.
2. `scripts/check_axioms.sh`: `EXPECTED_AXIOMS=14` + append the history note on line 24.
3. `GQ2/AxiomLedger.lean`: drop B12 from `bAxioms` (the file is *designed* to fail to compile
   on census drift — that failure is the check working; fix it here, same commit).
4. Live docs only (**do not touch the archived `docs/orchestration/`**):
   [`literature-axioms.md`](literature-axioms.md) B12 row → *discharged, proved in-repo* (keep
   the NSW/Serre citations), [`literature-axioms-onepage.md`](literature-axioms-onepage.md)
   foot, the census notes in [`tickets.md`](tickets.md), and regenerate `atlas-audit.md` with
   the B12-0.4 invocation.
5. Full `lake build` + `check_axioms.sh` + spot `lean_verify` on a B12 consumer
   (`DeepCount`/`DimClose` capstones): `kummerClassK_surjective` must vanish from their axiom
   traces, nothing else may change.

*Model note*: O — mechanical, but the gates are procedural, not mathematical: user approval,
quiet tree, and the four-shared-file blast radius.  Whoever runs it coordinates with every
active session first.
