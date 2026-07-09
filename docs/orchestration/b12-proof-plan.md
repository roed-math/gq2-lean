# B12 discharge plan: prove `kummerClassK_surjective` (landed as census 15 → 13)

> **2026-07-09 — COMPLETE, plan archived.**  All increments landed (board:
> [`b12-tickets.md`](b12-tickets.md)); the I4 flip shipped with explicit user approval, together
> with the deletion of the never-consumed **B2** (user directive at flip time), so the census
> moved 15 → **13** rather than this plan's 15 → 14.  Everything below is the historical record.

> **2026-07-09 (post-refactor):** ticket board at [`b12-tickets.md`](b12-tickets.md) —
> **B12-0 recon is ☑ done** (findings recorded there): the dedup (`2ce8bc8`) and subdirectory
> regrouping (`c6a2293`) left every §2 location and the §3 import-DAG argument intact, and
> **both I0 Mathlib lemmas exist** (names pinned below) — the finite-level-descent fallback is
> retired.  B12-1 ∥ B12-2 are ready.  Docs refactor note: the `docs/p*.md` lane files cited
> below now live in the **archived** `docs/orchestration/` (do not edit those).

**Goal.**  Replace the axiom

```lean
axiom kummerClassK_surjective (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    Function.Surjective (kummerClassK k)
```

(`GQ2/Foundations/Axioms.lean:571`) by a proof, following the discharge note already recorded in
its docstring: *"completing the square + the Krull–Galois correspondence."*  All new material is
std-3 (the proof consumes **no** B-axioms — it is Mathlib field theory + `ContCoh` plumbing).

**Estimated effort** (repo units): **4–7 lane-sessions** (≈ 1–1.5 days in one lane) — I0 recon ½,
I1 ≈ 1, I2 ≈ 1–2 (the only risk pocket), I3 ≈ 1, upstream-port ½–1, flip commit ½ plus
coordination.  *(Updated post-B12-0: remaining ≈ **3–5 lane-sessions**; the ×2 Mathlib-gap
buffer is retired — both I0 lemmas exist, see §4-I0.)*

---

## 0. Shared-tree constraints (read first)

* **Development happens entirely in ONE new file** `GQ2/KummerSurjectivity.lean` (untracked until
  committed ⇒ survives swarm resets; no other lane can be disturbed).
* **Do not touch** `Foundations/Axioms.lean`, `check_axioms.sh`, `AxiomLedger.lean`, `GQ2.lean`,
  or B2 (`cyclotomicCharacter_two_surjective` — another session is active on the tree; B2 stays
  put regardless) until the **flip commit** (§5), which is a separate, user-approved census
  change coordinated with whoever owns the tree at that point.
* Standard gates per increment: own-file `lake build`, `lean_verify` = exactly
  `{propext, Classical.choice, Quot.sound}` on every new theorem, `scripts/check_axioms.sh`
  (census stays 15 until the flip).

## 1. Mathematical route (one paragraph)

A class `c ∈ H¹(G_k, 𝔽₂)` (trivial action) is `H1mk z` for a cocycle `z ∈ Z1`, i.e. a
**continuous hom** `z : G_k → ℤ/2` (`mem_Z1_iff_of_trivial`).  If `z = 0`, then
`c = 0 = kummerClassK k 1`.  Otherwise `H := ker z` is an **open subgroup of index 2** (open:
`z` continuous, `ℤ/2` discrete; index 2: `Subgroup.index_ker` + range = ⊤).  The Krull–Galois
correspondence turns `H` into a quadratic subextension: `L := fixedField H'`
(`H' :=` image of `H` in `GaloisGroup ℚ_[2]`) satisfies `k ≤ L`,
`(L.fixingSubgroup).subgroupOf k.fixingSubgroup = H` (closed-subgroup Krull), and
`FiniteDimensional ℚ_[2] L`; the **already-proved** bridge
`InvolutionVanish.finrank_extendScalars_eq_two` gives `[L : k] = 2`, and the already-proved
`QuadraticAdjoin.exists_sqrt_generator` completes the square: `L = k⟮δ⟯`, `δ² = d ∈ kˣ`,
`δ ∉ k`.  By `QuadraticAdjoin.fixingSubgroup_subgroupOf_eq_stabilizer`, for `g ∈ G_k`:
`z g = 0 ⟺ g ∈ H ⟺ g • δ = δ`.  The `kummerClassK k d` cocycle is
`g ↦ [g • sqrtCl d ≠ sqrtCl d]`, and `(sqrtCl d)² = d = δ²` ⇒ (root-independence, the
`kcf_root_indep'` computation) it equals `g ↦ [g • δ ≠ δ]`.  So `z` and the Kummer cocycle are
two functions `G_k → ℤ/2` vanishing **exactly on `H`** — and both are homs, so both are the
indicator of the nontrivial coset (`ℤ/2` has one nonzero element) ⇒ equal as `Z1` elements ⇒
`kummerClassK k d = H1mk z = c`.  ∎

## 2. Verified ingredient inventory (checked 2026-07-09; **re-verified post-refactor by B12-0**
— all locations unchanged; only adjacent rename `ShapiroDeepness.lean` → `Shapiro/Deepness.lean`)

Already proved, **upstream of `Axioms.lean`** (usable directly):

| decl | location | role |
|---|---|---|
| `kummerClassK` (def) | `EvensKahn.lean:448` | target map; codomain `H1 k.fixingSubgroup (ZMod 2)`; built by `H1mk` from `kummerCocycleFun (sqrtCl a)` with `mem_Z1_iff_of_trivial (fun _ _ ↦ rfl)` |
| `ContCoh.mem_Z1_iff_of_trivial` | `Cohomology.lean:346` | Z1 = continuous + hom (trivial action) |
| `Kummer.kummerCocycleFun` (+ `_continuous`, `kummerCocycleFun_hom_on`) | `Kummer.lean:75` ff. | the cocycle `g ↦ [g•α ≠ α]` |
| `sqrtCl`, `sqrtCl_sq`, `sqrtCl_ne_zero` | `EvensKahn.lean:422–431` | canonical root |
| `InfiniteGalois.fixedField_fixingSubgroup`, `IntermediateField.mem_fixedField_iff` | Mathlib (used at `DeepCount.lean:64`) | Krull, field-side composite |
| `Subgroup.normal_of_index_eq_two` | Mathlib (used at `InvolutionVanish.lean:75`) | (if needed) |
| `Subgroup.index_ker : f.ker.index = Nat.card f.range` | Mathlib (verified during c2c2) | index-2 step |
| `InfiniteGalois.fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k))` | Mathlib `FieldTheory/Galois/Infinite.lean:145` | closed-subgroup Krull composite (I2) |
| `InfiniteGalois.isOpen_iff_finite` (**carrier form**) | ibid. `:240` | open ⇒ `FiniteDimensional` (I2) |
| `InfiniteGalois.fixingSubgroup_isClosed` / `IntermediateField.fixingSubgroup_isOpen` | ibid. `:63` / `KrullTopology.lean:173` | support (I2) |
| `Subgroup.isClosed_of_isOpen` · `IsOpen.isOpenMap_subtype_val` · `Subgroup.subgroupOf_map_subtype` | Mathlib (`OpenSubgroup.lean:273` · `Constructions.lean:392` · `Subgroup/Basic.lean`) | I2 glue, pinned by B12-0 |

Already proved but **downstream of `Axioms.lean`** (⇒ must be *ported*, see §4):

| decl | location | why downstream |
|---|---|---|
| `QuadraticAdjoin.exists_sqrt_generator` | `QuadraticAdjoin.lean:94` | file imports `HilbertLedger` → `Foundations.Axioms` |
| `QuadraticAdjoin.fixingSubgroup_subgroupOf_eq_stabilizer` | `QuadraticAdjoin.lean:292` | same |
| `QuadraticAdjoin.mem_bot_iff_mem` | `QuadraticAdjoin.lean:80` | same (support) |
| `InvolutionVanish.finrank_extendScalars_eq_two` (+ its `index_extendScalars_fixingSubgroup`) | `InvolutionVanish.lean:68` | imports `ShapiroDeepness` + `QuadraticAdjoin` |
| `HilbertLedger.kcf_root_indep'` (`α² = β² ⇒ κ_α = κ_β`) | `HilbertLedger.lean:113` | `HilbertLedger` imports `Foundations.Axioms` |
| `HilbertLedger.kummerClassK_one` | `HilbertLedger.lean` (☑ header list) | same |

**Key structural fact** (checked): consumers of the axiom are `DeepCount.lean` and `DimClose.lean`
(plus `AxiomLedger.lean`'s census list), and `DeepCount` is *upstream* of `QuadraticAdjoin` — so
the proof file **cannot** live downstream of `InvolutionVanish` and still serve the consumers via
a same-name theorem.  Hence:

## 3. File placement decision

`GQ2/KummerSurjectivity.lean` imports **only** `GQ2.EvensKahn` (which brings `GQ2.Kummer`,
`ContCoh`, `sqrtCl`, `kummerClassK`) + Mathlib.  That keeps it strictly upstream of
`Foundations/Axioms.lean`, so the flip (§5) is the zero-churn B11 pattern: `Axioms.lean` imports
this file and re-declares the axiom as a same-name theorem.  The price: the six downstream
ingredients in the second table are **re-proved as `private` copies** in this file
(≈ 200–250 lines, mostly mechanical transplantation — the precedented fallback from the f2b I0
plan).  Their proofs are pure Mathlib field theory; nothing in them needs the `HilbertLedger`
import their current homes carry.

*Rejected alternatives.*  (a) Re-pointing `QuadraticAdjoin`'s import from `HilbertLedger` to
something upstream — a cross-file edit in a shared tree for cosmetic benefit; can be a later
cleanup ticket that deduplicates the private copies.  (b) Proving the theorem downstream under a
primed name and threading it into consumers as a hypothesis — exactly the churn the B11
precedent exists to avoid.

## 4. Increments

### I0 — recon (½ session, no code) — **☑ DONE 2026-07-09** (full findings: board §B12-0)
1. ✓ `InfiniteGalois.fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k)) [IsGalois k K] :
   (IntermediateField.fixedField H).fixingSubgroup = H.1` — `Galois/Infinite.lean:145`.
2. ✓ `InfiniteGalois.isOpen_iff_finite (L) : IsOpen L.fixingSubgroup.carrier ↔
   FiniteDimensional k L` — ibid. `:240` (**carrier form**).  Fallback retired.
3. ✓ `IntermediateField.fixingSubgroup_isOpen` (`KrullTopology.lean:173`);
   transfer = `IsOpen.isOpenMap_subtype_val` (`Constructions.lean:392`); open ⇒ closed =
   `Subgroup.isClosed_of_isOpen` (`OpenSubgroup.lean:273`); round-trip =
   `Subgroup.subgroupOf_map_subtype`.  Shape check: `GaloisGroup K` is a *reducible* abbrev of
   `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` (`Kummer.lean:50`) — the exact `Gal(K̄/K)`
   shape these lemmas expect; `IsGalois ℚ_[2] ℚ̄₂` resolves (exercised at `DeepCount.lean:64`).
4. ◐ Import cones of the six ports confirmed axiom-free at file level (dedup `2ce8bc8` touched
   none of them); the line-level deep-read for `HilbertLedger`-only helpers is deferred to
   B12-3's transplant step, which carries the inline-it escape hatch.

### I1 — the hom/kernel layer (~1 session)
In namespace `GQ2.KummerSurjectivity`, over `G := ↥(k.fixingSubgroup)`:
* `H1mk_surjective : Function.Surjective (H1mk G (ZMod 2))` — `QuotientAddGroup.mk'_surjective`.
* For `z ∈ Z1` (unbundled by `mem_Z1_iff_of_trivial`): package the multiplicative-to-additive
  hom `zHom : G →* Multiplicative (ZMod 2)`; `ker_open : IsOpen (zHom.ker : Set G)`
  (continuity + `DiscreteTopology (ZMod 2)`).
* `index_ker_eq_two (hz : z ≠ 0) : zHom.ker.index = 2` — `Subgroup.index_ker` +
  `zHom.range = ⊤` (a nonzero value in `ZMod 2` is `1`, which generates).
* `hom_eq_of_ker_eq : zHom.ker = wHom.ker → z = w` — pointwise, `ZMod 2` case split.
* `kummerClassK_one` (private port, ~10 lines): `(sqrtCl 1)² = 1 ⇒ sqrtCl 1 = ±1 ∈ ℚ₂`, fixed by
  every `g`, so the cocycle is `0`.

### I2 — index-2 open subgroup ⇒ quadratic subextension (1–2 sessions; the risk pocket)
Input: `H ≤ k.fixingSubgroup` (as `Subgroup ↥(k.fixingSubgroup)`), `IsOpen`, `H.index = 2`.
Output:
```lean
∃ (L : IntermediateField ℚ_[2] ℚ̄₂) (hkL : k ≤ L), FiniteDimensional ℚ_[2] L ∧
  (L.fixingSubgroup).subgroupOf k.fixingSubgroup = H ∧
  Module.finrank ↥k ↥(IntermediateField.extendScalars hkL) = 2
```
Steps:
* `H' := H.map k.fixingSubgroup.subtype`; closed in `GaloisGroup ℚ_[2]`
  (index-2 ⇒ `H` closed in the subtype; `k.fixingSubgroup` closed in the ambient; composite).
* `L := IntermediateField.fixedField H'` — **directly** an `IntermediateField ℚ_[2] ℚ̄₂`
  (this is the move that avoids the `Gal(ℚ̄₂/↥k)`-vs-subtype instance split entirely: never
  leave the ambient group).  `k ≤ L`: elements of `H'` fix `k` pointwise by membership in
  `k.fixingSubgroup`.
* `H'` open in the ambient group: `H` open in the subtype topology of `k.fixingSubgroup`,
  which is open (`IntermediateField.fixingSubgroup_isOpen`, `k` fin-dim), and
  `IsOpen.isOpenMap_subtype_val` pushes the image forward; hence `H'` closed
  (`Subgroup.isClosed_of_isOpen`).
* Krull: `L.fixingSubgroup = H'` by `InfiniteGalois.fixingSubgroup_fixedField` at the
  `ClosedSubgroup` packaging of `H'`; **then** `FiniteDimensional ℚ_[2] L` by rewriting
  `H'`-openness through that equality into `InfiniteGalois.isOpen_iff_finite` (carrier form) —
  this is the resolution of the `finrank_extendScalars_eq_two` instance chicken-egg.
* Descend to `subgroupOf`-form: `(L.fixingSubgroup).subgroupOf k.fixingSubgroup = H` via
  `Subgroup.subgroupOf_map_subtype` (backup: `Subgroup.comap_map_eq_self_of_injective` with
  `Subtype.val_injective`).
* Degree: private port of `finrank_extendScalars_eq_two` (+ its helper
  `index_extendScalars_fixingSubgroup`), applied to `hindex` rewritten along the previous item
  (`H.index = 2`).

### I3 — assembly (~1 session)
* Private ports: `exists_sqrt_generator` (+ `mem_bot_iff_mem`),
  `fixingSubgroup_subgroupOf_eq_stabilizer`, `kcf_root_indep'`.
* `theorem kummerClassK_surjective' (k) [FiniteDimensional ℚ_[2] k] :
  Function.Surjective (kummerClassK k)`:
  obtain `z` (I1 surjectivity); split on `z = 0` (→ `⟨1, kummerClassK_one⟩`); otherwise run
  I2 at `H := zHom.ker`, extract `d, δ` via the ported `exists_sqrt_generator`, identify
  kernels via `fixingSubgroup_subgroupOf_eq_stabilizer` + `kcf_root_indep'`
  (`(sqrtCl d)² = d = δ²`), conclude cocycle equality by `hom_eq_of_ker_eq`, and finish with
  `congrArg (H1mk _ _)` + `Subtype.ext`.
* Gate: `lean_verify GQ2.KummerSurjectivity.kummerClassK_surjective'` = std-3 exactly.
* Commit the new file (stage **only** `GQ2/KummerSurjectivity.lean`; print the staged set
  first).  Registration in `GQ2.lean` per convention wants the same commit — `GQ2.lean` is a
  shared file, so take the working-tree-edit route used all week (add the import line, include
  it in the same commit *only if* no concurrent `GQ2.lean` churn is in flight; otherwise defer
  registration to the flip commit and note it in the commit message).

### I4 — flip commit (½ session + coordination; **user-approved census change**)
The B11/`dyadicNormCriterion` precedent, adapted:
1. `Foundations/Axioms.lean`: add `import GQ2.KummerSurjectivity`; replace the `axiom` block by
   ```lean
   theorem kummerClassK_surjective (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
       [FiniteDimensional ℚ_[2] k] :
       Function.Surjective (kummerClassK k) :=
     KummerSurjectivity.kummerClassK_surjective' k
   ```
   keeping the docstring (marked **discharged, P-xx**) — same fully-qualified name ⇒ zero
   consumer churn in `DeepCount.lean` / `DimClose.lean`.
2. `scripts/check_axioms.sh`: `EXPECTED_AXIOMS=14` + history note (same commit).
3. `GQ2/AxiomLedger.lean`: remove B12 from `bAxioms` (file is designed to fail to compile if
   the census drifts — this is the consistency check working as intended).
4. Live docs only (`docs/orchestration/` is archived — do not touch): `literature-axioms.md`
   (B12 → *discharged, proved in-repo*, keep the citation), `literature-axioms-onepage.md`
   foot, the census notes in `tickets.md`, and regenerate the machine-generated
   `atlas-audit.md` (lean-atlas).
5. Full `lake build` + `check_axioms.sh` + spot `lean_verify` on a B12 consumer
   (`DeepCount`/`DimClose` capstones): their traces must now show std-3 ∪ (their *other*
   B-leaves) with `kummerClassK_surjective` gone.
6. This commit touches four shared files — **coordinate with the active session(s)** and land it
   when the tree is quiet (the 2026-07-08 `SectionNine`/`check_axioms.sh` merge conflict must be
   fully resolved by its owners first).

## 5. Risks

* ~~Mathlib gap at I0-(1)/(2)~~ **retired by B12-0** (2026-07-09): both lemmas exist
  (`InfiniteGalois.fixingSubgroup_fixedField`, `isOpen_iff_finite`); only the carrier-form
  coercion shape remains as a minor rewrite friction.
* **Subtype/`subgroupOf` friction** around `H.map subtype` round-trips — the usual grind;
  mitigated by staying in the ambient group throughout (no `Gal(ℚ̄₂/↥k)` transport anywhere).
* **Port drift**: the six private copies must be transplanted verbatim-modulo-namespace; if one
  secretly uses a `HilbertLedger`-only helper, inline that too (they are all field-theoretic).
* Root-choice plumbing (`sqrtCl d` vs `δ`): handled at cocycle level by the ported
  `kcf_root_indep'`; no class-level root-independence lemma is needed.

## 6. Out of scope

* **B2 stays untouched** (deletion is a separate census decision; another agent is on the tree).
* No dedup refactor of `QuadraticAdjoin`/`InvolutionVanish` against the private ports (optional
  follow-up ticket once the tree is quiet).
* The other quick-win axioms (B7′, B13, B11b) — separate plans.
