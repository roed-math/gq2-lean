# P-17d handoff — `blockEnrichment` (§9 concrete enrichment)

**Purpose.** Self-contained handoff for continuing P-17d (filling `blockEnrichment`).
Everything a fresh session needs is here + in the two scratch files + `docs/tickets.md`
(rows P-17d, P-17d1, P-17d2, P-17d2a/b/c, P-17d3, P-17e). No chat-log or session-memory
dependency.

Author: Opus, 2026-07-06.

---

## 0. Status

| Sub-ticket | What | State |
|---|---|---|
| **P-17d1** | descent structure: `Vmod`/`addV`/`finV`/`actV` + `descend`(+`_surj`/`_ker`/`_conj`) | ☑ DONE, std-3 |
| **P-17d2a** | `blockLam` — the index-2 character `λ_l : R → 𝔽₂` (input to `prop_7_4`/`mForm_of_qbar`) | ☑ DONE, std-3 |
| **P-17d2c** | `hquad` (`IsQuadraticFp2 qbar`) + `hns` (`Nonsingular qbar`) — the "new math" | ☑ DONE, std-3 |
| **P-17d2b** | assembly: `qbar`/`q`/`hrad`/`hTzero`/`hqbar`/`hinv` (from `prop_7_4`+`mForm_of_qbar`) + `hq` (cover square) | ☐ TODO |
| **P-17d3** | `dat`/`hdat` (κ⁰ datum from `kappa0_exists`, rides P-17e) + final `blockEnrichment` assembly | ☐ TODO |

The **hard mathematical content is DONE** (d1, d2a, d2c). What remains (d2b, d3) is
**assembly** — wiring the proven pieces into the `Enrichment` record — plus two genuinely
new-but-small items: `hq` (cover-square, frame-local) and the `dat`/`hdat` κ⁰ datum (P-17e).

**Splice target:** `blockEnrichment` at `GQ2/SectionNine.lean:1375` is currently `:= by sorry`.
`blockFrame T Blk hE2 = blockFrameImpl T Blk hE2` (`SectionNine.lean:1368`), so all `RF.*`
projections reduce to the `blockFrameImpl` field values (§5 below).

---

## 1. The two scratch files (⚠ UNTRACKED)

- `GQ2/ScratchP17d1.lean` — d1 (23 decls). Imports `GQ2.SectionSeven`, `Mathlib.GroupTheory.IsPerfect`.
- `GQ2/ScratchP17d2.lean` — d2a + d2c (27 decls). Imports `GQ2.SectionSeven`, `GQ2.EvensKahn`.

Both are **`??` untracked** in git and **not in the lake build tree** (nothing imports them).
Verify with:
```
lake env lean GQ2/ScratchP17d1.lean      # 0 errors, 0 sorries
lake env lean GQ2/ScratchP17d2.lean      # 0 errors, 0 sorries
```
Both are **std-3 clean** (`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; no new
axioms). Every scratch decl is stated for a **generic** `B : SectionSeven.MinimalBlock L`; at the
splice `B := Blk`, `L := T.LY`.

**Handoff note:** these files are on disk but uncommitted (standing rule: parallel sessions own
commits). If handing to a fresh clone, commit them first or point the new session at this worktree.
When spliced, their content should move into a real build-tree file (suggested name
`GQ2/BlockForm.lean`, importing `SectionSeven`, `EvensKahn`, `BlockModule`, `QuadraticFp2`), then
the scratch files deleted.

---

## 2. Instance-binder convention (READ FIRST — affects every splice call)

The scratch decls carry the normality facts that appear in **types** (`Y⧸R`, `Y⧸K`, `↥P⧸(S∩P)`)
as **section-variable instance binders**, because `MinimalBlock`'s `hS`/`hK` are *data*, not
instances:

- d1 `section Descend`: `variable (B) [(B.R).Normal] [(B.S.subgroupOf B.P).Normal] [(B.K).Normal]`
- d2 `section Quad`:    `variable (B) [(B.S.subgroupOf B.P).Normal]`

At the splice these **disappear**: `RF.YB = Y⧸Blk.R` / `RF.YC = Y⧸Blk.K` already have their group
instances fixed by the frame, and for `↥Blk.P⧸(Blk.S.subgroupOf Blk.P)` you supply the instances
locally:
```
haveI hRn := SectionSeven.frattiniLike_normal Blk.K Blk.hK  -- Blk.R.Normal
haveI := Blk.hS.subgroupOf Blk.P ; haveI := Blk.hK
```
`Blk.R.Normal` is **derived** — `MinimalBlock` has **no `hR` field** — via
`SectionSeven.frattiniLike_normal Blk.K Blk.hK` (since `Blk.R = SectionSeven.frattiniLike Blk.K`
by def, `MinimalBlock.R`); call it `hRn` below. Proof-irrelevance makes the binder-instance and
the `haveI`-instance defeq, so the scratch lemmas apply.

---

## 3. P-17d1 inventory → Enrichment fields

`Vmod := Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)` (= `P/S`, additively).

| Enrichment field | Fill with | Notes |
|---|---|---|
| `Vmod` | `Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)` | |
| `addV` | `Additive.addCommGroup` from `blockPS_commGroup Blk` | `blockPS_commGroup` = `CommGroup(P/S)` (needs `commutator_P_le_S`) |
| `finV` | `inferInstance` | `Additive` of finite quotient |
| `actV` | `blockActV Blk` | `DistribMulAction (Y⧸Blk.K) (Additive(P/S))`; `RF.YC = Y⧸Blk.K` defeq |
| `descend` | `blockDescend Blk` | `↥(blockMB Blk) →* (↥P⧸(S∩P))`; `RF.MB = blockMB Blk` defeq; `Multiplicative Vmod = P/S` defeq (may need `ofAdd`/`toAdd` glue) |
| `descend_surj` | `blockDescend_surjective Blk` | uses `Blk.gen : K⊔S=P` |
| `descend_ker` | `blockDescend_ker Blk` | `RF.TBsub = blockTBsub Blk` defeq |
| `descend_conj` | `blockDescend_conj Blk` | scratch proves the **additive-intertwining** form `blockPiBC Blk bb • ofMul(descend m) = ofMul(descend ⟨…⟩)`; the field wants `descend ⟨…⟩ = ofAdd(RF.piBC bb • toAdd(descend m))`. Same fact modulo `ofAdd/ofMul/toAdd` relabeling + `RF.piBC = blockPiBC Blk` (defeq). Needs a ~2-line wrapper. |

**Supporting d1 decls** (used inside the above; you generally won't cite them directly):
`blockActVY`, `blockK_smul_eq`, `blockMB`, `blockKappa`, `blockKappa_coe`,
`blockKappa_surjective`, `blockAlpha`, `blockAlpha_apply`, `blockAlpha_eq_one_iff`,
`blockKappa_ker_le_alpha`, **`blockDescend_kappa`** (the characterizing identity
`descend∘κ' = α` — the linchpin; also needed for d2b's `hqbar`), `blockPiBC`, `blockPiBC_mk'`,
`blockActV_mk'`, `blockActVY_mk`.

---

## 4. P-17d2 inventory

### 4a. `blockLam` (P-17d2a) — the `lam` argument

`blockLam Blk l : ↥Blk.R → ZMod 2 := fun r => if (r:Y) ∈ l then 0 else 1`
(needs `open scoped Classical`; noncomputable).

| decl | statement |
|---|---|
| `blockLam` | the character |
| `blockLam_eq_zero_iff` | `blockLam B l r = 0 ↔ (r:Y) ∈ l` |
| `blockLam_hom` | additivity — arg `(hidx : (l.subgroupOf B.R).index = 2)` |
| `blockLam_conj` | Y-conj-invariance — arg `(hlN : l.Normal) (hRN : B.R.Normal)` |
| `blockLam_ne` | nonzero — arg `(hlt : l < B.R)` |
| `relIndex_two_of_le` | `l ≤ R`, `relIndex ≤ 2`, `l ≠ R` ⟹ `relIndex = 2` |

**Instantiation at the splice** (per `l : RF.DR`, `h : l ≠ RF.zeroDR`, with `RF.DR =
{R' // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}`, `RF.zeroDR = ⟨Blk.R, …⟩`):
- `l.1 ≠ Blk.R` from `h` via `fun heq => h (Subtype.ext heq)`.
- `hidx : (l.1.subgroupOf Blk.R).index = 2` = `relIndex_two_of_le Blk l.1 l.2.2.1 l.2.2.2 (l.1≠R)`
  (recall `relIndex = (subgroupOf).index` by def).
- `hlN := l.2.1`, `hlt := lt_of_le_of_ne l.2.2.1 (l.1≠R)`.

So `blockLam Blk l.1` + the three property-lemmas give the `(lam, hlam_hom, hlam_conj, hlam_ne)`
tuple that both `prop_7_4` and `mForm_of_qbar` consume.

### 4b. `hquad` (P-17d2c, DONE)

`β(⟦a⟧,⟦b⟧) = qbar(ab)+qbar a+qbar b = λ([b,a])` (single conjugated commutator) is the linchpin;
biadditivity then follows from the commutator identity + `hlam_hom`/`hlam_conj` (**no vanish
lemmas needed**).

| decl | role |
|---|---|
| `comm_mem_R_of_K` | `[b,a] ∈ R` for `a,b ∈ K` (via `a[b,a]a⁻¹ = (ab)²(a²b²)⁻¹` + `hsq`) |
| `mkK_mul` | `⟦a⟧⟦b⟧ = ⟦ab⟧` (K-membership form) |
| `exists_K_rep` | every `v : P/S` has a K-rep (from `Blk.gen`) |
| `blockQbar_beta` | **`β = λ([b,a])`** |
| `blockQbar_map_zero` | `qbar 1 = 0` |
| `blockQbar_polar_add` | **biadditivity** `β(u·v,w) = β(u,w)+β(v,w)` |
| `isQuadraticFp2_of_mul` | generic `[CommGroup G]` mul-form → `IsQuadraticFp2 (·∘toMul)` |

**Splice:** `hquad l h := isQuadraticFp2_of_mul (G := ↥P⧸(S∩P)) qbar_l (blockQbar_map_zero Blk …)
(blockQbar_polar_add Blk …)` — with `G`'s `CommGroup` = `blockPS_commGroup Blk` (so `Additive G =
Vmod`, matching `addV`). `qbar_l` = the `prop_7_4` output for `λ = blockLam Blk l.1`.

### 4c. `hns` (P-17d2c, DONE)

Radical built **directly as `Subgroup Y`** via a total extension `qbP y := if y∈P then qbar⟦y⟧
else 0`; `chief` ⟹ `radSub = P` ⟹ `β≡0` ⟹ `qbar` additive; endgame contradicts `lemma_7_1_dual`.

| decl | role |
|---|---|
| `qbP`, `qbP_mem` | total extension of `qbar` to `Y` |
| `mkP_mul` | `⟦a⟧⟦b⟧ = ⟦ab⟧` (P-membership form) |
| `beta_conj` | `β(g•a, g•b) = β(a,b)` from `hinv` |
| `betaP`, `betaP_biadd`, `betaP_one` | polar form as a `Y`-function + its subgroup-axiom facts |
| `radSub`, `radSub_le_P`, `S_le_radSub`, `radSub_normal` | the radical `{y∈P \| ∀q∈P, β(y,q)=0}` as a Y-normal subgroup, `S ≤ · ≤ P` |
| `blockQbar_nonsingular_mul` | multiplicative non-degeneracy (chief ⟹ radSub=P ⟹ additive ⟹ `additive_qbar_absurd`) |
| `additive_qbar_absurd` | endgame: `Xk={k∈K\|qbar⟦k⟧=0}` is Y-normal, `R≤Xk`, `[K:Xk]=2` (via `Subgroup.index_eq_two_iff` + witness) ⟹ contradicts `lemma_7_1_dual` |
| `nonsingular_of_mul` | generic `[CommGroup G]` mul-nondegeneracy → `Nonsingular (·∘toMul)` |

**Splice:** `hns l h := nonsingular_of_mul (G := ↥P⧸(S∩P)) qbar_l (blockQbar_nonsingular_mul Blk …
hqbar_ne_l hinv_l)` — `hqbar_ne_l : ∃ a, qbar_l a ≠ 0` and `hinv_l` from `prop_7_4`'s output
(2nd/3rd conjuncts). `G`'s `CommGroup` = `blockPS_commGroup Blk` (matches `addV`).

---

## 5. Frame facts (`blockFrameImpl`, `GQ2/BlockFrameImpl.lean`)

All `rfl`/defeq from `blockFrame = blockFrameImpl`:

- `RF.YB = Y ⧸ Blk.R`, `RF.YC = Y ⧸ Blk.K`
- `RF.MB = Blk.K.map (QuotientGroup.mk' Blk.R)` (`MB_eq := rfl`)
- `RF.TBsub = ((Blk.K ⊓ Blk.S) ⊔ Blk.R).map (QuotientGroup.mk' Blk.R)` (`TBsub_eq := rfl`)
- `RF.piBC = QuotientGroup.map Blk.R Blk.K (MonoidHom.id Y) _` (= `blockPiBC Blk`)
- `RF.DR = {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}`
- `RF.zeroDR = ⟨Blk.R, hRn, le_refl _, _⟩`
- `RF.scalarCover l h` : `CentralCover (Y⧸l.1)`-style — `cover := Y⧸l.1`,
  `p := QuotientGroup.map l.1 Blk.R (id) _`, `z := QuotientGroup.mk' l.1 r₀` (r₀ ∈ R∖l.1),
  `z_sq`, `central`, `ker_eq : p.ker = ⟨z⟩` (see `BlockFrameImpl.lean:91-191`).

`hRn : Blk.R.Normal := SectionSeven.frattiniLike_normal Blk.K Blk.hK` — **derived, NOT a
`MinimalBlock` field** (`Blk.R = SectionSeven.frattiniLike Blk.K` by def, `MinimalBlock.R`).

---

## 6. The `blockEnrichment` signature extension (REQUIRED for d2b)

`prop_7_4` (`SectionSeven.lean:2579`) needs a framed head **and the tame quotient**:
```
prop_7_4 (π : Y →* H) (hπ : Surjective π) (hkerπ : π.ker = L)
         (cH : ContinuousMonoidHom Ttame H) (hcH : Surjective cH)
         (B) (hRN) (hsq) (lam) (hlam_hom) (hlam_conj) (hlam_ne)
  : ∃ qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2,
      (∀ k ∈ K, lam⟨k²⟩ = qbar⟦k⟧)  -- hspec
      ∧ qbar ≠ 0                      -- nonzero
      ∧ (∀ y p ∈ P, qbar⟦ypy⁻¹⟧ = qbar⟦p⟧)  -- Y-invariance
```
- `π := T.piY`, `hπ := T.piY_surjective`, `hkerπ := T.ker_piY` (all from `MarkedTarget`, which
  is `blockEnrichment`'s `T`).
- **`cH`/`hcH` are NOT currently available** in `blockEnrichment`'s signature. So
  **`blockEnrichment` must gain `(cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)`.**
  This is benign (statement-safe extension; changes the def's own signature, no existing callers
  of `blockEnrichment` yet — grep to confirm). Per the design note, the induction has this: the
  §9 caller carries the target `F` and passes `F.alpha` (see P-17d parent ticket / `prop_8_9_aux`).
  **Confirm the exact `cH` source at the call site** (likely where `blockEnrichment`/`prop_8_9`
  meet in the §9 recursion) before finalizing the signature.

`mForm_of_qbar` (`FrameEnrichment.lean:48`) needs NO head — just `(piB := mk' Blk.R)`,
`(hker := QuotientGroup.ker_mk' Blk.R)`, `blockLam`, `hlam_hom`, `hsq`, `qbar`, `hspec`.

**`hsq : ∀ k ∈ Blk.K, k*k ∈ Blk.R`** (shared input to both) is derivable **publicly** — do NOT
reach for the `private` `sq_mem_R` (`SectionSeven.lean:835`). `Blk.R = frattiniLike Blk.K =
Subgroup.closure ({squares} ∪ {commutators})`, so
`fun k hk => Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)` gives `k*k ∈ Blk.R`.

---

## 7. Remaining work

### d2b — `qbar`/`q`/`hrad`/`hTzero`/`hqbar`/`hinv` + `hq`

For each `l : RF.DR`, `h : l ≠ RF.zeroDR`, set `λ := blockLam Blk l.1` and its props (§4a), then:

1. `⟨qbar_l, hspec_l, hne_l, hinv_raw_l⟩ := prop_7_4 T.piY … cH hcH Blk hRn hsq λ …`.
2. **`qbar l h`** := `fun v : Vmod => qbar_l (Additive.toMul v)`.
3. **`hinv l h`** := repackage `hinv_raw_l` (Y-conjugation invariance) as
   `IsInvariant RF.YC (qbar l h)`; the `RF.YC = Y⧸Blk.K` action is `blockActV`, whose `mk' K y`
   smul reduces to the `y`-conjugation (`blockActV_mk'` + `blockActVY_mk` from d1). ~10 lines.
4. `⟨qM_l, hval_l, hrad_l, hTzero_l⟩ := mForm_of_qbar Blk (mk' Blk.R) (ker_mk') λ hlam_hom hsq qbar_l hspec_l`.
   - **`q l h`** := `qM_l` (`↥(Blk.K.map (mk' Blk.R)) = ↥RF.MB` defeq).
   - **`hrad l h`**, **`hTzero l h`** := `hrad_l`, `hTzero_l` (match the field shapes; watch the
     `TBsub_le_MB` coercion — already the shape `mForm_of_qbar` outputs).
5. **`hqbar l h`** : `q l h m = qbar l h (toAdd (descend m))`. Couples `hval_l`
   (`qM_l⟦π_B k⟧ = λ(k²)`) with `hspec_l` (`λ(k²) = qbar_l⟦k⟧`) through **`blockDescend_kappa`**
   (`descend([k]_R) = [k]_S`) — i.e. `toAdd(descend ⟦k⟧_R) = ⟦k⟧_S`. ~15-25 lines, the main
   d2b glue.
6. **`hquad`/`hns`** := as §4b/§4c (DONE — just apply).
7. **`hq l h`** (cover square `x̃² = z^{(q l h ⟦p x⟧)}`): **frame-local**, NOT from `mForm_of_qbar`
   (see `FrameEnrichment.lean:20-22`). Prove from `RF.scalarCover l h`'s `z_sq`/`ker_eq` in
   `blockFrameImpl` — the concrete pushout cover `Y/l.1 ↠ Y/R`. This is the one genuinely-new
   d2b item; scope ~30-50 lines. Cross-check against how `RadicalCoverData`/`Enrichment.radData`
   (`SectionEight.lean:1657`) consume `hq`.

### d3 — `dat`/`hdat` + assembly

- `dat l h : FactorSet RF.YC Vmod`, `hdat l h : IsEquivariantFactorSet (qbar l h) (dat l h)` —
  from `kappa0_exists` (`SectionNine.lean` ~1351). **`kappa0_exists` is itself sorried (P-17e)**;
  `dat`/`hdat` consume its *settled statement* as a black box, so d3 closes "modulo P-17e".
  `kappa0_exists` needs `hsimple : FoxH.IsSimpleModTwo` (from `Blk.chief` + `nontrivial_action`)
  and `htame : ActsThroughTame` (head `H` via `Y/K ↠ Y/L_Y ≅ H`; `[K,P]≤S` + `FoxH.lemma_5_12`)
  — see P-17d3 ticket + `docs/p17e-kappa0-scoping.md`.
- Final: assemble the `Enrichment` record from all fields; discharge `blockEnrichment`'s `sorry`.

---

## 8. Known gotchas (all hit + resolved in the scratches)

- **`Multiplicative (Additive G)` vs `G`** — defeq but elaboration-fragile. `descend`/`actV`/`qbar`
  fields want `Multiplicative Vmod` / `Vmod = Additive(P/S)`; scratch works in `P/S` directly.
  Bridge with `Multiplicative.ofAdd`/`toAdd`/`Additive.ofMul`/`toMul` (all `rfl` on the synonym:
  `toMul_add`, `toMul_zero` are `rfl`). `nonsingular_of_mul`/`isQuadraticFp2_of_mul` already do
  this packaging generically — reuse them.
- **`rw [← QuotientGroup.mk_mul]` needs a trailing `rfl`** (`mkK_mul`/`mkP_mul` pattern): the
  subgroup product `⟨a,_⟩*⟨b,_⟩ = ⟨a*b,_⟩` is defeq but not auto-closed.
- **Dependent-motive `rw` failures**: rewriting a group element that a membership proof depends on
  (e.g. `↑(b*⟨k₁⟩)` inside `⟨_, hmem⟩`) fails "motive is not type correct". Fix: rewrite via a
  `Subtype.ext`/`show` equality of the whole `mk`, or `have he : mk⟨…⟩ = mk⟨…⟩*mk⟨…⟩ := by rw
  [mkP_mul]; rfl` then `rw [he]`.
- **`QuotientGroup.eq_one_iff.mpr` as a term** doesn't resolve — use it as a `rw` instead
  (`rw [QuotientGroup.eq_one_iff]; exact …`).
- **`Set` pointwise mul** (`↑K * ↑S` in `exists_K_rep`/`blockDescend_surjective`) needs
  `open scoped Pointwise` + `Subgroup.mul_normal` (needs `[Blk.S.Normal]`).
- **`Nonsingular`/`IsQuadraticFp2` need `[AddCommGroup Vmod]`** = `CommGroup(P/S)` =
  `blockPS_commGroup` — not present from the bare `Normal` instance. That is exactly why the
  scratch proves the *multiplicative* forms + generic packaging; supply `blockPS_commGroup Blk`
  at the splice.

---

## 9. Verification protocol

- Per-file while iterating: `lake env lean GQ2/<File>.lean` (0 errors, 0 sorries).
- Axioms: append `#print axioms GQ2.<decl>` and check ⊆ `{propext, Classical.choice, Quot.sound}`
  ∪ (ticket `Ax` column). **No new axioms** — census is fixed (B1,B2,B3c,B4,B5,B6,B7,B7',B8,B9,
  B10,B11a,B11b,B12,B13 = 15); adding one requires explicit user approval.
- Project gate: `bash scripts/check_axioms.sh` (sorried theorems must be in `SORRY_ALLOWLIST`).
- **Do NOT commit** (parallel sessions own commits). **Do NOT `git checkout` co-owned files**
  (`SectionNine.lean`, `SectionEight.lean`, `docs/tickets.md`, …) — re-read before every Edit;
  parallel agents touch them concurrently.

---

## 10. Pointers

- Tickets: `docs/tickets.md` rows P-17d, P-17d1, P-17d2(+a/b/c), P-17d3, P-17e.
- `Enrichment` struct: `GQ2/SectionEight.lean:1604-1649`.
- `prop_7_4`: `GQ2/SectionSeven.lean:2579`. `mForm_of_qbar`: `GQ2/FrameEnrichment.lean:48`.
- `QuadraticFp2` (`IsQuadraticFp2`/`Nonsingular`/`IsInvariant`/`polar`): `GQ2/QuadraticFp2.lean`.
- `blockAction`/`conjHom`: `GQ2/BlockModule.lean`. Frame: `GQ2/BlockFrameImpl.lean`.
- κ⁰ scoping: `docs/p17e-kappa0-scoping.md`. §9 map: `docs/section9-extraction.md`.
