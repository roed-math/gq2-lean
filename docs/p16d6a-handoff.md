# P-16d6a handoff — the concrete R-stage obstruction datum (`stageR136` input)

**Purpose.** Everything a fresh session needs to finish **P-16d6a** (the (136) `stageR136` field of
`prop_8_9`'s recursion inputs).  Self-contained: does not rely on chat history or session task
state.  Written 2026-07-06 (Opus).  All line numbers are approximate — grep the named declaration.

---

## 0. TL;DR

* **DONE & committed** — the whole concrete R-stage obstruction datum **`blockRObstructionData`**
  (the `RObstructionData` input that `stageR136_ofRSepData` consumes, incl. the full `(R^∨)^C`
  character duality), std-3 sorry-free.  **File renamed** `GQ2/ScratchP16d6a.lean` → **`GQ2/BlockRStage.lean`**
  (git mv, 2026-07-06) — no longer a "scratch"; it is the real P-16d6a leaf.
* **DONE (a-assemble, 2026-07-06)**: **`blockStageR136`** (std-3) — the general-Γ (136) identity for
  `blockFrameImpl`, produced by `stageR136_ofRSepData (blockRObstructionData …)`.  `hE2` is
  discharged from the frame's own argument; the source residues `htriv`/`hcard`/`hfg`/`hZcount`/
  `hsep_hom` are threaded as **hypotheses** (see the correction below).  Also `blockRChar_card`
  (`#(R^∨)^C = #D_R`, via `blockToDR`).
* **Scoping correction** (important): P-16d6a was originally scoped as "extend the co-owned
  `Enrichment` with R-stage fields".  **That is wrong / unnecessary.**  P-17c (`blockFrame`,
  `GQ2/BlockFrameImpl.lean`, **done**) realizes each scalar cover concretely as `Y/l ↠ Y/R`, so the
  datum is built **directly against `blockFrameImpl`** in a leaf file — no `SectionEight`
  edit.  (`docs/p16d6-concrete-spec.md` §3 is superseded by this file.)
* **RESIDUE ARCHITECTURE CORRECTION (2026-07-06)**: `hZcount` and `hsep_hom` are **not**
  general-Γ dischargeable, so they stay **hypothesis-side** at P-16d6a (exactly like `hcard`/`hfg`)
  and are supplied **per-Γ at the P-16d6e / P-17i assembly**.  Reason: the absolute crossed-cocycle
  count `#RCocycle = z_R` is the 5.15/5.16 Euler characteristic, whose theorems (`prop_5_16_bundle`
  / the `prop_5_15` `Γ_A` analogue) are **Γ-specific** — they cannot be invoked at a generic `Γ`
  (documented for the sibling (140)/T count in `GQ2/PhaseMuIndep.lean:21`, "`Γ ≠ AbsGalQ2`").  The
  parallel (139)/M count `hMcountM` is likewise kept a source hypothesis fed at assembly
  (`GQ2/RecursionSplice.lean`, `half139_via_radData`).  So the P-16d6a deliverable is the general-Γ
  **reduction** `blockStageR136` (done); the concrete counts belong to the assembly lane.
  **`hsep_hom` is ALSO Γ-specific 5.15/5.16 content, NOT a separate abstract build** (confirmed by
  reading the paper's Prop 8.9 proof, pp. 42–43): `obs g = 0 ⟺ ob(g) ∈ (D_R)^⊥` in `H²(Γ,R)`, and
  the separation is the **perfect pairing** `D_R = (R^∨)^C ≅ H²_{Γ,ρ}(R)^∨` (paper p. 42) — the same
  duality as `hZcount`.  It is discharged per-Γ at the assembly alongside `hZcount`, from ONE duality
  package.  (Earlier-in-session "P-16d6a-sep = missing character-separation infra" was wrong; §3.)

---

## 1. Where P-16d6a sits (context)

`prop_8_9` (`GQ2/SectionEight.lean:2143`, still `sorry`) is the §8 capstone.  Its reducer layer +
(140) engine are **done** in `GQ2/RecursionSplice.lean` (see `docs/p16d6-plan.md`).  The remaining
concrete work was split into **P-16d6a–e**:

| sub | scope | status |
|---|---|---|
| **P-16d6a** | (136) `stageR136`: the R-stage `RObstructionData` + residues | ← **this file** |
| P-16d6b | (140) μ-independence `hμ` | separate (another agent) |
| P-16d6c | (140) Prop-8.8 core (`hM`/`hphase`/witness) | separate |
| P-16d6d | (139) for `G_ℚ₂` | separate |
| P-16d6e | final assembly + `prop_8_9_of` splice | gated on a–d + P-16c |

`stageR136_ofRSepData` (proved, P-16d2) turns an `RObstructionData` + residues into the exact
`stageR136` field.  So P-16d6a = **build the `RObstructionData` for the concrete frame** (done) +
**discharge the residues** (remaining).

---

## 2. What is DONE — `GQ2/BlockRStage.lean` (renamed from `ScratchP16d6a.lean`)

Committed, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` for every declaration.
Build/verify:

```
lake build GQ2.BlockRStage
# (optional) lean_verify GQ2.blockRObstructionData ; lean_verify GQ2.blockStageR136
```

It is a **leaf** (not yet imported by the main build — like `ScratchP17d1/d2.lean`; wire into
`GQ2.lean` at the P-16d6e assembly, §5).  Sorry-free, so it needs no `SORRY_ALLOWLIST` entry.

Declarations, in dependency order (namespace `GQ2`, `open SectionEight SectionSeven`):

1. `blockRCoverData T Blk hE2 : RCoverData (blockFrameImpl T Blk hE2)` — the compat covers:
   `coverMap l h = QuotientGroup.mk' l.1` (the quotient `Y ↠ Y/l`), `coverMap_lifts = rfl`.
2. `RCharSub Blk : Submodule (ZMod 2) (Additive ↥Blk.R →+ ZMod 2)` — **`D_Rmod`** = the
   Y-conjugation-invariant 𝔽₂-characters of `R = Blk.R = Φ(K)`; + a `Finite` instance.
3. Forward map `χ ↦ ker χ`: `RCharKerSub` (kernel in `↥Blk.R`), `RCharMulHom` (χ as
   `↥R →* Multiplicative 𝔽₂`, for the index calculus), `RCharKerSub_eq_ker`, `RCharKer`
   (kernel pushed to `Subgroup Y`), and the three `D_R`-membership proofs `RCharKer_le`,
   `RCharKer_normal`, `RCharKer_relIndex_le`.
4. `BlockDR Blk` (abbrev = the `.DR` subtype), inverse map `RCharOfHom`/`RCharOf`
   (`R' ↦ [r ∉ R']`, the index-≤2 indicator; additive via `mul_mem_iff_of_index_two` with a `≤2`
   case-split covering `R' = R` = the zero character; Y-invariant from `R'.Normal`).
5. Bijectivity: `RChar_eq_ind` (a character is the indicator of its own kernel), `RCharKer_RCharOf`
   (right inverse), `RCharKer_inj` (injective).
6. `blockToDR T Blk hE2 : ↥(RCharSub Blk) ≃ (blockFrameImpl T Blk hE2).DR` = the `(R^∨)^C`
   bijection (`Equiv.ofBijective (χ ↦ ker χ)`).  Codomain is `.DR` (not the `BlockDR` abbrev) so
   the assembly's coercions line up.  `blockToDR_coe` (`= rfl`), `RCharKer_zero` (ker of `0` = `R`).
7. **`blockRObstructionData T Blk hE2 : RObstructionData (blockFrameImpl T Blk hE2)`** — the payload.
   Fields: `toRCoverData := blockRCoverData`, `DRmod := ↥(RCharSub Blk)`, `toDR := blockToDR`,
   `h0`, `pair :=` the submodule inclusion `(RCharSub Blk).subtype`, and `pair_coverMap` proving
   `d(r) = zsign(mk' (ker d) ↑r)` (character value = cover kernel-sign; via `RChar_eq_ind` +
   the `mk' N r = 1 ↔ r ∈ N` membership + `zsign_one`, phrased through `RCharKer Blk d` to dodge
   the opaque-`.DR` coercion).
8. **`blockRChar_card`** — `Nat.card ↥(RCharSub Blk) = Nat.card (blockFrameImpl T Blk hE2).DR`
   (`Nat.card_congr blockToDR`): the `(R^∨)^C = D_R` cardinality bridge, so `z_R`'s `#D_R` factor
   reads as the intrinsic invariant-character count `#(R^∨)^C`.
9. **`blockStageR136`** — the general-Γ (136) identity for `blockFrameImpl`, `= stageR136_ofRSepData
   (RF := blockFrameImpl T Blk hE2) b F (blockRObstructionData T Blk hE2) htriv hcard hfg hE2
   hsep_hom hZcount`.  Hypotheses `htriv`/`hcard`/`hfg`/`hsep_hom`/`hZcount` are the source residues
   (§3); `hE2` is the frame argument.  Conclusion = the `stageR136` field of `RecursionInputs`
   verbatim.  **Section-variable order gotcha**: `stageR136_ofRSepData` takes the section vars
   `RF b F` (declared in that order, all used) *before* its written binders — so the call is
   `stageR136_ofRSepData (RF := …) b F D htriv hcard hfg hE2 hsep_hom hZcount`, NOT `D` first.

### Lean gotchas already solved (reuse these)
* `(blockFrameImpl …).DR`, `.scalarCover`, `.zeroDR` **do** reduce (blockFrameImpl is term-mode
  after the outer `by`); field access like `coverMap … = mk' l.1` closes by `rfl`.
* Make `blockToDR` land in `.DR` (not a separate abbrev) or `rw` fails to match `↑x` vs `x.1`.
* In `pair_coverMap`, phrase membership through `RCharKer Blk d` (a clean `Subgroup Y`), **not**
  `(blockToDR … d).1`, to avoid the `.1`/`↑` coercion mismatch on the opaque `.DR`.
* `zsign` lives in `SectionEight.CentralObstruction`; `zsign D x = if x = 1 then 0 else 1`
  (`zsign_one`, `zsign_z`, `zsign_mul` are the useful lemmas).
* `Additive.ofMul (a*b) = ofMul a + ofMul b`, `ofMul 1 = 0`, `ofMul a⁻¹ = -ofMul a` are all `rfl`.

---

## 3. The residues — where each is discharged

> **Correction (2026-07-06).**  `blockStageR136` now threads all five source residues as
> hypotheses; `hE2` is discharged.  The earlier plan to *discharge* `hZcount`/`hsep_hom` inside
> P-16d6a is revised: the absolute count `#RCocycle = z_R` is a **Γ-specific** 5.15/5.16 fact
> (`prop_5_16_bundle` / `prop_5_15` cannot be invoked at a generic `Γ` — see `PhaseMuIndep.lean:21`),
> and the parallel (139) count `hMcountM` is kept a source hypothesis fed at assembly
> (`RecursionSplice.half139_via_radData`).  So `hZcount`/`hsep_hom` stay **hypothesis-side at
> P-16d6a** and are supplied **per-Γ at P-16d6e / P-17i**, alongside `hcard`/`hfg`.  What follows
> describes each residue and the concrete route the assembly (or `P-16d6a-sep`) will take.

**Consumer** (proved, `GQ2/RStageObstructionBuild.lean:686`):

```lean
theorem stageR136_ofRSepData (D : RObstructionData RF)
    (htriv  : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard  : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg    : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hE2    : ∀ e : E, e ^ 2 = 1)
    (hsep_hom : ∀ g : BoundaryLifts b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
                  ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLifts b F T, Nat.card (RCocycle RF f₀.1.1) = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR, (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB)
```

Its conclusion **is** the `stageR136` field of `RecursionInputs` verbatim (checked).  Instantiate
`RF := blockFrameImpl T Blk hE2`, `D := blockRObstructionData T Blk hE2`.  Residues to supply:

* **`hE2` — FREE.**  It is literally the `hE2` argument already threaded into `blockFrameImpl` /
  `blockRObstructionData`.
* **`htriv` — easy.**  The `DistribMulAction Γ (ZMod 2)` in play is the trivial action; discharge
  `fun _ _ => rfl` (or from the frame's action definition).  `Γ` is `GammaA` / `AbsGalQ2` at use.
* **`hcard : Nat.card (H2 Γ (ZMod 2)) = 2` — source.**  `#H²(Γ,𝔽₂) = 2`; a Γ-specific fact
  (props 5.15/5.16 territory).  Not part of the R-stage build.
* **`hfg` — source.**  t.f.g.: `GammaA` via P-03 (proved), `AbsGalQ2` via **B1** (reserve B1's
  first consumption for P-17i — keep `hfg` a hypothesis, do not discharge inside P-16d6a).
* **`hZcount : ∀ f₀, Nat.card (RCocycle RF f₀.1.1) = RF.zR` — the z_R torsor count (Γ-specific).**
  `RF.zR = (Nat.card ↥Blk.R)^2 * Nat.card RF.DR` (`SectionEight.lean:1398`).  `RCocycle`
  (`RStageObstructionBuild.lean:493`) is the crossed `Z¹(Γ, R)`.  **Route** (per-Γ, at assembly):
  (i) `R` is **abelian** — `SectionSeven.lean:623` `hRcentral` gives `R ≤ Z(K)` and `R ≤ K`, so an
  elem-ab-2 `𝔽₂`-module once one adds exp-2 (the scalar layer; check against `Blk`); (ii) then
  `RCocycle RF f₀ ≃ Z¹(Γ, R)` (multiplicative crossed ↔ additive, via `Additive`); (iii)
  `#Z¹(Γ,R) = #R²·#(R^∨)^C` is the 5.15/5.16 Euler characteristic (`prop_5_16_bundle` clause 2 for
  `AbsGalQ2`; the `prop_5_15`/`HalfTorsorGammaA` analogue for `GammaA`) — **Γ-specific, cannot run
  at generic `Γ`**; (iv) `#(R^∨)^C = #D_R` is **`blockRChar_card`** (done), giving `= #R²·#D_R = z_R`.
  So `hZcount` = steps (i)–(iii) at the concrete `Γ`; only (iv) is frame-abstract (done).
* **`hsep_hom` — the (R^∨)^C separation.  Γ-SPECIFIC (5.15/5.16 duality), NOT abstract infra.**
  `obs RF D htriv hcard g.1.1 = 0 ⟹ g` lifts to `Y`.  **Resolved by reading the paper's Prop 8.9
  proof (pp. 42–43).**  `obs g d = ⟨d, ob(g)⟩` is the `𝔽₂`-pairing of the character `d ∈ D_R` with
  the **full `R`-valued obstruction** `ob(g) ∈ H²(Γ,R)`; standard obstruction theory gives
  `ob(g) = 0 ⟺ g lifts to Y` (abstract).  So `obs g = 0` (all `d`) `⟺ ob(g) ∈ (D_R)^⊥`, and the
  separation is exactly `(D_R)^⊥ = 0`, i.e. the **perfect pairing** `D_R × H²(Γ,R) → 𝔽₂`.  The paper
  (p. 42, top) records this as the arithmetic duality
    `D = (T^∨)^C ≅ H²_{Γ,ρ}(T)^∨`   (here `T = R`),
  supplied by **props 5.15/5.16** — the SAME Γ-specific duality behind `hZcount`/`hcard`, NOT a
  general-Γ fact and NOT an `H²(Γ,R)` dévissage.  (My earlier-in-session "P-16d6a-sep = missing
  character-separation infra" framing was wrong: the duality detects ALL of `H²(Γ,R)`, so the
  `[Y,R] ≠ ⊥` worry — R is only hypercentral in `Y`, `lemma_7_2` gives central in `K` only — is
  moot.)  The paper's own finish is "Fourier inversion (125) on the full `R`-valued obstruction" +
  the Frattini surjectivity (`surj_of_piB_surj`, done) — no coordinate/separation lemma.
  **Existing hooks**: `mapCoeff2` (`Cohomology.lean:429`, `H²(Γ,R) → H²(Γ,𝔽₂)` along a character —
  functoriality DOES exist, contra `section8-extraction.md:262`), `homLift_of_split`,
  `obs_zero_iff_pairClass_zero`.  **Route** (P-16d6e, per Γ): set up `DistribMulAction Γ (Additive R)`
  (well-defined since `R` abelian — conj by any `π_B`-lift), build `ob(g) ∈ H²(Γ,R)`, supply the
  5.15/5.16 perfect pairing `D_R ≅ H²(Γ,R)^∨`; then `hsep_hom` follows.

**Order (at the P-16d6e assembly, per source Γ):** supply `htriv` (`fun _ _ => rfl` when the action
is trivial), `hcard`/`hfg` (source), then discharge `hZcount` and `hsep_hom` from the ONE Γ-specific
duality package `D_R ≅ H²(Γ,R)^∨` + `z_R = |Z¹_{Γ,ρ}(R)|` (props 5.15/5.16, paper p. 42; `prop_5_16`
for `AbsGalQ2`, `prop_5_15`/`HalfTorsorGammaA` for `GammaA`) → then `blockStageR136 … : (136)` for
that Γ directly (`blockStageR136` already IS the `stageR136_ofRSepData` call).  **There is no
separate abstract "P-16d6a-sep" build** — `hZcount` + `hsep_hom` are two faces of the same duality.

---

## 4. Key upstream facts (so you don't re-derive them)

* `blockFrameImpl T Blk hE2 : RecursionFrame T Blk` (`GQ2/BlockFrameImpl.lean`, P-17c ✓):
  `YB = Y/Blk.R`, `piB = mk' Blk.R`, `ker_piB = Blk.R`; `DR = {R' : Subgroup Y // R'.Normal ∧
  R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}`; `zeroDR = ⟨Blk.R, …⟩`; `scalarCover l h` = the cover
  `Y/l ↠ Y/R` with `cover = Y/l.1`, `p = QuotientGroup.map l.1 Blk.R id`, `z = mk' l.1 r₀`
  (`r₀ ∈ R∖l`), `ker p = ⟨z⟩`.
* `Blk.R = frattiniLike Blk.K` (`SectionSeven.MinimalBlock.R`, line ~157); normal via
  `frattiniLike_normal Blk.K Blk.hK`.
* `RObstructionData` / `RCoverData` / `obs` / `RCocycle` / `stageR136_ofRSepData` all live in
  `GQ2/RStageObstructionBuild.lean` (P-16d2, proved).  `stageR136_ofRObstructionData` (line ~422)
  is the version taking `hsep`/`hfib` directly if you prefer a different residue split.
* `EvensKahn.mul_mem_iff_of_index_two` (`GQ2/EvensKahn.lean`, namespace `GQ2`) is the index-2
  character additivity lemma (used in `RCharOfHom`; also in P-17d2a's `blockLam`).

**Overlap note:** P-17d2a's `blockLam` (`GQ2/ScratchP17d2.lean`, banked) is the same index-2
indicator character as the *inverse* of `blockToDR`.  When both P-16d6a and P-17d2 splice, factor
the shared index-2-character↔subgroup duality into one place.

---

## 5. Splicing plan (state + remaining)

`GQ2/BlockRStage.lean` is a **leaf**, imported by nothing, sorry-free, std-3.  Progress:

1. ✅ **DONE** — renamed `ScratchP16d6a.lean` → `GQ2/BlockRStage.lean` (git mv; imports
   `GQ2.BlockFrameImpl`, `GQ2.RStageObstructionBuild`).  Still a **leaf** (no co-owned
   `SectionEight` touch).
2. ✅ **DONE** — `blockStageR136 : (136) for blockFrameImpl` via `stageR136_ofRSepData`, with the
   residues as hypotheses; plus `blockRChar_card` (`#(R^∨)^C = #D_R`).
3. **REMAINING** — the residue lemmas `hZcount` (per-Γ count, §3) and `hsep_hom` (P-16d6a-sep) are
   supplied **at the P-16d6e assembly / P-17i**, per source `Γ` (`GammaA`, `AbsGalQ2`).  §9 (P-17i,
   the master induction) consumes `blockStageR136` as the `stageR136` field of each of the two
   `RecursionInputs` bundles.
4. **REMAINING** — wire `GQ2.BlockRStage` into the root import (`GQ2.lean`), a one-line non-co-owned
   edit, when P-16d6e lands (keep `lake build` + the sorry-allowlist gate green).  Deferred to
   P-16d6e so the leaf doesn't enter the full build before its consumers exist.

---

## 6. Pointers

* P-16d6a leaf (datum + `blockStageR136`): `GQ2/BlockRStage.lean` (renamed from `ScratchP16d6a.lean`).
* Reducer layer + (140) engine: `GQ2/RecursionSplice.lean`; narrative `docs/p16d6-plan.md`.
* Concrete-pass spec for the whole capstone: `docs/p16d6-concrete-spec.md` (its **§3 (stageR136)
  is superseded by this file** — the "extend Enrichment" framing is obsolete).
* Ticket board rows P-16d6a–e: `docs/tickets.md` (co-owned; may be uncommitted — this file is the
  durable copy of the P-16d6a breakdown).  Dependency diagram: `docs/p16-ticket-split.md`.
* P-16d2 obstruction engine: `GQ2/RStageObstructionBuild.lean`.  Concrete frame: `GQ2/BlockFrameImpl.lean`.
