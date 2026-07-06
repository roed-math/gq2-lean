# P-16d6a handoff — the concrete R-stage obstruction datum (`stageR136` input)

**Purpose.** Everything a fresh session needs to finish **P-16d6a** (the (136) `stageR136` field of
`prop_8_9`'s recursion inputs).  Self-contained: does not rely on chat history or session task
state.  Written 2026-07-06 (Opus).  All line numbers are approximate — grep the named declaration.

---

## 0. TL;DR

* **DONE & committed** (`GQ2/ScratchP16d6a.lean`, std-3 sorry-free, commit `5d43131`): the whole
  concrete R-stage obstruction datum **`blockRObstructionData`**, i.e. the `RObstructionData`
  input that `stageR136_ofRSepData` consumes.  This includes the full `(R^∨)^C` character duality.
* **Scoping correction** (important): P-16d6a was originally scoped as "extend the co-owned
  `Enrichment` with R-stage fields".  **That is wrong / unnecessary.**  P-17c (`blockFrame`,
  `GQ2/BlockFrameImpl.lean`, **done**) realizes each scalar cover concretely as `Y/l ↠ Y/R`, so the
  datum is built **directly against `blockFrameImpl`** in a leaf scratch file — no `SectionEight`
  edit.  (`docs/p16d6-concrete-spec.md` §3 is superseded by this file.)
* **REMAINING** (the "a-residues" sub-task): discharge the source residues **`hsep_hom`** (hard
  separation) and **`hZcount`** (z_R torsor count) plus the easy `htriv`/`hcard`, then call
  `stageR136_ofRSepData` to produce the (136) identity.  `hE2` is free.

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

## 2. What is DONE — `GQ2/ScratchP16d6a.lean`

Committed, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` for every declaration.
Build/verify:

```
lake build GQ2.ScratchP16d6a
# (optional) lean_verify GQ2.blockRObstructionData
```

It is a **banked scratch** (not imported by the main build — like `ScratchP17d1/d2.lean`).  See §5
for splicing.

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

## 3. What REMAINS — the residues (the a-residues sub-task)

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
* **`hZcount : ∀ f₀, Nat.card (RCocycle RF f₀.1.1) = RF.zR` — the z_R torsor count.**
  `RF.zR = (Nat.card ↥Blk.R)^2 * Nat.card RF.DR` (`SectionEight.lean:1398`).  `RCocycle`
  (`RStageObstructionBuild.lean:493`) is the crossed `Z¹(Γ, R)`.  This is the 5.15/5.16 count for
  the R-extension — a source/numeric obligation, analogous to `hMcount` in the (139) lane.
* **`hsep_hom` — THE HARD PIECE (the (R^∨)^C separation).**  `obs RF D htriv hcard g.1.1 = 0 ⟹ g`
  lifts to `Y`.  `obs` (`RStageObstructionBuild.lean:336`) is the scalar obstruction class in
  `H²(Γ,𝔽₂)` detecting whether a `B`-stage boundary lift `g` lifts through the `D_R` covers.
  P-16d2 proved the **abstract** direction (`obs_zero_iff_lifts`, `obs_zero_iff_pairClass_zero`),
  but `hsep_hom` itself is **not abstractly derivable** — it is the concrete
  `R`-elementary-abelian + Frattini + `C`-action property that the `(R^∨)^C`-pairing actually
  *detects* the lift.  Expect this to be its own focused pass (comparable to P-16d2's `hsep`);
  likely wants a sub-ticket **P-16d6a-sep**.

**Recommended order:** `hE2`/`htriv` (trivial) → `hZcount` (numeric, mirror the (139) `hMcount`
route) → `hsep_hom` (the hard separation, dedicated pass).  Then one `stageR136_ofRSepData …` call
gives the `stageR136` field for the concrete frame.

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

## 5. Splicing plan (when residues land)

`ScratchP16d6a.lean` is banked WIP, imported by nothing.  To integrate:

1. Rename/move to a real leaf, e.g. `GQ2/BlockRStage.lean` (imports `GQ2.BlockFrameImpl`,
   `GQ2.RStageObstructionBuild`).  Keep it a **leaf** (do not touch co-owned `SectionEight`).
2. Add the residue lemmas (`hZcount`, `hsep_hom`, …) and a
   `blockStageR136 : (the (136) identity for blockFrameImpl)` via `stageR136_ofRSepData`.
3. §9 (P-17i, the master induction) consumes it as the `stageR136` field when building the two
   `RecursionInputs` bundles; that is the P-16d6e assembly, not P-16d6a.
4. Wire the file into the root import (`GQ2.lean`) — a one-line, non-co-owned edit — and confirm
   `lake build` + the sorry-allowlist gate stay green.

---

## 6. Pointers

* Banked datum: `GQ2/ScratchP16d6a.lean` (commit `5d43131`).
* Reducer layer + (140) engine: `GQ2/RecursionSplice.lean`; narrative `docs/p16d6-plan.md`.
* Concrete-pass spec for the whole capstone: `docs/p16d6-concrete-spec.md` (its **§3 (stageR136)
  is superseded by this file** — the "extend Enrichment" framing is obsolete).
* Ticket board rows P-16d6a–e: `docs/tickets.md` (co-owned; may be uncommitted — this file is the
  durable copy of the P-16d6a breakdown).  Dependency diagram: `docs/p16-ticket-split.md`.
* P-16d2 obstruction engine: `GQ2/RStageObstructionBuild.lean`.  Concrete frame: `GQ2/BlockFrameImpl.lean`.
