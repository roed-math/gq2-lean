# P-16d6e handoff — the Γ_A (136) recursion residues

**Status 2026-07-07 (Opus).**  The heavy mathematical content of P-16d6e5 is **done**; one sorry
remains (`hsep_hom_gammaA`, the L4/L5 assembly).  This document lets a fresh agent finish it.

---

## 0. Where P-16d6e sits

P-16d6e discharges the **candidate-source** (`Γ := GammaA`) residues of the §8 recursion identity
(136), mirroring the local (`AbsGalQ2`) discharge in `GQ2/RStageLocal.lean`.  Subtickets:

| sub | deliverable | state |
|---|---|---|
| **e5** | `GQ2/RStageGammaA.lean` — `htriv_gammaA`, `hZcount_gammaA`, `hsep_hom_gammaA`, and the `stageR136_gammaA_of_hcard` assembly | **this file; 1 sorry left** |
| e6 | `card_H2_gammaA_eq_two` (supplies the `hcard_A` hypothesis e5 threads) | separate ticket |
| e7 | the `RecursionInputs B.bA` bundle assembly (consumes `stageR136_gammaA`) | separate ticket |

`stageR136_gammaA_of_hcard` threads `hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2` as a hypothesis, so
**e5 is decoupled from e6** — when e6 lands, add the one-line hypothesis-free `stageR136_gammaA`.

Design doc with full derivations: **`docs/p16d6e5-plan.md`** (read it — it has the interface pin table
§3 and the L1–L5 DAG §2).  This handoff is the executive summary + the L4/L5 recipe.

---

## 1. Current state of `GQ2/RStageGammaA.lean`

* **Builds green**: `lake build GQ2.RStageGammaA` (8662 jobs).  Root-imported (`GQ2.lean`).
* **Exactly one sorry**: `hsep_hom_gammaA` (~line 625).  Allowlisted in `scripts/check_axioms.sh`
  (`SORRY_ALLOWLIST`); **remove `RStageGammaA.lean` from the allowlist once it fills**.
* **Every landed lemma is std-3 or propext-only** — NO B-axioms.  The candidate-duality route is
  axiom-free (`prop_5_15`/`IsSelfDual` is std-3, unlike the local `card_Z1_eq` which carries B6/B7).

### What is already proved (the inherited API)

Residues + assembly:
- `htriv_gammaA (γ : GammaA) (m : ZMod 2) : γ • m = m` — registers the trivial action (`rfl`).
- `hZcount_gammaA` — **the z_R torsor count, PROVED** (`z1Equiv` + `prop_5_15` cl.2 + `blockRChar_card`).
- `stageR136_gammaA_of_hcard` — the (136) identity, **proved modulo the single `hsep_hom` sorry**.

Word-complex / trace-span package (§2 L2–L3, all std-3), in namespace `GQ2.RStageGammaA`:
- **L2** `d1Fun_naturality` — a `C`-equivariant `f : A →+ A'` intertwines `d¹`.
- **L3a** `wTrace (t) (ht) (hw) (lam : ElemDual A) (hlam : d0 lam = 0) : H2w A t →+ ZMod 2` — the
  (2,0)-trace `Φ_λ`, well-defined via `prop_5_8_right` (this IS the "gap (i)" pairing).
- **L3b** `wTrace_injective`, **L3c** `wTrace_surjective` (⟹ `λ ↦ Φ_λ` bijective onto `H2w →+ 𝔽₂`),
  **L3d** `sep_word` (the separation), **L3e** `trace_kills_im_trivial`.
- L4 additive closed forms: `d1Fun_tame_trivial` / `d1Fun_wild_trivial` — `(d¹x) = (x 1, x 1)` at
  trivial `𝔽₂` (so `im d¹(𝔽₂-triv)` is the diagonal `{(a,a)}`).

**L1 — the group-level relator correction — COMPLETE (both rows).**  For a marking corrected by
central involutions `r⃗` (at a central 2-torsion kernel):
- `tameValue_correction : tameValue(r⃗·ŷ) = r₁ · tameValue ŷ` (propext).
- `wildValue_correction : wildValue(r⃗·ŷ) = r₁ · wildValue ŷ` (std-3).
- Building blocks (reusable): `powOmega2_central_involution` (the `ω₂` crux),
  `conjP_central_correction`, `conjP_central_left`, `commP_central_correction`, `central_pair`,
  `central_mul_comm`, `central_mul_sq`; the `corrMark` record + `corrMark_{σ,τ,x₀,x₁}` field-simp
  lemmas + the ten auxiliary-word corrections `corrMark_{sigma2,u0,u1,g0,z0,d0,c0,dg,hc,h0}`.
- Both Fox derivatives are `r₁` (the τ-correction) — matching the closed forms.

---

## 2. The one remaining task — `hsep_hom_gammaA` (L4/L5)

```lean
theorem hsep_hom_gammaA
    (hE2 : ∀ e : E, e ^ 2 = 1) (hRK …) (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
    (g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_gammaA
        hcard_A g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom GammaA Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ
```

**This is boundary-frame *plumbing*, not word algebra.**  The word/group machinery it needs (L1–L3)
is all proved above; the remaining work is wiring `obs g = 0` through the scalar covers into a marking
that descends to `GammaA`.  Do NOT try to mirror `hsep_hom_local`'s proof (`RStageLocal.lean:307`) —
that uses the **AbsGalQ2 twisted-`H²` cohomological route** (`Z2 AbsGalQ2 (Additive R)`), which is not
available for `GammaA` (this is exactly why the marking route L1–L5 exists; see plan §0 gap (ii)).

### Verified interface pins (checked 2026-07-07)

| need | pinned | where |
|---|---|---|
| `obs g = 0` → per-cover continuous lift | `obs_zero_iff_lifts RF D htriv hcard g d (h : D.toDR d ≠ RF.zeroDR)` `: obs … = 0 ↔ ∃ gc : ContinuousMonoidHom Γ (RF.scalarCover (D.toDR d) h).cover, ∀ γ, (RF.scalarCover …).p (gc γ) = g γ` | `RStageObstructionBuild.lean:358` |
| invariant chars ↔ cover index | `RCharSub Blk` (finite), `RCharKer Blk χ : Subgroup Y`, `RCharKer_le/_normal`, `RCharKerSub_eq_ker`, `blockToDR`/`blockToDR_coe` | `BlockRStage.lean:53,105,97,…` |
| relator value naturality (push through `red_l : Y → Y/l`) | `Marking.map_tameValue`, `Marking.map_wildValue` (needs `Finite`) | `FoxHeisenberg.lean:119,126` |
| descent `F₄ → ↥J → GammaA` | `NA_le_ker` (`GammaA.lean:232`), `FreeProfiniteGroup.homEquiv`, `quotientLift` | P-04/P-05 |
| topological-generator agreement (close `π_B ∘ φ = g`) | `monoidHom_eq_of_topGen` pattern | `BoundaryMapsWitness.lean:190` |
| `Γ_A` fin-gen | `gammaA_topologicallyFinitelyGenerated` | `FinitelyGenerated.lean:82` |

### The recipe

**L4 — feed `sep_word`.**  Its hypothesis is `∀ lam : ElemDual (Additive Blk.R), d0 lam = 0 →
lam (v.1 + v.2) = 0`, where `v := (tameValue ŷ, wildValue ŷ) ∈ R × R` is the relator-value pair of a
fixed set-lift `ŷ : Fin 4 → Y` of `g`'s marking (`v ∈ R × R` because `g`'s marking satisfies the
relations in `Y/R = B`).  For `lam = 0` it's `0 = 0`; for each nonzero invariant `lam = d`
(⟺ `l := RCharKer d`, cover `Y/l` with kernel `R/l ≅ 𝔽₂` — **central 2-torsion**, since `Aut 𝔽₂ = 1`):

1. `obs_zero_iff_lifts … (LinearMap.congr_fun hg d)` ⟹ continuous hom `gc : GammaA → (scalarCover …).cover`
   (`= Y/l`) with `p ∘ gc = g`.
2. `red_l ŷ` (the set-lift reduced mod `l`) and `gc`'s generator images both lift `g`'s marking mod
   `R/l`, so they differ by corrections `r̄ : Fin 4 → R/l` (central involutions in `Y/l`):
   `red_l ŷ = corrMark ⟨gc gens⟩ r̄`.
3. `gc` is a homomorphism ⟹ its generators satisfy the tame+wild relations in `Y/l` (they are images
   of `GammaA`'s canonical marking, whose relators are `1` — **find/​prove the `GammaA`-relations
   lemma near `GammaA.lean`**), i.e. `tameValue ⟨gc gens⟩ = wildValue ⟨gc gens⟩ = 1`.
4. Apply **`tameValue_correction`** and **`wildValue_correction`** at `Y' := Y/l`:
   `tameValue(red_l ŷ) = r̄₁ · 1 = r̄₁` and `wildValue(red_l ŷ) = r̄₁ · 1 = r̄₁`.
5. By `map_tameValue`/`map_wildValue`: `d(v.1) = red_l(v.1) = tameValue(red_l ŷ) = r̄₁ =
   wildValue(red_l ŷ) = red_l(v.2) = d(v.2)` (via the `R/l ≅ 𝔽₂` identification given by `d`).  Hence
   `lam(v.1 + v.2) = d(v.1) + d(v.2) = 0` (char two).  ∎ hypothesis.

   *(Alternative, per plan §2 L4: push the R-level identity to `𝔽₂` via `d1Fun_naturality` and read
   off the correction as a `d¹`-image using `d1Fun_tame/wild_trivial`, then `trace_kills_im_trivial`.
   The direct route above via `tameValue/wildValue_correction` + naturality is shorter and uses the
   landed L1 most directly — recommended.  The additive lemmas remain as a cross-check.)*

Then `sep_word … v (hyp)` ⟹ `v ∈ (d1 (A := Additive Blk.R) t).range` ⟹ corrections
`r⃗ : Fin 4 → Blk.R` with `d1Fun t r⃗ = v` (i.e. the corrected relator values are `1`).

**L5 — correct + descend.**  With `r⃗` from `sep_word`, the corrected tuple `x̂ᵢ := rᵢ⁻¹ · ŷᵢ`
(sign/orientation: match `d1Fun`'s rows — check against `d1Fun_tame`, `FoxHeisenberg.lean:518`) has
both relators `= 1`.  Build `J := Subgroup.closure (range x̂)`; the `Marking ↥J` from the corrected
tuple `Generates` (closure `= ⊤`), satisfies `TameRel`/`WildRel` (values `1`), and `Pro2Core` (finite
2-group extension: `normalClosure {x̂₂,x̂₃}` onto the `B`-side wild closure with kernel `≤ R ∩ J`, both
2-groups — use `markC_admissible` `.2.2.2` + `hR2`; small `IsPGroup`-extension lemma may exist near
`MaxProP`).  Then `f : F₄ → ↥J` via `FreeProfiniteGroup.homEquiv.symm` on the corrected tuple;
`NA_le_ker` ⟹ `quotientLift NA f …` ⟹ `φ' : GammaA → ↥J`; `φ := (J.subtype).comp φ'`.  Close
`π_B ∘ φ = g` by `monoidHom_eq_of_topGen` (two continuous homs `GammaA → Y/R` agreeing on the four
topological generators — `π(x̂ᵢ) = π(ŷᵢ) = g(genᵢ)` since corrections `∈ R`).

---

## 3. Gotchas & reusable patterns (learned the hard way)

* **T-14 `ElemDual` codomain-action diamond.**  `ElemDual A = A →+ ZMod 2` is a *def-synonym*, not
  reducible.  Writing `AddMonoidHom.id (ZMod 2)` where `ElemDual (ZMod 2)` is expected, then `ext`/
  `DFunLike.ext`, decays it to a bare `AddMonoidHom` and resolves `c • ·` to
  `AddMonoidHom.instSMulZeroClassOfDistribSMul` (codomain action) instead of the contragredient →
  every downstream `rw`/`exact` mismatches instances.  **Fix**: force the type with a typed `let`
  (`let idE : ElemDual (ZMod 2) := AddMonoidHom.id _`).  `ElemDual.smul_apply` is `rfl`.
* **GA/GammaA bridge.**  `GammaA ≡ GA := FreeProfiniteGroup (Fin 4) ⧸ NA` are defeq, but their
  instances don't cross-resolve (`GA` lacks auto `TotallyDisconnectedSpace`).  State theorems over
  `Γ := GammaA` (so `blockStageR136`/`RecursionInputs` instances resolve); word-machinery is over
  `GA`.  Close `GA`-crossing goals with **term-mode** steps (`exact congrArg …`) — `simpa`/`simp`
  re-elaborate under strict `instances` transparency and reject the defeq.
* **Central-element manipulation idioms** (used throughout L1; will recur in L5):
  - Central conjugation is trivial: `r * X * r⁻¹ = X` — reassoc (`by group` proves the pure-assoc
    step), then `(hr X).eq` + `group`.
  - `central_pair (c·a)(c·b) = a·b` for a shared central involution; `mul_mul_mul_comm` to combine
    two corrections; `r⁻¹ = r` for an involution via `inv_eq_of_mul_eq_one_right`.
  - The reliable closer shape: move a central factor adjacent to its inverse so `group` cancels it,
    then one `Commute.eq`/`.symm.eq` (or `.zpow_left`/`.zpow_right` after `group` puts things in
    `zpow` form) for the surviving swap.
* `powOmega2 x = x^(omega2Exp (orderOf x))` is the **2-primary projection**.  Under a central
  involution `s`, `powOmega2 (s·a) = s · powOmega2 a` — the `orderOf(s·a)`-shift is a red herring:
  evaluate all `ω₂`-powers at a common modulus (`powOmega2_pow_eq`, à la `powOmega2_prod`).  Done
  (`powOmega2_central_involution`).

---

## 4. Working conventions (shared tree — READ)

* Branch `p15f6-conjact-deepclasses`; **multiple agents share this working tree/index.**  Stage ONLY
  files you touched this session — never `git add -A`.  **Print the exact staged set before every
  commit.**  Commit as soon as a piece is verified green (a concurrent commit can otherwise sweep your
  staged files).
* Commit messages end with `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` (or your model).
* **Do NOT touch `docs/tickets.md`** — the e-lane author has it mid-restructure.  Record durable status
  in `docs/p16d6e5-plan.md` (§5) instead.
* Only commit **fully-proved** (sorry-free) pieces beyond the single `hsep_hom_gammaA` sorry; the file
  must stay at ≤1 sorry.  When `hsep_hom_gammaA` fills, delete `GQ2/RStageGammaA.lean` from
  `SORRY_ALLOWLIST` in `scripts/check_axioms.sh` (and update the trailing comment).

### Verify

```
lake build GQ2.RStageGammaA                    # per-file gate (~30–45s)
```
Then `lean_verify` (LSP) or `#print axioms GQ2.RStageGammaA.<thm>` on new decls — expect std-3
(`propext, Classical.choice, Quot.sound`) or propext-only; **any B-axiom or sorryAx is a red flag**
(the candidate route is axiom-free).  Note: the full-library build may be red from unrelated foreign
files in the shared tree — the per-file subtree gate is authoritative for this work.

---

## 5. Pointers

* **Design**: `docs/p16d6e5-plan.md` (§2 the L1–L5 DAG, §3 interface pins, §5 execution status).
* **Statement template**: `GQ2/RStageLocal.lean` — mirror `hsep_hom_local:307` /
  `stageR136_local:603` for *shapes*, but its `hsep_hom` **proof** is the cohomological route (not
  reusable for `GammaA`; see §2 warning).  Its Γ-generic helpers `RStageLocal.{rCommGroup, conjC,
  conj_mem_R, conjC_smul_of_mk, conj_eq_of_mk_eq_K}` ARE reused (already imported).
* Session commits (P-16d6e5, 2026-07-07): `hZcount` `51b83e5`; L2/L3 `3838eb2…e8b19c0`; L3e `44b8dfa`;
  L4 closed forms `a7ec061`/`577f0b8`; L1 tame `7c0c673`; L1-wild crux/blocks `9fdf0a5`/`53b43c3`;
  L1-wild chain `b0d8e8f`/`91831c7`.
