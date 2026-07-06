# P-16d6b handoff — μ-independence of the `T`-cocycle count

*Self-contained handoff (Fable, 2026-07-06).  Everything a fresh session needs to finish
P-16d6b is here — no chat/session-memory dependency.  Companion to
[`GQ2/PhaseMuIndep.lean`](../GQ2/PhaseMuIndep.lean) (committed, allowlisted: 1 sorry).*

## 1. The deliverable

The (140) engine consumes a constant `μ` with the hypothesis

```
hμ : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ
```

i.e. the crossed-cocycle count `#Z¹_{Γ,ρ}(T)` is **independent of the exact-image map `ρ`**.

**Consumers** (both in `GQ2/RecursionSplice.lean`, take `μ`/`hμ` as explicit args — proved):
* `zBC_eq_mu_mul_reductionCount` (line ~243)
* `phase140_of_nonsingular` (line ~435), the (140) reducer feeding `RecursionInputs.phase140`.

They will call `obtain ⟨μ, hμ⟩ := tcocycle_mu_indep RF b F D hD` and pass them through.

## 2. What is already DONE (committed, `GQ2/PhaseMuIndep.lean`, std-3 / Ax ∅)

* **`tcocycle_mu_indep`** — the `∃ μ, ∀ ρ, Nat.card (TCocycle D (rhoPrime ρ)) = μ` **packaging**,
  in exactly the shape the consumers want.  It reduces the whole deliverable to the single
  pairwise lemma `tcocycle_card_indep` (nonempty index ⟹ pick a reference ρ₀; empty ⟹ vacuous,
  μ := 0).  **No further work needed on the packaging.**
* **`boundaryLift_diff_mem_LY`** — two boundary lifts of the same C-target agree after `π_Y`, so
  `ρ'(γ)·ρ(γ)⁻¹ ∈ ker π_Y = RF.TC.LY (= L_C)`.  (Banked; **not** on the Route B critical path —
  see §4 — but a true lemma, keep it.)

## 3. The ONE remaining lemma

```
theorem tcocycle_card_indep (ρ ρ' : BoundaryLifts b F RF.TC) :
    Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ))
      = Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ')) := by sorry
```

Once this lands, `tcocycle_mu_indep` is sorry-free and P-16d6b closes.  Delete the
`GQ2/PhaseMuIndep.lean` entry from `scripts/check_axioms.sh`'s `SORRY_ALLOWLIST` in the same commit,
and flip the P-16d6b board row to ☑.

## 4. ⚠️ ROUTE: use B (Euler characteristic), NOT A (twist) — this was verified the hard way

**Route A (coboundary twist) does NOT work.**  The two ρ-actions on `T` are *genuinely different*
`Γ`-modules: only `M = D.M` centralizes `T` (`RadicalCoverData` gives `M_cent_T`), while the
difference cochain `w γ := (piBCiso).symm(ρ'/ρ)` lands in `L_B/M ⊋ M`, which acts on `T` by a
**non-identity unipotent map**.  There is no elementary bijection `TCocycle(ρ) ≃ TCocycle(ρ')`.
(The ticket's "cohomologous actions ⟹ equal counts" phrasing is misleading — do not chase it.)

**Route B (the real one).**  The counts coincide by the **local Euler characteristic**:

1. **Bridge** `TCocycle D ρ ≃ GQ2.Z1 Γ T`.  Turn the crossed-cocycle structure into the abstract
   additive `Z1` for `T` viewed as an `𝔽₂[Γ]`-module with the **ρ-twisted `DistribMulAction`**
   `γ • t := c · t · c⁻¹` (any `c` with `mk c = ρ γ`; well-defined by `M_cent_T`; `𝔽₂`-linear —
   `T` abelian exponent-2 via `D.helem`/`D.hcomm`, `T ≤ M ≤` abelian).  The crossed condition
   `u(γδ) = u(γ)·(c·u(δ)·c⁻¹)` is exactly the additive 1-cocycle condition after `T`-additivization.
2. **Count** via `GQ2.FoxH.LocalLiftingDuality.prop_5_16_bundle` clause 2:
   `Nat.card (Z1 G A) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))`,
   applied at `A := T`.  Supply its two-action hypotheses at the T-layer: `hcomp` from the bridge's
   action, `hA₂ := D.helem`, `hpair` from the polar form, `htriv`, the dual action.
3. **ρ-independence.**  Every boundary lift is **surjective** onto `YC` (`BoundaryLifts` wraps
   `ContSurj`), so `ρ(Γ) = C`, hence `fixedPts(ρ(Γ), T^∨) = fixedPts(C, T^∨) = (T^∨)^C` — one and
   the same value for `ρ` and `ρ'` (and for both sources; see §6).  Therefore both cards equal
   `|T|² · |(T^∨)^C|`.  Set `μ := |T|² · Nat.card (fixedPts C (ElemDual T))`.

## 5. Name/location ledger (all verified present)

| thing | where |
|---|---|
| `TCocycle` (structure `u`/`mem`/`cont`/`crossed`) | `GQ2/CentralObstruction.lean:619`, ns `GQ2.SectionEight.CentralObstruction` |
| `MLifts`, `redT`, `twist`, `tcocycle_torsor_equiv`, `lemma_8_7_count` | `CentralObstruction.lean` / `AffineTLift.lean` |
| `RadicalCoverData` (`C`/`M`/`T`/`hT`/`hTM`/`helem`/`hcomm`/`q`/`hq`…) + `M_cent_T` | `GQ2/RadicalEdgeData.lean:70` |
| `RecursionFrame.rhoPrime`, `piBCiso`, `piBCisoSymm`, `rhoPrime_apply`, `liftsOver_equiv` | `GQ2/RadicalEdgeBridge.lean:145–181` |
| `prop_5_16_bundle` (6 clauses; clause 2 = the Z1 count) | `GQ2/LocalLiftingDuality.lean:515` |
| `Z1` (`AddSubgroup (G → M)`) | `GQ2/Cohomology.lean:111` |
| `fixedPts C M`, `ElemDual A = A →+ ZMod 2` | `GQ2/FoxHeisenberg.lean:1644 / :537` |
| `BoundaryLifts = {f : ContSurj Γ Y // IsBoundaryLift …}`, `ContSurj` | `GQ2/BoundaryFrame.lean:350` / `Reconstruction.lean:23` |
| the `hμ` consumers | `GQ2/RecursionSplice.lean:243, 435` |

Context/imports to mirror: `GQ2/PhaseMuIndep.lean` already has the right `variable` block (copied
from `zBC_eq_mu_mul_reductionCount`) and `open CentralObstruction AffineTLift`.

## 6. ⚠️ Open risk to resolve FIRST (the biggest unknown)

`prop_5_16_bundle` is stated over **`AbsGalQ2` (= G_ℚ₂)** specifically (it carries B6/B7 — Tate
duality + the local Euler characteristic axiom for `G_ℚ₂`).  But `hμ` must hold for **both sources**
`Γ ∈ {Γ_A, G_ℚ₂}` with the **same** `μ` (prop_8_9's witness is shared).  So:

* **G_ℚ₂ source:** Route B applies directly (`prop_5_16_bundle` at `Γ = AbsGalQ2`).
* **Γ_A source:** `prop_5_16_bundle` does **not** apply as-is (`Γ_A ≠ G_ℚ₂`).  Options to
  investigate, in order of likelihood:
  1. **Same value via the target.**  `μ = |T|²·|(T^∨)^C|` depends only on `C` and `T`, not on the
     source `Γ` — because ρ is surjective onto `C` for either source.  So *if* an Euler-char count
     `#Z¹_{Γ_A,ρ}(T) = |T|²·|fixedPts(ρ(Γ_A), T^∨)|` holds for `Γ_A`, the value is automatically the
     same `μ`.  Look for a `Γ_A`/`GammaA` analog of `prop_5_16_bundle` (grep `gammaA`, `prop_5_15`,
     `prop_3_10_gammaA`), or transport along `Γ_A ≅ Π` (`prop_3_10_gammaA`).
  2. **Source-uniform bridge.**  The half-139 machinery already gives `#MLifts = |MB|²`
     (`hMcountM`, ρ- and source-independent) *as a fed hypothesis* in `half139_via_radData`.  The
     honest discharge of that `#MLifts = |MB|²` is the same 5.15/5.16 content — check whether it (or
     its source) is proved anywhere, and whether `#TCocycle` can be read off from it via the
     `red_T`-fibre relation `#MLifts = #(red_T image)·#TCocycle` (`tcocycle_torsor_equiv` /
     `lemma_8_7_count`) with a ρ/source-independent `#(red_T image)`.
  3. **Take `hμ` as a per-source hypothesis**, like `half139_via_radData` takes `hMcountM` — i.e.
     P-16d6b delivers `tcocycle_mu_indep` conditional on the source count, and the true 5.15/5.16
     discharge is a separate (already-scoped-as-source) obligation.  Only fall back to this if 1/2
     are blocked; confirm with the P-16 lead before weakening the deliverable.

**Do not start the Z1 bridge (§4 step 1) before deciding §6** — it determines whether one bridge
suffices or two (per source) are needed.

## 7. Build / gate / coordination

* Build: `lake env lean GQ2/PhaseMuIndep.lean` (fast; imports only `RadicalEdgeBridge` + `AffineTLift`).
* `#print axioms GQ2.SectionEight.tcocycle_mu_indep` should be std-3 + {B6,B7} (Euler char) once the
  core lands; the packaging + `boundaryLift_diff_mem_LY` are std-3 now.
* Gate: `scripts/check_axioms.sh` — `PhaseMuIndep.lean` is on the `SORRY_ALLOWLIST` while the core
  is open; **remove it when sorry-free**.
* **Coordination:** own leaf, off the co-owned `RecursionSplice.lean`/`SectionEight.lean`.  Disjoint
  from **P-16d6a** (`GQ2/RStageObstructionBuild.lean`, `GQ2/ScratchP16d6a.lean` — another agent).
  The final splice into `RecursionSplice.lean`'s `phase140`/`prop_8_9_of` is the P-16d6e assembly's
  job, not this ticket.

## 8. Commits in this handoff

* `f2dfca1` — PhaseMuIndep.lean created (packaging + boundary fact); board ◐.
* `003d3f2` — board row corrected Route A→B.
* *(this commit)* — PhaseMuIndep.lean tracked + allowlisted; this handoff doc.
