# P-16d6d handoff — (139) for `G_ℚ₂`

**Written 2026-07-06 (Opus).** Self-contained handoff so another session can pick up P-16d6d
from the repo alone. Companion to `docs/p16d6-plan.md` (the full P-16d6 plan) and the P-16d6d
row in `docs/tickets.md`.

---

## 0. Context: P-16c is CLOSED (this session)

The entire P-16c lane (c1–c5) landed this session, **all std-3**, `lake build GQ2` exit 0
(8678 jobs, 0 errors). This **unblocks the `Γ_A` half of P-16d6d/d6e** (the `Γ_A` `hlem86M`
was the only P-16c-blocked input in the plan).

New files (all `#print axioms = {propext, Classical.choice, Quot.sound}`):

| file | key exports (namespace `GQ2.SectionEight.LedgerGammaA` unless noted) |
|---|---|
| `GQ2/MixedBObs.lean` (ns `GQ2.MixedBObs`) | `kappaHeis`, `PhiHeis`, `mixedB_eq_relZPair` (mixedB **is** a `WordCoh2.relZPair`), `obs_inflation` (obs of a pointwise-inflated cocycle) |
| `GQ2/LedgerGammaA.lean` | `pairHom`, `obs_varCoc_eq_mixedB` (the ledger `obs(varCoc u)=mixedB`), `varCoc_class_ne_zero` (`hvar`), `exists_phiF` (the shifted-edge dual cocycle) |
| `GQ2/HalfTorsorGammaA.lean` | **`exists_nonzero_varCoc_gammaA`** (`∃ u, [varCoc u]≠0`), **`card_H2_gammaA_eq_two`** (`#H²=2`), **`half_torsor_gammaA`** (the Lemma-8.6 count for `Γ_A`) |

`SectionEight.lemma_8_6_gammaA` (was `sorry` @1288) is now **proved** by
`:= LedgerGammaA.half_torsor_gammaA D hedge ρ hρ` (import `GQ2.HalfTorsorGammaA` added).

**Repo hygiene note:** the three new `.lean` files are **untracked** (`git status` = `??`); they
plus the edits to `SectionEight.lean` / `docs/tickets.md` need `git add` + commit.

---

## 1. What P-16d6d is

Discharge the two per-source hypotheses of **`half139_via_radData`** (`RecursionSplice.lean:78`,
✓ std-3) for the **local (`G_ℚ₂` = `AbsGalQ2`) source**, producing the (139) identity
`2·zBC = |M_B|²·exactImageCount` for that source. This becomes the `half139` field of the local
`RecursionInputs` bundle consumed at **d6e** (final `prop_8_9` splice).

`half139_via_radData` signature (the target reducer):
```
half139_via_radData (RF : RecursionFrame T Blk) (b) (F) (En : RF.Enrichment) (l h) (hfg)
    (hlem86M : ∀ ρ : BoundaryLifts b F RF.TC,
        2 * Nat.card {f : MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) // f.Central}
          = Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)))
    (hMcountM : ∀ ρ : BoundaryLifts b F RF.TC,
        Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
          = (Nat.card ↥RF.MB) ^ 2) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC
```

The `Γ_A` twin is **not** here — it is built at d6e from P-16c's `half_torsor_gammaA` (now ✓).

---

## 2. The two hypotheses — discharge paths

### 2a. `hlem86M` — genuine plumbing ✓ (the easy half)

The half-torsor count is **already proved** for `G_ℚ₂`: `SectionEight.lemma_8_6_local`
(`SectionEight.lean:1302`, = `RadicalEdgeLocal.half_torsor_local`, Ax B6/B7):
```
lemma_8_6_local (D : RadicalCoverData Bg) [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfg) (hedge : D.NoDescent) (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) (hρ : Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ)
```
So `hlem86M ρ` is `lemma_8_6_local (En.radData l h) hfg hedge (rhoPrime … ρ) hρ'` where you must
supply, **per `ρ : BoundaryLifts`**:

- **`hedge : (En.radData l h).NoDescent`** — from `l ≠ RF.zeroDR` (`h`) via the characterization
  **`(E.radData l h).NoDescent ↔ …` at `SectionEight.lean:1677`**. (Find its exact RHS; it should
  reduce to `h` / an `En` field.)
- **`hfg`** — the local topological finite generation of `AbsGalQ2` (the standing B1-shaped input;
  it is already a parameter of `half139_via_radData`, so just thread it).
- **`hρ' : Function.Surjective (rhoPrime … ρ)`** — from `ρ` being a `BoundaryLifts`/exact-image.
  `rhoPrime` is `RadicalEdgeBridge.lean:152`, `rhoPrime_apply` at `:156`. Look for a
  surjectivity lemma for `rhoPrime` (or derive from the `BoundaryLifts` exact-image property).

This half is a ~15-line `fun ρ => lemma_8_6_local …`.

### 2b. `hMcountM` — the real content ⚠ (NOT an existing lemma)

`hMcountM ρ : Nat.card (MLifts (En.radData l h) (rhoPrime … ρ)) = (Nat.card ↥RF.MB) ^ 2`.

**This is NOT a one-liner and is the substance of d6d.** Searched the whole repo: `#MLifts = |M_B|²`
appears **only as a hypothesis** — there is no proved lemma for it yet. `MLifts D ρ` is
`{f : ContinuousMonoidHom Γ' Bg // ∀ γ, QuotientGroup.mk (f γ) = ρ γ}` (`RadicalEdgeData.lean:137`).

The count is genuine cohomology arithmetic:
1. **The lifts of a fixed `ρ` are a `Z¹_cont(Γ, M_B)`-torsor** (`M_B = ker(B ↠ B/M)`, a `Γ`-module
   via `ρ`); need a base lift (nonemptiness — from the profinite cover `B ↠ B/M` / exact image),
   then `MLifts ≃ Z¹_cont(Γ, M_B)`.
2. **`#Z¹_cont(Γ, M_B) = |M_B|²`** from the §5.15/5.16 numerics (the self-dual `H⁰/H¹/H²`
   cardinalities of `M_B`; `#Z¹ = #B¹·#H¹ = (#M/#H⁰)·#H¹`).

`docs/p16d6-plan.md` (line 110) marks this "◑ dischargeable … from `prop_5_16`/`prop_5_15` (✓)" —
i.e. the *path is considered clear*, but the wiring (torsor structure + numerics → `#MLifts`) is
not yet written. **Before building from scratch, search for reusable pieces:**
- `GQ2/RadicalEdgeLocal.lean` / `GQ2/CentralObstruction.lean` — the `half_torsor_local` proof
  already manipulates `MLifts` and their `Z¹(T)` torsor structure (`TCocycle`); there may be a
  `MLifts ≃ Z¹`/nonemptiness lemma to reuse.
- `RecursionSplice.lean:164` `central_card_eq_reductions_mul_tcocycle`
  (`#{central MLifts} = #reductions · #TCocycle`) — related torsor-count machinery.
- `RadicalEdgeData.lean:107` `two_mul_card_fiber` (`2·#{v // ℓv=c} = #V`) — the fiber-count atom.
- The `prop_5_15`/`prop_5_16` card outputs (the `IsSelfDual` clauses / `H*` cardinalities).

**Bottom line:** `hlem86M` ≈ 15 lines of plumbing; `hMcountM` is the real ~??-line build and needs
the §8/§5 cohomology-count machinery loaded. The ticket's "⭐ pure plumbing" is optimistic for a
cold start.

---

## 3. Key file:line reference map (P-16d / §8 recursion)

| object | location | role |
|---|---|---|
| `half139_via_radData` | `RecursionSplice.lean:78` | ✓ reduces (139) to `hlem86M`+`hMcountM` — **the d6d target reducer** |
| `half139_of` | `RadicalEdgeBridge.lean:103` | ✓ the P-16d3 bridge (takes `hlem86`+`hMcount` over `CentralOver`/`LiftsOver`) |
| `lemma_8_6_local` | `SectionEight.lean:1302` | ✓ discharges local `hlem86M` |
| `lemma_8_6_gammaA` | `SectionEight.lean:1288` | ✓ (this session) discharges `Γ_A` `hlem86M` — for d6e |
| `MLifts` / `.Central` | `RadicalEdgeData.lean:137` / `:142` | the counted objects |
| `two_mul_card_fiber` | `RadicalEdgeData.lean:107` | fiber-count atom |
| `Enrichment` | `SectionEight.lean:1605` | carries `radData`, `Vmod`, `qbar`, … (see plan §witness) |
| `(En.radData l h).NoDescent ↔ …` | `SectionEight.lean:1677` | gives `hedge` |
| `rhoPrime` / `rhoPrime_apply` | `RadicalEdgeBridge.lean:152` / `:156` | the transported lower map |
| `RecursionInputs` | `SectionEight.lean:1972` | per-source bundle; `.half139` field is d6d's output |
| `prop_8_9_of` / `prop_8_9_aux` | `RecursionSplice.lean:38` / (used `:63`) | the d6e splice backbone |
| `central_card_eq_reductions_mul_tcocycle` | `RecursionSplice.lean:164` | torsor-count machinery (reusable?) |
| `phase140_ofPhaseData`, `zBC_eq_sum_centralOver` | `RecursionSplice.lean:135`, `:103` | (140) reducers (d6-adjacent) |

---

## 4. Reusable gotcha: the `GA` ↔ `GammaA` transport

Any future work applying the raw-`Γ_A`-machinery (`WordCohBridge.GA = FreeProfiniteGroup (Fin 4) ⧸ NA`,
an `abbrev`) to a **`GammaA`-typed** caller (`GQ2.GammaA : ProfiniteGrp := profiniteQuotient NA`)
hits this: `↑GammaA` is **defeq but not reducibly-defeq** to `GA`, so *instance synthesis*
(`DistribMulAction`, `Finite`, …) fails across the two forms even though term-unification succeeds.

Pattern used in `half_torsor_gammaA` (`GQ2/HalfTorsorGammaA.lean`) to bridge:
```
let ρ0 : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) (Bg ⧸ D.M) := ρ   -- retype to the raw quotient
haveI : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NA) :=
  inferInstanceAs (TotallyDisconnectedSpace (GammaA : Type))                       -- transport the missing instance
-- then do all GA-machinery work over ρ0; `exact … ρ0` closes the `ρ`-goal (defeq)
```
`CompactSpace`/`IsTopologicalGroup` synthesize for the raw quotient automatically; only
`TotallyDisconnectedSpace` needs the transport. Finite generation:
`gammaA_topologicallyFinitelyGenerated` (`FinitelyGenerated.lean`) ascribes to `Finset (F₄/NA)`.

(P-16d6d itself is over `G_ℚ₂ = AbsGalQ2`, which is a plain type — so it should **not** hit this;
recorded here because it bit the `Γ_A` side and will bite any future `GammaA`-typed caller.)

---

## 5. Stale docs fixed / to watch

- **`docs/p16d6-plan.md`** — lines ~110/117 said `lemma_8_6_gammaA` is a `sorry` and "Only `Γ_A`
  is blocked, on P-16c." **Updated this session** to reflect P-16c closure. (If you see any
  remaining "P-16c blocks…" language there or in `tickets.md`, it is stale.)
- **`scripts/check_axioms.sh`** SORRY_ALLOWLIST comment lists `SectionEight`'s intentional sorries
  as "8.2×2, 8.3, 8.6×2, prop_8_9". Now **both 8.6's are proved**; only `prop_8_9` (`SectionEight.lean:2144`)
  remains, so `SectionEight.lean` legitimately stays on the allowlist — the "8.6×2" in the *comment*
  is stale but harmless (gate still passes). Trim when convenient.
- **`docs/tickets.md`** — P-16c parent + c4 + c5 rows marked ☑ (this session); P-16d6d row still
  ☐ and now says the M-count (`hMcountM`) is the real work (updated this session).

## 6. Suggested first moves for the next session

1. Read `half139_via_radData` (`RecursionSplice.lean:78`) + `docs/p16d6-plan.md` §"four remaining inputs".
2. Do `hlem86M` first (easy): write `fun ρ => lemma_8_6_local …`, discharging `hedge` (via `:1677`),
   `hρ'` (rhoPrime surjectivity), `hfg` (thread the parameter).
3. Then `hMcountM`: grep `GQ2/RadicalEdgeLocal.lean` + `GQ2/CentralObstruction.lean` for an
   existing `MLifts ≃ Z¹`/nonemptiness/count lemma before building the torsor argument; wire the
   `#Z¹ = |M_B|²` numerics from the `prop_5_15`/`prop_5_16` (`IsSelfDual`) card outputs.
4. Assemble `half139_local := half139_via_radData … (hlem86M) (hMcountM)`; gate with
   `lake build` + `#print axioms` (expect B6/B7 via `lemma_8_6_local`, else std-3).
