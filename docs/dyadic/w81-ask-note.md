# Lane W81-ASK: the ASK counting pack at `G_K`

Worktree `claude/w81-ask`, based on `6f2916f3`.  Verification of record: `scripts/mirror.sh`
(sweep, gen, check).  **No `lake` command was run.**

One new module, `GQ2/Dyadic/Instances/AskCounting.lean`, prefix `askC`.  Thirteen declarations,
no `sorry`, no new axiom, no `native_decide`, per-declaration `#print axioms` recorded in the
file with the measured split.  Not registered in `GQ2.lean` (the housekeeping sibling owns it).

---

## 0. Headline

The lane was opened on the premise that the two ASK bundles at `G_K` are unowned.  **Both are
already theorems at head.**  The briefing, `docs/dyadic/w74-critical-path.md` §1.4, and
`KSupply.lean`'s own §4 and §6 are stale on this, in exactly the way W79-HOUSE found them stale
on `determinant`.

What actually survives is one **coefficient mismatch**, and it is not a missing clone.

| bundle at `galKProfinite K` | status at `6f2916f3` | supplier |
|---|---|---|
| `StokesDualityCertificate`, all four clauses | **theorem**, hypothesis `hdeg` only | `stokesDualityCertificate_galK`, `Instances/KAnalytic.lean` |
| `ExactLiftingSemanticsRN`, all three clauses | **theorem** at every degree | `exactLiftingSemanticsRN_galK`, `Instances/KExactLiftingGalK.lean` |
| `AffineDeterminantCertificate` | **theorem** given the packet's `ramifiedData` | `affineDeterminant_galK`, `GaussZ/FinalDK.lean` |
| `ExactLiftingSemantics` (frozen) | theorem at `[K : ℚ₂] = 1` **only** | `exactLiftingSemantics_galK`, same file |

Every live row sits at `n = 2`.  The row records ask for the **frozen** bundle.

---

## 1. T1: the `half_torsor_local` K-analogue

**Status: already closed at head; verified here, not cloned.**

`KSupply.lean:256-260` narrows the whole `exactLifting` bundle to one existential and calls it
"the `K` analogue of `RadicalEdgeLocal.exists_good_twist`, unowned".  It is owned:

| rung | `ℚ₂` ancestor | `K` supplier at head |
|---|---|---|
| the good-twist existential | `RadicalEdgeLocal.exists_good_twist` (`GQ2/RadicalEdge/Local.lean:475`, `private`) | `Count.exists_nonzero_varCoc_of_tateDualityG` (`Instances/KExactLiftingVar.lean:109`) |
| the half-torsor count | `half_torsor_local` (`GQ2/RadicalEdge/Local.lean:523`) / `lemma_8_6_local` (`SectionEight/Partition.lean:307`) | `Count.lem86_of_tateDualityG` then `lem86_galK_of_noDescent` (`Instances/KExactLiftingGalK.lean:106`) |
| `liftsOver_card` | `MStageCount.liftsOver_card_local` | `liftsOver_card_galK` (same file) |
| stage (136) | `RStageLocal.stageR136_local` | `correctedRStageSemantics_galK` (`Instances/KAnalytic.lean:740`) |

The ℚ₂ vs carrier-generic split: `GQ2/RadicalEdge/Local.lean` is carrier-generic apart from three
things (the type `AbsGalQ2`, the B6 bundle `GQ2.tateDuality 2`, and `smul_muN_two_trivial`), and
all three already have `TateDualityG`-parametrized twins.  Nothing was owed.

`askC_halfTorsor_galK` restates the clause at the row shape so the claim is checked against the
Lean rather than cited.  Measured: std-3 + `tateDualityAt` (B6) +
`absGalQ2_isTopologicallyFinitelyGenerated` (B1), and **no B7**, the half-torsor clause being
degree-free, exactly as `KExactLiftingGalK.lean` predicted.

---

## 2. T2: the Stokes bundle's four clauses at `G_K`

**Status: all four closed at head; verified here.  Per-clause table:**

| clause | `ℚ₂` ancestor (hard-pinned) | carrier-generic supplier | at `G_K` |
|---|---|---|---|
| `tcocycle_card` | `tcocycle_card_local`, `Phase140/Local.lean:258` | `Count.tcocycle_field_of_localDualityG`, `Count/LocalDuality.lean:152` | **proved** |
| `hsep` | `hsep_local`, `Phase140/Local.lean:537` | `Count.hsep_field_of_localDualityG`, `Count/LocalDuality.lean:210` | **proved** |
| `hpartial` | `hpartial_local`, `Phase140/Local.lean:864` | `Count.hpartial_field_of_localDualityG`, `Count/LocalDuality.lean:252` | **proved** |
| `hZcard` | `hZcard_local`, `Phase140/Local.lean:325` | `Count.hZcard_field_of_localDualityG`, `Count/LocalDuality.lean:178` | **proved** |

All four ℚ₂ ancestors are pinned three ways at once: carrier `AbsGalQ2`, the fixed
`boundarySubgroup` rather than the parametric `boundarySubgroupQ q nuP`, and a hard-coded
exponent `2` (which is `d + 1` at `d = 1`).  All four generic successors take the same two
inputs and nothing else: `TateDualityG Gam 2` and `LocalEulerChar Gam d`.

Both inputs exist at `G_K`: `LiftingDualityG.tateDualityGalK K` and
`localEulerChar_galK_of_finrank K hdeg`.  The assembly is
`stokesDualityCertificate_of_localDualityG` then `stokesDualityCertificate_galK`, and
`askC_stokes_galK` restates it at `q := qOf K FF`, the spelling `KSupply.stokes` and
`GenAsmRowResidual.stokes` are written at.  Nothing is carried.

---

## 3. The residue: one coefficient

The frozen third conjunct pins the equation-(136) coefficient to
`RecursionFrame.zR = #R² · #D_R`.  The R-cocycle count at `G_K` is
`zRN RF (standardNumerics n) = #R^{n+1} · #D_R` (`correctedRStage_hZcount_galK`).  Both clauses
evaluate the same left-hand side, so:

* `askC_zRN_eq_zR_of_card_one`: the coefficients agree when `#R = 1`, in every degree;
* `askC_zRN_ne_zR`: they differ whenever `#R > 1` and `2 ≤ n`.

Both print **std-3 and nothing else**.  That measurement is the point: the gap between what is
proved and what is asked is not arithmetic.

The named residual Prop is `askCStageVanishing`: on every frame with `1 < #R`, the (136)
alternating sum vanishes.  Its binder list is byte-for-byte the frozen conjunct's.

| direction | declaration | condition |
|---|---|---|
| sufficient | `askC_exactLiftingSemantics_galK` | every degree |
| necessary | `askC_stageVanishing_of_exactLifting` | `2 ≤ n` |
| equivalence | `askC_exactLifting_iff_stageVanishing` | `2 ≤ n` |

So at `n = 2`, the degree every live row sits at, the frozen bundle and `askCStageVanishing` are
**the same statement**.  There is no smaller residue.

### 3.1 What that costs, and why it is a warning

`askC_exactImageCount_eq_zero_of_exactLifting`: at `2 ≤ n` the frozen field forces
`exactImageCountK b F T = 0` on every nontrivial-`R` frame.  That count is
`Nat.card (BoundaryLiftsK b F T)`, and `BoundaryLiftsK` is finite at `G_K` because `G_K` is
topologically finitely generated, so:

`askC_isEmpty_boundaryLifts_of_exactLifting`: **carrying the frozen `ExactLiftingSemantics` at
`2 ≤ n` asserts that `G_K` admits no boundary-framed surjection whatever onto any marked target
whose Frattini block is nontrivial.**

The recursion exists to count exactly those surjections.  Either that emptiness is a true fact
about `G_K` and wants a proof, or the five row records and `GenAsmRowResidual` are asking for
something no arithmetic supports.

**The lane's recommendation is the statement change: restate the row records against
`ExactLiftingSemanticsRN`.**  `askC_exactLiftingRN_galK` proves it at every degree with nothing
carried, and `SourceDataRN`/`KExactSupplyRN` already consume that shape.  This is a statement
change and is therefore reported, not made, in line with the ruling W74-HOUSE §1.5 applied to
the pilot's producer generation.

---

## 4. T3: the record consequence

**With `askCStageVanishing`** (`askCKSupply_of_markedCore`): the whole `KSupply` record closes at
general degree.  Its nine fields cost the degree pin, the four marked-core pro-`2` data
(workstream CLASS), the two `params` pins, the packet's `ramifiedData` input, and that one Prop.

| `KSupply` field | before this lane | after |
|---|---|---|
| `hdeg`, `hhom` | DONE | DONE |
| `pro2`, `hpro2`, `ker_pro2`, `nu_compat` | CLASS | CLASS (unchanged) |
| `exactLifting` | **ASK, open** | one Prop, `askCStageVanishing` |
| `stokes` | **ASK, open** | **free** |
| `determinant` | **ASK, open** | **free**, given `ramifiedData` |

So the ASK block of `GenAsmRowResidual` (fields `exactLifting`, `stokes`, `determinant`) goes
from three carried clauses to **one**, and that one is a coefficient condition rather than a
counting theorem.  `askCKExactSupply_of_markedCore` is the general-degree analogue of
`kExactSupply_of_markedCore_degreeOne`: the degree-one restriction of that constructor was never
an artefact, it was exactly `askCStageVanishing`, which is free at `n = 1` because the
coefficients coincide there.

**If the statement change of §3.1 is taken instead**, the ASK block becomes a **zero-block
record**: `sourceRN_of_markedCore` (already at head) plus `askC_stokes_galK` plus
`affineDeterminant_galK` leave nothing on the arithmetic side at any degree.

---

## 5. Where things stopped

* Whether `askCStageVanishing` is **true** at `G_K` is open, and the lane did not resolve it.
  §3.1 argues it is the wrong thing to want rather than a thing to prove; that argument is a
  recommendation, not a refutation, and is labelled as such in the module.
* No refutation was attempted, because refuting it requires exhibiting a concrete frame at `G_K`
  with `1 < #R` and a nonempty `BoundaryLiftsK`, which is branch data the ASK layer does not own.
* `GQ2.lean` registration for the new module is not done (protocol: the housekeeping sibling
  owns that file).
* The stale sentences in `KSupply.lean` §4/§6 and `w74-critical-path.md` §1.4 were **not**
  edited, per the lane's "one new module, no edits to existing modules" scope.  They are listed
  here so the housekeeping lane can correct them: `KSupply.lean`'s "at `K` it is unowned" for the
  half-torsor existential, and the critical path's "the K-clones of the `ℚ₂` counting pack" row
  for `exactLifting`/`stokes`/`determinant`.
