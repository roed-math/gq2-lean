# W51-EV3F — the chain map and the F1/F2 seam

Produced by **W51-EV3F1** (the span/bracket half of EV-3f,
`docs/dyadic/ev4b-stage-abstraction.md` §4) before writing any Lean, as the ticket
requires.  The orchestrator pastes §2 and §4 into the **EV-3F2** brief.

## 1. The committed L template chain, as it actually is

`ls` confirms the seven station files (all under `GQ2/Dyadic/Instances/`, all with the
prefix `GammaLSylowPreimageFieldLabute`).  Their real import edges are **not** the linear
`RawSpan → RawSpanStep → BracketSpan → StageHandles → …` order the board's station list
suggests.  Measured from the `import` lines:

| file | lines | imports (within the station) |
|---|---|---|
| `…LabuteStage.lean` | 1731 | (below the station; the generic stage layer) |
| `…StageHandles.lean` | 1293 | `…LabuteStage` |
| `…RawSpan.lean` | 609 | **`…StageHandles`** |
| `…RawSpanStep.lean` | 620 | `…RawSpan` |
| `…ForwardSpanAudit.lean` | 217 | (via `…StageHandles`) |
| `…BracketSpan.lean` | 428 | **`…ForwardSpanAudit`** |
| `…StageRankOne.lean` | 590 | `…LabuteStage`, `…CoreRankOne`, `…Rigidity`, `Roe/Labute/StageLemma/StageTwo` |
| `…KernelAdaptedSupply.lean` | 594 | `…StageFunctionals`, `…ForwardCapstone` |
| `…VariableStageTwo.lean` | 142 | `…VariableStageOne` |

So the true partial order inside the station is

```
        LabuteStage
             |
        StageHandles ──────────────┐
        /          \               │
   RawSpan     ForwardSpanAudit    │  (StageRankOne, KernelAdaptedSupply,
       |             |             │   VariableStageTwo hang off other
  RawSpanStep   BracketSpan        │   committed files, not off RawSpan)
```

**`StageHandles.lean` is the root of the span half, not a sibling of it.**  That is the
one fact the orchestrator's split did not have, and it is why §2 re-cuts the seam.

### 1.1 What `StageHandles.lean` actually contains — two separable blocks

The file is two layers stacked in one place, and the cut between them is clean:

* **Block H-lit, lines 31–415, "the literal word factorization"** —
  `commP_mem_lambdaImage_two`, `conj_lambdaImage_two_eq_self_of_depth`,
  `handlePair_mul_lambdaImage`, `commP_mul_left_of_depth`, `handlePairDbar_mul`,
  `sqHandleDbarWord` (+`_mem_zLayer`/`_one`/`_mul`), `sqCoreHandleDbarWord`
  (+ the same three), `handleWord_mul_lambdaImage`, and the endpoint
  `stageShift_eq_dbarWordR2_mul_sqHandleDbarWord`.
  Character-free, purely presentation-theoretic.  **`RawSpan` consumes only this block.**
* **Block H-sharp, lines 416–1293, "the sharp-neutral correction layer"** —
  `exists_exactStageRepresentative`, `admissibleCorrection_nonempty`,
  `sharpAdmissibleCorrection_nonempty`, `SharpNeutralCorrection` (+ group structure),
  `sharpNeutralShiftHom`, `sharpNeutralCoordinate{Subgroup,Hom,ShiftHom}` and its five
  `_apply` rows, `SharpAdmissibleCorrection.{mulNeutral,differenceNeutral}`,
  `CoreHandleSharpActualDefectSupply` and its five constructors/adapters.
  Every declaration is stated against `sharpChiLevel`.  **`ForwardSpanAudit` and
  `BracketSpan` consume only this block.**

## 2. The re-cut seam (this is the F1/F2 contract)

Cutting at "does it mention the character" instead of at file boundaries gives two halves
that build in parallel:

* **F1 (this agent) — the raw/character-free span calculus.**  Block H-lit re-derived at
  the even words, then `RawSpan`, then `RawSpanStep`, then the bracket-atom identification
  of the raw coordinate span.  Files `StageAbstractionEvenRawSpan.lean`,
  `StageAbstractionEvenRawSpanStep.lean`, `StageAbstractionEvenBracketSpan.lean`.
  Reserved prefixes `evenRaw` / `evenBracket` / `evenSpan`.
* **F2 — the sharp/character-refined layer and the assembly.**  Block H-sharp,
  `ForwardSpanAudit`, the sharp half of `BracketSpan`, `StageRankOne`,
  `KernelAdaptedSupply`, `VariableStageTwo`, the SL1 crossed-derivation crux and the deep
  seam core-row upgrade.

**Consequence for F2, stated bluntly: F2 must not re-derive Block H-lit.**  The even
literal factorization is delivered by F1 in `StageAbstractionEvenRawSpan.lean` §1–§2 and is
imported, not cloned.  In the L chain that material sits in `StageHandles.lean`; in the
even chain it sits below the span files, where it belongs.

The even module import order is therefore

```
StageAbstractionEvenWords  (committed)
        |
StageAbstractionEvenRawSpan      §1 literal factorization  +  §2 raw span   [F1]
        |
StageAbstractionEvenRawSpanStep                                            [F1]
        |
StageAbstractionEvenBracketSpan                                            [F1]
        |
   (F2's sharp-neutral layer, then the assembly)
```

## 3. The mathematics that is genuinely new at the even words

The template step that does **not** survive verbatim is the crossed-derivation ("dbar")
word.  For the L relator the shift is the committed
`dbarWordR2 s x y w = w₂² · [w₂,y] · [w₀,x] · [w₁,s]` at `(s,x,y) = (base 0, base 1, base 2)`:
the diagonal square sits on coordinate 2, its bracket partner is the *same* letter, and
coordinates 0,1 are cross-paired.

At the even cores the shape moves.  Writing the correction as `w` and the base as
`(a,b,c,d) = (base 0, base 1, base 2, base 3)`, with `w i ∈ λ_{k-1}` and `2 ≤ α`:

| coordinate | L row (`dbarWordR2`) | even row |
|---|---|---|
| 0 | `[w₀, base 1]` | `w₀² · [w₀, base 0 · base 1]` ← **diagonal, product partner** |
| 1 | `[w₁, base 0]` | `[w₁, base 0]` |
| 2 | `w₂² · [w₂, base 2]` | `[w₂, base 3]` |
| 3 | — (rank 3) | `[w₃, base 2]` |
| `U_j` | `[w, base (V_j)]` | `[w, base (V_j)]` |
| `V_j` | `[w, base (U_j)]` | `[w, base (U_j)]` |

Two things to note.

**(a) The N and M shift words coincide at `2 ≤ α`.**  `nWord α a b c d = a^{2+2^α}·[a,b]·[c,d]`
and `mWord α a b c d = a²·[a,b]·c^{2^α}·[c,d]` have the *same* crossed derivation.  For a
depth-`k-1` correction `p` and `c := [p,x]` central of exponent two, the general expansion
is `(x·p)^e = x^e · p^e · c^{binom e 2}`, so the `e`-th power contributes
`p^e · c^{binom e 2}`, and modulo `p² ∈ Z_k` (exponent two) only `e mod 4` and
`binom e 2 mod 2` survive:

* `e = 2` (M's first letter): `p² · c`.
* `e = 2 + 2^α` (N's first letter): `binom e 2 = (1+2^{α-1})(1+2^α)` is **odd** for `α ≥ 2`,
  and `p^{2+2^α} = p²`.  So again `p² · c`.
* `e = 2^α` (M's third letter): `binom e 2 = 2^{α-1}(2^α − 1)` is **even** for `α ≥ 2`, and
  `p^{2^α} = 1`.  So this power contributes **nothing**.

Hence one `evenRawDbarWord` serves both branches, and the "M twin" of the ticket is the
same lemma applied to a second word datum rather than a second proof.

**(b) `2 ≤ α` is genuinely needed here, and `α = 1` genuinely fails.**  At `α = 1` the N
exponent is `4`: `binom 4 2 = 6` is even and `p⁴ = 1`, so the coordinate-0 row collapses to
`1` and the shift word loses its diagonal atom altogether.  This is the machine-level
version of the board's "at `α = 1` the mod-2 quadratic initial form dies" and confirms the
lane's standing `α ≥ 2` is not a convenience.  Declarations that consume only *evenness*
of the exponents (the naturality and central-shift plumbing) stay at `1 ≤ α`; every
declaration that consumes the diagonal atom is stated at `2 ≤ α`, marked per declaration.

**(c) The pure-square supply is still exactly the mismatch.**  The L proof recovers
`[p, base i]` for every `i` from the coordinate rows plus the pure squares.  The even proof
does the same with one extra step: coordinate 1 gives `[p, base 0]` directly, and then
`[p, base 1]` is extracted from the coordinate-0 row by dividing off `p²` *and* `[p, base 0]`,
using `commP_mul_right_of_mem` to split the product partner.  So
`EvenRawPureSquareSpanSupply` is the verbatim analogue of `RawPureSquareSpanSupply` and the
`iff` with `evenRawShiftSpan = zLayer` survives.

**(d) The twisted index moves to `1`, and not to `0`.**  The committed engine
`span_base_core_of_generators` (`GQ2/Roe/Labute/GradedLie/SpanBase.lean`) wants, at a
distinguished index `t`, the shape `v² · [v, marked t]`.  The even coordinate-`0` row is
`v² · [v, base 0] · [v, base 1]`, which is that shape for no letter at all.  Dividing it by
the coordinate-`1` row `[v, base 0]` gives `v² · [v, base 1]`, so the letter that cannot be
separated from the square is `base 1`, and the augmented span's tail set must omit index `1`.
The L template omits its index `2`.  This is the same asymmetry as (c), one level up.

## 4. Endpoints F2 consumes from F1

A cross-reference of the committed chain settles what actually crosses the seam.  In the L
chain **only `KernelAdaptedSupply.lean` textually consumes span-half names, and only four**,
all from `RawSpan.lean`: `rawShiftSpan`, `rawDepthShiftHom`,
`rawDepthShift_mem_rawShiftSpan`, `sqRawDefectReachable_iff_defect_mem_rawShiftSpan`.
`RawSpanStep.lean`'s endpoints reach no assembly-half file at all (they are consumed by
`VariableStage.lean` and the dead-end `RawSpanObstruction.lean`), and `BracketSpan.lean`'s
crossing endpoint is `nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan`, which
reaches `StageRankOne.lean` through `FieldRigidity`.

So the F1 surface F2 must program against is small.  Delivered, all in namespace
`GQ2.Dyadic.StageGeneric`:

| L name F2 would have used | F1 replacement | file |
|---|---|---|
| `rawShiftSpan` | `evenRawShiftSpan base hk : Subgroup (levelQuot G (k+1))` | part 1 |
| `rawDepthShiftHom` | `evenRawDepthShiftHom base hk : EvenRawDepthCorrection G h k →* zLayer G k` | part 1 |
| `rawDepthShift_mem_rawShiftSpan` | `evenRawDepthShift_mem_shiftSpan` | part 1 |
| `sqRawDefectReachable_iff_defect_mem_rawShiftSpan` | `evenRawDefectReachable_n_iff` / `_m_iff` | part 2 |

with the extra convenience endpoints `evenRawDefectReachable_n_of_pureSquareSpan` /
`_m_of_pureSquareSpan` (part 2), and, below them, the literal factorizations
`evenRawStageShift_n` / `evenRawStageShift_m` (part 1 §4), which are what F2 needs whenever it
must rewrite an actual `stageShift` into the explicit shift word.

**F2 must not re-derive Block H-lit** (§1.1).  Its even form is `evenRawHandleDbarWord`,
`evenRawCoreDbarWord`, `evenRawDbarWord` with their `_mem_zLayer`, `_one`, `_mul` lemmas,
plus `evenRawHandlePair_mul`, `evenRawCommP_mul_left_of_depth`, `evenRawHandlePairDbar_mul`
and `evenRawHandleWord_mul_lambdaImage`, all in part 1 §2–§3.

### 4.1 What of the span half is not delivered

`RawSpanStep.lean`'s successor engine is not cloned: the private `rawLiftSq`
lift-with-square machinery, the square-transport lemmas (`sqHandleDbarWord_sq`,
`sqCoreHandleDbarWord_sq`, `levelProj_sqCoreHandleDbarWord`), and the four theorems above
them (`rawSquare_mem_augmentedSpan_succ`, `rawAugmentedSpan_step`,
`rawAugmentedSpan_of_base_of_step`, `sqCore_rawAugmentedSpan_all`).  Everything the engine
consumes at the even words *is* delivered: the augmented span, the tail span, and the cubic
base case `evenRawAugmentedSpanBaseSupply_of_generates` with its two instantiations
`evenRawAugmentedSpanBaseSupply_dn` / `_dm`.  The remaining work is the induction turning
that base into `EvenRawPureSquareSpanSupply` at every `k ≥ 3`.  It is mechanical relative to
the L template, and its only even-specific input, the twisted index `1`, is already proved
(§3(d)).

`BracketSpan.lean` is not cloned either, and by §1.1 it should not be attempted from the span
side: every one of its declarations is stated against `sharpChiLevel` and it consumes Block
H-sharp, which is F2's.  Its span content (identifying a coordinate image set with a set of
bracket atoms) is the sharp-level shadow of part 1's six coordinate rows, so F2 can build it
directly on `evenRawDepthShiftHom_*_apply` once the even sharp-neutral layer exists.

## 5. Notes carried from the orchestrator

* The deep-seam depth verdict is uniform, `s = α − 1` on both branches for `α ≥ 2`; the
  supplies `evenRow_deepSupply_imChiN` and `evenRow_deepSupply_imChiM_of_two_le`
  (`GQ2.Dyadic.EvenRowSupply`) are F2 inputs.  The F1 span half is character-free and
  consumes neither.
* Mirror protocol when the shared cache advances: resweep with `ln -sf`, **then** regenerate
  own oleans, **then** run the collision test.  A resweep after generation silently restores
  stale copies of one's own modules.
