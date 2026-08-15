# W72: the class-four leftover, reduced to the two defects

Lane W72-DEFECTS.  New module `GQ2/Dyadic/SqCore/GradedClassFourDefect.lean`; no edits to
existing files.  Prefix `cfourDef`.  Base `e2e8917a`, lane branch `claude/w72-defects`.

## 0.  Headline

**`SqClassClearingSupply h 4` is NOT discharged, and it is NOT refuted.**  What this wave adds is
a *computation*: the whole class-four leftover of wave 68's frame is now reduced, by one explicit
admissible correction, to a product of two named `Z`-elements, and the second of them is
resolved down to the frame's own letters.

```text
  sqRelWord (wave 68's frame · cfourDefCorr nu' j)
    = cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆
```

with `A = bridgeDress nu' j` and

```text
  cfourDefCore nu' j = ⁅σ, A⁆ · ⁅A, x₀⁆ · cfourEichDefect nu' j  ∈  Z = γ₃/γ₄ .
```

That is `cfourDef_leftover_reduce_merged`.  The relator identity needs **no** hypothesis on the
marking; only admissibility of the correction does.

Wave 71's three leftover items (its note §4) land as follows.

| wave-71 item | wave-72 disposition |
|---|---|
| 1. the two defects `⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect` | **expanded and split** (`cfourDef_defect_eq`); the triple part is absorbed into the reduction, the core part `cfourDefCore` is the residue |
| 2. the square `⁅A, x₀⁆²` | **committed** (`cfourDef_commSq_correction`), residue Jacobi-reduced |
| 3. the pairing residue `⁅⁅A, x₁⁆, A⁆` | **committed**: it cancels against the `σ`-slot knob of `⁅x₁, A⁆` (they are the same element of `Z`), and the far-slot machinery it needed is `cfourDef_comm_dress_mem` |

## 1.  The two defects, expanded (target 2)

⭐⭐⭐ `cfourDef_common_dress`, the class-four replacement for wave 68's
`bridge_comm_common_dress`.  In `Q₄`,

```text
  ⁅s·a, x·a⁆ = ⁅s, x⁆ · (⁅s, a⁆ · ⁅a, x⁆) · (⁅⁅s, a⁆, a⁆ · ⁅⁅a, x⁆, a⁆) .
```

Five surviving factors, and **nothing else**: the term `⁅⁅s, x⁆, a⁆` arises twice, once from the
free identity in the far slot and once from the correction term in the near slot, and the two
cancel because `Z` has exponent two.  Wave 68's `⁅s·x, a⁆` does not survive as such; one class up
it splits into the two brackets `⁅s, a⁆ · ⁅a, x⁆` plus the two triple brackets.

Stripping `⁅σ, x₀⁆` (`cfourDef_strip`, `Y` being abelian) gives ⭐⭐⭐ `cfourDef_defect_eq`:

```text
  ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect = cfourDefCore · cfourDefTriple
```

with `cfourDefTriple = ⁅⁅σ, A⁆, A⁆ · ⁅⁅A, x₀⁆, A⁆`.

**Which of these are knobs.**  Read against wave 70's inventory (`cfour_dress_zero`,
`cfour_dress_one`, `cfour_dress_two`, `cfourId_dress_handleU`, `cfourId_dress_handleV`):

* `cfourDefTriple` and the Jacobi term merge into one bracket `⁅y, A⁆` with
  `y = ⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆ ∈ Y` (`cfourDef_triple_mul_jacobi`), whose **far slot is the
  dressing**.  §3 below puts this inside the frame's knob expressions.
* `cfourDefCore` is **not** of that shape.  It is a product of three `Y`-elements which happens
  to lie in `Z` because its three class-three images cancel (`cfourDef_core_mem_zLayer`, proved
  through `cfourId_leftover_mem_zLayer`), and none of its factors is a bracket with a
  `Y`-element in a slot.  **This is the residue.**

`cfourDefCore` is `x₁`-free: every letter in it is `σ`, `x₀`, a handle letter or the pivot.

## 2.  The reduction (target 1)

⭐⭐ `cfourDefCorr nu' j` is the explicit correction

```text
  σ-slot:  ⁅x₁, A⁆ ,     x₁-slot:  A² · ⁅A, x₁⁆ · ⁅A, x₀⁆ ,     every other slot:  1 ,
```

exactly row-trivial slot by slot (`cfourDefCorr_admissible`, using
`cfourKnob_dressSq_admissible` and `cfourKnob_comm_admissible`, which need the selected-marking
hypotheses).

⭐⭐⭐ `cfourDef_leftover_reduce` / `cfourDef_leftover_reduce_merged`.  Against
`cfourKnob_leftover_eq` five factors annihilate pairwise, `Z` being central of exponent two
(`cfourDef_assemble`, stated with named atoms so the bookkeeping is separate from the
identification):

| corrected-relator factor | killed by |
|---|---|
| `A⁴` (leftover) | the `A²`-part of the `x₁`-slot correction |
| `⁅A, x₀⁆²` (leftover) | the `⁅A, x₀⁆`-part of the `x₁`-slot correction |
| `⁅x₁, ⁅x₁, A⁆⁆` (leftover) | the `⁅A, x₁⁆`-part, through `cfourKnob_dress_pair` |
| `⁅⁅A, x₁⁆, A⁆` (pairing residue, knob-internal) | the `σ`-slot knob's first bracket `⁅⁅x₁, A⁆, A⁆`, the same element of `Z` (`cfourDef_swap_inner`) |
| `⁅⁅x₁, A⁆, x₀⁆` (Jacobi residue, knob-internal) | the `σ`-slot knob's second bracket, literally equal |

> **[W74-HOUSE, background sweep: column retitled.]**  The column was headed "leftover factor",
> and only the first three are.  Read against `cfourKnob_leftover_eq`, whose right-hand side is
> `⁅σA,x₀A⁆·⁅σ,x₀⁆⁻¹ · cfourEichDefect · (A⁴ · ⁅A,x₀⁆²) · ⁅x₁,⁅x₁,A⁆⁆`, the last two rows appear
> **nowhere**: they arise from the correction and each occurs twice *inside the knob*.  The
> module's own `cfourDef_assemble` docstring (`GradedClassFourDefect.lean:360`) has it right,
> "five of the **eight factors of the corrected relator**"; the module's two wrong copies at
> `:53` and `:443` are corrected at wave 74 under round 10's §3.1(b).

The `σ`-slot knob is `⁅c, x₀·A⁆ = ⁅c, A⁆ · ⁅c, x₀⁆` at `c = ⁅x₁, A⁆`; that it pays for **two** of
the five is the reason one correction suffices.

The intermediate `cfourDef_relator_step` records the frame surgery alone (through
`cfourId_dress_core`), which is worth keeping separate: it is the only part that touches
`sqArbFrame`.

## 3.  The far slot of the dressing (target 1b)

⭐⭐ `cfourDef_comm_dress_mem`: for `y ∈ Y`, `⁅y, A⁆` lies in any subgroup holding `⁅y, u_j⁆` and
`⁅y, v_j⁆`.  Proof: `A = u_j^{ν'(v_j)} · v_j^{ν'(u_j)} · w^{-2ν'(u_j)ν'(v_j)}`; the pivot factor
has an even exponent, hence lies in `γ₂` and is invisible to a bracket with a `Y`-element in the
near slot; the two handle powers are read through their exponents' parity only
(`cfourDef_comm_zpow_mem`, stated against an arbitrary subgroup so that no decidability of
`2 ∣ k` in `ℤ₂` is needed).  This is exactly "bilinearity in the far slot plus the `zpow`
bookkeeping of `bridgeDress`" from the wave-71 ticket.

The frame does not carry `u_j` and `v_j` but the **cleared** letters `U_j = w^{-ν'(u_j)}·u_j` and
`V_j = v_j·w^{-ν'(v_j)}`.  `cfourDef_comm_genU_mem` / `cfourDef_comm_genV_mem` cross that gap at
the cost of one pivot bracket each, and ⭐⭐ `cfourDef_comm_dress_frame_mem` chains all three:

```text
  ⁅y, w⁆, ⁅y, U_j⁆, ⁅y, V_j⁆  ∈ S   ⟹   ⁅y, A⁆ ∈ S .
```

⭐⭐⭐ `cfourDef_core_knob_pair`: the pivot bracket is the product of the **two core knobs at a
common correction**.  The `σ`-slot knob at `c` is `⁅c, x₀·A⁆`, the `x₀`-slot knob at `c` is
`⁅σ·A, c⁆`; each carries a copy of `⁅c, A⁆`, the two cancel, and what survives is
`⁅c, x₀⁆·⁅c, σ⁆ = ⁅c, σ·x₀⁆ = ⁅c, w⁆`, because `σ·x₀` is the pivot modulo `γ₂`
(`bridge_sigma_x0_eq_pivot`).  This is the class-four shadow of wave 68's own `bridgeDefect`,
which is `⁅w, A⁆` in `Q₃`.

And `⁅y, V_j⁆` is the `u_j`-slot knob of `cfourId_dress_handleU`, while
`⁅U_j, y⁆ = ⁅y, U_j⁆` (`cfourDef_comm_swap`) is the `v_j`-slot knob of `cfourId_dress_handleV`.

**So all three inputs are knob expressions of the frame's remaining slots.**

## 4.  What is left, exactly (targets 2 and 3)

`CfourDefResidual h` names it, and ⭐⭐ `cfourDef_supply_of_residual` shows it discharges
`SqClassClearingSupply h 4`.  It says: some further admissible correction of the
**already-corrected** frame kills the relator, and by §2 the relator there is exactly

```text
  cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆ .
```

`cfourDef_residual_of_vanish` is the trivial sufficient condition (the residue is `1`); nothing
here says it holds.

**Target 3 (`SqClassClearingSupply h 4`) did not land, and this is where it stopped.**  Two
things are missing, and they are different in kind.

1. **A composition lemma, purely technical.**  §3 puts `⁅y, A⁆` inside the frame's knob
   *expressions*, not inside the knob *subgroup*, because the tree has no lemma composing a
   handle-slot correction with a core-slot correction.  `cfourId_dress_core` composes the three
   core slots; `cfourId_dress_handleU`/`cfourId_dress_handleV` move one handle slot with the core
   slots held fixed.  What is needed is one lemma of the shape

   ```text
     m' = m dressed on slots 0, 1, 2 by c₀, c₁, c₂ and on the j-th handle by c_U, c_V
       ⟹ sqRelWord m' = sqRelWord m · (the five knobs, all central)
   ```

   All the ingredients exist (every knob is a `Z`-element, hence central, so the chaining is the
   same argument `cfourId_dress_core` already makes for its three slots).  A wave-73 lane should
   do this first; it is a day's work at most, and with it §3 turns `⁅y, A⁆` into an actual
   correction and the residue collapses to `cfourDefCore` alone.
2. **The core defect itself, mathematical.**  Even with 1, the residue is `cfourDefCore`, and
   nothing in this wave says whether it is a knob.  It is a product of three `Y`-elements lying
   in `Z` for a *reason* (the class-three images cancel), and the knob inventory produces
   `Z`-elements of two shapes only: brackets `⁅y, g⁆` with `y ∈ Y`, and squares `y²` bundled with
   `⁅y, x₁⁆`.  Deciding whether `cfourDefCore` has such a presentation is the real remaining
   question, and it is the one this wave hands on.

   Note what makes it delicate: `cfourDefCore` is `x₁`-free, and the whole `x₁`-slot bundle is
   spent already.  So the presentation, if it exists, must come from the `σ`-, `x₀`- and
   handle-slot knobs, i.e. from brackets `⁅y, g⁆` with `g` in the span of `σ`, `x₀`, the handle
   letters and the pivot - which by §3 is all of `V` except the `x₁`-direction.

   **[W75-HOUSE, waves 73-74.**  Wave 73 replaced this question by a stronger one that does not
   mention `cfourDefCore` (`cfourCmp_residual_of_span`), and wave 74 refuted **that** one at
   `h ≥ 1` (`gDelta_cfourCmp_span_hyp_false`).  Note carefully what does and does not follow:
   the question asked here -- **is `cfourDefCore` a knob?** -- is *not* answered.  Wave 73's
   replacement was strictly stronger (a subgroup containing all three families, versus one
   element), so refuting the replacement leaves this item open.  What the refutation does supply
   is the reason to stop looking along this route, and a better place to look:
   `cfourDefCore`'s functional reading is `S^{-1} X^{-1} (S - X) · gDelta(A)` with
   `v₂(S - X) = 3` exactly (`gDelta_coreLift_eq`), so it is functional-invisible at the layer bit
   -- which is the hypothesis the Lemma 3 analogue of `w74-func-note.md` §4.3(2) consumes.]**

## 5.  Honesty markers

* Nothing in this wave is evidence that **no** dressing works.  Everything above concerns one
  sufficient route, `γ₂`-valued corrections of wave 68's frame (wave 70's `CfourIdReachable`),
  and a failure of that route would not touch `SqClassClearingSupply h 4`, which is what wave
  67's equivalence is stated against.  This wave produces no statement about the supply itself
  other than the sufficient condition `cfourDef_supply_of_residual`.
* `cfourDef_comm_dress_frame_mem` and `cfourDef_core_knob_pair` are stated about knob
  **expressions**.  The docstrings say so explicitly.  They do not assert that the corresponding
  correction tuple exists; see §4.1.
* The reusable tooling here has been checked for satisfiable hypotheses, not merely general
  binders (the wave-71 trap).  `cfourDef_jacobi_solve`, `cfourDef_swap_inner`,
  `cfourDef_common_dress`, `cfourDef_strip`, `cfourDef_shuffle`, `cfourDef_z_push`,
  `cfourDef_z_sq`, `cfourDef_z_cancel`, `cfourDef_assemble`, `cfourDef_comm_inv_right`,
  `cfourDef_comm_swap` are stated over `levelQuot G 4` for an arbitrary topological group; their
  hypotheses are `Y`-membership and `Z`-membership, both of which are inhabited at `γ₃/γ₄` by
  every bracket and every triple bracket respectively, and both of which are the *same two*
  predicates wave 70's `gThreeFour_*` family uses.  **They are class-four, not layer-agnostic**:
  each rests on "`Y` is abelian" and "`Z` is central of exponent two", and wave 70's §5 warning
  applies - one layer up `Y` is no longer abelian, so `cfourDef_common_dress` in particular would
  have to be re-proved and would not have five factors.  The only genuinely layer-free statements
  in the file are the four in `section Involutions` (`cfourDef_z_push`, `cfourDef_z_sq`,
  `cfourDef_z_cancel`, `cfourDef_assemble`), whose only input is a central subgroup of exponent
  two.

## 6.  Verification record

* Base `e2e8917a`, lane branch `claude/w72-defects`.  Five code commits plus this note, all path-limited.  Not pushed.  `GQ2.lean` not edited; no existing file edited.
* `scripts/mirror.sh sweep` at lane start (5813 artifacts), `scripts/mirror.sh check
  GQ2/Dyadic/SqCore/GradedClassFourDefect.lean` after every increment, and
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedClassFourDefect` at the end.  Clean.  No name
  collisions: `grep -rl cfourDef GQ2/ docs/` returns this file only.
* One import, `GQ2.Dyadic.SqCore.GradedClassFourKnob`.  No `SqCore → Count` import.
* **38 declarations, 34 axiom pins, every one `[propext, Classical.choice, Quot.sound]`.**  No
  `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.  (Corrected at
  W74-HOUSE: the figure read "34 declarations", which is the count of *pinned theorems*.  The
  module has 34 theorems and 4 unpinned `def`s, disclosed below, so 38 in all.  The disclosure
  reads "three definitions ... and the `Prop`", four items in a sentence that says three, which is
  how a reader reconciling the two figures lands on 37.)

  `cfourDef_jacobi_solve`, `cfourDef_swap_inner`, `cfourDef_commSq_correction`,
  `cfourDef_shuffle`, `cfourDef_common_dress`, `cfourDef_strip`, `cfourDef_triple_mem_zLayer`,
  `cfourDef_defect_eq`, `cfourDef_defect_mem_zLayer`, `cfourDef_core_mem_zLayer`,
  `cfourDef_z_push`, `cfourDef_z_sq`, `cfourDef_z_cancel`, `cfourDef_assemble`,
  `cfourDefCorr_zero`, `cfourDefCorr_one`, `cfourDefCorr_two`, `cfourDefCorr_handleU`,
  `cfourDefCorr_handleV`, `cfourDefCorr_admissible`, `cfourDef_relator_step`,
  `cfourDef_leftover_reduce`, `cfourDef_triple_mul_jacobi`, `cfourDef_leftover_reduce_merged`,
  `cfourDef_comm_inv_right`, `cfourDef_comm_swap`, `cfourDef_comm_zpow_mem`,
  `cfourDef_comm_dress_mem`, `cfourDef_comm_genU_mem`, `cfourDef_comm_genV_mem`,
  `cfourDef_comm_dress_frame_mem`, `cfourDef_core_knob_pair`, `cfourDef_supply_of_residual`,
  `cfourDef_residual_of_vanish`.

  (Four unpinned declarations: the three definitions `cfourDefCore`, `cfourDefTriple`,
  `cfourDefCorr` and the `Prop`
  `CfourDefResidual` carry no proof term and are not pinned.)
* The element bracket `⁅ , ⁆` is again avoided throughout; everything is written in `commP`.
