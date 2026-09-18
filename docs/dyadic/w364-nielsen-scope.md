# W364: original-specification scope of the finite Nielsen-list artifacts

2026-09-17. Independent read-only review of the three wave-363/364 Nielsen
modules, with fresh default-limit elaboration of all three by the auditing lane
`w364-audit2`. This note does not approve a release, amend the authoritative
packet, or change any freeze. It is the MC-M/MC-N twin of
`docs/dyadic/w363-m-full-stabilizer-scope.md` and
`docs/dyadic/w361-n-full-stabilizer-scope.md`. The proof-level evidence is in the
companion `docs/dyadic/w364-nielsen-independent-audit.md`.

## What the packet asks for

`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex`, lines 1077-1082,
rows MC-M and MC-N:

> A finite list of orientation-preserving Nielsen generators lifts the
> Smith--Witt stabilizer on the abelianization; composition gives every
> required marking correction.

Both rows are explicitly about the **rank-four** cores.

## What is now proved, at M

In `GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean`:

* `mNielsenGenList ha gamma k b e beta c d`, a list of **seven** honest
  `ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)`, one drawn from each of
  memo section 2.4's seven families `Σ_γ, Λ_k, X_b, E_e, Σ_β, Y_c, Z_d`; each has
  an explicit inverse inside its own family, so none is a bare map.
* `mNielsenGen_finite_list (ha : 2 ≤ alpha) (p : MStabParam)`: for every
  stabilizer parameter there are witnesses making that list satisfy all four of
  (i) length 7; (ii) every member preserves the transported **actual** orientation
  `mFrameOrientation` and the full semantic `MCupFrameCupIsometry`, hence lifts to
  an actual `chiM`-preserving continuous automorphism of `D_M` with the exact
  all-element commuting frame square; (iii) the composite of the list is `p`'s own
  frame action; (iv) the composite lifts, and its lift is built by composing the
  members' lifts.
* `mNielsenGen_stabilizer_induced`: for
  every `alpha >= 2`, every orientation character `chi` with the four pinned
  generator values, and **every** continuous automorphism `xi` of
  `topAbelianization (DM alpha 0)` satisfying `IsMStabilizer`, there is an actual
  continuous automorphism `Psi` of `D_M` with

  ```text
  chiM alpha 0 (Psi x) = chiM alpha 0 x        for every group element x
  abMk (Psi x) = xi (abMk x)                   for every group element x
  ```

  `IsMStabilizer` is chi-preservation plus `M̄ᵀ G_M M̄ = G_M`, with nothing added,
  so the quantifier is the packet's own: every element of the Smith-Witt
  stabilizer, not every element of some parameter type.

## What is now proved, at N

In `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean` (with the W363 bridge
`NNielsenGenerators.lean`):

* `nFamN1` .. `nFamN6`, memo section 3.4's six families as `NStabParam` values,
  each `Admissible`, and `nNielsenFacN1` .. `nNielsenFacN6` as honest continuous
  automorphisms of `NFrameModel 0`.
* `nNielsen_factorization (P : NStabParam) (hP : P.Admissible)`: the frame action
  of every admissible parameter is the composite of the **eight** fixed slots
  `N2(z), N3(y), N2(x), N4(κ), N3(w), N5(p), N6(q), N1(k)`, leftmost applied
  first, with `κ = det g` and `w ∈ {0, 1}` both recorded in the statement. This
  statement carries **no `alpha` binder at all**, as memo section 3.3's
  "completely α-independent" predicts.
* `nNielsenFac_finite_list (ha : 2 ≤ alpha) (P) (hP : P.Admissible)`: the four
  clauses of `mNielsenGen_finite_list`, at length 8, against `nFrameOrientation`
  and the full semantic `NFrameCupIsometry`.
* `nNielsenFac_stabilizer_induced`: for every `alpha >= 2` and **every** continuous
  automorphism `xi` of `topAbelianization (DN alpha 0)` whose rows in the
  canonical frame satisfy `IsNStab`, there is an actual continuous automorphism
  `Psi` of `D_N` with `chiN alpha 0 (Psi x) = chiN alpha 0 x` and
  `abMk (Psi x) = xi (abMk x)` for every group element `x`.
* `nNielsenFacLifts_of_param_families`: a **second, independent** lift of every
  list member, assembled from the six families' own constructions rather than from
  the compactness theorem. M has no counterpart.

The frames are the actual objects. `mFrameExists_phiEquiv` and
`nFrameExists_phiEquiv` are proved `ContinuousMulEquiv`s onto the topological
abelianizations, the commuting squares are stated on `mPhiHom ... (abMk ...)` and
`nPhiHom ... (abMk ...)` directly, and both cup predicates quantify over **all**
continuous `F2` characters of the frame, torsion character included. No
`MStabParam`/`NStabParam` coordinate model is interposed between the final
theorems and the group.

## Exactly what is not claimed

### 1. Handle rank

Rank **zero** only, at both cores. This is what the packet rows ask for, but it is
worth stating that it does not extend for free: the lifting halves
(`mFullStabilizer_lift`, `nFullStabilizer_lift`) are general in `h`, but
`mStabilizer_classification`, `M.lean`'s `mNielsen_factorization` and
`nStabilizer_classification` are rank-four statements, so the list is rank-four.
At `h > 0` one would first need a classification of the full-frame stabilizer
including the handle block. No such classification exists in the repository.

The weaker statement that the core families, extended by the identity on the
handle tail, still preserve orientation and cup at every `h` is **not** claimed
here and is not in the tree, though the coordinate and character machinery
(`mNielsenGen_coord_*`, `mNielsenGen_character_apply`,
`nNielsenGen_coord_*`, `nNielsenGen_character_apply`) is already stated at general
`h`.

### 2. `alpha`

`alpha >= 2` in every statement that mentions the actual frame. At M the binder is
load-bearing and not decorative: it is consumed through `mFrame_nRed_halfExp`,
which is **false at `alpha = 1`**, where the forced `A`-row correction
`Ā = t − 2^{α−1}C̄₀` becomes visible mod two. Nothing is asserted at
`alpha <= 1`. The N parameter-level statements (`nNielsen_factorization`,
`nNielsenFac_gl2_factor`, `nNielsenFac_couple`) are genuinely `alpha`-free.

### 3. "Finite list" means finitely many families

The seven M families and six N families are each parameterized by a 2-adic number
or a 2-adic unit. What either theorem produces for a given stabilizer element is
**one member of each slot**, seven slots at M and eight at N. A literally finite
generating **set** is impossible: the stabilizers are not finitely generated as
abstract groups (`St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)`). Both modules and both lane notes
say this explicitly; this note records that the auditing lane agrees it is the
only available reading and that it is the reading the theorems satisfy.

### 4. Lift provenance: this is the owner's adjudication

The per-generator lifts inside `mNielsenGen_finite_list` and
`nNielsenFac_finite_list` are supplied by the wave-361/362 compactness theorems
`mFullStabilizer_lift_of_frame` and `nFullStabilizer_lift`. **No generator is
lifted by an explicit closed-form group-level construction in either finite-list
theorem, and neither module claims one.** The finite list is a genuinely new
object and the compactness proof is not relabelled as a finite-list proof, which
is what Codex's warning in `docs/dyadic/w361-claude-code-handoff.md` section 3
asked for; that discipline is kept.

What group-level constructions do exist, for the record:

* **M1** `Λ_k`: `M.lean`'s `mLambdaEquiv`. Closed form.
* **M2** `E_e`: HM4's `dmTauDEquiv`. Closed form.
* **M3** `Σ_γ`: `MarkedCore/MScaling.lean`'s `mScaleEquiv`, with
  `chiM_mScaleEquiv` and `mScaleEquiv_C_row`, discharged unconditionally by
  `mScalingHypothesis_zero`. This pins the `C` row and orientation; it is **not**
  stated to induce the full M3 frame action including the memo's coupled
  `A ↦ A·C₀^{m(1−γ)}` correction. See FLAG-1 of the companion audit: the module
  docstring and the lane note disagree about whether this counts.
* **M4, M5, M6, M7**: no group-level construction anywhere in the repository.
* **N1, N2, N3**: `dnTauBEquiv`, `dnTauDEquiv`, `dnTauCEquiv`. Closed form.
* **N5, N6**: the `CoreMix`/`ClearWide` constructions behind
  `nMixPairHypothesis_coreMix`.
* **N4**: `nPlaneScalingHypothesis_general`, which is itself a compactness limit
  of the N-plane stages, **not** a closed formula.

So if the owner reads the packet sentence as demanding generator-level lifts, the
outstanding work is: at M, families M4 through M7 (and M3 if the narrower reading
of `MScalingHypothesis` is taken); at N, family N4 only.

### 5. The M orientation character

`mNielsenGen_stabilizer_induced` takes an abstract `chi` together with its four
pinned generator values, exactly as `mStabilizer_classification` does. It does not
construct a descended `chiMab` and prove that clause redundant. This is `M.lean`'s
own recorded finding 6, inherited, not a new gap. The N side has no analogue: its
stabilizer clause `IsNStab` is intrinsic, so the N quantifier closure needs no
character to be supplied.

### 6. Minimality

Neither the seven-slot M bound nor the eight-slot N bound is claimed minimal, and
neither is proved minimal. `docs/dyadic/w364-nfactor-note.md` argues informally
that the `GL₂(ℤ₂)` block cannot be done in four slots of the `E, F, diag(κ,1)`
families; that argument is unformalized (FLAG-3 of the companion audit). No
statement about the minimal number of slots is in the tree.

### 7. What this does not touch

* No claim about the M or N **word certificates** (packet rows WC-*), about LG-K,
  or about any other packet row.
* No claim that the campaign or the owner acceptance ledger is complete.
* No re-verification of `mFullStabilizer_lift` / `nFullStabilizer_lift`
  themselves; see `docs/dyadic/w363-m-full-stabilizer-independent-audit.md` and
  `docs/dyadic/w361-n-full-stabilizer-independent-audit.md`.

## Axiom and build scope

All three modules recompile clean at default limits against the shared dependency
cache at base `d2056503`, with 70, 16 and 94 pinned declarations respectively.
**All 180 pins print exactly `propext, Classical.choice, Quot.sound`**; no
`sorry`, no `native_decide`, no `set_option`, no bare `axiom`. In particular the
B8 peripheral axiom is **not** in the footprint of either finite-list theorem:
`peripheralCyclotomicAction` is a genuine `axiom`
(`GQ2/Foundations/Axioms.lean:259`), so anything routed through
`mScalingHypothesis_zero` would print it, and none of the 180 pins does. The S2
stratum enters the finite list only through the frame action. The same pin dump
certifies transitively that `nStabParam_fullFrame_lift_general`, and therefore the
whole per-family N route, is std-3 as well, since
`nNielsenFacLifts_of_param_families` is among the 94.

Pin totals for the MC-M/MC-N block after W363 and W364: the nine consolidated
wave-362 M modules still carry 217 pins, the three Nielsen modules add 180, giving
**397**.

These are incremental source compilations against the shared cache, not a
source-only transitive rebuild, and they do not extend the historical frozen
clean-build report.
