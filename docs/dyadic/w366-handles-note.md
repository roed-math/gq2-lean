# W366-HANDLES: the finite Nielsen-family lists at every handle count

Lane note, wave 366. Module: `GQ2/Dyadic/MarkedCore/MNielsenHandles.lean`.

## Scope (read this first)

This lane is **optional mathematics beyond the packet's rank-four rows**. The owner has
accepted (Option A, 2026-09-18) the compactness proof method and the families reading of
the finite lists at rank four. Nothing in this lane is needed for that acceptance, and
nothing in it changes it. Every docstring in the module says so.

What is delivered is exactly the weaker statement flagged at
`docs/dyadic/w363-nielsen-note.md` lines 190-200:

> A weaker statement is within easy reach and is not claimed here: the seven core families,
> extended by the identity on the handle tail, still preserve orientation and cup at every
> `h`, hence still lift.

That statement is now a theorem. `alpha >= 2` throughout, as at rank four.

## What is NOT claimed

**There is no handle-mixing classification, here or anywhere in the repo.** The maps this
lane builds are the identity on the `2h` handle coordinates, on the nose, and their core
parameter is a *rank-four* `MStabParam`. Precisely:

* `mNielsenHdlMap_core` : the extension agrees with `mNielsenGenMap` on the rank-four core;
* `mNielsenHdlMap_handle` : the extension is the identity on the handle tail.

Those two theorems are the exact scope. A full-frame automorphism that moves the handle
block satisfies neither and is outside every theorem in the module. The stabilizer elements
covered are therefore those that fix the handle block **pointwise**, not merely up to
something the lift theorem tolerates: the lift theorem
(`MFullStabilizerLift.mFullStabilizer_lift`) has always allowed handles to mix arbitrarily,
and that generality is untouched and unused here.

The closure `mNielsenHdl_stabilizer_induced` is stated in the identity-tail form for the
same reason: at rank four the quantifier is closed against `mStabilizer_classification`,
which is a rank-four statement with no general-`h` counterpart, so at general `h` the two
block conditions are hypotheses rather than consequences.

## T1 (M side): what landed

All in `GQ2/Dyadic/MarkedCore/MNielsenHandles.lean`, namespace
`GQ2.Dyadic.MarkedCore`, prefix `mNielsenHdl`. Every declaration in the file carries a
`#print axioms` pin and every pin is std-3 (`propext`, `Classical.choice`, `Quot.sound`).
No `sorry`, no `native_decide`, no new axioms, no resource options.

* `mNielsenHdlCore`, `mNielsenHdlMap`, `mNielsenHdlEquiv` : the extension, as a
  `ContinuousMulEquiv (MFrameModel h) (MFrameModel h)`, together with
  `mNielsenHdlMap_zero` / `_core` / `_handle` pinning what it is.
* `mNielsenHdl_orientation` : it preserves `mFrameOrientation` at every `h`. Free, because
  `mFrameOrientation_apply` shows the orientation never reads the handle slots.
* `mNielsenHdl_cupIsometry` : it satisfies `MCupFrameCupIsometry` at every `h`. This is the
  one that needed work, and the reason is the **character-pair predicate**:
  `MCupFrameCupIsometry` quantifies over pairs of continuous mod-two characters of the
  *full* frame, which at handle count `h` see all `4 + 2h` coordinates, so the rank-four
  instance of the predicate is not a hypothesis one can transport. The route taken is the
  rank-four one of `MNielsenGenerators` rerun at general `h`. Its two main inputs,
  `mNielsenGen_character_apply` and `mNielsenGen_coord_*`, were already stated at general
  `h`; what is new is
  - `mNielsenHdl_coord_handle` : the mod-two reading of a handle coordinate,
  - `mNielsenHdl_sum_split` : the head-plus-handles split of a `Fin (coreRank h)` sum,
  - `mNielsenHdl_fix_markU` / `_fix_markV` : the handle marks are fixed **on the nose**
    (not merely mod two), which is what makes the handle block of `evenCupForm` literally
    the same term on both sides of the isometry equation.
  Only the head block then has to be checked, and that check is the rank-four one
  (`mNielsenHdl_cup_core`, a `decide` over `ZMod 2`; `MNielsenGenerators`' copy is
  `private`, so it is restated).
* `mNielsenHdlM1` ... `mNielsenHdlM7`, `mNielsenHdlList`, `mNielsenHdlCompose`,
  `MNielsenHdlLifts`, `mNielsenHdl_finite_list`, `mNielsenHdl_param_realized` : the packet's
  MC-M list artifact at every handle count. Seven members, each lifting by
  `mFullStabilizer_lift`, composite equal to the extension of the parameter's frame action,
  and the composite of the lifts a lift of the composite.
* `mNielsenHdl_eq_of_blocks`, `mNielsenHdl_stabilizer_induced` : the closure in the
  identity-tail form described above.

As at rank four, the lifts come from `mFullStabilizer_lift`, i.e. from the uniform
filtered-correction and compactness argument, **not** from generator-by-generator
group-level constructions. The rank-four inventory of which families do have independent
group-level lifts (M1, M2, and M3/M5 conditionally) is unchanged and is recorded in
`MNielsenGenerators.lean`; this lane adds none.

The list is, as at rank four, a list of seven family *members*, not seven *families*: each
family is parameterized by a 2-adic number or unit, and what the theorem produces for a
given parameter is one member of each. That reading is the one the owner accepted.

## T3: the classification that does not exist

`MNielsenHdlStabilizerShape ha h` is a named `Prop`, **stated and not proved**, saying that
every orientation-preserving full-frame cup isometry at handle count `h` is given in
coordinates by

* a core parameter `p : MStabParam` on the rank-four block,
* an invertible handle block `S` preserving the handle block's own mod-two symplectic form
  (`mNielsenHdlHandleForm`) -- the `GL` factor, and the whole difference between this and
  the identity-tail statement,
* handle-to-core shears into the torsion, `B` and `C` slots, and
* core-to-handle shears out of the `B`, `C` and `D` slots.

Two slots are absent by design and the docstring says why: there is no core-to-handle shear
out of the torsion slot because `Z_2` is torsion free, and no handle-to-`D` shear because
`mFrameOrientation_preserved_iff` already forces the integral `D` coordinate to be fixed on
the nose at every `h`. The identity-tail theorem of this lane is the special case `S = 1`
with all shears zero.

`mNielsenHdlShape_lifts` is the one direction that is free, and it is free because it is
`mFullStabilizer_lift` **restated**: that theorem never restricted the handle block. It is
recorded only to make explicit which half of a handle-mixing classification is already
available. It proves no part of `MNielsenHdlStabilizerShape`; the missing half is the shape
statement itself, and nothing in the repo bears on it.

## T2 (N side): what landed

`GQ2/Dyadic/MarkedCore/NNielsenHandles.lean`, namespace `GQ2.Dyadic.MarkedCore`, prefix
`nNielsenHdl`. All 45 declarations pinned, all std-3.

Same architecture as the M side, with one real difference. `nNielsenHdlCore`,
`nNielsenHdlMap`, `nNielsenHdlEquiv` and `nNielsenHdlMap_core` / `_handle` are the
extension and its exact scope; `nNielsenHdl_orientation` is free, because the `N`
orientation reads only the integral `x1` coordinate, which the extension fixes on the nose.
`nNielsenHdlN1` ... `nNielsenHdlN6`, `nNielsenHdlList` (eight slots, in
`NNielsenFactorization`'s order), `nNielsenHdl_finite_list`, `nNielsenHdl_param_realized`,
`nNielsenHdl_eq_of_blocks` and `nNielsenHdl_stabilizer_induced` complete the artifact and
its closure, in the same identity-tail form as at M.

**The difference is the cup head block.** `MNielsenHandles` closes its head with a `decide`,
because `MStabParam.act` carries no relation between its entries. The `N` head block does
carry one: the `(sigma, x2)` block of an `NStabParam` is a genuine `GL_2(Z_2)`, and the cup
condition on it is a relation supplied by `NStabParam.Admissible` through `N.lean`'s
`NStabParam.rows_isCupIsometry`. So `NNielsenGenerators.nNielsenGen_cup_of_mat`, which is a
rank-four matrix criterion, had to be restated at general `h` for the identity-tail maps:
`nNielsenHdl_char_of_core` (a character on an element with trivial handle tail is its
rank-four coordinate expansion), `nNielsenHdl_char_coreMark` (the value on the image of a
core mark, in the parameter's own mod-two matrix), and `nNielsenHdl_cup_head` (the head
check, `NNielsenGenerators`' `private` `nNielsenGen_cup_core` restated in the explicit
eight-variable form the general-`h` `evenCupForm` head presents). Every N-side theorem
therefore carries `P.Admissible`, exactly as at rank four.

The handle block behaves identically to M: `nNielsenHdl_fix_markU` / `_fix_markV` fix the
handle marks on the nose, so the handle term of `evenCupForm` is literally the same on both
sides. `nNielsenHdl_sum_split` is a copy of the M module's, because the `N` file's import
closure does not see `MNielsenHandles`; that is the only duplication between the two
modules.

T3 has no N counterpart in this lane: the shape statement is stated once, at M, and its
`GL`-of-the-handle-block content is the same object on both sides.

## Verification

Checked with `bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/MNielsenHandles.lean`
against the shared cache at base `9dd8a307`. No `lake` invocation, no cache mutation,
no artifacts written. `GQ2.lean` untouched; no existing module edited.
