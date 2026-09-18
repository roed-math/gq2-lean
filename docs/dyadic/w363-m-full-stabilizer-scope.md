# W363 full M stabilizer: original-specification scope

**[W364 annotation: this document pins module hashes and the theorem name `mFullStabilizer_lift_of_frame` from before the W363-MCONSOL consolidation (`acffa057`, `492fe22e`). That pass renamed the conditional shape to `mFullStabilizer_lift_of_interfaces`, introduced the plain-named unconditional `mFullStabilizer_lift` with `_of_frame` kept as an alias, moved two head-module re-exports, and revised docstrings; the packet lane diff-checked zero declaration-line changes in the supporting modules and rename-plus-alias only in the endpoint. The verdict stands at the new hashes; pin count after the pass is 217 for the nine modules.]**

2026-09-17. Independent read-only proof/interface review of the nine wave-362
`GQ2/Dyadic/MarkedCore/M*` modules, with fresh default-limit elaboration of all
nine by the auditing lane. This note does not approve a release, amend the
authoritative packet, or change any freeze. It is the M twin of
`docs/dyadic/w361-n-full-stabilizer-scope.md`. The proof-level evidence is in
the companion `docs/dyadic/w363-m-full-stabilizer-independent-audit.md`.

## The mathematical M lifting assertion is now proved

In `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`,
`GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_of_frame` proves, for every
`alpha >= 2` and every handle count `h`, that every continuous automorphism
`phi` of

```text
MFrameModel h = Z/2 x Z_2^3 x Z_2^(2h)
```

preserving the transported **actual** orientation `mFrameOrientation` and the
full `MCupFrameCupIsometry` has an actual continuous automorphism
`Psi : D_M -> D_M` such that, simultaneously for **every group element** `x`,

```text
chiM alpha h (Psi x) = chiM alpha h x
mPhiHom (mStageOneLe ha) h (abMk (Psi x)) = phi (mPhiHom (mStageOneLe ha) h (abMk x)).
```

`mFullStabilizer_lift_iff` proves the converse as well, so the displayed
condition is exactly the image of the group-level stabilizer in the frame
automorphism group. No identity-handle restriction, no diagonal-matrix
restriction, no `MStabParam` classification, no finite-stage supply, no
initial-error assumption, no matrix realization and no hypothetical group lift
is an input, and neither theorem carries a single instance hypothesis. The
torsion coordinate and all `2h` handle coordinates are retained throughout.

The frame is the actual object, not an unrelated coordinate model:
`mFrameExists_phiEquiv` is a **proved** `ContinuousMulEquiv` between
`topAbelianization (DM alpha h)` and `MFrameModel h`, built from
`mPhiHom_injective` and `mPhiHom_surjective`. The commuting square above is
stated directly on `mPhiHom ... (abMk ...)`, that is on the actual
abelianization map, so no transport step is interposed between the theorem and
`D_M^ab`.

The orientation is not chosen after finding a lift. `mFrameOrientation` is
`abLiftG (chiM alpha h)` composed with the inverse of that canonical
equivalence, and `mFrameOrientation_cupFrameOfDM` evaluates it on the frame
image of an arbitrary core element to recover `chiM` itself. The cup predicate
quantifies over **all** continuous `F2` characters of the frame, its torsion
character included, and assumes no group lift and no matrix.

The M **torsion relation clause** of the packet is automatic on both sides of
the free cover, and is proved rather than omitted. On the frame, the torsion
class `t = Abar * Cbar^(2^(alpha-1))` (`mPhiHom_t`) spans the unique order-two
subgroup of the coordinate model, so every frame automorphism fixes it; this is
`nFrameModel_map_t`, which applies verbatim because `MFrameModel h` and
`NFrameModel h` are the same Lean type (the auditing lane confirmed the `rfl`).
On the free cover, the constructed lift fixes the composite word
`T = A * C^(2^(alpha-1))` literally (`mFrameLiftEquiv_head`), and literal head
fixation forces the primitive relation vector `r = e_A + 2^(alpha-1) e_C`
exactly in the original integral coordinates
(`mFrameRelVec_fixed_of_head_fixed`, `mFrameLiftEquiv_relVec`). The Lean
hypothesis set is therefore strictly smaller than the packet's, not larger.

Checked proof anchors:

- `MHeadCleanup`: the **coupled** ordinary row `2 f(A) + 2^alpha f(C)` at
  arbitrary rank and arbitrary target, and the head digit extracted from it
  with no vanishing-`C` and no orientation premise.
- `MFrameMatrixLift`: actual full-frame automorphism to an actual free pro-two
  basis fixing `T`, through `mCoordHom` Frattini surjectivity and
  `profinite_hopfian`; exact all-element frame projection; actual orientation
  preserved; and the **negative** statement that independent zero/one torsion
  sections on the `A` and `C` columns do not suffice, with an exhibited
  orientation-preserving counterexample (the torsion shear).
- `MInitialCupDepth`: `C^(2^alpha)` dies in the class-two quotient and the
  surviving head is a square, so agreement modulo `lambda_2` suffices; actual
  quotient membership of the literal relator error in `lambda_3`, not membership
  in a formal bracket span. The commutator tail is imported from
  `NInitialCupDepth` and not reproved.
- `MFrameCupCoordinates`: all-element coordinate-character pullback, the
  semantic full-frame cup isometry converted to the reduced row-cup system in
  the column-image variance `Abar G Abar^T = G`, and the converse ingredient
  through `dmObs` and uniqueness of the one-dimensional degree-two obstruction.
- `MBasisRowRefinement`, `MPlaneAmbientStage`: the closed N correction kernel
  transported to the M word by one identity in the actual quotient group
  (`evenRawStageShift_m`), the M ambient stage at every depth, and
  `mStageStep_holds`, which discharges the `MStageStep` interface at every
  `alpha >= 2` and every rank.
- `MFullFrameCompactness`, `MFullFrameStages`: torsion-sensitive stage sets
  whose marking condition is an equation between literal `abMk` columns, exact
  stages at every depth retaining the whole initial coordinate matrix, and the
  compact limit; the generator equations are lifted to the all-element square
  by `dm_hom_ext`.

This is a uniform proof at every `(alpha >= 2, h)`, not a rank or class sweep
and not a finite-target test.

## What this settles in the governing packet

The authoritative proof packet
`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex:732-735` asks,
inside `prop:marked-reduction`, for the per-standard-core statement

> Every automorphism of `D_P^ab` preserving the canonical orientation, the
> torsion relation vector, and the mod-2 cup form that occurs in the marked
> Smith-Witt classification lifts to an automorphism of `D_P`.

For `P = M` this mathematical sufficiency is now supplied, including arbitrary
handle mixing, together with an exact image characterization, and with the
relation-vector clause discharged rather than assumed. The rank-four case is
`h = 0`; no further handle decomposition is needed for larger `h`. There is no
longer a missing mathematical M stabilizer-surjectivity theorem.

However, packet lines 1077-1082 state the MC-M row of the completion table:

> MC-M | Marked automorphism lifting for the rank-four `M_alpha` core |
> A finite list of orientation-preserving Nielsen generators lifts the
> Smith-Witt stabilizer on the abelianization; composition gives every
> required marking correction.

The new proof does **not** exhibit such a finite list or a finite-word
decomposition of every final automorphism. Its initial basis uses explicit
coordinate words, but the corrected limit comes from filtered refinement and a
compactness argument. These are different assertions, exactly as on the N side.
`M.lean`'s `mNielsen_factorization` supplies a finite seven-family
factorization **of the frame action** at rank four; that is not group-level
lifting of those factors, and the scaffold note already warned against
conflating the two.

So MC-M now needs either a literal finite-family/decomposition artifact, or an
owner/editorial decision to accept this proved general lifting theorem as the
replacement proof method for the relevant section. Such acceptance need not
weaken the mathematical target. Do not describe the proof now present as a
finite Nielsen-list certificate, and do not infer from it an algorithm
producing a finite expression for its compact-limit witness.

Historical notes saying that the unrestricted M stabilizer claim remains
unproved, including remaining-requirement item 2 of
`docs/dyadic/w361-n-full-stabilizer-scope.md` ("M is separate. N's full lifting
theorem does not prove the analogous unrestricted M stabilizer claim."), refer
to the state before this wave and need a dated update, not a retroactive change
of what the earlier snapshots verified.

## Remaining campaign requirements for the next agent

1. **Integration and verification of this increment.** The nine modules were
   re-elaborated incrementally against the shared dependency cache, all clean,
   all 216 pins inside the standard three. That is not a source-only transitive
   clean build. Preserve the immutable historical snapshots, register the nine
   reviewed modules and their pins, and rerun the whole-tree and axiom gates
   before claiming a newly integrated verified endpoint. `GQ2.lean` already
   imports all nine at lines 1445-1453.
2. **The matrix-level entry point is not built.** `MCupFrameCupIsometry`
   appears only in its defining module and in the endpoint module. Nothing in
   the tree relates it to `M.lean`'s `mCupIsometry` / `IsMStabilizer`, which is
   what `mStabilizer_classification` consumes and produces. A consumer wanting
   to feed the rank-four marked Smith-Witt classification into
   `mFullStabilizer_lift_iff` must build that bridge, and it is precisely where
   `MarkedCore/Variance.lean`'s row/column dictionary re-enters. The semantic
   predicate is the safer public boundary and should not be replaced; the
   bridge should be added beside it.
3. **Two documentation repairs.** The endpoint module's docstring and the
   MASSEMBLE lane note both assert "Nothing from the N theorem is reused; only
   its shape is matched", which is false as written and contradicts the other
   eight modules' own docstrings; and two lane notes both claim route item 5 of
   the scaffold. Both are comment-only and are itemized as FLAG-1 and FLAG-2 in
   the companion audit. Also worth a later consolidation wave: the name
   `mFullStabilizer_lift` in namespace `GQ2.Dyadic.MarkedCore` is occupied by
   `MFullFrameStages`'s **conditional** composition shape, so a grep for the
   obvious name finds the wrong theorem first.
4. **Field scope is unchanged.** This is an M-core result about `DM alpha h`.
   It adds no field coverage, eliminates none of the field endpoint's inherited
   local axioms, and does not resurrect the obstructed universal frozen-M
   placement claim or establish a tame-compatible identification with that old
   candidate. The existing M marking consumers and the
   canonical-or-strict-handle alternative already sufficed for the selected
   field theorem; this theorem does not identify them with every originally
   requested pure Nielsen-family lift.
5. **Publication and release work remains untouched.** Appendix skeletons,
   staged display contract, frozen-artifact decisions, strong replay and
   accepted-checker binding are all outside this wave. Authoritative
   packet, freeze, census and release updates require owner authority.
6. **No extrapolation to `alpha = 1`.** Four named lemmas are false there, not
   merely unproved (see the companion audit's Scope section). `MStageStep alpha
   h` is *stated* at every `alpha` but has no producer below `alpha = 2`.

## Independent check evidence

Fresh default-limit elaboration of all nine modules with
`bash scripts/w361_lean_runner.sh <source>` (pinned `leanprover/lean4:v4.31.0-rc2`
against the shared dependency cache; `lake` was never invoked and nothing was
written). All nine exited zero without warnings. 216 `#print axioms` lines;
215 print exactly `[propext, Classical.choice, Quot.sound]` and the remaining
one, `mStageOneLe`, prints the smaller `[propext]`. No `sorry`, no
`native_decide`, no `set_option` of any kind in any of the nine sources.

Source SHA-256 of the three critical new boundaries:

```text
MFullStabilizerLift.lean   bac55a1a4268bdc1bac2e647a9c2c6b3c70d1dba8c3483421ea57e9ee36da783
MFrameCupCoordinates.lean  0880b52342e6a658c492121323cccb18f508ce63d7400a8f97539b571aaed525
MFrameMatrixLift.lean      7f918a6679b77fc1be00e64ebf3a1ceeda3fb8ca65ba423ec379359699c925a3
```

The two deepest external inputs were separately pinned by this lane and are
also standard three:
`GQ2.Dyadic.Instances.M0C0PivotAutomorphism.evenCupForm_comp_dm_aut` (the
converse) and `GQ2.Dyadic.StageGeneric.evenRawStageShift_m` (the kernel
interpolation). The full per-module table, the printed endpoint signatures and
the hygiene greps are in the companion audit note.
