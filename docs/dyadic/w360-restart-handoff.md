# W360 restart handoff: general even-M source and odd-L arithmetic

Date audited: 2026-09-17 (resumption audit; supersedes the September 4 frontier claims).

This handoff supersedes the temporary `/private/tmp/W360-HANDOFF.md`, which is no longer on
disk. It records the local history through `2bf856c9` and the September 17 working-tree
proofs. The new W360 results below are saved as source, checked, and not yet committed.

## Repository state

- Branch: `dyadic`.
- Local tip: `2bf856c9` (`2026-08-21`, “close full hyperbolic ramified Stokes transport”).
- Worktree contained only this untracked handoff at the start of the resumption audit.
- The local branch was 92 commits ahead of the recorded `origin/dyadic`; the remote-tracking
  tip was `dd9339bc` from 2026-08-18.  Do not discard or reset the local history.  Confirm the
  intended remote and push policy before publishing.
- `GQ2.lean` now imports the eleven W360 modules as well as the earlier campaign modules.
  The September 4 assertion that the scoreboard had verified the old state is withdrawn:
  no authoritative probe output was retained, and the campaign's shared build directory and
  package artifacts were absent at resumption. Fresh verification is recorded below.

## What is closed

The corrected-RN record and analytic work is no longer a list of finite classes.

- N0 and Npc are closed uniformly on the selected N side once the ordinary oriented field
  equivalence is supplied; Npc has general `alpha`, level, unit, and handle analytic supply.
- The all-degree Mpc pivot ladder is closed by `MpcMk.mpcMk_pivShift`; the old M6/class-six
  item is not an open blocker.  Epsilon-true Mpc is closed uniformly, including handles.
- The frozen corrected endpoints for `sqrt(-2)`, `sqrt(2)`, `sqrt(5)`, `sqrt(10)`, and
  `sqrt(-10)` are closed.
- W303 packages the selected corrected-row problem in one all-degree dispatcher.  W320
  reduces the unchanged standard even-M presentation to a single distinguished-C placement
  boundary.
- W323 proves that boundary can genuinely fail (already for the selected M0 alpha=2,
  odd-residue case).  W341--W344 prove that changing only coordinates, the boundary, or an
  equivalent presentation cannot remove it.  The general solution therefore requires a
  genuinely new source family, not a new class-by-class calculation.
- W345--W359 construct that positive-handle source direction: pair promotion, uniform wild
  normalization, tame correction, coefficient-independent resolvers, rank-uniform Fox rows,
  normal forms, and hyperbolic pairing identities.
- `stokesDuality_headHandleHyperbolicFullFamily_ramified` is landed and uniform in the
  rank and coefficient module under its sigma/wild-triviality premises. It applies to the
  *full* Nielsen transform, where both tame and wild relators are transformed.

## W360 completed: raw hyperbolic ramified Stokes duality

The field-facing changed source must retain the canonical tame relator and use only the
changed wild relator.  That is
`EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily`, not W359's
`headHandleHyperbolicFullFamily`.  Consequently W359 is a strong regression/transport result
but does not by itself finish the corrected source.

The principal new endpoint is
`Instances.EvenMHeadHandleHyperbolicRawStokes.stokesDuality_headHandleHyperbolicRawFamily_ramified_uniform`
in `GQ2/Dyadic/Instances/EvenMHeadHandleHyperbolicRawStokes.lean`.

It is uniform in `alpha >= 2`, positive handle rank (with a chosen `j : Fin h`), the finite
acting group, and the finite elementary coefficient module. Its hypotheses are even `q`,
trivial wild action, fixed-point-free tau with trivially acting 2-primary part, and death of
the actual two raw relators.
**There is no sigma-triviality premise, normal-pairing premise, or supplied separation law.**
The finite resolver depends only on `4 * Monoid.exponent C`; the theorem discharges its
resolver obligations. The preceding general-resolver theorem is also available.

The original zero-U route was replaced by a stronger zero-V argument:

1. `EvenMHeadHandleHyperbolicGeneralFox` proves the exact ramified Fox row without sigma
   triviality, by viewing the hyperbolic word as a head shear of the pair word.
2. `EvenMHeadHandleHyperbolicRawCore`, `RawHelpers`, and `RawNormal` give the compact-core
   cancellation with arbitrary sigma offsets and the actual backward-substitution coordinates.
3. `RawPairing.heisEta1_headHandleHyperbolicRawFamily_normal_zeroV` proves the full ordinary
   core-plus-handles form when both selected V coordinates vanish. `RawDetection` proves that
   pairing any primal normal with pure dual U evaluates its selected V coordinate.
4. `StokesTranspose` supplies the opposite cross term, and `EvenHyperbolicCompletion` proves
   separation algebraically. The old normal-form engine then gives the complete raw theorem.

The new public declarations use no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
No new heartbeat override, axiom, proof placeholder, finite-degree, or nilpotency-class split
is used. The obsolete reconstructed zero-U proof remains scratch only and is not needed.

## Next general-case task: the actual normalized source

Do not equate the new raw theorem with a finished `SourceAnalyticCoreRN`. W348--W351's
normalization/tame-correction instances are for the earlier pair word. Their application to
the hyperbolic word has substantive action and structural obligations.

The additional checked theorem
`EvenMHeadHandleHyperbolicNormalize.exists_hyperbolicUnitHead_of_strictHandle` handles the
unit-head normalization cleanly. If `nu(U)=1`, `nu(V)=0`, and `nu(C)=c` is even, a lifted
handle-plane diagonal move changes U's row to `1+c`, preserves V=0 and all other rows, and
gives `nu(U C^-1)=1`. It preserves chi and C's **nu-row**, not necessarily the group element C.

At this unit head, write `b=nu(B)`, `c=nu(C)`, and `d=nu(D)`. The ensuing wild shear has
coefficients `x0:0`, `x1:b`, `x2:0`, `U_j:c`, `V_j:d`, with the other handle coefficients
equal to their original nu-values. They are not all zero. At a final wild-trivial marking,
pullback makes these raw generators act by the corresponding powers of the 2-primary sigma
action `S2`. After the hyperbolic backward substitution, the compact actions are:

| Compact letter | Action |
| --- | --- |
| sigma | `S2^c` |
| tau | `T` |
| x0 | identity |
| x1 | `S2^b` |
| x2 | `S2^d` |
| selected U | `S S2^c` |
| selected V | identity |
| other handles | `S2` to their corresponding nu-values |

Thus `stokesDuality_wildShearBackward_iff` is valid but does **not** discharge raw wild
triviality. Evenness of c is insufficient: sigma can have 2-power order greater than two on
a ramified simple module. Tame correction preserves the endpoint, but corrected-relator
death does not imply uncorrected-relator death. On normal offsets with sigma=tau=0, the
appended tau-power has zero jets and charge, a useful ingredient for a direct comparison.

The next analytic target is direct normal forms and pairing separation for the **sheared,
prime-to-two-corrected hyperbolic word**, at the final tame marking, with the displayed action
profile. Do not silently transport the raw theorem through failed action premises.

Additional remaining work: both unramified action branches; the scalar clause and affine
determinant; a genuine `SourceAnalyticCoreRN` producer and selector replacement. Positive-
level epsilon-false Mpc also needs a further structural construction: strict U has value
`2^r` and C is deeper, so `U C^-1` is not a unit for `r>0`. The existing head=1 constructor
does not cover that case. Do not try to prove the false distinguished-C condition for the
unchanged compact-M word.

## Shared field-arithmetic task

The September 4 handoff named an obsolete frontier.  W185 already proves finite odd-root
lifting and `absoluteResidueAlgAction_surjective`.  W186 already constructs the normalized
`absoluteInertiaQuotientEquivZhat`.  W303 closes the selected corrected odd-L row without a
reciprocity-law premise.  Do not rebuild these results.

The latest full odd-L endpoint is
`LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeNormReciprocity` in
`RamifiedCertificateRelativeNormReciprocity.lean` (W300).  Beyond ordinary field/tame/degree
data, its precise remaining inputs are:

1. `AbsoluteResidueBaseReciprocityLaw R`: compatibility of actual absolute residue action
   with reciprocity over Q2.  W298 transports this base law to each finite K.
2. `AbstractTameLocalReciprocityLaw T`: compatibility of the full tame unramified coordinate
   with reciprocity over K.
3. `RelativeFiniteAbelianNormReciprocity B`: the full relative Artin map, its surjectivity,
   norm-subgroup kernel, and compatibility with the supplied reciprocity map at every finite
   abelian layer.  W299--W300 derive the anchored unit-index and norm-value consequences.

No current theorem discharges these three laws from the existing bundle alone.  The unit-count
argument is complete; its remaining input is the standard finite-layer local-CFT theorem.

The exact assembler-level input `CompatibleRamifiedDataAt` is shared by all final field
identifications (`GenAsmCompatibleFieldInputs`, W322), not only the odd-L candidate.  The W300
route is the most developed standard-CFT producer for odd degree.  These field-arithmetic
inputs are independent of the changed even-M candidate construction.

## Recommended order of work

1. Start from the new checked arbitrary-sigma raw theorem; do not reconstruct zero-U or
   repeat class-by-class calculations.
2. Prove direct analytic supply for the sheared/tame-corrected source with its true action
   profile. Treat unramified branches, scalar/determinant data, and positive-level head
   structure explicitly.
3. Assemble a genuine flexible certificate/selector producer only after these inputs close.
4. In parallel only if capacity permits, attack the three remaining reciprocity laws above.
   Keep the compatible-use/custom-action instances explicit and reuse W185--W186/W298--W300.
5. Regenerate the umbrella after imports change, then run the scoreboard and dyadic gate.
   Read the current verification notes before choosing package/cache paths.

## Verification and environment recovery (September 17)

- Rebuilt the complete updated `GQ2` import closure: **1,351 modules**, successful.
  Reuse was limited to artifacts with identical source and transitive imports; all eleven
  new modules were freshly compiled and their final logs contain no warnings or errors.
- The new endpoint's six printed axiom audits are exactly the standard three. The broader
  source hygiene scan found no new `sorry`, `admit`, `native_decide`, axiom, or `set_option`.
- `scripts/check_dyadic.sh` passed, including the 11-axiom census, terminal/dyadic capstone
  audits, obligation/sign-row guards, hash check, and sanity harness. Its optional D6 axiom
  ledger was not enabled; this is a default-gate pass, not a D6 claim.
- `git diff --check` and scoreboard shell syntax check passed. No commit or push was made.
- A focused run of the **unchanged scoreboard machinery**, selecting its six new W360 rows,
  passed: every declaration is `EXISTS` with `std-3`; umbrella freshness passed; the only
  source module outside registration is the intentionally cyclic `GQ2.AxiomLedger`.
  Its transcript is `/private/tmp/gq2-w360-focused-scoreboard.log`. The historical owner-memo
  / house-note prose count still disagrees (0 versus 9); this is not a proof or build failure.
- The full scoreboard inventory subsequently completed (terminal session `31954`, exit 0),
  with all six W360 declarations `EXISTS` / `std-3`. Its log is
  `/private/tmp/gq2-w360-scoreboard.log`, generated September 17 at 02:41 local. Historical
  structure-name `MISSING` rows remain; this does not manufacture their missing producers.

The eight-hour continuation beginning September 17 at 09:10 UTC is tracked separately in
`w361-overnight-progress.md`; consult that file for the newest frontier and active ownership.

The shared build symlink is restored at
`/Users/roed/claude/cla/work/main-build-cache`. The package source checkout's own artifacts
are still missing, so verification used the byte-identical pinned package set at
`/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages`.
Its manifest matches this worktree exactly, including mathlib
`ec410d23dfa4e7540d4663405b5e0dc71f3c3363`; the toolchain remains
`leanprover/lean4:v4.31.0-rc2`. No package pin changed.

For future mirror checks, set `GQ2_PKG` to that package directory, sweep a private mirror,
then regenerate edited modules before checking dependents. The temporary recovery driver
`/private/tmp/gq2-rebuild-campaign.py` records transitive source hashes in the shared cache;
`/private/tmp/gq2-w360-lean.sh` invokes raw Lean with the standing verification flags and
the matching package path. Recovery logs are in `/private/tmp/gq2-w360-build-logs`, and the
gate transcript is `/private/tmp/gq2-w360-gate.log`. These temporary helpers are convenient,
not required project source or proof dependencies.

## Guardrails

- Keep the focus on arbitrary rank/handle count and general selected families.  Low-class
  computations are regressions only.
- Do not reopen M6: the pivot shift and sqrt(-10) endpoint are closed.
- Do not assert isolated ramified `powCharge` quadraticity; only the full diagonal has the
  necessary cancellation.
- Do not reuse the standard compact-M source for the obstructed even-M fields.  W323 and
  W341--W344 rule out that route.
- Do not infer full tame inertia from `ker nuTq`; the odd-primary unramified direction gives a
  formal counterexample.
- Preserve the local 92-commit lead until its publication status is resolved.
