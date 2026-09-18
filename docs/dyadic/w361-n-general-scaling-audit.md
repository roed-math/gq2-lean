# W361 independent audit — uniform strong N-plane scaling

Current-status addendum, 2026-09-17 17:02 UTC: the five proof modules reviewed
below are now integrated under their production names, with umbrella imports
and public artifact pins. Their proof content was retained; the subsequent
torsion-sensitive full core lift is separately audited in
`w361-n-full-row-independent-audit.md`. The original audit below is retained
as a historical record of the scratch-to-production review. Current final
clean-build and replay status is recorded in `w361-final-verification.md`;
integration is not a claim of release or owner acceptance.

2026-09-17, 16:13 UTC. **Mathematical scratch proof verified; not yet an
integrated-source or release certificate.** No Lean source, umbrella, frozen
artifact, owner decision, or authoritative proof packet was changed by this
audit.

## Checked conclusion and exact scope

The scratch declaration
`GQ2.Dyadic.MarkedCore.nPlaneScalingHypothesis_general` proves

```text
∀ {alpha h : Nat}, 2 ≤ alpha → NPlaneScalingHypothesis alpha h.
```

Thus for every two-adic unit `kappa`, one continuous automorphism of
`DN alpha h` preserves the canonical orientation and realizes the integral
core-plane matrix `diag(kappa,1)` **simultaneously for every continuous
ordinary Z₂-valued character**. All other frame rows are fixed as required
by `NPlaneRealizes`. There is no bound on the handle rank `h`, no finite
class list, no extra scaling premise, and no supplied stage-existence premise.
The threshold `alpha >= 2` is essential to this proof: its head coefficient
`2+2^alpha` is twice a unit and the even shift formulas have this range.

The checked corollaries are:

- `nCorePlane_gl2_lift_general`: every integral two-by-two matrix with unit
  determinant has an orientation-preserving lift in the exact
  `NPlaneRealizes` sense.
- `nStabParam_lift_general`: every admissible `NStabParam` has its named
  simultaneous ordinary-character action `P.nuAction` realized by one
  orientation-preserving automorphism. This is the existing ν-frame
  interface. The ν-invisible torsion parameters are not thereby asserted
  to have newly specified images on the full torsion abelianization.

This distinction leaves an **original-specification obligation**, not merely
an optional strengthening: the governing packet's marked-lifting statement
(`refs/dyadic-presentations-formalization-proof.tex:732`–735) and MC-N table
(1077–1082) explicitly require lifting on the full abelianization. The new
theorem closes the formal ordinary-character consumer, but does not by itself
establish that full torsion-sensitive statement. In particular `P.nuAction`
omits the `tau`, `tauSigma`, and `tauX2` components retained in `P.rows`.

## Proof audit

1. **The moving marking is an actual free basis.** Write
   `F = FreeTwoRank (coreRank h)`, `x` for its canonical generators, and
   `y_i = e(x_i)` for an actual continuous automorphism `e`. The coordinate
   family is built from the already proved explicit finite crossed maps
   on `DN`, precomposed with the canonical projection `F → DN` and `e⁻¹`.
   It consequently has literal Kronecker-delta offsets on the current
   basis. The model maps use only the presentation's universal property
   and its universal word-lift identity, not the scaling theorem being
   proved. Exact orientation equality on generators extends to all of `F`.

2. **The target is the original free relator, not one.** The tested error
   is literally `E = r(y) r(x)⁻¹` in `F`. The hypothesis is `E in lambda_k`;
   neither `r(y)=1` nor `r(x)=1` in the free group is assumed. For every
   finite coordinate crossed map, both relator evaluations are one at the
   canonical orientation. The finite identity lifts each offset by its
   natural representative to Z₂ and reduces the known integral word-lift
   identity. Hence the actual error, not a substituted stage defect,
   belongs to every required `derivKer`.

3. **The auxiliary constant-one word is legitimate and non-vacuous.**
   `oneWord` supplies the otherwise irrelevant `Tuple.relation` field.
   The old `evenDeriv_mem_rawShiftSpan_of_forall_derivKer` applies to an
   arbitrary word datum and an independently supplied central class. Its
   proof uses actual tuple generation, exact orientation lifts, the
   coordinate derivation family, and the even shift formula; it does not
   use the tuple's word or relation to identify that class. Here the class
   is independently proved to be the image of `E` in `Z_k`. Thus choosing
   `oneWord` does not claim that the actual N relator vanishes.

4. **The old general span criterion produces an actual correction.**
   `evenRawShiftSpan` is the image of the depth-correction homomorphism,
   not merely an unevaluated closure. Membership of `E⁻¹` therefore gives
   actual correction classes, which are lifted to ambient elements in
   `lambda_(k-1)`. The family's central-base-shift lemma replaces canonical
   lifts by the actual `y_i`. The literal N shift identity and centrality
   of `E` then give
   `r(y*t) r(x)⁻¹ in lambda_(k+1)`. No orientation condition is claimed
   for this first correction.

   There is no false full descent of `WL(k+1)` through `Q_(k+1)` in this
   argument. Such descent is not generally available: a `lambda_(k+1)`
   offset is only divisible by `2^k`. The proof uses `derivKer`'s actual
   representative/divisibility definition and exact error kill instead.

5. **The formerly excluded b-coordinate is removable.** The new kernel
   extension proves the actual derivative-kernel identity also for
   `v=b`. In the five-increment tuple, `[b,g][g,b]=1` and `[b,b]=1`
   eliminate the two additional increments exactly. The remaining three
   increments satisfy the existing uniform mixed-power identity, including
   repeated slots. Thus kernel witnesses exist for every coordinate `v`
   at every correction slot `i != 0`. No claim that these intermediate
   witnesses preserve orientation is needed.

6. **Full integral rows are restored at the actual current basis.**
   With current diagonal unit weights `u_v`, each kernel witness has the
   single ordinary coefficient `2^(n+1)*u_v`. The closed-kernel finite-row
   interpolation uses these actual weights, not the original unscaled
   generators. Nonhead divisibility follows from depth. At the head, the
   improved literal error and exact current/target ordinary-row equality
   supply the extra digit; exact head removal in the same filtered class
   preserves the relator stage by the checked slack identity. Interpolation
   then kills **all** ordinary coordinates, including b, without an
   orientation hypothesis on the input correction. Exact zero orientation
   of the output follows from its zero b-coordinate.

7. **The stage induction and limit are genuinely composed.** The initial
   slot-two unit-power substitution is an actual free automorphism with
   error in `lambda_3` and the desired exact diagonal. At each step,
   the unconditional ambient correction is refined as above. Corrections
   lie in `lambda_2`, so the Frattini/Hopfian basis-persistence theorem
   gives another actual free automorphism; all integral rows and the
   original orientation remain exact. The canonical free-to-DN projection
   supplies the exact quotient stages, generation, and all-character rows.
   The previously checked nested compactness theorem yields the final
   DN automorphism. No compatible choices of independent finite-stage
   witnesses and no extra image/supply hypothesis are assumed at the endpoint.

## Independent replay and trust boundary

All five sources were read in full and freshly elaborated at default limits.
Their **26 public axiom prints** contain exactly `propext`, `Classical.choice`,
and `Quot.sound`; no new or inherited arithmetic axiom enters this core result.
No placeholders, `unsafe` hooks, native decisions, or option changes occur
in these sources.

A second replay rebuilt these five modules in dependency order into
`/private/tmp/gq2-w361-ambient-independent-4zcs3k_r`, with that directory first
on the search path and **no general `/private/tmp` artifact fallback**.
Every module exited zero, warning-free, with unchanged source bytes. Existing
campaign/dependency artifacts were reused; this is not a transitive fresh
build claim.

| Scratch module | Public pins | SHA-256 |
|---|---:|---|
| `NFreeAmbientFamily` | 14 | `12552b4eac9eb0f0eb9ceb819c7609d31be8ae63ceb68429f7959157393d2be5` |
| `NPlaneKernelBExtension` | 3 | `8701889668b7523c9f2078f5dbd3a673c196f85a20f139527bf445eff60e2a7f` |
| `NPlaneFullRowRefinement` | 1 | `5b71b7300aeb2a1afb0a143ce4f5358e5b51b32184e939a5149fb1ef81a55bd7` |
| `NPlaneFullRelativeRefinement` | 1 | `a1cee06f0782866347582b446fd3664d2c81a55278f527f39eaf74c8c445eaf9` |
| `NPlaneAmbientScaling` | 7 | `8806398fdd9e93dbbbb31be14f49920e47344351e297771e9b1721ccca7a18b0` |

The prior **1,531-module / 504-pin** snapshot remains the earlier conditional
source state. The five modules above are scratch sources at this audit
checkpoint, pending root integration and a new source-bound build. This new
route proves strong scaling without proving the older, stronger
`NUnrestrictedStageSupply` separately: it first allows arbitrary ambient
corrections and restores orientation only along the exact-diagonal induction.
That distinction does not leave a premise in the new scaling theorem.

## Production-name staging comparison, 16:22 UTC

The five files staged under
`/private/tmp/gq2-w361-ambient-bank.ttfxXo/GQ2/Dyadic/MarkedCore/` were
compared against the **immutable independently replayed scratch copies**
above, not merely the subsequently polished live `/private/tmp` files.
Every mathematical declaration and proof body matches after the intended
import renaming and `NFreeAmbientAudit` → `NPlaneAmbientStage` namespace
change. The remaining differences are module documentation and whitespace.
No hypothesis, conclusion, proof step, or axiom pin was added or removed.
The production-name compilation log
`/private/tmp/gq2-w361-ambient-bank-check.log` reports all 26 standard-three
pins, without errors or warnings. These bytes are still staging, not a claim
that the repository or the old 1,531-module snapshot already contains them.

| Production module | SHA-256 of exact staged source |
|---|---|
| `NPlaneKernelAllRows` | `ce8265e9d2b3d09662d803b36db36f0a7644c16e8f318de5973241204fa9ee46` |
| `NPlaneFullRowRefinement` | `96f89d18619d1095247a8322f99dbf82144b8f89b002ca26f859a1b9ab7b58af` |
| `NPlaneFullRelativeRefinement` | `fca523c0d3ea968391167d8fd56eceeed02c0d2bdd7d676fa12ef0d0a6d531ee` |
| `NPlaneAmbientStage` | `b5217e5e2f2d6be11e6b56e817c91868378bc2976793868c19d2a4f0bf4c8b1e` |
| `NPlaneGeneralScaling` | `ddd4e79e91876b35b7785b0d2d4e2d1a3e5e68439a35fd4da99428b8d4489a0a` |

No revision of the ramified-i field scope, frozen M-word claims, marking
calibration scope, citation posture, or publication/owner-approval gates
follows merely from this additional core theorem.
