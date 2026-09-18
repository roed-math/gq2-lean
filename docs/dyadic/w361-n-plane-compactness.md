# W361 — the exact-row N limit is checked

Historical checkpoint: 2026-09-17. This module gives the general-rank exact-row
compactness reduction, not by itself a construction of its stage inputs.
Those inputs have subsequently been constructed by the integrated ambient
free-basis argument in `NPlaneAmbientStage.lean`; `NPlaneGeneralScaling.lean`
now closes strong N-plane scaling for every `alpha >= 2` and every handle rank.
The conditional compactness theorem described below remains the checked limit
step. See `w361-n-general-scaling-audit.md` and `w361-final-verification.md` for
the later argument and current verification status.

`GQ2/Dyadic/MarkedCore/NPlaneCompactness.lean` proves

```
NPlaneScalingHypothesis alpha h
  ↔ ∀ kappa : Z2ˣ, ∀ k,
      (nPlaneStageSet alpha h (nPlaneDet kappa) k).Nonempty.
```

The right side quantifies over actual tuples in `DN alpha h`, not tuples
only in finite quotients. Each tuple must satisfy all of the following:

1. Its orientation values equal the original generator values exactly.
2. For every continuous ordinary Z2 character simultaneously, its entire
   frame is the prescribed `nCoreMat` frame. These are integral equalities,
   not congruences and not a correction chosen separately for each character.
3. No index-two open normal subgroup contains all tuple entries. This is
   the Frattini-generation requirement, including the torsion head which
   ordinary Z2 characters alone cannot detect.
4. The N relator evaluated at the tuple lies in the depth-k two-central term.

Only the last condition depends on k. The solution sets are closed and
nested in the compact finite product of copies of DN. Their intersection
is therefore nonempty if each is nonempty, without any compatible-choice
or Cauchy-sequence premise. Separation of the two-central filtration turns
the limiting relator condition into an exact identity. The presentation
universal property gives a continuous endomorphism; the index-two tests
make it surjective, and the existing finitely generated profinite Hopfian
theorem makes it an automorphism. Generator-wise orientation equality
extends to the whole group by the presentation's hom-extensionality theorem.

Conversely, any actual `NPlaneRealizes` automorphism supplies a point in
every set. Hence the reduction is an iff, for an arbitrary plane matrix,
with no extra invertibility premise. The matrix-specific stage premise
already entails any restrictions needed for existence.

## Audit and scope

All twelve public pins compile at the default limits, warning-free, using
only `propext`, `Classical.choice`, and `Quot.sound`. The independent
read-through checked closedness of the uncountable family of ordinary-row
conditions, finite-slot closedness of the Frattini-generation condition,
nestedness, separation, and the surjectivity/Hopfian promotion. The local
compile log is `/private/tmp/gq2-w361-nplane-compactness.log`.

The hard remaining input is **uniform nonemptiness** of these exact-row
upstairs sets. A finite-quotient calculation with rows only correct modulo
2^k does not supply it. The new free-pro-two coordinate-removal theorem and
mixed-Lie kernel vector target that gap; their concrete filtered derivative
and unrestricted correction-image adapters still need proof. If proceeding
through free-group tuples, one must also transfer them to DN using character
pullback and continuous functoriality of the filtration.

This closes the conditional limit and DN automorphism-promotion step. It
does not prove a literal free-group relator-preserving automorphism, properness
of a proposed pro-two HNN splitting, or `NPlaneScalingHypothesis` itself.
It is not a new premise of the already completed general presentation endpoint.
