# General Labute interface: landed seam and exact remaining DAG

Date: 2026-08-02

## What is now a checked Lean interface

`GQ2/Dyadic/LabuteInterface.lean` lands four pieces without adding a classification axiom or a
new classification-shaped hypothesis.

1. `MarkedCoreCertificateKTwoM`, `MarkedCoreCertificateKTwoN`, and
   `MarkedCoreCertificateKTwoSq` type the existing marked-core certificates directly at the
   canonical characters `chiCycKTwo` and `nuUrKTwo` on `G_K(2)`.  The corresponding
   `marked_matching_certificate_KTwo*` producers remove the noncanonical `piAb`, `hpiAb`, and
   `hpiNu` interface used by the quadratic pilot.
2. `abstractEquiv_KTwoM` and `abstractEquiv_KTwoN` apply the existing, explicitly conditional
   `MLabHypothesis` and `NLabHypothesis` definitions.  Their statements keep `IsDemushkin`,
   rank, `q = 2`, exact image equality, and (for `M`) orientation canonicity visible.
3. `BranchData.CoreCertificate` and `SelectedBranchRealization` give one type for all five rows.
   A value contains an **actual** marked-core certificate plus the compatible display selecting
   `SelectedPresentation.ofBranch`; compact and procyclic rows share the same abstract core but
   select different improved words.
4. `MarkedCoreRealization` factors the corrected equivalence, maximal-pro-2 projection,
   surjectivity, kernel, and full `Ztwo` marking calculation.  Its `ofCertificateM/N/Sq`
   adapters and `KSupply.ofMarkedCoreRealization` remove the duplicated pro-2 block from future
   branch constructors.

No declaration asserts that a realization exists for every field.  In particular, the file
does not introduce the provisional `SqLabHypothesis` proposed in the earlier plan.

## Important interface finding

The existing `MLabHypothesis` and `NLabHypothesis` are not yet sufficient to construct a
marked-core certificate, even after all their antecedents are proved.  They conclude only

```lean
Nonempty (ContinuousMulEquiv G (DM alpha h : Type))
Nonempty (ContinuousMulEquiv G (DN alpha h : Type))
```

whereas the certificate producers require a particular inverse equivalence `f : core ≃ G`
together with

```lean
forall x, chiG (f x) = chiM alpha h x
forall x, chiG (f x) = chiN alpha h x.
```

For `M`, `MLabHypothesis` takes a canonical-orientation predicate in its antecedent, but its
conclusion forgets orientation compatibility.  For `N`, the antecedent records only the image.
Thus a future general Labute theorem should produce an **oriented equivalence**, not merely prove
the existing hypotheses verbatim and then expect marked matching to follow.  Image equality
alone must not be used as a substitute for orientation canonicity.

## Exact missing mathematical signatures

The first block is the still-incomplete transfer of the field-side Demushkin data to `G_K(2)`:

```lean
theorem isDemushkin_maxProTwo_galK :
  IsDemushkin 2 (maxProPQuotient 2 (GalK K))

theorem demushkinRank_maxProTwo_galK :
  demushkinRank 2 (maxProPQuotient 2 (GalK K))
    = Module.finrank Q2 K + 2

theorem demushkinQ_maxProTwo_galK
    (ramified_i : ...) :
  demushkinQ (maxProPQuotient 2 (GalK K)) = 2
```

At the current head, degree-one inflation is an equivalence, degree-two inflation is injective,
and cup naturality is proved.  Degree-two surjectivity/cardinality on the quotient is still
needed before the first two headlines can be assembled.  The `q` theorem is separate
local-reciprocity/abelianization mathematics and cannot be inferred from the mod-2 cup form.

The family selector must supply exact closed-subgroup equalities, not only parity or an abstract
isomorphism:

```lean
inductive LabuteBranchWitness (K) : Type
  | L (h : Nat) (degree : Module.finrank Q2 K = 2 * h + 1)
      (range : range chiCycKTwo = range (chiSq h))
  | M (alpha h : Nat) (alpha_valid : 2 <= alpha)
      (degree : Module.finrank Q2 K = 2 + 2 * h)
      (range : range chiCycKTwo = imChiM alpha)
  | N (alpha h : Nat) (alpha_valid : 2 <= alpha)
      (degree : Module.finrank Q2 K = 2 + 2 * h)
      (range : range chiCycKTwo = imChiN alpha)
```

The notation above abbreviates `MonoidHom.range (chiCycKTwo ...).toMonoidHom`.  The theorem
inhabiting this witness must come from the arithmetic cyclotomic image, not from
`Branches.branchData_five_rows`, which is only case analysis on a branch already supplied.

The classification outputs should be orientation-preserving in the direction consumed by the
certificate layer.  Schematically:

```lean
theorem orientedLabuteN
    (hD : IsDemushkin 2 G) (hrank : demushkinRank 2 G = coreRank h)
    (hq : demushkinQ G = 2) (hrange : range chiG = imChiN alpha) :
  Nonempty {e : ContinuousMulEquiv (DN alpha h : Type) G //
    forall x, chiG (e x) = chiN alpha h x}

theorem orientedLabuteM
    (hD : IsDemushkin 2 G) (hrank : demushkinRank 2 G = coreRank h)
    (hq : demushkinQ G = 2) (hcanonical : IsCanonical G chiG)
    (hrange : range chiG = imChiM alpha) :
  Nonempty {e : ContinuousMulEquiv (DM alpha h : Type) G //
    forall x, chiG (e x) = chiM alpha h x}

theorem orientedLabuteSq ... :
  Nonempty {e : ContinuousMulEquiv (DSq h : Type) G //
    forall x, chiG (e x) = chiSq h x}
```

The missing abstract definition is `IsCanonical` on a general profinite group.  The repository's
`IsLabuteOrientation` is tied to the presented rank-three `DR`; consequently the odd theorem
must not be frozen until an abstract canonical-orientation characterization is chosen.  At
`h = 0`, it must agree with the proved `bLab`/`DSq 0 = DR` seam.

## Dependency DAG

```text
H1 equivalence + H2 equivalence + cup naturality
                         |
                         v
        IsDemushkin and rank on G_K(2)       local reciprocity
                         |                         |
                         |                         v
                         +-------------------- q = 2
                         |
descended chiCycKTwo ----+---- cyclotomic-image/family selector
                         |          |
                         |          +--> BranchData parameters alpha/r/epsilon/eta
                         v
        oriented Labute classification (L, M, or N)
                         |
descended nuUrKTwo ------+---- branch marked-data theorem
                         |          |
                         |          +--> NScaling / MMix / Sq correction discharge
                         v
              MarkedCoreCertificateKTwo*
                         |
             SelectedBranchRealization
             /                         \
 improved SelectedPresentation word    MarkedCoreRealization
             |                         |
 branch WordCertificate tail           KSupply.ofMarkedCoreRealization
             \                         /
              candidate_equiv_galK_of_supply
```

## Per-row consumers

| row | abstract core | classification inputs | marked-correction inputs | selected improved word |
|---|---|---|---|---|
| `L` | `DSq h` | odd oriented theorem; rank `3+2h`; `q=2` | `SqHandleMixHypothesis` + `SqCoreShearHypothesis`, or the stronger one-binder route; pivot value | `Words.LSq.lSqW` |
| `N0` | `DN alpha h` | `NLabHypothesis` today; exact `imChiN alpha` | `NScalingHypothesis`; pair-unimodularity | `Words.nCompactW` |
| `Npc` | `DN alpha h` | same as `N0` | same core correction, with procyclic marked data | corrected `Words.Npc.npcW` |
| `M0` | `DM alpha h` | `MLabHypothesis` today; canonicality and exact `imChiM alpha` | `MMixHypothesis`; compact chi-kernel/pivot theorem | `Words.MCompact.mCompactW` |
| `Mpc` | `DM alpha h` | same as `M0` | `MMixHypothesis`; procyclic pivot data | `Words.Mpc.mpcW alpha r (p epsilon r) ...` |

The selected display still has an independent arithmetic existence obligation for arbitrary
`eta`.  `SelectedEta.lean` proves that compatible displays have the correct semantics; it does
not prove that every arbitrary branch unit admits the required finite display.

Finally, reaching `SelectedBranchRealization` is not yet a presentation theorem.  The branch's
`WordCertificate` analytic tail and the arithmetic `ExactLiftingSemantics`,
`StokesDualityCertificate`, and `AffineDeterminantCertificate` inputs remain independent of
Labute classification and are consumed only at `candidate_equiv_galK_of_supply`.
