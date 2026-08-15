# Lane W81-ASK: the ASK counting pack at `G_K`

Worktree `claude/w81-ask`, based on `6f2916f3`.  Verification of record: `scripts/mirror.sh`
(sweep, gen, check).  **No `lake` command was run.**

## Headline (first pass, to be revised as the lane proceeds)

The lane opened on the premise that the two ASK bundles at `G_K` are unowned.  **Both are
already theorems at head.**  The briefing (and `docs/dyadic/w74-critical-path.md` §1.4, and
`KSupply.lean`'s own §6) are stale on this point, in the same way W79-HOUSE found them stale
on `determinant`.

| bundle | status at `6f2916f3` | supplier |
|---|---|---|
| `StokesDualityCertificate (galKProfinite K) n q P nuP (standardNumerics n) (smulZmod2GalK K)` | **PROVED**, all four clauses, hypothesis `hdeg` only | `stokesDualityCertificate_galK`, `GQ2/Dyadic/Instances/KAnalytic.lean` |
| `ExactLiftingSemanticsRN (galKProfinite K) n ...` | **PROVED** at every `n` | `exactLiftingSemanticsRN_galK`, `GQ2/Dyadic/Instances/KExactLiftingGalK.lean` |
| `ExactLiftingSemantics (galKProfinite K) n ...` (frozen) | **PROVED at `n = 1` only** | `exactLiftingSemantics_galK`, same file |

The residue is therefore not "the K-clones of the counting pack".  It is a **coefficient
mismatch between the frozen and corrected R-stage clauses at `n = 2`**, which is the degree
every live row sits at.  Section 2 below is the lane's real work.
