# W363-PUB2 lane note: the six missing L/N exporters

**Status: staged proposal only. Nothing in this lane is owner adoption, acceptance,
census amendment, appendix migration, or release authorization.** Staged artifacts are
proposals. No frozen identifier or hash is changed, no historical verification report is
relabelled as current, and no universal frozen-M placement claim is made or revived.

Worktree `cla/worktrees/w363-pub2`, branch `claude/w363-pub2`, base `b87bfa06`.
The frozen `generated/appendix/*.tex`, `generated/hash-manifest.json`, `GQ2.lean`, every
module under `GQ2/`, and the W361/W362 check scripts are out of scope and untouched.
No `lake` invocation at any point in this lane.

## The ticket

`docs/dyadic/w362-pub-note.md` section T2.d lists six ledger items that have a Lean source
(T1.a) but no generated display, each naming an exporter that does not exist in this tree:

| Item | Named missing exporter | Lane stage |
|---|---|---|
| 2 two specializations | `W362LNSpecialization.specializationTemplate` | T3 |
| 3 evaluated Fox Jacobian | `W362LNFox.inputRowsTemplate` | T1 |
| 6 Stokes chain identity | `W362LNStokes.chainTemplate` | T1 |
| 7 extraspecial Hessian | `W362LNPhase.hessianTemplate` | T2 |
| 8 quadratic normal form | `W362LNPhase.coordinateTemplate` | T2 |
| 9 affine phase-cover | `W362LNCover.phaseCoverTemplate` | T3 |

This note is updated as each item lands. Until an item has a row in the per-item table
below saying otherwise, it is still a proposal for work not done.

## Per-item status

(to be filled as the lane proceeds)
