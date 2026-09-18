# W364-NFACTOR: the N frame-stabilizer factorization into the six Nielsen families

Lane note. Branch `claude/w364-nfactor`, base `3d64cd99`.

## Scope

The missing half of the MC-N finite-list artifact: the six N Nielsen families
(N1..N6 of `docs/dyadic/mc-design.md` section 3.4) as frame actions, the
factorization of every admissible `NStabParam` through a fixed finite slot list,
and the N twin of `mNielsenGen_finite_list`.

Modules (new, never editing existing ones):

- `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean` (prefix `nNielsenFac`).

## Status

Started. Nothing proved yet.
