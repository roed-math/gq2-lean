# Stokes local-duality implementation status

Date: 2026-08-02

## Landed in this branch

`GQ2/Dyadic/Count/LocalDuality.lean` closes the reusable mathematics:

- raw and `standardNumerics d` forms of the `TCocycle` count;
- raw and outer/inner `standardNumerics d` forms of the `VCocycle` count;
- verbatim recursion-field suppliers for `tcocycle_card`, `hsep`, `hpartial`, and `hZcard`.

`GQ2/Dyadic/Instances/KAnalytic.lean` assembles those four suppliers into
`stokesDualityCertificate_of_localDualityG`.  Thus the complete certificate is proved over the
weak interface `TateDualityG Gam 2` plus `LocalEulerChar Gam d`, with the scalar action,
continuity, and triviality passed explicitly.

## Remaining `G_K` wrapper

The intended leaf is:

```lean
theorem stokesDualityCertificate_galK
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    StokesDualityCertificate (galKProfinite K) n q P nuP
      (standardNumerics n) (smulZmod2GalK K)
```

Its proof is mathematically immediate: rewrite `localEulerChar_galK K` using
`IntermediateField.finrank_eq_fixingSubgroup_index` and `hdeg`, then apply
`stokesDualityCertificate_of_localDualityG` to `tateDualityGalK K`,
`smulZmod2GalK K`, `contSMulZmod2GalK K`, and `htriv_galK K`.

The direct declaration deterministically timed out in `whnf` at 800,000 heartbeats; pinning the
`GalK K` actions on `MuN 2` did not change that result, and 4,000,000 heartbeats also timed out.
This is the existing `galKProfinite`/`GalKsub` instance-path elaboration problem, not an open
proof field.  The wrapper is deliberately omitted rather than landed with a large heartbeat
override.  A follow-up should introduce the same small carrier/instance firewall pattern used in
`GQ2/Dyadic/GaussZ/FinalDK.lean`, then add this assembly-only theorem.
