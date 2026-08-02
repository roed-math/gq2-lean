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

## Landed `G_K` wrapper

`GQ2/Dyadic/Instances/KAnalytic.lean` now provides the intended leaf:

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

Its proof is mathematically immediate: `localEulerChar_galK_of_finrank` rewrites
`localEulerChar_galK K` using `IntermediateField.finrank_eq_fixingSubgroup_index` and `hdeg`,
then the wrapper applies `stokesDualityCertificate_of_localDualityG` to
`FieldData.tateDualityGalK K`, `smulZmod2GalK K`, `contSMulZmod2GalK K`, and
`htriv_galK K`.

The elaboration firewall follows `GQ2/Dyadic/GaussZ/FinalDK.lean`: pin the `MuN 2` action and
continuity instances at the subtype spelling `GalK K`, bind the duality bundle and Euler
characteristic there, and invoke the generic theorem with its carrier and instance arguments
explicit.  The resulting certificate is first typed at `ProfiniteGrp.of (GalK K)`; a final
`exact` crosses the definitional equality to `galKProfinite K`.  This avoids the previous
deterministic `whnf` timeout without any heartbeat override or duplicated mathematical proof.
