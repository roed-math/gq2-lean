# Analytic bridges follow-up plan

Date: 2026-08-02  
Scope: the analytic fields of `WordCertificate` and `KSupply`, after the completed dyadic
campaign at `ce2ccc0`.

## 1. Executive result of the audit

The repository is farther along than the handover comments in `CertificateMain.lean` and
`Instances/KSupply.lean` suggest.  The following are **landed prerequisites**, not future work:

1. `GQ2.Dyadic.LiftingDualityG.prop_5_16_gen` is the full `Γ`-generic local lifting-duality
   theorem over `D : TateDualityG Γ 2` and `hE : LocalEulerChar Γ d`.
2. `prop_5_16_galK_of` and `prop_5_16_galK` instantiate it at `G_K`.
3. The candidate-side comparison/count lane is landed in `GQ2/Dyadic/Count/`:
   `liftsOver_cardN`, `tcocycle_cardN`, `hZcardN`, `homCardN`, the scalar `H²` rung,
   `hpartialN`, and both routes to `hsep` are present.  `Variation.lean` also reduces/assembles
   `lem86` and `stageR136` from its named source-side inputs.
4. The arithmetic determinant bridge is landed:
   `GQ2.Dyadic.affineDeterminant_galK` in `Dyadic/GaussZ/FinalDK.lean` produces the exact
   `KSupply.determinant` field.
5. The scalar arithmetic field is landed as `scalarHilbert_galK`.

The next actual analytic consumer gaps are therefore:

- the four arithmetic fields of `StokesDualityCertificate` at `G_K`;
- the three arithmetic fields of `ExactLiftingSemantics` at `G_K`;
- branch-specific candidate hypotheses such as `hsimp`, the stage-separation/count inputs, and
  the candidate Hessian-to-`GaussZResidueK` bridge.  These are not generic local-duality gaps and
  should remain on their branch/candidate tracks.

The old statements that `prop_5_16` must still be generalized and that the arithmetic
determinant bridge is absent are stale and should be corrected in a documentation-only PR.

## 2. Mandatory degree correction

The `G_ℚ₂` formula

```text
#Z¹(A) = #A² * #fixedPts(C, A^∨)
```

does **not** generalize verbatim.  If `d` is the degree in the local Euler characteristic, the
correct formula is

```text
#Z¹(A) = #A^(d + 1) * #fixedPts(C, A^∨).
```

This is already enforced by `LiftingDualityG.card_Z1_eqG`.  The file also proves the scalar
countercheck `card_Z1_zmod2G_eq_eight_iff`: the old value `8` occurs if and only if `d = 1`.
Every follow-up theorem must use `standardNumerics d` or explicit numeric pins, never copy a
`^ 2` from the `G_ℚ₂` files.

The three relevant standard values are:

```text
(standardNumerics d).mMult M  = M^(d + 1)
(standardNumerics d).tMult T  = T^(d + 1)
(standardNumerics d).h1Mult V = V^d
```

## 3. First landed refactor in this track

`TateDualityG` exposes `perfect02`, `perfect11`, and `perfect20`, but its three cardinality
consequences were previously available only through the `AbsGalQ2` abbreviation
`TateDuality`.  This track adds the genuinely group-generic API:

```lean
theorem TateDualityG.card_H0_dual
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {n : ℕ} [NeZero n] [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
    (D : TateDualityG G n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (htor : ∀ x : M, n • x = 0) :
    Nat.card (H0 G (MuDual n M)) = Nat.card (H2 G M →+ ZMod n)

theorem TateDualityG.card_H1_dual ... :
    Nat.card (H1 G (MuDual n M)) = Nat.card (H1 G M →+ ZMod n)

theorem TateDualityG.card_H2_dual ... :
    Nat.card (H2 G (MuDual n M)) = Nat.card ((H0 G M) →+ ZMod n)
```

The old `TateDuality.card_H*_dual` declarations remain as compatibility wrappers.  The generic
local-duality proof now consumes the new declarations instead of reopening the three bundle
fields.  All three new declarations print exactly the standard three axioms.

## 4. Exact target interfaces

The signatures below are the intended public endpoints.  The proofs may introduce smaller
private helpers, but should not weaken these statements or expose implementation-specific
instances to callers.

### 4.1 Generic local cocycle counts

Place in `GQ2/Dyadic/Count/LocalDuality.lean`.  These helpers should be generic in a profinite
source and should reuse `Count.tcocycleEquivZ1`, `Count.vcocycleEquivZ1`,
`LiftingDualityG.card_Z1_eqG`, and the existing fixed-point lemmas.

```lean
theorem tcocycle_card_of_localDualityG
    {Gam : ProfiniteGrp} {d : ℕ}
    (DΓ : TateDualityG (Gam : Type) 2)
    (hE : LiftingDualityG.LocalEulerChar (Gam : Type) d)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg)
    (rho : ContinuousMonoidHom (Gam : Type) (Bg ⧸ D.M))
    (hcomp : ∀ γ a, γ • a = rho γ • a) :
    Nat.card (TCocycle D rho) =
      Nat.card (Additive ↥D.T) ^ (d + 1) *
        Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T)))

theorem vcocycle_card_of_localDualityG
    {Gam : ProfiniteGrp} {d : ℕ}
    (DΓ : TateDualityG (Gam : Type) 2)
    (hE : LiftingDualityG.LocalEulerChar (Gam : Type) d)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    {E : Type} [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    (theta : ContinuousMonoidHom (Gam : Type) E)
    (hround : ∀ γ v, rho0 DD rho γ • v = theta γ • v)
    (hact : ∀ γ v, γ • v = theta γ • v)
    (hsimple : IsSimpleModTwo E DD.Vmod)
    (hnt : ∃ g v, g • v ≠ v) :
    Nat.card (VCocycle DD rho) = Nat.card DD.Vmod ^ (d + 1)
```

The actual Lean binder list must include the same topology/action instances as the existing
equivalences.  The conclusions above are fixed.  A second pair of wrappers should state the
same results directly in `SourceNumerics` form:

```lean
... = (standardNumerics d).tMult ... * Nat.card (fixedPts ...)
... = Nat.card DD.Vmod * (standardNumerics d).h1Mult (Nat.card DD.Vmod)
```

### 4.2 Generic arithmetic Stokes constructor

After the count helpers, assemble all four record fields in the same file.  This is the principal
next consumer target:

```lean
theorem stokesDualityCertificate_of_localDualityG
    {Gam : ProfiniteGrp} {d q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    (DΓ : TateDualityG (Gam : Type) 2)
    (hE : LiftingDualityG.LocalEulerChar (Gam : Type) d)
    (smulZ2 : DistribMulAction (Gam : Type) (ZMod 2))
    (htriv : letI := smulZ2; ∀ γ m, γ • m = m) :
    StokesDualityCertificate Gam d q P nuP (standardNumerics d) smulZ2
```

The four fields should be supplied as follows:

- `tcocycle_card`: `tcocycle_card_of_localDualityG`;
- `hsep`: `Count.hsep_field_goal` with
  `Count.isTwoSeparating_of_tateDualityG`;
- `hpartial`: `Count.hpartial_field_goal` with
  `Count.isRightSeparating_of_tateDualityG` and `card_H2_zmod2_eq_twoG`;
- `hZcard`: `vcocycle_card_of_localDualityG`.

No `StokesDuality` word payload, `IsStokesEndpoint`, presentation, resolver, or `hsimp` belongs
in this arithmetic theorem.  Those inputs are candidate-side only.

### 4.3 `G_K` Stokes endpoint

Place the field-level wrapper in `GQ2/Dyadic/Instances/KAnalytic.lean`:

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

Use the supplied or canonical field bundle consistently:

- in a `DyadicLocalInput` consumer, prefer its `duality` field and expose an `_of` theorem;
- the convenience theorem may use `LiftingDualityG.tateDualityGalK K`;
- rewrite the Euler degree exactly once with `hdeg`.

The `GalKsub`/`galKProfinite` instance-path firewall used by `FinalDK.lean` should be copied as a
pattern, not rediscovered through repeated `change`/`simpa` calls.

### 4.4 Generic/K-side lifting count

The first clause of `ExactLiftingSemantics` should be separated from its other two clauses.
Place the generic work in `GQ2/Dyadic/Count/LocalLifts.lean`:

```lean
theorem liftsOver_card_of_localDualityG
    {Gam : ProfiniteGrp} {d q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo}
    (DΓ : TateDualityG (Gam : Type) 2)
    (hE : LiftingDualityG.LocalEulerChar (Gam : Type) d) :
    ∀ {H E Y} ... {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY}
      (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E)
      (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics d).mMult (Nat.card ↥RF.MB)
```

Recommended proof route:

1. reuse `Count.card_liftsOverK_eq_card_Z1` for the torsor cardinality;
2. prove nonemptiness from `#H²(Gam, M_B) = 1` using
   `card_H2_eq_fixedPtsG` and the existing `card_fixedPts_MB_dual` group-theoretic lemma;
3. use `card_Z1_eqG` and the same fixed-point lemma for the count.

Do not make this theorem depend on a word presentation or a Fox certificate.  The candidate
lane already showed those are unnecessary for the abstract count.

The `G_K` wrapper should be:

```lean
theorem liftsOver_card_galK ...
    (hdeg : Module.finrank ℚ_[2] K = n) :
    ∀ RF b F rho,
      Nat.card (LiftsOverK RF b F rho) =
        (standardNumerics n).mMult (Nat.card ↥RF.MB)
```

### 4.5 Half-torsor clause (`lem86`)

`KSupply.lem86_galK` is only a reduction: it still takes a chosen complement, cocycle, and a
nonzero variation class.  The public target must match the record field and eliminate those
choices:

```lean
theorem lem86_galK_closed
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) ...
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (rho : ContinuousMonoidHom (GalK K) (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) :
    2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho)
```

This is the high-risk part of the exact-lifting package.  Audit and generalize
`RadicalEdgeLocal.half_torsor_local`; do not turn the nonzero-variation statement into an axiom.
If useful, expose the intermediate reusable theorem:

```lean
theorem exists_nonzero_variation_of_noDescentG
    (DΓ : TateDualityG Γ 2) ... (hedge : D.NoDescent) (hrho : Surjective rho) :
    ∃ S u, H2mk Γ (ZMod 2) ⟨varCoc ..., ...⟩ ≠ 0
```

### 4.6 Stage-(136) clause

The target is the third conjunct of `ExactLiftingSemantics`, without source-specific binders:

```lean
theorem stageR136_galK
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) ... :
    ∀ {H E Y} ... {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY}
      (hE2 : ∀ e : E, e ^ 2 = 1)
      (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
      (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
      (b : ContinuousMonoidHom (GalK K) ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E),
      (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T =
        (blockFrameImpl T Blk hE2).zR * ∑ᶠ l, ...
```

Reuse `Dyadic/Recursion/RStage.lean` and `BlockRStage.lean`.  The two arithmetic inputs should
come from the same local-duality machinery as the Stokes constructor:

- the required separation from `isTwoSeparating_of_tateDualityG`/the existing field-goal API;
- the `R`-cocycle count from the degree-correct Euler formula.

### 4.7 Final exact-lifting constructor

Only after §§4.4–4.6 are individually checked should they be bundled:

```lean
theorem exactLiftingSemantics_galK
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) ...
    {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n) :
    ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n)
```

This theorem should be assembly only: `⟨liftsOver_card_galK, lem86_galK_closed,
stageR136_galK⟩`.

## 5. Dependency DAG

```text
TateDualityG + LocalEulerChar
  ├── [LANDED] prop_5_16_gen / prop_5_16_galK_of
  │     ├── card_Z1_eqG (#A^(d+1), not #A^2)
  │     ├── card_H2_eq_fixedPtsG
  │     ├── cup11 right separation
  │     └── cup20/two separation
  ├── [THIS PR] TateDualityG.card_H{0,1,2}_dual
  ├── generic TCocycle/VCocycle counts
  │     └── StokesDualityCertificate at G_K
  └── generic lifting count
        ├── nonempty lift fibre
        └── liftsOver_card at G_K

TateDualityG + no-descent + topological finite generation
  └── nonzero variation
        └── lem86 at G_K

TateDualityG + scalar H2 + R-separation/R-count
  └── stageR136 at G_K

liftsOver_card + lem86 + stageR136
  └── ExactLiftingSemantics at G_K

[LANDED] affineDeterminant_galK
[LANDED] scalarHilbert_galK
StokesDualityCertificate + ExactLiftingSemantics + determinant + scalar
  └── KSupply with no analytic binders
```

Candidate-side branch certificates are parallel consumers, not dependencies of the arithmetic
lane.  Their remaining `hsimp`, stage, and determinant inputs should not be pulled into the
generic `G_K` theorems.

## 6. Ordered small PR sequence

1. **AB-0: truth-sync documentation.**  Correct the stale obligation inventories in
   `CertificateMain.lean` and `KSupply.lean`: mark `prop_5_16_gen`, the candidate count lane, and
   `affineDeterminant_galK` landed.  No code changes.
2. **AB-1: bundle cardinality API.**  The `TateDualityG.card_H*_dual` refactor implemented in
   this branch.  Small, std-3, no downstream statement changes.
3. **AB-2: local cocycle counts.**  Add `Count/LocalDuality.lean` with the generic
   `TCocycle`/`VCocycle` cardinalities and exact `standardNumerics` wrappers.
4. **AB-3: arithmetic Stokes constructor.**  Assemble
   `stokesDualityCertificate_of_localDualityG`, then the `G_K` wrapper.  Add a verbatim record
   field-shape `example`.
5. **AB-4: local lift fibre.**  Prove nonemptiness and `liftsOver_card_of_localDualityG` only.
   Do not bundle `ExactLiftingSemantics` yet.
6. **AB-5: half-torsor.**  Generalize the nonzero-variation/half-torsor proof and close
   `lem86_galK_closed`.  This deserves its own review because it is the main mathematical risk.
7. **AB-6: stage (136).**  Generalize the arithmetic `hsep_hom`/`hZcount` suppliers and close
   `stageR136_galK`.
8. **AB-7: exact-lifting assembly.**  Add `exactLiftingSemantics_galK` as a three-line bundle
   constructor and a verbatim field-shape test.
9. **AB-8: `KSupply` cleanup.**  Add a constructor that fills `scalar`, `stokes`, `exactLifting`,
   and `determinant` from `hdeg`, `params`, and `ramifiedData`; remove analytic binders from the
   per-field `KSupply` producers without changing the final theorem statements.

Do not combine AB-3, AB-5, and AB-6 into one large port.  They have different failure modes and
different trust footprints.

## 7. Candidate-side reuse and non-reuse

The candidate lane should continue to use the existing word/presentation APIs:

- `Count.liftsOver_cardN`, not the arithmetic `H²` proof;
- `Count.tcocycle_cardN`/`hZcardN`, not `prop_5_16_gen`;
- `Count.hsep_field_goal_marking` and `isRightSeparating_of_selfDualN`;
- `Count.cardH2_field_goal_closed`, `lem86_of_variation`, and
  `stageR136_of_variation`.

The arithmetic and candidate sides reuse the same recursion field types and the same low-level
`TCocycle ≃ Z¹`/`VCocycle ≃ Z¹` bridges, but their proof inputs intentionally fork:

| Field | Candidate source | Arithmetic source |
|---|---|---|
| cocycle counts | marked presentation + `StokesDuality` | Tate duality + Euler |
| `hpartial` | word `IsSelfDualN` | Tate `(1,1)` separation |
| `hsep` | marking route | Tate `(2,0)` separation |
| scalar `H²` | word obstruction rung | Tate invariant map |
| determinant | branch Hessian/phase bridge (open) | `affineDeterminant_galK` (landed) |

Trying to force one proof route on both sides would reintroduce either a circular presentation
assumption at `G_K` or an unavailable continuous module-`H²` comparison at `Γ_R`.

## 8. File placement and import discipline

- `GQ2/TateDuality.lean`: only bundle-parametric consequences; must remain independent of the
  dyadic tree.
- `GQ2/Dyadic/LiftingDualityG.lean`: generic local duality and `G_K` instantiation; no recursion
  record constructors.
- `GQ2/Dyadic/Count/LocalDuality.lean`: generic arithmetic count/separation assembly.  Plain
  import, beside the existing generic count bridges.
- `GQ2/Dyadic/Count/LocalLifts.lean`: generic lift-fibre count.
- `GQ2/Dyadic/Instances/KAnalytic.lean`: `G_K` wrappers and exact record-field smoke tests.
- `GQ2/Dyadic/Instances/KSupply.lean`: package assembly only after the lower APIs land.

Before adding a file, check for import cycles against `CertificateMain.lean`.  If the record
definition cannot be imported from a low-level generic file without a cycle, keep the low-level
lemmas record-free and place only the final constructor in `Instances/KAnalytic.lean`.

## 9. Verification matrix

Every PR should run:

1. targeted elaboration of each changed file with `lake env lean`;
2. `lake build` of the changed public modules and their immediate record consumer;
3. `#print axioms` for every new headline;
4. `rg -n 'sorry|native_decide|axiom ' <changed files>`;
5. a verbatim `ExactLiftingSemantics`, `StokesDualityCertificate`, or `KSupply` field-shape
   `example` where applicable;
6. `bash scripts/check_dyadic.sh` before merge.

Regression tests specific to this lane:

- `prop_5_16_of_gen` still has the exact old `G_ℚ₂` conclusion;
- `card_Z1_zmod2G_eq_eight_iff` remains available, guarding the degree correction;
- all arithmetic numeric results rewrite to `standardNumerics n` without ad hoc exponent pins;
- both `GalKsub K` and `galKProfinite K` smoke tests elaborate, guarding the instance-path trap;
- no new headline mentions B5-K or B10-K unless it explicitly invokes their producers.

## 10. Trust-boundary impact

The generic layers (`TateDualityG.card_H*_dual`, generic count bridges, and generic record
constructors parameterized by `DΓ` and `hE`) should print exactly the standard three axioms:
`propext`, `Classical.choice`, and `Quot.sound`.

At `G_K`:

- B6 enters through `tateDualityAt`/`tateDualityGalK`;
- B7 enters through the Shapiro-derived `localEulerCharacteristic_open`;
- B1 enters only where topological finite generation is genuinely used (`lem86`/stage work);
- B9 and B11a enter through the already-landed determinant theorem;
- no new axiom is permitted;
- B5-K and B10-K should remain absent from the generic analytic headlines.  They may enter only
  through explicit field-data/bundle producers at final instantiation.

Thus this plan reduces hypotheses; it does not enlarge the eleven-axiom census or change the
meaning of the existing final theorems.

## 11. Main risks and stopping rules

1. **Half-torsor/nonzero variation — high risk.**  If the `G_ℚ₂` proof uses an arithmetic fact
   not encoded by `TateDualityG` plus Euler/topological finite generation, stop and name the
   missing theorem.  Do not add it as an axiom or silently strengthen the bundle.
2. **Degree mistakes — high impact.**  Any appearance of `^ 2` in a `G_K` count must be justified
   as a degree-independent group-theoretic square, not copied from local Euler at `ℚ₂`.
3. **Instance-path mismatch — medium risk.**  Prefer a single `GalKsub`-typed proof followed by
   one boundary-map firewall, following `FinalDK.lean`.
4. **Import cycles — medium risk.**  Keep generic mathematics record-free when necessary; put
   record assembly at the leaf.
5. **Candidate determinant — separate high-risk track.**  It is not solved by any theorem in
   this plan.  Do not report a complete `WordCertificate` merely because the arithmetic
   determinant field is closed.

