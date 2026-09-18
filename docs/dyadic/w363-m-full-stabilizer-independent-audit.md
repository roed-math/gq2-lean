# W363: independent audit of the full M stabilizer lift

Date: 2026-09-17. Audit lane: `w363-maudit`. No proof, umbrella, or script
changes are made by this lane; comment-only findings are FLAGGED here for the
orchestrator.

**VERDICT: proved as stated, with two documentation caveats (FLAG-1, FLAG-2)
and one interface observation (FLAG-3). No mathematical caveat. No hidden
premise. No `sorry`, no `native_decide`, no `set_option`, all 216 pins inside
the standard three.**

## Verdict and exact scope

`GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_iff`, in
`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`, proves the following for
every `alpha >= 2` and every handle count `h`. The full binder list is the one
the elaborator prints, quoted here from this lane's own probe run, so that
nothing is hidden in a `variable` block or an instance argument:

```text
@mFullStabilizer_lift_iff : forall {alpha h : ℕ} (ha : 2 ≤ alpha) (phi : MFrameModel h ≃ₜ* MFrameModel h),
  (∃ Psi,
      (∀ (x : ↑(DM alpha h).toProfinite.toTop), (chiM alpha h) (Psi x) = (chiM alpha h) x) ∧
        ∀ (x : ↑(DM alpha h).toProfinite.toTop),
          (mPhiHom ⋯ h) (abMk (Psi x)) = phi ((mPhiHom ⋯ h) (abMk x))) ↔
    (∀ (z : MFrameModel h), (mFrameOrientation ha h) (phi z) = (mFrameOrientation ha h) z) ∧
      MCupFrameCupIsometry ha phi
```

In source form, the two landed theorems are

```lean
theorem mFullStabilizer_lift_of_frame {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))
```

```lean
theorem mFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))) ↔
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi
```

The frame is the full topological abelianization model, `ZMod 2` torsion
coordinate and all `3 + 2h` integral coordinates included. There is no
identity-handle, plane-block, diagonal-matrix, initial-basis, initial-depth,
derivative-image, matrix-realization or stage-supply premise in either
direction, and no instance hypothesis. The torsion relation vector is
*preserved automatically*, not assumed, and this is proved twice over (below).

This closes the **general, torsion-sensitive M stabilizer lifting existence
statement**, including arbitrary allowed handle mixing, and gives its exact
image characterization. It is not an assertion that every integral matrix
lifts, and it is not a finite Nielsen-generator presentation of the stabilizer;
see **Explicit nonclaims**.

## Critical proof checks

### 1. Is `MFrameModel h` the actual topological abelianization, torsion included?

Yes. `GQ2/Dyadic/MarkedCore/MFrame.lean:87`:

```lean
abbrev MFrameModel (h : ℕ) : Type :=
  Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]))
```

and `GQ2/Dyadic/MarkedCore/MFrameExists.lean:739` proves the identification
rather than assuming it:

```lean
noncomputable def mFrameExists_phiEquiv {α : ℕ} (hα : 1 ≤ α) (h : ℕ) :
    ContinuousMulEquiv (topAbelianization (DM α h : Type)) (MFrameModel h) :=
  continuousMulEquivOfBijective ⟨mPhiHom hα h, continuous_mPhiHom hα h⟩
    ⟨mPhiHom_injective hα h, mPhiHom_surjective hα h⟩
```

Crucially the endpoint theorem does not state its square on a transported
model: it states it on `mPhiHom (mStageOneLe ha) h (abMk _)` directly, that is
on the actual abelianization map of `DM alpha h`. The first coordinate is the
`alpha`-dependent torsion class `t = Abar * Cbar^(2^(alpha-1))`, by
`MFrameExists.mPhiHom_t`:

```lean
theorem mPhiHom_t : mPhiHom hα h (abMk (dmA α h * dmC α h ^ (2 ^ (α - 1))))
```
with value `ofAdd (1, 0, 0, 0, 0)` (`MFrame.lean`'s `MFrame.map_t` field
records the same datum). It is emphatically not the class of `Abar`; the M
frame differs from the N frame exactly here, and `MFullFrameStages` re-checks
it for the free-cover word:

```lean
theorem mPhiHom_mStageTorsionWord {alpha : ℕ} (ha : 1 ≤ alpha) (h : ℕ) :
    mPhiHom ha h (abMk (mStageTorsionWord alpha (dmGen alpha h))) =
      ofAdd (1, 0, 0, 0, 0) := mPhiHom_t ha h
```

The retention lemmas do retain the torsion slot, and they say so as an equation
between literal `abMk` columns rather than between selected markings
(`MFullFrameCompactness.lean:158, :168`):

```lean
theorem mStageFullFrameStageSet_abMk_eq ... : abMk (m i) = abMk (m' i) :=
  mPhiHom_injective ha h ((hm.2.1 i).trans (hm'.2.1 i).symm)

theorem mStageFullFrameRealizes_abMk_eq ... :
    abMk (Psi (dmGen alpha h i)) = abMk (Psi' (dmGen alpha h i)) :=
  mPhiHom_injective ha h ((hPsi.2 i).trans (hPsi'.2 i).symm)
```

The stage-set membership condition is itself `∀ i, mPhiHom ha h (abMk (m i)) =
mark i` on the full frame, so nothing in the compactness argument drops to a
torsion-free quotient or to an unramified marking.

### 2. Is `mFrameOrientation` the transported original `chiM`?

Yes, and it is transported, not re-chosen. `MFrameMatrixLift.lean:153`:

```lean
def mFrameOrientation {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    ContinuousMonoidHom (MFrameModel h) ℤ_[2]ˣ :=
  (abLiftG (chiM α h)).comp
    ⟨(mFrameExists_phiEquiv (mStageOneLe hα) h).symm.toMulEquiv.toMonoidHom,
      (mFrameExists_phiEquiv (mStageOneLe hα) h).symm.continuous_toFun⟩
```

That is literally `chiM` pulled back along the inverse of the proved canonical
frame equivalence. The audit's decisive check that no orientation is chosen
after the lift is the necessity bridge
(`MFullStabilizerLift.lean`), which evaluates it on the frame image of an
arbitrary core element and recovers `chiM` on the nose:

```lean
theorem mFrameOrientation_cupFrameOfDM {alpha h : ℕ} (ha : 2 ≤ alpha)
    (x : DM alpha h) :
    mFrameOrientation ha h (mCupFrameOfDM ha h x) = chiM alpha h x
```

The M orientation is genuinely not the N one, and the file proves the
difference rather than assuming it (`MFrameMatrixLift.lean:188`):

```lean
theorem mFrameOrientation_preserved_iff ... :
    (∀ z, mFrameOrientation hα h (φ z) = mFrameOrientation hα h z) ↔
      ∀ z, mParityZ (φ z).toAdd.2.1 = mParityZ z.toAdd.2.1 ∧
        (φ z).toAdd.2.2.2.1 = z.toAdd.2.2.2.1
```

so orientation preservation fixes the **parity** of the integral `B` slot and
the integral `D` slot. It does not fix the integral `B` row, as the N
orientation does. The scaffold plan warned against inventing the stronger row
condition; the landed statement does not.

### 3. Is `MCupFrameCupIsometry` intrinsic?

Yes. `MFrameCupCoordinates.lean:74`:

```lean
def MCupFrameCupIsometry {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) : Prop :=
  ∀ c d : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (phi (mCupFrameCanonicalMark ha h i))))
        (fun i => toAdd (d (phi (mCupFrameCanonicalMark ha h i)))) =
      evenCupForm (fun i => toAdd (c (mCupFrameCanonicalMark ha h i)))
        (fun i => toAdd (d (mCupFrameCanonicalMark ha h i)))
```

The quantifier ranges over **every** continuous `F2` character of the actual
full frame, with no marking, matrix or group-lift datum. The torsion character
is one of them: `mCupFrameModTwoCoordinate ha h i` is constructed for every
`i`, index `0` included, and the obligation it has to discharge is the M one,
not the N one:

```lean
private theorem mCupFrameCoordinate_head_relation {alpha h : ℕ} (ha : 2 ≤ alpha)
    (i : Fin (coreRank h)) :
    (ofAdd (if (0 : Fin (coreRank h)) = i then (1 : ZMod 2) else 0)) ^ 2 *
      (ofAdd (if (2 : Fin (coreRank h)) = i then (1 : ZMod 2) else 0)) ^ (2 ^ alpha)
        = 1
```

so all `4 + 2h` mod-two coordinates really are characters, the `C` index `i = 2`
included. The pullback to the free cover is exact on **every** element, not
only on generators (`mCupFrameModTwoCoordinate_projection`):

```lean
    toAdd (mCupFrameModTwoCoordinate ha h i (mCupFreeFrameProjection ha h x)) =
      nRed (toAdd (freeTwoCoordinate (coreRank h) i x))
```

### 4. Is the torsion relation vector preserved automatically or assumed?

Automatically, and the audit finds it proved twice, on both sides of the cover.

**On the frame.** `MFrameModel h` and `NFrameModel h` are the *same Lean type*:
this lane confirmed it by elaborating `example (h : ℕ) : MFrameModel h =
NFrameModel h := rfl`, which typechecks. `N.lean:1064` is therefore applicable
verbatim, and it is a statement about the abstract coordinate group:

```text
@nFrameModel_map_t : ∀ {h : ℕ} (φ : NFrameModel h ≃* NFrameModel h),
  φ (Multiplicative.ofAdd (1, 0, 0, 0, 0)) = Multiplicative.ofAdd (1, 0, 0, 0, 0)
```

Since `ℤ_[2]` is torsion free, `ofAdd (1,0,0,0,0)` is the unique element of
order two, so every frame automorphism fixes it. This is a sound reuse: the
lemma quantifies over `MulEquiv`s of the coordinate model and knows nothing
about which class of `D^ab` sits in the slot. It is applied at
`MFrameMatrixLift.lean:594` and `:740`.

**On the free cover.** The constructed lift fixes the head literally, and
literal head fixation forces the relation vector exactly, in the *original*
integral coordinates:

```lean
def mFrameHead (α h : ℕ) : FreeTwoRank (coreRank h) :=
  freeTwoRankGen (coreRank h) 0 * freeTwoRankGen (coreRank h) 2 ^ (2 ^ (α - 1))

def mFrameRelVec (α : ℕ) {h : ℕ} (j : Fin (coreRank h)) : ℤ_[2] :=
  if j = 0 then 1 else if j = 2 then (2 : ℤ_[2]) ^ (α - 1) else 0

theorem mFrameRelVec_fixed_of_head_fixed (α h : ℕ) (e : ...)
    (he : e (mFrameHead α h) = mFrameHead α h) (j : Fin (coreRank h)) :
    ∑ i, toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) i))) *
      mFrameRelVec α i = mFrameRelVec α j

theorem mFrameLiftEquiv_head : mFrameLiftEquiv hα h φ (mFrameHead α h) = mFrameHead α h
theorem mFrameLiftEquiv_relVec (j : Fin (coreRank h)) :
    ∑ i, toAdd (freeTwoCoordinate (coreRank h) j
      (mFrameLiftEquiv hα h φ (freeTwoRankGen (coreRank h) i))) * mFrameRelVec α i =
      mFrameRelVec α j
```

Neither appears as a hypothesis of the endpoint. The packet's relation-vector
clause is therefore discharged, not omitted, and the Lean hypothesis set is
strictly *smaller* than the packet's: orientation plus cup, with the relation
vector free.

### 5. Is the conclusion the full abelianization square on every element, and is
the converse the image characterization?

Yes to both. The square is `∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
phi (mPhiHom (mStageOneLe ha) h (abMk x))`, quantified over all `x : DM alpha
h`. In `MFullFrameStages.mFullStabilizer_lift` the generator equations are
upgraded by hom-extensionality for continuous homomorphisms
(`Cores.lean:934`):

```lean
theorem dm_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    {α h : ℕ} (φ ψ : ContinuousMonoidHom (DM α h : Type) A)
    (hgen : ∀ i, φ (dmGen α h i) = ψ (dmGen α h i)) : φ = ψ
```

and the `chiM` clause is `∀ x` from `MStageFullFrameRealizes`'s first
component, never only on generators. `Psi` is a `ContinuousMulEquiv`, that is
an actual continuous automorphism, not merely an endomorphism.

The converse is genuine. Its orientation half rewrites an arbitrary frame
element as the frame image of a core element, using

```lean
theorem mCupFrameOfDM_surjective {alpha h : ℕ} (ha : 2 ≤ alpha) :
    Function.Surjective (mCupFrameOfDM ha h) :=
  (mFrameExists_phiEquiv (mStageOneLe ha) h).surjective.comp abMk_surjective
```

and its cup half needs no `chiM` hypothesis at all: it is
`mCupFrameCupIsometry_of_aut`, proved through `dmObs` and uniqueness of the
one-dimensional degree-two obstruction via
`GQ2.Dyadic.Instances.M0C0PivotAutomorphism.evenCupForm_comp_dm_aut` (checked
by this lane: std-3), with no coordinate computation.

### 6. No hidden premise anywhere on the seam

The chain from the endpoint down is short and every link was checked:

```text
mFullStabilizer_lift_of_frame            (MFullStabilizerLift.lean:127)
  = mFullStabilizer_lift_of_fixedHead ha phi hchi
      (mFullStabilizer_relError_of_cup ha phi hcup) (mStageStep_holds ha)
mFullStabilizer_lift_of_fixedHead        (MFrameMatrixLift.lean:1096)
  = mFullStabilizer_lift_of_initialLift hα φ
      (mStageInitialLift_of_fixedHead_error hα h φ hχ herror) hstep
mFullStabilizer_lift_of_initialLift      (MFullFrameStages.lean, conditional)
mStageStep_holds                         (MPlaneAmbientStage.lean:366)
```

`MStageStep alpha h` is the only named `Prop` interface in the wave that the
stage induction consumes, and it is discharged:

```text
@mStageStep_holds : ∀ {alpha h : ℕ}, 2 ≤ alpha → MStageStep alpha h
```

unconditionally in `h`. The other named `Prop`,
`MPlaneAmbientStage.MBasisAmbientStageSupply`, is likewise a theorem
(`mBasisAmbientStageSupply {alpha h : ℕ} (halpha : 2 ≤ alpha)`), not an
assumption. `MStageInitialLift` is constructed by
`mStageInitialLift_of_fixedHead_error` from the orientation hypothesis and the
cup-derived error; nothing about the initial basis is assumed at the endpoint.

**Instance hypotheses.** `MBasisRowRefinement`'s adapter section and
`MHeadCleanup`'s MKernelCoordination section carry
`[CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]` on a generic `G`,
inherited from `evenRawStageShift_m`. They are discharged by instance
resolution at `FreeTwoRank (coreRank h)` and at `DM alpha h`, and the evidence
is that neither `mStageStep_holds` nor `mFullStabilizer_lift_of_frame` carries
any instance binder in the printed signatures above. There is no `variable`
block in `MFullStabilizerLift.lean` at all, so nothing is auto-bound there, and
the runner is invoked with `-DautoImplicit=false -DrelaxedAutoImplicit=false`.

### 7. The M-specific mathematics

**The coupled row.** `MHeadCleanup.mHead_ordinary_row` is the two-letter row,
and it is proved for an arbitrary continuous `ℤ_[2]` character, arbitrary rank:

```lean
theorem mHead_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y : Fin (coreRank h) → G) :
    (f (mRelWord alpha y)).toAdd =
      2 * (f (y 0)).toAdd + (2 : ℤ_[2]) ^ alpha * (f (y 2)).toAdd
```

The head digit is then extracted from that coupled row **without** setting the
`C` row to zero:

```lean
theorem mHead_dvd_of_coupled_row {alpha d : ℕ} (halpha : 2 ≤ alpha) (hd : 1 ≤ d)
    {A C : ℤ_[2]} (hCrow : (2 : ℤ_[2]) ^ (d - 1) ∣ C)
    (hdefect : (2 : ℤ_[2]) ^ (d + 1) ∣ 2 * A + (2 : ℤ_[2]) ^ alpha * C) :
    (2 : ℤ_[2]) ^ d ∣ A
```

**The primitive relation and the torsion generator.** `mFrameRelVec` is
`e_A + 2^(alpha-1) e_C` (quoted above), `mFrameHead` is `T = A * C^(2^(alpha-1))`,
and `mFrameHead_coordinate` proves that the coordinate vector of `T` is exactly
`mFrameRelVec`. `MFullFrameStages.mStageTorsionWord alpha y = y 0 * y 2 ^ (2 ^
(alpha - 1))` is the same word on an arbitrary marking, and
`mFrameHead_eq_torsionWord` is `rfl`.

**The basis change, and the negative statement about naive sections.** This is
the strongest M-specific content in the wave and it is an exhibited
counterexample, not a remark.
`mFrameBasisChangeHom` sends `A ↦ T`, everything else fixed, with explicit
inverse `mFrameBasisChangeInvHom` (slot `0` to `X_0 * X_2^(-m)`). The naive
transcription of the N lift matrix, which applies the canonical zero/one
torsion section independently to the `A` and `C` columns, is defined and then
*refuted*:

```lean
theorem mFrameNaiveLiftMatrix_relVec ... :
    ∑ i, mFrameNaiveLiftMatrix hα h φ j i * mFrameRelVec α i =
      (1 + (2 : ℤ_[2]) ^ (α - 1) * ((... .toAdd.1.val : ℕ) : ℤ_[2])) * mFrameRelVec α j

theorem mFrameNaiveLiftMatrix_relVec_iff ... :
    (∀ j, ∑ i, mFrameNaiveLiftMatrix hα h φ j i * mFrameRelVec α i = mFrameRelVec α j) ↔
      (φ (mFrameProjection hα h (freeTwoRankGen (coreRank h) 2))).toAdd.1 = 0
```

and the file then exhibits an orientation-preserving frame automorphism for
which the right-hand side fails: the torsion shear
`(ε, b, c, d, f) ↦ (ε + parity c, b, c, d, f)`
(`mFrameTorsionShear`, with `mFrameTorsionShear_orientation` and
`mFrameNaiveLiftMatrix_torsionShear_not_relVec`). The fixed-`T` lift is
therefore not a stylistic preference; the naive route is false.

**The depth-three step.** Two facts, both `alpha >= 2`, replace the N head
argument (`MInitialCupDepth.lean`):

```lean
theorem mCupPow_eq_one {α : ℕ} (hα : 2 ≤ α) (p : levelQuot G 3) : p ^ 2 ^ α = 1
theorem mCupSq_levelMk_eq_of_mem_two {u v : G}
    (huv : u * v⁻¹ ∈ twoCentralSeries G 2) :
    levelMk G 3 u ^ 2 = levelMk G 3 v ^ 2
```

so `C^(2^alpha)` dies in the class-two quotient (it lies in `lambda_(alpha+1)`
and `alpha + 1 >= 3`), and the surviving head is a **square**, which depends
only on the class of its base modulo `lambda_2`. That is exactly why fixing `T`
rather than `A` suffices:

```lean
theorem mCupPowHalf_mem_two {α : ℕ} (hα : 2 ≤ α) (g : G) :
    g ^ 2 ^ (α - 1) ∈ twoCentralSeries G 2
theorem mCupHead_mem_two_of_fixed_T {α : ℕ} (hα : 2 ≤ α) (a c a' c' : G)
    (hT : a * c ^ 2 ^ (α - 1) = a' * c' ^ 2 ^ (α - 1)) :
    a * a'⁻¹ ∈ twoCentralSeries G 2
```

The conclusion is genuine quotient membership of the actual word, not
membership in a formal bracket span:

```lean
theorem mCupRelWord_error_mem_three_of_fixed_T ... :
    mRelWord α m * (mRelWord α m')⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3
```

The commutator tail is imported from `NInitialCupDepth` (`freeTail_eq_of_cup`,
`freeTail_value`, `reducedRows`) and explicitly *not* reproved; the N file's own
final N-relator theorem is not used and is not claimed to be an M theorem.

**The variance.** `NInitialCupDepth.reducedRows m i j = nRed (toAdd
(freeTwoCoordinate _ i (m j)))`, that is, coordinate `i` of the image of
generator `j`. The matrix therefore has **columns = generator images**, and the
condition proved is `Abar G Abar^T = G`. Every statement in all nine modules
stays inside that convention, so the row/column dictionary is not a proof
input: `Variance.lean` is cited by `MFrameCupCoordinates`'s docstring as the
reader's dictionary to `M.lean`'s row convention `Mbar^T G Mbar = G`, which is
accurate, and `MFrame.lean`'s own scope note already records that
`mFrameMatrix_transpose_eq_nMatOf` "is **not** invoked and no transposition is
needed". The Gram is shared and not M-specific: `Variance.lean:107` has
`theorem mGram_eq_nGram : mGram = Matrix.of nGram := rfl`, and the nine modules
use `evenCupForm` throughout. See FLAG-3 for what this leaves for a consumer.

**The arbitrary-basis kernel interpolation.** What transfers from N is the
*closed correction-kernel subgroup* `nPlaneCorrectionKernel`, its closedness,
the row witnesses `nBasisKernelWitness_mem` / `_row`, and the generic finite
interpolation. The soundness of that transfer at M is one identity, and it is
an identity in the actual quotient group, not a graded analogy
(`MBasisRowRefinement.lean:53`):

```lean
theorem mBasis_mFiltered_mRelWord (k : ℕ) (hk : 3 ≤ k) (alpha : ℕ) (halpha : 2 ≤ alpha)
    {h : ℕ} (m t : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1)) :
    mRelWord alpha (fun i => m i * t i) = mRelWord alpha m * nFilteredDerivative m t
```

proved from `StageGeneric.evenRawStageShift_m` (checked by this lane: std-3)
composed with `mBasis_nFilteredDerivative_eq_evenRawDbarWord`. Note that the M
defect is shifted by the **M** stage identity `evenRawStageShift_m`, not by the
N one; `evenRawStageShift_n` enters only to identify the N *derivative word*
with the shared even crossed-derivation word. `MHeadCleanup`'s
`mHead_mRelWord_shift_eq_nRelWord_shift` states the resulting agreement openly
and disclaims the wrong reading in its own docstring: "It is **not** a claim
that any `N`-relator conclusion is an `M` theorem." That disclaimer is
accurate; this audit checked that no N relator conclusion is used at M. What
does not transfer is stated too: the head row `t 0` is not killed by the kernel
(the witnesses exist only at `i ≠ 0`), which is precisely why the separate
coupled head cleanup exists.

## Scope

### `alpha >= 2`: where it is used and what fails at `alpha = 1`

`2 ≤ alpha` is a binder of every public statement of the endpoint module and of
`mStageStep_holds`. It is genuinely load bearing at four independent places,
and the audit names the lemmas that are *false* at `alpha = 1`, not merely
unproved:

| Lemma | Statement | Why `alpha = 1` fails |
| --- | --- | --- |
| `MFrameMatrixLift.mFrame_halfExp_smul_zmod2` | `(2 ^ (α - 1)) • ε = 0` for `ε : ZMod 2` | at `α = 1` this is `1 • ε = ε`, false at `ε = 1`; this is the step that kills the torsion digit in `mFrameNaive_image_zero`, so the fixed-`T` lift's `A` column formula collapses |
| `MInitialCupDepth.mCupPowHalf_mem_two` | `g ^ 2 ^ (α - 1) ∈ twoCentralSeries G 2` | at `α = 1` it reads `g ∈ lambda_2`, false for a generator; the file's own docstring says "it is false at `alpha = 1`" |
| `MInitialCupDepth.mCupPow_eq_one` | `p ^ 2 ^ α = 1` in `levelQuot G 3` | the proof needs `g ^ 2 ^ α ∈ lambda_(α+1)` with `α + 1 ≥ 3`; at `α = 1` the `C` block survives into the class-two quotient |
| `MHeadCleanup.mHead_dvd_of_coupled_row` | `2 ^ d ∣ A` from the coupled row | it consumes `alpha = a + 2`; at `α = 1` the `C` summand `2 ^ α * C` is not already divisible by `2 ^ d` |

Two further consumers inherit the binder rather than adding one:
`MFrameMatrixLift.mFrame_pow_halfExp_mem_two` and `mFrame_nRed_halfExp` (the
cup-side interface saying the reduced `A` column of the lift is the first
standard basis vector), and `StageGeneric.evenRawStageShift_m`, whose own
signature begins `(hα : 2 ≤ α)` and which is the identity the whole kernel
interpolation rests on.

### The `1 <= alpha` bridges

`mPhiHom`, `mFrameExists_phiEquiv` and the whole of `MFullFrameCompactness`
need only `1 ≤ alpha`. The wave does not blur this. The bridge is a named
one-line theorem, `MFullFrameCompactness.lean:31`:

```lean
theorem mStageOneLe {alpha : ℕ} (ha : 2 ≤ alpha) : 1 ≤ alpha := le_trans one_le_two ha
```

and it is applied explicitly at every crossing, which is why the endpoint's
conclusion reads `mPhiHom (mStageOneLe ha) h` rather than carrying a second
binder. `mStageOneLe` is also the one pin in the wave that prints smaller than
the standard three (`[propext]`). Distribution of binders across the nine
modules, by grep: `2 ≤ alpha` appears in all nine; `1 ≤ alpha` appears 13 times
in `MFullFrameCompactness` and 0 times in `MFrameMatrixLift`,
`MInitialCupDepth`, `MFrameCupCoordinates` and `MFullStabilizerLift`.

### `h` is arbitrary; nothing assumes `h = 0`

Every statement in all nine modules is binder-general in `h`, over
`coreRank h`, `Fin (2 * h)` handle indices and `DM alpha h`. Greps for
`(h := 0)`, `h = 0`, `coreRank 0`, `MModel` and `mFrameModelZero` across the
nine return exactly one hit, and it is a docstring aside inside
`MFrameCupCoordinates.lean:34` about where the rank-four Gram identity lives.
`mStageStep_holds` is `∀ {alpha h : ℕ}, 2 ≤ alpha → MStageStep alpha h`, with no
constraint on `h` whatsoever, and the handle coordinates are carried through the
frame explicitly (`MFrame.map_U`, `map_V`, `mFrameRelVec_handle`,
`mSurjVec_handle`). The rank-four case is `h = 0`; no handle decomposition or
identity-handle restriction is used to reach larger `h`.

## Verification performed

Every one of the nine wave-362 modules was read and separately re-elaborated by
this audit lane with `bash scripts/w361_lean_runner.sh <source>` (the pinned
`leanprover/lean4:v4.31.0-rc2` compiler against the shared dependency cache; no
`lake`, no cache mutation). All nine exited zero with no warnings, and every
printed pin is inside the standard three.

| Module, under `GQ2/Dyadic/MarkedCore/` | Public axiom pins | Source SHA-256 |
| --- | ---: | --- |
| `MHeadCleanup.lean` | 7 | `b632b27cbfbaa3e070a24b72a332a6eab00efdfbefc3239bf348831b0fa7f209` |
| `MFullFrameCompactness.lean` | 25 | `bfb1cebd28b74549a71a252e0dabf95bad5d20d82b5819f10e8f47f2d6bb9d05` |
| `MFullFrameStages.lean` | 12 | `0f5e55200f2ff423c96bc8e8e4601e09b268988f6378398f18a05000ca078238` |
| `MFrameMatrixLift.lean` | 111 | `7f918a6679b77fc1be00e64ebf3a1ceeda3fb8ca65ba423ec379359699c925a3` |
| `MInitialCupDepth.lean` | 9 | `d7c2eb53138d7c2a48fc93f714175429820df2169dbad0f01938ff2b33dcaae8` |
| `MFrameCupCoordinates.lean` | 16 | `0880b52342e6a658c492121323cccb18f508ce63d7400a8f97539b571aaed525` |
| `MBasisRowRefinement.lean` | 9 | `fa0b97b9950fedf4595fa5d92aacb4f9599d98949e1855b54e236103f044aceb` |
| `MPlaneAmbientStage.lean` | 18 | `5de574be85b686242a48287176fca24e9fef5ab5dc743302a6f6fc128ffff686` |
| `MFullStabilizerLift.lean` | 9 | `bac55a1a4268bdc1bac2e647a9c2c6b3c70d1dba8c3483421ea57e9ee36da783` |

216 pins in total. 215 print exactly

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the remaining one is strictly smaller:
`'GQ2.Dyadic.MarkedCore.mStageOneLe' depends on axioms: [propext]`. The nine
pins of the endpoint module print, verbatim from the runner:

```text
'GQ2.Dyadic.MarkedCore.mFullStabilizer_liftEquiv_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_relError_of_cup' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mCupFrameOfDM_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFrameOrientation_cupFrameOfDM' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_orientation_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_cup_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_orientation_cup_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Hygiene

`grep -nE "sorry|native_decide|set_option|^axiom |admit|#exit"` over all nine
sources returns exactly one line, and it is prose inside a docstring:

```text
GQ2/Dyadic/MarkedCore/MPlaneAmbientStage.lean:202:target-relative M defect lies in `lambda_k` admits a depth-`(k-1)` correction
```

No `sorry`, no `native_decide`, no `set_option` of any kind (so no raised
`maxHeartbeats`, no disabled linter), no bare `axiom`. All nine modules are
registered in `GQ2.lean` at lines 1445-1453, in dependency order:

```text
1445:import GQ2.Dyadic.MarkedCore.MHeadCleanup
1446:import GQ2.Dyadic.MarkedCore.MFullFrameCompactness
1447:import GQ2.Dyadic.MarkedCore.MFullFrameStages
1448:import GQ2.Dyadic.MarkedCore.MFrameMatrixLift
1449:import GQ2.Dyadic.MarkedCore.MInitialCupDepth
1450:import GQ2.Dyadic.MarkedCore.MFrameCupCoordinates
1451:import GQ2.Dyadic.MarkedCore.MBasisRowRefinement
1452:import GQ2.Dyadic.MarkedCore.MPlaneAmbientStage
1453:import GQ2.Dyadic.MarkedCore.MFullStabilizerLift
```

These are incremental source compilations against the shared dependency cache,
not a new source-only transitive clean build. They do not extend any historical
frozen whole-tree report; that remains a parent-owned step.

## Flagged items

FLAG-1 (comment only, medium). `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`
module docstring, and `docs/dyadic/w362-massemble-note.md`, both assert:

```text
Nothing from the N theorem is reused; only its shape is matched.
```

That sentence is false as written, and it contradicts the sibling modules' own
docstrings. What is in fact reused from the N development, soundly and by
design:

* `N.lean`'s `nFrameModel_map_t` is applied verbatim to M frame automorphisms
  at `MFrameMatrixLift.lean:594` and `:740`.
* `MInitialCupDepth.lean` imports `NInitialCupDepth` and says so itself:
  "Everything about the commutator tail is shared with the N calculation and is
  imported from `NInitialCupDepth`".
* `MBasisRowRefinement.lean` reuses `nPlaneCorrectionKernel`,
  `nFilteredDerivative` and the N row witnesses through an adapter, and says so
  itself.
* `MPlaneAmbientStage.lean` imports `NPlaneAmbientStage` and uses its
  `oneWord`; `MFrameCupCoordinates.lean` imports `NFrameCupCoordinates` and
  opens `NInitialCupDepth` for `reducedRows`.

The defensible claim, which the other eight modules make correctly, is that the
M *route* is not a text substitution of the N proof. Suggested repair: replace
the sentence by something like "The M route is not a text substitution of the N
proof; what it does reuse from the N development is shared infrastructure
(`nFrameModel_map_t`, the N commutator-tail calculation, the closed N
correction kernel), never an N relator conclusion." This is a provenance
statement, not a mathematical one, and no proof depends on it.

FLAG-2 (comment only, low). Route bookkeeping in the lane notes is
inconsistent. `docs/dyadic/w361-m-next-general-scaffold.md` has five numbered
research items; item 5 is "Later exact rows and compactness should retain the
full frame", which is what `docs/dyadic/w362-mstages-note.md` did, and that note
calls itself "step 5 of 5". `docs/dyadic/w362-massemble-note.md` also calls
itself "step 5 of 5 (the assembly...)" and cites "Route item 5 of
`docs/dyadic/w361-m-next-general-scaffold.md`", but the assembly is not one of
the scaffold's five items at all: the scaffold stops at the stage/compactness
wrapper and explicitly says "The M adapters and their composition have not been
proved by this note". Two lanes claiming the same route item makes the wave
harder to reconstruct. No Lean is affected.

FLAG-3 (interface observation, low; not a defect in the theorem). The wave's
cup predicate `MCupFrameCupIsometry` occurs in exactly two files,
`MFrameCupCoordinates.lean` (its definition) and `MFullStabilizerLift.lean`
(its consumers). There is no declaration anywhere in the tree relating it to
`M.lean`'s matrix-level `mCupIsometry` / `IsMStabilizer`, which is what
`mStabilizer_classification` (rank four, `alpha >= 2`) consumes and produces.
So a consumer that wants to enter `mFullStabilizer_lift_iff` from the rank-four
marked Smith-Witt classification still has to build that bridge, and it is
exactly the bridge that needs `Variance.lean`'s row/column dictionary. The
MASSEMBLE note calls this "a convenience, not a gap"; this audit agrees that it
is not a gap *in the theorem*, which is complete and self-contained on the
frame, but records it as a real missing interface for that particular consumer
path, so that a later wave does not discover it late. `MCupFrameCupIsometry` is
the semantically safer public boundary and the scaffold recommended it; nothing
here argues for changing it.

### Checked and found accurate (no flag)

The remaining prose was checked claim by claim against the Lean and is correct.
In particular:

* The name-collision explanation is exact. `MFullFrameStages.lean` really does
  define `mFullStabilizer_lift` in namespace `GQ2.Dyadic.MarkedCore` as the
  **conditional** composition shape with five interface hypotheses
  (`e0, hT, hchi0, hframe0, herror0, hstep`), and its own docstring opens "This
  is *not* a proved lift". The unconditional landed theorem is
  `mFullStabilizer_lift_of_frame` in `MFullStabilizerLift.lean`. Anyone
  grepping for `mFullStabilizer_lift` will hit the conditional one first; the
  MASSEMBLE note's suggested later rename is the right repair.
* `MFullFrameStages.exists_mStageBasis_exact_stage` deliberately carries no
  `2 ≤ alpha` binder, and its docstring says why and warns "This is not a claim
  that anything is available at `alpha = 1`, where `MStageStep` has no producer
  at all." Checked: `MStageStep alpha h` is indeed *stated* at every `alpha`,
  and the only producer, `mStageStep_holds`, requires `2 ≤ alpha`. The warning
  is accurate and the arrangement is safe.
* `MFullFrameCompactness.lean`'s scope claim, "this module needs only
  `1 <= alpha`", is accurate: 13 of its binders are `1 ≤ alpha` and the bridge
  `mStageOneLe {alpha : ℕ} (ha : 2 ≤ alpha) : 1 ≤ alpha` is kept explicit
  rather than inlined, so no statement silently weakens.
* The MCUP note's "`mCupStageError_of_frame` ... omits `hchi0` and is the
  stronger one" is accurate; `mFullStabilizer_relError_of_cup` in the endpoint
  module likewise takes no orientation hypothesis.
* Every "no `sorry` / no option / std-3" claim in all six lane notes matches
  what this lane re-measured independently.
* `decide` is used six times across the nine modules, always on a tiny finite
  `ZMod 2` or `Multiplicative (ZMod 2)` goal. All are kernel-checked; there is
  no `native_decide`.

## Explicit nonclaims

- The final `Psi` is obtained through a compactness limit
  (`exists_mStageFullFrameRealizes_of_stages` over nested closed stage sets).
  No finite explicit Nielsen-generator list, and no finite-word decomposition
  of the limit automorphism, is produced. The packet's separate MC-M completion
  criterion at lines 1077-1082 is therefore **not** certified by this theorem;
  see the companion scope note.
- Literal head fixation is a property of the **initial free lift**
  (`mFrameLiftEquiv_head`). The final `Psi` is asserted to have the prescribed
  full abelianization and to preserve `chiM`; it is not asserted to fix any
  group generator literally, and in particular it does not fix `A`.
- `alpha >= 2` throughout. Nothing is asserted at `alpha = 0` or `alpha = 1`,
  and several load-bearing lemmas are false there (see **Scope** above).
- This is an M-core result about `DM alpha h`. It certifies no field endpoint,
  no census or freeze update, no release, and no publication artifact, and it
  does not extend any historical frozen whole-tree verification report.
- The nine modules were re-elaborated incrementally against the shared
  dependency cache. This audit did not perform, and does not claim, a
  source-only transitive clean build of the tree at this base.
