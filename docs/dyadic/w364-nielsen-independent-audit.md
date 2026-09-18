# W364: independent audit of the finite Nielsen-list artifacts (MC-M, MC-N)

Date: 2026-09-17. Audit lane: `w364-audit2`, branch `claude/w364-audit2`, base
`d2056503`, Lean 4.31.0-rc2. Read-only with respect to Lean: this lane makes no
proof, umbrella, module or script change. Comment-only findings are FLAGGED
below for the orchestrator.

**VERDICT (MC-M list, `mNielsenGen_finite_list` + `mNielsenGen_stabilizer_induced`):
supplies the finite list, the lifts and the quantifier closure WITH CAVEATS.**

**VERDICT (MC-N list, `nNielsenFac_finite_list` + `nNielsenFac_stabilizer_induced`):
supplies the finite list, the lifts and the quantifier closure WITH CAVEATS.**

The caveats are the same four at both cores, they are scope and provenance, not
defects in what is proved, and **every one of them is already disclosed in the
artifact's own module docstring and lane note**:

1. handle rank **zero** only (which is what the packet's MC-M/MC-N rows ask for);
2. `alpha >= 2` wherever the actual frame appears (the N *factorization* alone is
   genuinely `alpha`-free, checked below);
3. "a finite list of generators" is satisfied in the **families** reading, not the
   generator-level-closed-form reading: what is produced for a given stabilizer
   element is one member of each of seven (M) or eight (N) fixed slots, and each
   member is lifted by the wave-361/362 compactness theorem, not by a closed
   formula. A literally finite generating **set** is impossible and is not claimed;
4. the M quantifier closure carries an abstract orientation character `chi` with
   four pinned generator values, inherited from `mStabilizer_classification`.

Nothing is proved twice over as something it is not. The compactness theorems are
not relabelled: the finite list is a new object, and the theorems say so.

No mathematical error was found in any of the three modules. Three FLAGGED items
below are comment-only: one genuine contradiction between a module docstring and
its own lane note (FLAG-1, medium), one literally false prose sentence whose
substantive claim is nevertheless correct (FLAG-2, low), and one unformalized
mathematical assertion stated without a hedge in a lane note (FLAG-3, low). Three
further INFO items record wording that is loose but not wrong.

## Scope of this audit

Audited: `GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean` (W363, 70 pinned
declarations), `GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean` (W363, 16),
`GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean` (W364, 94), the notes
`docs/dyadic/w363-nielsen-note.md`, `docs/dyadic/w364-nfactor-note.md`,
`docs/dyadic/w363-mconsol-note.md`, and the W363-MCONSOL consolidation of the nine
wave-362 M modules. Matched against the packet
`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` lines 1077-1082
and the design table `docs/dyadic/mc-design.md` sections 2.4 and 3.4.

Companion: `docs/dyadic/w364-nielsen-scope.md` states the exact scope of the two
artifacts, in the shape of `docs/dyadic/w363-m-full-stabilizer-scope.md`.

## 1. The statements versus the packet sentence

The packet row, verbatim (`.tex` lines 1077-1082):

> MC-M & Marked automorphism lifting for the rank-four \(M_\alpha\) core &
> A finite list of orientation-preserving Nielsen generators lifts the
> Smith--Witt stabilizer on the abelianization; composition gives every
> required marking correction.
> MC-N & Marked automorphism lifting for the rank-four \(N_\alpha\) core &
> Same criterion for the \(N\)-relation vector and cup form.

The sentence has three clauses. Taken one at a time.

### 1.1 "A finite list of orientation-preserving Nielsen generators"

At M, `MNielsenGenerators.lean:633`:

```lean
noncomputable def mNielsenGenList {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) :
    List (ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)) :=
  [mNielsenGenM3 gamma, mNielsenGenM1 ha k, mNielsenGenM5 b, mNielsenGenM2 e,
    mNielsenGenM4 beta, mNielsenGenM6 c, mNielsenGenM7 d]
```

with `mNielsenGenList_length ... = 7` by `rfl`. At N,
`NNielsenFactorization.lean:711`:

```lean
def nNielsenFacList (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) :
    List (ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) :=
  [nNielsenFacN2 z, nNielsenFacN3 y, nNielsenFacN2 x, nNielsenFacN4 κ, nNielsenFacN3 w,
    nNielsenFacN5 p, nNielsenFacN6 q, nNielsenFacN1 k]
```

with `nNielsenFacList_length ... = 8` by `rfl`. Both lists are lists of **actual
continuous automorphisms of the actual frame model**, not of matrices or of
abstract data: each entry is an `nNielsenFacEquiv`/`mNielsenGenEquiv`, whose inverse
is supplied by the same family at the negated parameter (or the inverted unit), so
they are honest `ContinuousMulEquiv`s. Checked entry by entry at N in
`nNielsenFac_N1_inv` through `nNielsenFac_N6_inv`, at M in `mNielsenGen_M1_inv`
through `mNielsenGen_M7_inv`.

Orientation preservation is literal and is proved for **every** parameter, not only
for the listed ones. At M this is `mNielsenGen_orientation`, at N
`nNielsenFac_orientation`; both conclude
`... Orientation ha 0 (phi z) = ... Orientation ha 0 z` for all `z`, against the
transported actual characters `mFrameOrientation` / `nFrameOrientation`. The N
clause is the stronger of the two (the integral `x1` coordinate is fixed on the
nose, `nNielsenFacMap_coord_x1`, which is `rfl`), the M clause the weaker (only the
`B` parity is pinned, plus the integral `D` coordinate). That asymmetry is correctly
recorded in both lane notes.

**Which reading of "a finite list of generators lifts" is satisfied.** The satisfied
reading is: *finitely many families, at a fixed slot count, every member of which
lifts, the lift being supplied by the compactness theorem.* Precisely:

* satisfied: for each stabilizer element there is a list of 7 (M) or 8 (N)
  automorphisms, one drawn from each slot, each of which lifts, whose composite is
  that element's frame action, and whose lifts compose to a lift of it;
* **not** satisfied: generator-level closed-form lifts. At M, families M4 through
  M7 (and, on the module docstring's reading, M3) have no group-level construction
  anywhere in the repository; at N, family N4's own construction
  (`nPlaneScalingHypothesis_general`) is itself a compactness limit of the N-plane
  stages. The N side does have a genuinely independent second lift of every slot
  (section 2.6 below), which M does not;
* **not** satisfied, and impossible: a literally finite generating *set*. The seven
  (M) / six (N) families are each parameterized by a 2-adic number or unit, and
  `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` is not finitely generated as an abstract group.
  Both files say this out loud.

### 1.2 "lifts the Smith-Witt stabilizer on the abelianization": is the quantifier literal?

**Yes, at both cores.** The two closures are different in shape because the two
classifications are.

At M, `MNielsenGenerators.lean:845`, quoted with the binder list the elaborator
prints (this lane's own probe run):

```text
@mNielsenGen_stabilizer_induced : ∀ {alpha : ℕ} (ha : 2 ≤ alpha)
  (chi : topAbelianization ↑(DM alpha 0).toProfinite.toTop →ₜ* ℤ_[2]ˣ),
  chi (abMk (dmA alpha 0)) = 1 →
    chi (abMk (dmB alpha 0)) = -1 →
      chi (abMk (dmC alpha 0)) = 1 →
        chi (abMk (dmD alpha 0)) = mUnit alpha →
          ∀ (xi : topAbelianization ↑(DM alpha 0).toProfinite.toTop ≃ₜ*
                  topAbelianization ↑(DM alpha 0).toProfinite.toTop),
            IsMStabilizer (mNielsenGenFrame ha).toMDecomposition chi xi →
              ∃ Psi,
                (∀ x, (chiM alpha 0) (Psi x) = (chiM alpha 0) x) ∧
                  ∀ x, abMk (Psi x) = xi (abMk x)
```

`IsMStabilizer` (`M.lean:830`) is

```lean
def IsMStabilizer {α : ℕ} (B : MDecomposition α)
    (χ : ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) ℤ_[2]ˣ)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) : Prop :=
  (∀ x, χ (ξ x) = χ x)
    ∧ (mFrameMatrix B ξ).transpose * mGram * mFrameMatrix B ξ = mGram
```

so the hypothesis is exactly chi-preservation plus the mod-2 Witt isometry: the
Smith-Witt stabilizer, with no extra premise. `xi` is an arbitrary continuous
automorphism of the full topological abelianization, torsion coordinate included.
The conclusion is the **exact square** `abMk (Psi x) = xi (abMk x)` for every `x`,
i.e. `xi` really is the map induced by an actual `chiM`-preserving continuous
automorphism of `D_M`, not merely agreement on generators or on a quotient.

At N, `NNielsenFactorization.lean:911`:

```text
@nNielsenFac_stabilizer_induced : ∀ {alpha : ℕ} (ha : 2 ≤ alpha)
  (xi : topAbelianization ↑(DN alpha 0).toProfinite.toTop ≃ₜ*
        topAbelianization ↑(DN alpha 0).toProfinite.toTop),
  IsNStab alpha (nNielsenFacRows ha (nNielsenFacTransport ha xi)) →
    ∃ Psi,
      (∀ x, (chiN alpha 0) (Psi x) = (chiN alpha 0) x) ∧
        ∀ x, abMk (Psi x) = xi (abMk x)
```

with `IsNStab` (`N.lean:874`) the four-field structure `chi_x1`, `chi_sigma`,
`chi_x2`, `cup : R.IsCupIsometry`. The stabilizer clause is on the **rows** of `xi`
read in the canonical frame, which is `N.lean`'s own vocabulary; there is no N
analogue of `IsMStabilizer`'s abstract `chi`, because `nChiVec` is intrinsic. The
rows really are `xi`'s rows: `nNielsenFacTransport_mark` proves

```lean
    nNielsenFacTransport ha xi (nFrameCanonicalMark ha 0 j)
      = nPhiHom ha 0 (xi (abMk (dnGen alpha 0 j)))
```

So the N closure is **cleaner** than the M one: no abstract character has to be
supplied, and no generator values have to be pinned by hand.

Both closures are genuine, and in both cases the step from "for every parameter" to
"for every stabilizer element" is a separate, checked lemma:

* M: `mNielsenGen_frameAction_of_realizes` (hom-extensionality on `MFrameModel 0`
  against `MStabParam.Realizes`'s three rows plus the forced `A`-row
  `mStabilizer_A_row`; the four mark cases are discharged by explicit `show` goals
  closed with `ring`, all four inspected);
* N: `nNielsenFac_frameAction_of_rows` (hom-extensionality against the three rows
  plus the **automatic** `t`-row `nFrameModel_map_t`, so nothing is assumed about
  the torsion generator).

Both use a hom-extensionality lemma proved in-file from the topological generation
of the frame by the canonical marks (`mNielsenGen_frame_hom_ext`,
`nNielsenFac_frame_hom_ext`), through `presPro2_hom_ext` and the frame-cover
surjectivity. No `Prop`-valued interface, no instance hypothesis, no choice of
witness is smuggled in.

### 1.3 "composition gives every required marking correction"

This is exactly what the composite clauses say. At M, `MNielsenGenerators.lean:685`,
clauses (3) and (4) of the conclusion:

```lean
      (∀ z, mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇) z
        = mNielsenGenMap p z) ∧
      MNielsenGenLifts ha
        (mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇))
```

and the same two at N in `nNielsenFac_finite_list`. `MNielsenGenLifts` /
`NNielsenFacLifts` are *verbatim the conclusion of the compactness theorem*, so the
fourth clause is genuinely "the composite lifts", not a restatement of the third:

```lean
def MNielsenGenLifts {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
    (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
    (∀ x, mPhiHom (mStageOneLe ha) 0 (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) 0 (abMk x)))
```

Critically, the fourth clause is *not* obtained by applying the compactness theorem
to the composite directly. It is obtained by **composing the members' own lifts**:
`mNielsenGenLifts_compose` is a list induction over `mNielsenGenLifts_trans`, whose
proof builds `P.trans Q` out of the two witnesses and checks the two clauses. So
"composition gives every required marking correction" is what is proved, in the
strong sense: the correction realizing a stabilizer element is literally the
composite of the seven (M) / eight (N) per-generator corrections. Same at N
(`nNielsenFacLifts_compose`, `nNielsenFacLifts_trans`).

`mNielsenGen_param_realized` and `nNielsenFac_param_realized` project the list away
and give the bare realization statement.

### 1.4 Rank and `alpha`

Both artifacts are handle rank **zero** only, which is what the packet rows ask for
("the rank-four \(M_\alpha\) core", "the rank-four \(N_\alpha\) core"). The binding
reason is stated correctly in both files: `mStabilizer_classification`,
`mNielsen_factorization` and `nStabilizer_classification` are rank-four statements.
The lifting halves (`mFullStabilizer_lift`, `nFullStabilizer_lift`) are general in
`h`; the classification is not.

`alpha >= 2` appears in every statement that mentions the actual frame. The W364
note's claim that **the N factorization itself is `alpha`-free** is **correct and
literal**: the probe prints

```text
nNielsen_factorization : ∀ (P : NStabParam), P.Admissible → ∃ k q p w x y z κ, ...
```

with no `alpha` binder anywhere, matching memo section 3.3 ("Completely
α-independent"). Its two feeders `nNielsenFac_gl2_factor` and `nNielsenFac_couple`
are also `alpha`-free.

At M, `alpha >= 2` is genuinely load-bearing and not decorative. It is consumed in
`mNielsenGen_coord_two`, through

```lean
theorem mFrame_nRed_halfExp {α : ℕ} (hα : 2 ≤ α) : nRed ((2 : ℤ_[2]) ^ (α - 1)) = 0
```

(`MFrameMatrixLift.lean:1024`), whose proof writes `α - 1 = r + 1` and therefore
**fails at `α = 1`**, where `2 ^ (α - 1) = 1` has odd reduction. That is exactly the
forced `A`-row correction `Ā = t - 2^{α−1}C̄₀` becoming visible mod two, which would
change the mod-2 column of the `A` mark and hence the whole cup computation. The
note's sentence "that is where the binder is used" is accurate.

## 2. The N factorization mathematics

### 2.1 The six families against the design table

`docs/dyadic/mc-design.md` section 3.4 and `NNielsenFactorization.lean:136-156`
agree family by family. Memo, verbatim:

| # | family | parameter | frame action | stratum |
|---|---|---|---|---|
| N1 | `x₁ ↦ x₀^k·x₁` | `k ∈ ℤ₂` | `τ = k mod 2` | **S1** |
| N2 | `x₂ ↦ x₂·σ^k`, `(x₀,x₁) ↦ (x₀,x₁)^{σ^k}` | `k ∈ ℤ₂` | transvection `x̄₂ ↦ x̄₂ + kσ̄` | **S1** |
| N3 | `σ ↦ σ·x₂^k`, `(x₀,x₁) ↦ (x₀,x₁)^{x₂^k}` | `k ∈ ℤ₂` | transvection `σ̄ ↦ σ̄ + kx̄₂` | **S1** |
| N4 | handle determinant `det g = κ ∈ ℤ₂ˣ` | `κ` | `σ̄ ↦ κσ̄` (+shears) | **S2** (B8) |
| N5 | `x₁ ↦ x₁σ^p` (+ coupled `x₂ ↦ x₀^{p}x₂`) | `p ∈ ℤ₂` | `p` | **S3** |
| N6 | `x₁ ↦ x₁x₂^q` (+ coupled `σ ↦ x₀^{q}σ`) | `q ∈ ℤ₂` | `q` | **S3** |

Lean, verbatim:

```lean
def nNielsenFacBlock (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) : NStabParam := ⟨0, 0, 0, 0, 0, g⟩
def nFamN1 (k : ℤ_[2]) : NStabParam := ⟨nRed k, 0, 0, 0, 0, 1⟩
def nFamN2 (k : ℤ_[2]) : NStabParam := nNielsenFacBlock (planeElemU k)
def nFamN3 (k : ℤ_[2]) : NStabParam := nNielsenFacBlock (planeElemV k)
def nFamN4 (κ : ℤ_[2]ˣ) : NStabParam := nNielsenFacBlock (nPlaneDet κ)
def nFamN5 (p : ℤ_[2]) : NStabParam := ⟨0, p, 0, 0, nRed p, 1⟩
def nFamN6 (q : ℤ_[2]) : NStabParam := ⟨0, 0, q, nRed q, 0, 1⟩
```

with `NStabParam = ⟨tau, p, q, tauSigma, tauX2, g⟩` and `planeElemU k = !![1, k; 0, 1]`,
`planeElemV k = !![1, 0; k, 1]`, `nPlaneDet κ = !![(κ : ℤ_[2]), 0; 0, 1]`. Checking the
frame actions against the table, using `NStabParam.act (v1, a, b, c)` in the basis
`(t, x̄₁, σ̄, x̄₂)`:

* **N1**: `nFamN1_act` gives `(v1 + ā·k̄, a, b, c)`, i.e. `τ = k mod 2`. Matches.
* **N2**: `nFamN2_act` gives `(v1, a, b + c·k, c)`. In coordinates, `x̄₂ ↦ x̄₂ + kσ̄`
  means the `σ̄`-coefficient of a vector picks up `k` times its `x̄₂`-coefficient.
  Matches.
* **N3**: `nFamN3_act` gives `(v1, a, b, b·k + c)`, the mirror. Matches.
* **N4**: `nFamN4_act` gives `(v1, a, b·κ, c)`, i.e. `σ̄ ↦ κσ̄`. Matches the table's
  frame action. The table's parenthetical "(+shears)" has **no** counterpart in the
  Lean: `nFamN4 κ` is pure `diag(κ, 1)`, confirmed by this lane's probe
  (`(nFamN4 κ).g = !![(κ : ℤ_[2]), 0; 0, 1]` by `rfl`). This is correct rather than a
  gap, because the shears are separately supplied by N2 and N3 and the factorization
  composes them explicitly; see INFO-1.
* **N5**: `nFamN5_act` gives `(v1 + c̄·p̄, a, a·p + b, c)`: the `σ̄`-coefficient picks
  up `p` times the `x̄₁`-coefficient (`x̄₁ ↦ x̄₁ + pσ̄`), and the `x̄₂` column carries the
  coupled `t`-shift `τ_{x₂} = p mod 2` (`x₂ ↦ x₀^p x₂`). Matches, coupling included.
* **N6**: `nFamN6_act` gives `(v1 + b̄·q̄, a, b, a·q + c)`, the mirror with
  `τ_σ = q mod 2`. Matches.

`NStabParam.act` itself is verified against memo section 3.3's closed form by
`act_t`, `act_x1`, `act_sigma`, `act_x2`, which prove that the four basis columns are
`NRows.col` at `NStabParam.rows` **on the nose**. This is the right check: it ties the
new action to the object `nStabilizer_classification` actually classifies.

### 2.2 `nNielsenFac_gl2_factor`: the local-ring case split and the five block slots

```lean
theorem nNielsenFac_gl2_factor (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hg : IsUnit g.det) :
    ∃ (w x y z : ℤ_[2]), (w = 0 ∨ w = 1) ∧
      g = planeElemV w * nPlaneDet hg.unit * planeElemU x * planeElemV y * planeElemU z
```

Audited in full. The core case (`key`) asserts, for a **unit** `(1,0)` entry `c`,

```
!![a, b; c, d] = diag(δ,1) · E((a−δ)δ⁻¹c⁻¹) · F(c) · E((d−1)c⁻¹),    δ = det.
```

Verified by hand: `diag(δ,1)·E(u)·F(c)·E(s)` has entries
`(0,0) = δ + δuc`, `(1,0) = c`, `(1,1) = cs + 1`, `(0,1) = (δ+δuc)s + δu`. With
`u = (a−δ)δ⁻¹c⁻¹` one gets `δuc = a − δ`, so `(0,0) = a`; with `s = (d−1)c⁻¹`,
`(1,1) = d`; and `(0,1) = a(d−1)c⁻¹ + (a−δ)c⁻¹ = c⁻¹(ad − δ) = c⁻¹·bc = b`, using
`δ = ad − bc`, which is exactly the hypothesis `hd` the lemma takes. The Lean closes
the four entries with `Matrix.mul_fin_two` plus three `linear_combination`s over
`hδi` and `hci`, the two unit relations. Sound.

The case split is the local-ring step and it is correct:

* if `g 1 0` is a unit, `key` applies directly and `w = 0` (`planeElemV_zero` makes
  the first slot the identity);
* otherwise `IsLocalRing.isUnit_or_isUnit_of_isUnit_add` applied to
  `g00·g11 + −(g01·g10)` (which is `det`, a unit) gives `IsUnit (g00·g11)`, hence
  `IsUnit (g 0 0)` (the alternative would force `g 1 0` to be a unit,
  contradiction); the same lemma applied to `(g00 − g10) + g10` then gives
  `IsUnit (g 1 0 − g 0 0)`. `F(−1)·g = !![g00, g01; g10−g00, g11−g01]` has a unit
  `(1,0)` entry and the same determinant, so `key` applies to it and
  `g = F(1)·(F(−1)·g)` with `w = 1`.

So the Boolean slot `w ∈ {0, 1}` is exactly the "is the `(1,0)` entry a unit"
dichotomy, and **five** block slots suffice uniformly. The **eight-slot bound** is
then `5 + N5 + N6 + N1`. This is the bounded form of `N.lean`'s `nGL_factor`, which
only gives membership in a submonoid closure; the note's description of the
improvement is accurate.

The composition law is matrix multiplication, proved rather than asserted:

```lean
theorem nNielsenFacBlock_act_comp (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    (nNielsenFacBlock g₁).act ∘ (nNielsenFacBlock g₂).act = (nNielsenFacBlock (g₁ * g₂)).act
```

and the block half of the factorization is that identity applied four times against
`nNielsenFac_gl2_factor`'s `hg`, with `Matrix.mul_assoc` reassociating. The slot
order in the list (`N2(z), N3(y), N2(x), N4(κ), N3(w)`, leftmost applied first) is
the reverse of the `∘`-order `F(w)·diag·E(x)·F(y)·E(z)`, which is the correct
convention and is what `nNielsenFacCompose_list` (an `rfl`) pins.

### 2.3 The two `Admissible` couplings, and that they close the `t`-slot

`NStabParam.Admissible` (`N.lean:931`) is three fields: `det : IsUnit P.g.det`,
`couple_p : nRed P.p = P.tauX2 * nRed (P.g 0 0) + P.tauSigma * nRed (P.g 0 1)`,
`couple_q : nRed P.q = P.tauX2 * nRed (P.g 1 0) + P.tauSigma * nRed (P.g 1 1)`.
These are memo section 3.3's `(p̄, q̄) = (τ̄_{x₂}·g₁ + τ̄_σ·g₂, τ̄_{x₂}·h₁ + τ̄_σ·h₂)`
verbatim, with `g 0 0 = g₁`, `g 0 1 = g₂`, `g 1 0 = h₁`, `g 1 1 = h₂` (confirmed
against `NStabParam.rows_sigma` / `rows_x2`).

They are used **exactly once**, through

```lean
private theorem nNielsenFac_couple (τσ τx p q g₁ g₂ h₁ h₂ : ZMod 2)
    (hdet : g₁ * h₂ + g₂ * h₁ = 1) (hp : p = τx * g₁ + τσ * g₂) (hq : q = τx * h₁ + τσ * h₂) :
    h₁ * p + g₁ * q = τσ ∧ h₂ * p + g₂ * q = τx
```

which is the inversion of the 2x2 system over `F2` (adjugate `[[h̄₂, ḡ₂], [h̄₁, ḡ₁]]`,
signs invisible in characteristic two), closed by `decide` over the `2⁶`
assignments after `subst`. Independently verified by hand; the `hdet` hypothesis is
supplied from `Admissible.det` through `nIsUnit_det_iff`.

**That this is what closes the `t`-slot** is the substantive check, and it passes.
Tracing the composite in `nNielsen_factorization`: the block slots leave the `t`-slot
alone; N5 adds `c̄'·p̄` where `(b̄', c̄')` are the post-block coordinates; N6 adds
`(ā·p̄ + b̄')·q̄`; N1 adds `ā·k̄`. Expanding with `b̄' = b̄ḡ₁ + c̄ḡ₂` and
`c̄' = b̄h̄₁ + c̄h̄₂` gives

```
v1 + b̄(h̄₁p̄ + ḡ₁q̄) + c̄(h̄₂p̄ + ḡ₂q̄) + ā(τ + p̄q̄) + ā·p̄q̄
```

and the two bracketed quantities are `τ_σ` and `τ_{x₂}` by `nNielsenFac_couple`,
while the two `ā·p̄q̄` terms cancel in characteristic two. That leaves
`v1 + āτ + b̄τ_σ + c̄τ_{x₂}`, which is `NStabParam.act`'s `t`-slot exactly. The Lean
closes it with

```lean
    linear_combination (-(nRed b)) * hii + (-(nRed c)) * hiii
      + (-(nRed a * nRed P.p * nRed P.q)) * h2
```

which is precisely those three facts with those three coefficients. The witness
`k = ((P.tau + nRed P.p * nRed P.q).val : ℤ_[2])` is the `p̄q̄` correction the
cancellation needs, and `nNielsenFac_nRed_val` reads it back. Nothing else in the
proof sees the couplings. The note's claim "necessary and sufficient for the
`t`-slot to close; nothing else in the proof sees them" is accurate.

### 2.4 The identification `nNielsenFac_mat` with `nNielsenGenMat` and `NRows.mat`

```lean
theorem nNielsenFac_mat {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v)
    (i j : Fin (coreRank 0)) :
    nNielsenGenMat ha (nNielsenFacEquiv P Q hPQ hQP) i j = P.rows.mat i j
```

This is the bridge W363 built `NNielsenGenerators.lean` for, and it lands. The chain
is: `nNielsenFacMap_mark` (the image of the `j`-th canonical mark is the `j`-th
column of `NRows.col` at `P.rows`, by the four `act_*` row lemmas, with an empty
handle tail), then the four `nNielsenGen_coord_*` reductions, then `rfl` in each of
the four `i` cases. `NRows.mat R i j = nMod2 (R.col j) i` (`N.lean:840`), which is
the same column convention, so the identification is exact and not up to transpose.

Downstream, `nNielsenFac_cupIsometry` feeds it to W363's `nNielsenGen_cup_of_mat`
together with `N.lean`'s `NStabParam.rows_isCupIsometry`, yielding the semantic
`NFrameCupIsometry`. The W363 side of that bridge is itself sound:
`nNielsenGen_cup_core` is the statement that a matrix satisfying `A G Aᵀ = G`
transports `nCupForm`, proved by a 16-term `linear_combination` over the sixteen
Gram entries; expanded by hand,
`nCupForm(Aᵀu, Aᵀv) = Σ_{j,l} u_j v_l nCupForm(A_j, A_l) = Σ_{j,l} u_j v_l G_{jl}`,
which is the identity used. Sound.

### 2.5 Family admissibility, and that the list is legitimate

`nFamN1_admissible` through `nFamN6_admissible` check `Admissible` for every member
of every family. This matters: `nNielsenFac_cupIsometry` needs it, so without it the
list members would not be provably cup isometries and would not lift. All six are
one-liners over `nNielsenFacBlock_admissible` (unit determinant, both couplings
vacuous since the block families have `p = q = τ_σ = τ_{x₂} = 0`) or direct. Note in
particular that N5 and N6 are admissible **because** their coupled `t`-shifts are
set to `nRed p` / `nRed q`: dropping the coupling would break `Admissible` and the
list would not go through `nNielsenFacList_props`. The stress pin

```lean
example : (nFamN5 1).act ((0 : ZMod 2), 0, 0, 1) = ((1 : ZMod 2), 0, 0, 1)
```

confirms the coupled shift is not vacuous.

### 2.6 The per-family route

`nNielsenFacLifts_of_param_families` is a genuinely independent second lift of every
list member, through `nStabParam_fullFrame_lift_general` and the identification
`nNielsenFac_fullFrameMark` of `NStabilizerFullRows.fullFrameMark P 0 i` with
`nNielsenFacMap P` at the `i`-th mark. It does not route through
`nFullStabilizer_lift`. The docstring's own caveat, that the N4 ingredient
`nPlaneScalingHypothesis_general` is itself a compactness limit so this route is
*not* a closed-formula lift of every generator, is correct and is stated in both the
module and the note. Accepted as stated.

## 3. The M-side reduction of the semantic cup predicate to a finite F2 check

`MCupFrameCupIsometry` (`MFrameCupCoordinates.lean:80`) quantifies over **all**
continuous mod-two characters of the frame:

```lean
def MCupFrameCupIsometry {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) : Prop :=
  ∀ c d : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (phi (mCupFrameCanonicalMark ha h i))))
        (fun i => toAdd (d (phi (mCupFrameCanonicalMark ha h i)))) =
      evenCupForm (fun i => toAdd (c (mCupFrameCanonicalMark ha h i)))
        (fun i => toAdd (d (mCupFrameCanonicalMark ha h i)))
```

so it is the honest pullback-isometry statement on `H¹`, not a coordinate identity.
**The reduction is sound.** The chain:

1. `mNielsenGen_coord_zero` .. `_three` read the four mod-two coordinates off an
   arbitrary frame element. Only `_two` consumes `ha`, through
   `mFrame_nRed_halfExp` (section 1.4). These are proved from
   `mFrameProjection_coordinateSection`, i.e. from the actual frame surjection, not
   assumed.
2. `mNielsenGen_character_apply` expands an **arbitrary** continuous mod-two
   character in those coordinates, by pushing
   `freeTwo_commutative_hom_coordinates` through the surjection
   `mCupFreeFrameProjection`. This is the step that makes the reduction complete
   rather than partial: every character, not just the four coordinate characters, is
   accounted for.
3. `mNielsenGen_image_coord_*` compute the reduced column-convention matrix of a
   parameter directly from the semantics; `mNielsenGen_char_mark_zero` .. `_three`
   evaluate an arbitrary character on the image of each mark.
4. `mNielsenGen_cup_core` is the resulting `F2` identity, in eleven free variables,
   closed by `decide` (`2¹¹ = 2048` cases, no `native_decide`):

```lean
private theorem mNielsenGen_cup_core (s m n a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2) :
    a0 * b0 + (a0 * (s * b0 + b1 + m * b2) + (s * a0 + a1 + m * a2) * b0)
        + (a2 * (m * b0 + n * b2 + b3) + (m * a0 + n * a2 + a3) * b2)
      = a0 * b0 + (a0 * b1 + a1 * b0) + (a2 * b3 + a3 * b2)
```

Verified by hand: expanding the left side, the four cross terms `s a0 b0`,
`m a0 b2`, `m a2 b0` and `n a2 b2` each occur twice and cancel in characteristic
two, leaving the right side. **The cancellation of `m a0 b2` against `m a2 b0` is
exactly the Witt coupling earning its keep**: those two terms come from the `B`-row's
`C̄₀`-component and the `D`-row's `t`-component respectively, and if the latter were
an independent parameter `n'` rather than `m = mParityZ p.bc`, they would not cancel
and the identity would be false. So the finite check is not vacuous, and it is the
right check: it is where memo section 2.3's coupling is consumed. That the identity
holds for **all** `s, m, n` is correct rather than suspicious, because the two Witt
constraints (`φ(C̄₀)` has no `t`-component, and the coupling) are built into the
shape of `MStabParam.act`, not tested by the identity.

`evenCupForm` at `coreRank 0` is `v0w0 + (v0w1 + v1w0) + (v2w3 + v3w2)` plus an
empty handle sum, and `mNielsenGen_evenCup_zero` discharges the sum. Correct.

**Is `Variance.lean` genuinely not needed?** Substantively **yes**, with a wording
defect. Findings:

* No declaration of `MarkedCore/Variance.lean` is used by any of the three modules.
  The only textual occurrences of `mFrameMatrix` in all three files are the two
  prose lines of `MNielsenGenerators.lean`'s own docstring (lines 76-77).
* The matrix the cup computation produces, read off `mNielsenGen_char_mark_*`, is
  the column-convention

  ```
  column of t   (1, 0, 0, 0)
  column of B   (tau, 1, parity B_c, 0)
  column of C   (0, 0, 1, 0)
  column of D   (parity B_c, 0, parity e, 1)
  ```

  which is **exactly** the transpose of `Variance.mFrameMatrix_of_realizes`'s

  ```lean
    mFrameMatrix B ξ = Matrix.of ![![1, 0, 0, 0], ![p.tau, 1, mParityZ p.bc, 0],
      ![0, 0, 1, 0], ![mParityZ p.bc, 0, mParityZ p.e, 1]]
  ```

  The note's prediction is confirmed entry by entry, without the dictionary being
  invoked.
* **But** `Variance.lean` *is* in the transitive import closure of both
  `MNielsenGenerators` and `NNielsenFactorization` (measured: 728 GQ2-internal
  modules each, `Variance` present, reached through
  `GQ2/Dyadic/Instances/StageAbstractionEvenFrameCore.lean`, the only direct
  importer in the tree). And `IsMStabilizer`, which
  `mNielsenGen_stabilizer_induced` takes as a hypothesis, *is defined in terms of*
  `mFrameMatrix`. So the sentence "nothing here reads `M.lean`'s row-convention
  `mFrameMatrix`" is literally false. See FLAG-2.

## 4. The W363-MCONSOL consolidation

Every claim in `docs/dyadic/w363-mconsol-note.md` that this lane can check
mechanically was checked. All pass; no defect was found.

### 4.1 The renames

Exhaustive grep over `GQ2/` for every spelling in the rename map:

| declaration | file | status |
| --- | --- | --- |
| `mFullStabilizer_lift_of_interfaces` | `MFullFrameStages.lean:251` | present, sole owner of the composition shape |
| `mFullStabilizer_lift` | `MFullStabilizerLift.lean:144` | present, the unconditional theorem |
| `mFullStabilizer_lift_of_frame` | `MFullStabilizerLift.lean:159` | present, alias |
| `mFullStabilizer_lift_iff` | `MFullStabilizerLift.lean:238` | unchanged |
| `mFullStabilizer_lift_of_initialLift` | `MFullFrameStages.lean:327` | unchanged |
| `mFullStabilizer_lift_of_fixedHead` | `MFrameMatrixLift.lean:1105` | unchanged |
| `mBasis_mFullStabilizer_lift_of_initialLift` | `MPlaneAmbientStage.lean:384` | unchanged |

No occurrence of `mFullStabilizer_lift` anywhere in the tree still names the
composition shape: the four `MFullFrameStages.lean` hits and the three
`MFrameCupCoordinates.lean` hits are all the `_of_interfaces` spelling. The alias is
definitionally the theorem, checked by this lane's probe:

```lean
example : @mFullStabilizer_lift = @mFullStabilizer_lift_of_frame := rfl
```

which elaborates. The sibling Nielsen lane's seven references to the old spelling
(`MNielsenGenerators.lean`) therefore keep elaborating, as the note predicted, and
the module compiles clean (section 5).

### 4.2 The moved re-exports

Both are still `theorem`s, both are in their new home, both are pinned:

```
GQ2/Dyadic/MarkedCore/MBasisRowRefinement.lean:76:theorem mHead_mRelWord_shift_eq_evenRawDbarWord
GQ2/Dyadic/MarkedCore/MBasisRowRefinement.lean:91:theorem mHead_mRelWord_shift_eq_nRelWord_shift
GQ2/Dyadic/MarkedCore/MBasisRowRefinement.lean:276-277:#print axioms (both)
```

and the second is now proved *from* the first, as the note says. `MHeadCleanup.lean`
no longer imports `StageAbstractionEvenRawSpan` (its three imports are `Cores`,
`FreeProTwoCharacterCorrection`, `Roe.Labute.AdditiveCharacters`), and the note's
statement that `MBasisRowRefinement` still imports it directly is correct.

### 4.3 No consumer broken

Nothing outside `GQ2.lean` imports any of the three Nielsen modules except
`NNielsenFactorization`'s own import of `NNielsenGenerators`. All three are
registered:

```
GQ2.lean:1454:import GQ2.Dyadic.MarkedCore.MNielsenGenerators
GQ2.lean:1455:import GQ2.Dyadic.MarkedCore.NNielsenGenerators
GQ2.lean:1456:import GQ2.Dyadic.MarkedCore.NNielsenFactorization
```

All three recompile clean against the shared cache at this base (section 5), which
exercises the renamed and moved declarations through their whole import chain.

### 4.4 The pin count, recounted

The nine consolidated M modules still carry **217** `#print axioms` lines at this
base, unchanged from the note's figure:

| module | pins |
| --- | ---: |
| `MHeadCleanup` | 5 |
| `MFullFrameCompactness` | 25 |
| `MFullFrameStages` | 12 |
| `MInitialCupDepth` | 9 |
| `MFrameCupCoordinates` | 16 |
| `MBasisRowRefinement` | 11 |
| `MFrameMatrixLift` | 111 |
| `MPlaneAmbientStage` | 18 |
| `MFullStabilizerLift` | 10 |
| **nine-module total** | **217** |

W363 and W364 add three modules on top, so **the current MC-M/MC-N pin total is
397**:

| module | pins | all std-3? |
| --- | ---: | --- |
| `MNielsenGenerators` | 70 | yes |
| `NNielsenGenerators` | 16 | yes |
| `NNielsenFactorization` | 94 | yes |
| **three-module subtotal** | **180** | |
| **grand total with the nine** | **397** | |

The note's "216 std-3 and `mStageOneLe` on `[propext]` alone" is consistent with
what is in the tree: `mStageOneLe` is `MFullFrameCompactness.lean:37`,
`le_trans one_le_two ha`, which cannot pin more than `propext`.

### 4.5 `MFrameModel h = NFrameModel h` by `rfl`

Still true. This lane's probe

```lean
example (h : ℕ) : MFrameModel h = NFrameModel h := rfl
```

elaborates against the current tree. This is what makes `nFrameModel_map_t`
reusable at M, which the consolidation's FLAG-1 rewrite relies on.

## 5. Hygiene and verification of record

All three modules were separately recompiled by this audit lane with

```
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/<module>.lean
```

against the shared dependency cache at base `d2056503`. `lake` was never invoked,
in any form; `scripts/check_dyadic.sh` was never run; the shared cache was never
written to. Results:

| module | exit | wall | declarations | pins | axiom set |
| --- | ---: | ---: | ---: | ---: | --- |
| `MNielsenGenerators.lean` | 0 | 11.1 s | 70 | 70 | `propext, Classical.choice, Quot.sound` |
| `NNielsenGenerators.lean` | 0 | 8.2 s | 16 | 16 | `propext, Classical.choice, Quot.sound` |
| `NNielsenFactorization.lean` | 0 | 14.3 s | 94 | 94 | `propext, Classical.choice, Quot.sound` |

**Every one of the 180 pins prints exactly the standard three**, with no other
output of any kind: parsing the three dumps leaves no non-pin text, so there were
**no errors and no warnings** at default limits, with `autoImplicit=false` and
`relaxedAutoImplicit=false` as the runner sets them.

The five headline statements pin individually:

```text
'GQ2.Dyadic.MarkedCore.mNielsenGen_finite_list' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mNielsenGen_stabilizer_induced' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.nNielsen_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.nNielsenFac_finite_list' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.nNielsenFac_stabilizer_induced' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so in particular the B8 peripheral axiom is **not** in the footprint of either
finite-list artifact.

Other hygiene, all clean:

* no `sorry`, no `admit`, no `native_decide`, no `set_option` of any kind, no bare
  `axiom`, no `opaque`, no `@[implemented_by]` in any of the three modules;
* pin-block completeness, machine-checked by this lane: 70/70, 16/16, 94/94
  top-level declarations pinned, **zero missing, zero stale** in all three. (The
  four `example`s in `NNielsenFactorization`'s stress section are anonymous and
  cannot be pinned; they are instantiations of already-pinned theorems.)
* all three registered in `GQ2.lean`, lines 1454-1456, in dependency order.

These are default **incremental source compilations against the shared dependency
cache**, not a source-only transitive rebuild. They do not extend the historical
frozen clean-build report. Final integration verification remains a parent-owned
step.

## 6. Prose versus statements: FLAGGED items

### FLAG-1 (medium, comment-only): the M3 group-level lift, module docstring versus lane note

`MNielsenGenerators.lean:45-48` says:

> Families M1 and M2 do have honest independent group-level lifts elsewhere in the
> repo (`M.lean`'s `mLambdaEquiv` and HM4's `dmTauDEquiv`); families M3 through M7
> do not, and this file does not supply them.

`docs/dyadic/w363-nielsen-note.md`, "What this does NOT do", item 1, says the
opposite about M3:

> **M3** is the S2 unit scaling, built in `MarkedCore/MScaling.lean` at handle level
> zero. **M4, M5, M6, M7** are the S3 residue and have no group-level construction
> anywhere in the repo. If the owner reads the packet sentence as demanding
> generator-level lifts, the outstanding work is exactly those four families.

The note is closer to the truth. `GQ2/Dyadic/MarkedCore/MScaling.lean:497` has

```lean
noncomputable def mScaleEquiv : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type)
```

with `chiM_mScaleEquiv` (orientation preserved) and `mScaleEquiv_C_row` (every
additive character sees `toAdd (f (mScaleEquiv R α u C)) = u * toAdd (f C)`), and
`mScalingHypothesis_zero (α : ℕ) : MScalingHypothesis α 0` discharges the binder
from the repository's own B8 witness. That is a genuine group-level M3 automorphism
of `D_M` at handle rank zero.

The docstring is nevertheless defensible on the narrower reading that
`MScalingHypothesis` pins only the `C` row, not the whole M3 frame action including
the memo's coupled `A ↦ A·C₀^{m(1−γ)}` correction, so `mScaleEquiv` is not stated to
induce `mNielsenGenM3 γ` on the full frame. **Recommendation**: replace the
docstring sentence with the narrower and correct one, naming `MScaling.lean` and
saying what is and is not pinned there. As written, a reader of the two documents
gets flatly contradictory answers to "which M families have group-level lifts", and
the difference matters because it is exactly the owner's adjudication in item 1 of
the note: four families outstanding, or five.

### FLAG-2 (low, comment-only): "nothing here reads `mFrameMatrix`"

`MNielsenGenerators.lean:75-77`, and the identical sentence in
`docs/dyadic/w363-nielsen-note.md`:

> `MarkedCore/Variance.lean` is therefore not an input: nothing here reads `M.lean`'s
> row-convention `mFrameMatrix`, so no transposition has to be arranged.

Literally false in two ways: (i) `Variance.lean` is in the transitive import closure
(section 3), and (ii) `IsMStabilizer`, the hypothesis of
`mNielsenGen_stabilizer_induced`, unfolds to a condition on `mFrameMatrix`, so the
row-convention matrix *is* read, as a hypothesis passed straight through to
`mStabilizer_classification`. The substantive claim, that no declaration of
`Variance.lean` is used and that the cup computation arranges no transposition, is
**correct**, and was independently confirmed here, including the predicted transpose
relationship to `mFrameMatrix_of_realizes`. **Recommendation**: "no declaration of
`Variance.lean` is used, and nothing here *computes with* `M.lean`'s row-convention
`mFrameMatrix`: it appears only inside the `IsMStabilizer` hypothesis, which is
handed straight to `mStabilizer_classification`."

### FLAG-3 (low, comment-only): an unformalized minimality claim stated flatly

`docs/dyadic/w364-nfactor-note.md`, T2:

> Four slots cannot do it uniformly: any word with a single `F` has `(1,1)` entry
> `1` when its `(0,1)` entry vanishes, so `diag(1, u)`, `u ≠ 1`, needs the fifth.

There is no Lean declaration behind this, and the note does not mark it as
unformalized at the point of use (caveat 5 further down hedges the *eight*-slot
bound, not this one). The conclusion is in fact **true**, and this lane checked it: a
four-slot word normalizes, via `diag(κ,1)·E(x) = E(κx)·diag(κ,1)` and
`diag(κ,1)·F(y) = F(y/κ)·diag(κ,1)`, to `W·diag(κ,1)` with `W` a three-elementary
word; `diag(1,u)` then forces `W = diag(u⁻¹,u)`, which lies in neither `EFE` nor
`FEF` for `u ≠ ±1`. But the one-line argument as written covers only the single-`F`
arrangements, not the two-`F` ones, and a reader cannot tell that the sentence is a
note-level claim rather than a theorem. **Recommendation**: mark it "(not
formalized)" and either give the normalization step or weaken to the single-`F` case
it actually argues.

### INFO-1: the memo table's "(+shears)" at N4

`mc-design.md` section 3.4 gives N4's frame action as `σ̄ ↦ κσ̄` **(+shears)**;
`nFamN4 κ` is pure `diag(κ, 1)` with no shear (probe-confirmed by `rfl`). This is
not a defect: the shears are the B8 construction's own business, and the
factorization supplies them separately as N2/N3 slots. Worth a half-line in the memo
or the note so a reader does not go looking for a shear term in `nFamN4`.

### INFO-2: "in the memo order" at M

`MNielsenGenerators.lean:631-632` calls
`Sigma_gamma, Lambda_k, X_b, E_e, Sigma_beta, Y_c, Z_d` "the memo order". It is not
an order the memo gives: `mc-design.md` section 2.4's table is `M1..M7` =
`Λ, E, Σ_γ, Σ_β, X, Y, Z`, and its completeness sketch kills in the order
`Σ_γ, Σ_β, Y_c, Z_d, X_b, Λ_k, E_e`. The order in the list is the one chosen by
`M.lean`'s own `mNielsen_factorization`, whose docstring explains why ("the order
puts the `C̄₀`-writing families first so that they still read the untouched
`B̄`-coordinate"). Suggest "in `mNielsen_factorization`'s slot order".

### INFO-3: one passage made stale by its successor

`docs/dyadic/w363-nielsen-note.md`, section "The N side (MC-N)", says

> **The N-side finite list cannot be produced, because the N-side factorization does
> not exist in the repo.**

and closes with "What the MC-N row still needs: `nFamN1` through `nFamN6` ... and a
completeness theorem". W364 supplied both. As a lane note the passage is a correct
historical record, and `w364-nfactor-note.md` opens by citing it; a one-line forward
pointer in the W363 note would prevent a reader arriving from the docs index from
concluding MC-N is still missing its factorization. Not a defect.

### Prose that was checked and is accurate

Recorded so that a later reader does not re-litigate these:

* the W364 note's coupling display
  `ḡ₁₀·p̄ + ḡ₀₀·q̄ = τ_σ`, `ḡ₁₁·p̄ + ḡ₀₁·q̄ = τ_{x₂}` matches
  `nNielsenFac_couple`'s conclusion exactly under
  `g₁ = ḡ₀₀, g₂ = ḡ₀₁, h₁ = ḡ₁₀, h₂ = ḡ₁₁`;
* the W364 note's `k = τ + p̄·q̄ read in ℤ₂ through ZMod.val` matches the Lean witness;
* the W364 note's slot list, its "seven slots carry a free 2-adic parameter and the
  eighth is a Boolean correction that is the identity when `g₁₀` is a unit", and its
  five honesty caveats are all accurate;
* the W363 note's displayed column-convention matrix is correct entry by entry, and
  its claim that it is the transpose of `mFrameMatrix_of_realizes`'s is correct;
* the W363 note's "`alpha >= 2` ... that is where the binder is used" is correct and
  the binder is genuinely load-bearing;
* the W363 note's handles paragraph, including the "weaker statement within easy
  reach and *not* claimed here", is accurate: `mNielsenGen_coord_*` and
  `mNielsenGen_character_apply` are indeed stated at general `h`, and only the
  `evenCupForm` expansion is specialized to `h = 0`;
* `docs/dyadic/w363-mconsol-note.md` is accurate on every point checked (section 4).

## Explicit nonclaims of this audit

* This audit does not certify the packet's MC-M or MC-N row as accepted. Caveat 3
  of the verdict, the compactness-supplied per-generator lifts, is the owner's
  adjudication, exactly as `docs/dyadic/w363-nielsen-note.md` says; this lane
  confirms that the adjudication is still open and that nothing in the tree
  pre-empts it.
* This audit does not re-verify wave 361/362's `mFullStabilizer_lift` /
  `nFullStabilizer_lift` themselves. Those are the subject of
  `docs/dyadic/w363-m-full-stabilizer-independent-audit.md` (PROVED AS STATED) and
  `docs/dyadic/w361-n-full-stabilizer-independent-audit.md` (PASS), and are taken
  as given here.
* This audit does not re-verify `mStabilizer_classification`,
  `nStabilizer_classification`, `M.lean`'s `mNielsen_factorization` or
  `NStabParam.rows_isCupIsometry`. Their *statements* were read and matched against
  what the Nielsen modules consume; their proofs were not re-audited.
* Nothing here is a claim about handle rank `h > 0`, about `alpha <= 1`, or about a
  source-only transitive rebuild.
