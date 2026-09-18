# W364-NFACTOR: the N frame-stabilizer factorization into the six Nielsen families

Lane W364-NFACTOR of the general-K campaign. Base `3d64cd99`, branch `claude/w364-nfactor`,
Lean 4.31.0-rc2. New module: `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean` (94 pinned
declarations, all std-3). No existing module was edited; `GQ2.lean` untouched; not pushed.

## What the lane was asked for

Wave 363 (`docs/dyadic/w363-nielsen-note.md`, "The N side") found that the packet's **MC-N**
finite-list artifact could not be produced because the N-side factorization did not exist:
no `nNielsen_factorization`, no `nFamN1` to `nFamN6` anywhere under `GQ2/`, the six families
only a table in `docs/dyadic/mc-design.md` section 3.4, and the completeness argument ("N2/N3
generate `SL_2(Z_2)` on the block, N4 supplies the determinant") unformalized. This lane
supplies exactly that half, in the shape of `M.lean`'s `mNielsen_factorization` and
`MNielsenGenerators.lean`'s `mNielsenGen_finite_list`. Everything in this note was verified
against the Lean, not relayed.

## T1: the six families as frame actions

* `NStabParam.act (P) (v : NVec) : NVec`, the N twin of `MStabParam.act`. On `(τ_v, a, b, c)`
  in the basis `(t, x̄₁, σ̄, x̄₂)`:

  ```
  (τ_v + ā·τ + b̄·τ_σ + c̄·τ_{x₂},  a,  a·p + b·g₀₀ + c·g₀₁,  a·q + b·g₁₀ + c·g₁₁)
  ```

  with bars the `nRed` reductions. `act_t`, `act_x1`, `act_sigma`, `act_x2` check that the
  four basis rows are `NRows.col` at `NStabParam.rows` on the nose, so the factorization really
  is about the classified frame action. (`N.lean` had no such action; its classification
  `nStabilizer_classification` is stated on `NRows`, the three non-torsion columns.)
* The families, as `NStabParam` values `⟨τ, p, q, τ_σ, τ_{x₂}, g⟩`:

  | family | value | frame action |
  |---|---|---|
  | `nFamN1 k` | `⟨nRed k, 0, 0, 0, 0, 1⟩` | `τ = k mod 2` |
  | `nFamN2 k` | block `E(k) = [[1, k], [0, 1]]` | `x̄₂ ↦ x̄₂ + k·σ̄` |
  | `nFamN3 k` | block `F(k) = [[1, 0], [k, 1]]` | `σ̄ ↦ σ̄ + k·x̄₂` |
  | `nFamN4 κ` | block `diag(κ, 1)` (`nPlaneDet κ`) | `σ̄ ↦ κ·σ̄` |
  | `nFamN5 p` | `⟨0, p, 0, 0, nRed p, 1⟩` | `x̄₁ ↦ x̄₁ + p·σ̄`, coupled `x̄₂ ↦ (p mod 2)·t + x̄₂` |
  | `nFamN6 q` | `⟨0, 0, q, nRed q, 0, 1⟩` | `x̄₁ ↦ x̄₁ + q·x̄₂`, coupled `σ̄ ↦ (q mod 2)·t + σ̄` |

  N2, N3, N4 are instances of the pure block parameter `nNielsenFacBlock g = ⟨0,0,0,0,0,g⟩`,
  whose action is the matrix action of `g` on the column `(b, c)`; `nNielsenFacBlock_act_comp`
  says composition of block actions is matrix multiplication. The block matrices are the repo's
  own `planeElemU`, `planeElemV` (HM3) and `nPlaneDet` (`N.lean`).
* `nFamN1_act` to `nFamN6_act` are the closed forms; `nFamN1_admissible` to
  `nFamN6_admissible` check `NStabParam.Admissible` (unit determinant and the two couplings) for
  every member.

## T2: the factorization, eight slots

`nNielsenFac_gl2_factor (g) (hg : IsUnit g.det)`:

```
∃ w x y z, (w = 0 ∨ w = 1) ∧ g = F(w) · diag(det g, 1) · E(x) · F(y) · E(z)
```

the **bounded** form of `N.lean`'s `nGL_factor` (which only gives membership in a submonoid
closure, hence no fixed slot count). Proof, by hand as the ticket allowed: if `g₁₀` is a unit,
`g = diag(δ, 1)·E((g₀₀ − δ)δ⁻¹g₁₀⁻¹)·F(g₁₀)·E((g₁₁ − 1)g₁₀⁻¹)` outright, a `Matrix.mul_fin_two`
identity closed by three `linear_combination`s over the unit relations; otherwise `Z_2` being
local makes `g₀₀` a unit (`ad − bc` is), hence `g₁₀ − g₀₀` a unit, and `F(−1)·g` is in the first
case. Four slots cannot do it uniformly: any word with a single `F` has `(1,1)` entry `1` when
its `(0,1)` entry vanishes, so `diag(1, u)`, `u ≠ 1`, needs the fifth.

`nNielsen_factorization (P : NStabParam) (hP : P.Admissible)`:

```
∃ (k q p w x y z : Z_2) (κ : Z_2ˣ), (w = 0 ∨ w = 1) ∧ (κ : Z_2) = P.g.det ∧
  P.act = (nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
          (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act
```

**The exact slot list, leftmost applied first:**

```
N2(z), N3(y), N2(x), N4(κ), N3(w), N5(p), N6(q), N1(k)          (8 slots)
```

with `κ = det g`, `w ∈ {0, 1}`, `(x, y, z)` from `nNielsenFac_gl2_factor`, `p, q` the
parameters of `P` itself, and `k = τ + p̄·q̄` read in `Z_2` through `ZMod.val`. Seven slots carry a
free 2-adic parameter; the eighth, `N3(w)`, is a Boolean correction that is the identity when
`g₁₀` is a unit. This is the memo's recipe ("kill the block by N2 to N4, then `(p, q)` by N5/N6,
then `τ` by N1") followed literally, in the order the memo gives.

**The coupling check the ticket asked for.** The block families do not touch the `t`-slot.
After the block, N5 then N6 add `c̄'·p̄ + (ā·p̄ + b̄')·q̄` to it, where `(b̄', c̄') = ḡ·(b̄, c̄)`, and
N1 adds `ā·k̄`. Matching against `ā·τ + b̄·τ_σ + c̄·τ_{x₂}` needs `k̄ = τ + p̄q̄` and

```
ḡ₁₀·p̄ + ḡ₀₀·q̄ = τ_σ,     ḡ₁₁·p̄ + ḡ₀₁·q̄ = τ_{x₂},
```

which is exactly what the two `Admissible` couplings `p̄ = τ_{x₂}ḡ₀₀ + τ_σḡ₀₁`,
`q̄ = τ_{x₂}ḡ₁₀ + τ_σḡ₁₁` give once `det ḡ = 1` (`nNielsenFac_couple`, a `decide` over the `2⁶`
assignments). So the couplings are consumed exactly once, and they are necessary and sufficient
for the `t`-slot to close; nothing else in the proof sees them.

The statement is `α`-free: no `2 ≤ α` binder, because nothing in the N stabilizer depends on
`α` (memo §3.3, "completely α-independent"), and the unused-variable linter would flag one. The
ticket's suggested signature carried `ha`; the actual-frame statements below do.

## T3: the artifact

* `nNielsenFacMap P : NFrameModel 0 → NFrameModel 0` carries `P.act` onto the actual full
  rank-four frame (empty handle tail untouched); multiplicative (`nNielsenFacMap_mul`),
  continuous (`nNielsenFacMap_continuous`, through `continuous_nRed`), and `nNielsenFacEquiv`
  packages a mutually inverse pair as a `ContinuousMulEquiv`.
* Orientation, for **every** parameter: the integral `x̄₁` coordinate is fixed on the nose
  (`nNielsenFacMap_coord_x1`, by `rfl`), which is `nFrameOrientation_preserved_iff`'s concrete
  form (`nNielsenFac_orientation`).
* Cup, for every **admissible** parameter: `nNielsenFac_mat` shows the reduced mod-two matrix
  `nNielsenGenMat` (W363) of the frame action is `NRows.mat` at `P.rows`, entry by entry; then
  W363's `nNielsenGen_cup_of_mat` and `N.lean`'s `NStabParam.rows_isCupIsometry` give
  `NFrameCupIsometry` (`nNielsenFac_cupIsometry`). This is the consumer W363 built the bridge
  for.
* Lifts: `nNielsenFacLifts_of_param` feeds both to `nFullStabilizer_lift`.
* `nNielsenFacN1` to `nNielsenFacN6`: the families as honest continuous automorphisms, each
  inverted inside its own family (`nNielsenFac_N*_inv`; the block ones through
  `planeElemU_mul_planeElemU`, `planeElemV_mul_planeElemV`, `nPlaneDet_mul`).
* `nNielsenFacList z y x κ w p q k` = `[N2 z, N3 y, N2 x, N4 κ, N3 w, N5 p, N6 q, N1 k]`,
  `nNielsenFacCompose` the leftmost-first composite, and `nNielsenFacCompose_list` is `rfl`.
* **`nNielsenFac_finite_list (ha : 2 ≤ α) (P) (hP : P.Admissible)`**, the MC-N twin of
  `mNielsenGen_finite_list`: there are parameters such that the list has length 8, every
  member preserves `nFrameOrientation`, is an `NFrameCupIsometry`, and lifts
  (`NNielsenFacLifts`, verbatim the conclusion of `nFullStabilizer_lift`), the composite of the
  list is `nNielsenFacMap P`, and the composite lifts. `nNielsenFac_param_realized` projects the
  list away.
* **Quantifier closure.** `nNielsenFacRows ha phi : NRows` reads the rows of a continuous frame
  automorphism; `nNielsenFac_frameAction_of_rows` shows an automorphism whose rows are `P.rows`
  *is* `nNielsenFacMap P` (hom-extensionality on the canonical marks,
  `nNielsenFac_frame_hom_ext`, plus the automatic `t`-row `nFrameModel_map_t`). Hence
  `nNielsenFac_stabilizer_list`: every `phi` with `IsNStab α (nNielsenFacRows ha phi)` is the
  composite of the list, with all members and the composite lifting; and
  `nNielsenFac_stabilizer_induced`: every continuous automorphism `xi` of the rank-four
  abelianization whose rows in the canonical frame (`nNielsenFacTransport`,
  `nNielsenFacTransport_mark`) satisfy `IsNStab` is induced by a `chiN`-preserving continuous
  automorphism `Psi` of `D_N` with the exact square `abMk (Psi x) = xi (abMk x)`. The N side has
  no `IsNStabilizer`-style predicate on abelianization automorphisms with an abstract `chi`; the
  classification's own vocabulary is `IsNStab` on rows, and that is what is closed here.
* **The per-family route** (not asked for; it answers W363's caveat 1 at N).
  `nNielsenFac_fullFrameMark` identifies `NStabilizerFullRows.fullFrameMark P 0 i` with
  `nNielsenFacMap P` at the `i`-th mark, so `nStabParam_fullFrame_lift_general` (std-3, from
  `NStabilizerFullLift.lean`) gives `nNielsenFacLifts_of_param_families`: every list member is
  *also* lifted, with the same exact square, by the automorphism assembled from the families'
  own constructions (N1, N2, N3: the exact `dnTauBEquiv`, `dnTauDEquiv`, `dnTauCEquiv`; N5, N6:
  `nMixPairHypothesis_coreMix`; N4: `nPlaneScalingHypothesis_general`; then `nTorsionAdjust`).
  `nNielsenFacList_lifts_families` is the list form.

## Honesty caveats

Wave 363's caveats apply, with one difference at N.

1. **The lifts of `nNielsenFac_finite_list` come from the compactness theorem**
   `nFullStabilizer_lift`, not from generator-level constructions, exactly as at M. The
   per-family route is a second, independent theorem, but its N4 ingredient
   `nPlaneScalingHypothesis_general` is itself a compactness limit of the N-plane stages
   (`NPlaneCompactness`), so it is **not** true that every generator is lifted by a closed
   formula: N1, N2, N3 are, N5 and N6 are the `CoreMix`/`ClearWide` constructions, N4 is not.
   Nothing here relabels either compactness proof as a finite-list proof; the finite list is the
   new object.
2. **"Finite list" means finitely many families.** Eight slots, one member of each per
   stabilizer element; the stabilizer `(Z/2 × Z_2²) ⋊ GL_2(Z_2)` is not finitely generated as an
   abstract group.
3. **Handles do not fall out for free.** Everything is at `h = 0`, since
   `nStabilizer_classification` is a rank-four statement. The lifting halves
   (`nFullStabilizer_lift`, `nStabParam_fullFrame_lift_general`) are general in `h`; the frame
   action, the factorization and the list are not, and a classification of the handle-mixing
   stabilizer would be needed first. (The `GL_2` factorization itself is `h`-free and would also
   serve the handle planes.)
4. `α ≥ 2` wherever the actual frame is involved; the parameter-level statements (T1, T2) are
   `α`-free.
5. The bound is a bound for this slot list, not a proof of minimality of eight overall; the
   note above only shows that the *block* cannot be done in four slots of the `E, F, diag(κ,1)`
   families uniformly.

## What remains

* Nothing on the MC-N row's finite-list artifact at rank four as the packet words it, modulo
  caveat 1, which is the owner's call (the same call as at M, but with the per-family route
  available at N).
* A stress section (`nNielsenFac_id_admissible` and four `example`s) pins the identity
  parameter through the eight slots, the list at `α = 2`, N5 at `p = 1` moving the torsion
  slot and at `p = 2` not, and the block factorization at the identity matrix (the branch
  where the Boolean slot does real work).
* Not registered in `GQ2.lean` (never edited by a lane); the orchestrator registers.

## Verification

```
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean
scripts/mirror.sh sweep && scripts/mirror.sh gen GQ2.Dyadic.MarkedCore.NNielsenFactorization
```

against the shared cache at base `3d64cd99`: no errors, no warnings, every one of the 94
`#print axioms` lines prints `[propext, Classical.choice, Quot.sound]`; no `sorry`, `admit`,
`native_decide`, resource option or new axiom; default heartbeats, `autoImplicit=false`. The
module imports `NNielsenGenerators` (W363) and `NStabilizerFullLift`; nothing imports it.
