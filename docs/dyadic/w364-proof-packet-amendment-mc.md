# W364 proposed packet amendment: the MC-M and MC-N obligations

**PROPOSAL for the owner. Not approved, not an acceptance record, not an edit to
the packet.** 2026-09-17, lane W364-PACKET, base `d2056503`. This note proposes
replacement wording for two places in the vendored proof packet
`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex`: the per-core
lifting assertion inside `prop:marked-reduction` (lines 732-735) and the MC-M /
MC-N rows of the remaining-theorem inventory (lines 1077-1082). It edits
nothing. It is the MC companion of
[the W361 amendment](w361-proof-packet-amendment.md), whose section 4 covers the
same ground for MC-N at the earlier state of the tree; where the two differ,
this note is the later one and says so explicitly.

Verified facts, proposed wording, and owner decisions are kept in separate
labelled sections below. Section 2 is measurement. Sections 3 and 4 are
proposals. Section 5 is the decision. Section 6 records where the inputs
contradict each other.

## 0. What this note does not touch

No Lean, no `generated/`, no packet TeX, no ledger, no freeze, no census, no
release record, and no existing W361 amendment or readiness document. The
companion readiness rows are in
[w364-acceptance-readiness-mc.md](w364-acceptance-readiness-mc.md).

The standing field scope is unchanged. Everything below is about the standard
cores `D_M` and `D_N`. It certifies no field endpoint, adds no field coverage,
and eliminates none of the general endpoint's inherited local axioms.

## 1. The obligations as they stand

### 1.1 The per-core assertion

`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex:732-735`, inside
`prop:marked-reduction`:

```tex
\emph{Every automorphism of \(D_P^{\mathrm{ab}}\) preserving the canonical
orientation, the torsion relation vector, and the mod-\(2\) cup form that
occurs in the marked Smith--Witt classification lifts to an automorphism
of \(D_P\).}
```

### 1.2 The inventory rows

`...:1077-1082`:

```tex
MC-M & Marked automorphism lifting for the rank-four \(M_\alpha\) core &
A finite list of orientation-preserving Nielsen generators lifts the
Smith--Witt stabilizer on the abelianization; composition gives every
required marking correction.\\
MC-N & Marked automorphism lifting for the rank-four \(N_\alpha\) core &
Same criterion for the \(N\)-relation vector and cup form.\\
```

### 1.3 A numbering correction, offered separately

The assertion of 1.1 sits in the eighth numbered `\section` of the packet,
`\label{sec:marked}`, so in the compiled document it is **Section 8**, with the
marked-core certificate as Definition 8.1 and the reduction as Proposition 8.2.
The lane brief for this wave and `docs/dyadic/refs/README.md` line 19 both call
it section 7 and "Def. 7.1 + Prop. 7.2". The inventory is Section 14, as those
sources say. Proposed: cite these obligations by label
(`prop:marked-reduction`, `def:core-certificate`) or by line range, not by
number, and correct the README line if the packet is reprinted. This is a
citation repair, not a mathematical change.

## 2. Verified facts

Every statement in this section was read from the Lean source in this
worktree at `d2056503` and is quoted verbatim. The axiom pins were measured by
this lane, not relayed.

### 2.1 The two full-stabilizer lifting theorems

`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean:144` and `:238`:

```lean
theorem mFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
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

`GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean:80`:

```lean
theorem nFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
    (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))) ↔
    (∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z) ∧
      NFrameCupIsometry ha phi
```

`mFullStabilizer_lift_of_frame` is retained as a definitional alias of
`mFullStabilizer_lift`; the W363 audits cite the theorem under that older name.

The cup hypothesis is semantic on both sides, quantified over **all** continuous
mod-two characters of the frame
(`MFrameCupCoordinates.lean:80`, `NFrameCupCoordinates.lean:31`):

```lean
def MCupFrameCupIsometry {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) : Prop :=
  ∀ c d : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (phi (mCupFrameCanonicalMark ha h i))))
        (fun i => toAdd (d (phi (mCupFrameCanonicalMark ha h i)))) =
      evenCupForm (fun i => toAdd (c (mCupFrameCanonicalMark ha h i)))
        (fun i => toAdd (d (mCupFrameCanonicalMark ha h i)))
```

### 2.2 The two finite lists and the N factorization

`GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean:685`:

```lean
theorem mNielsenGen_finite_list {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam) :
    ∃ (k b₅ e₅ c₆ d₇ : ℤ_[2]) (β₄ : ℤ_[2]ˣ),
      (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇).length = 7 ∧
      (∀ g ∈ mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇,
        (∀ z, mFrameOrientation ha 0 (g z) = mFrameOrientation ha 0 z) ∧
          MCupFrameCupIsometry ha g ∧ MNielsenGenLifts ha g) ∧
      (∀ z, mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇) z
        = mNielsenGenMap p z) ∧
      MNielsenGenLifts ha
        (mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇))
```

with the list itself literal (`:633`):

```lean
noncomputable def mNielsenGenList {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) :
    List (ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)) :=
  [mNielsenGenM3 gamma, mNielsenGenM1 ha k, mNielsenGenM5 b, mNielsenGenM2 e,
    mNielsenGenM4 beta, mNielsenGenM6 c, mNielsenGenM7 d]
```

`MNielsenGenerators.lean:845`, the same with the packet's own quantifier:

```lean
theorem mNielsenGen_stabilizer_induced {alpha : ℕ} (ha : 2 ≤ alpha)
    (chi : ContinuousMonoidHom (topAbelianization (DM alpha 0 : Type)) ℤ_[2]ˣ)
    (hchiA : chi (abMk (dmA alpha 0)) = 1) (hchiB : chi (abMk (dmB alpha 0)) = -1)
    (hchiC : chi (abMk (dmC alpha 0)) = 1) (hchiD : chi (abMk (dmD alpha 0)) = mUnit alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DM alpha 0 : Type))
      (topAbelianization (DM alpha 0 : Type)))
    (hxi : IsMStabilizer (mNielsenGenFrame ha).toMDecomposition chi xi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
      (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
      (∀ x, abMk (Psi x) = xi (abMk x))
```

`GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:357`, the completeness half
that wave 363 found absent:

```lean
theorem nNielsen_factorization (P : NStabParam) (hP : P.Admissible) :
    ∃ (k q p w x y z : ℤ_[2]) (κ : ℤ_[2]ˣ), (w = 0 ∨ w = 1) ∧ (κ : ℤ_[2]) = P.g.det ∧
      P.act = (nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
        (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act
```

`NNielsenFactorization.lean:758` and `:911`:

```lean
theorem nNielsenFac_finite_list {alpha : ℕ} (ha : 2 ≤ alpha) (P : NStabParam)
    (hP : P.Admissible) :
    ∃ (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]),
      (nNielsenFacList z y x κ w p q k).length = 8 ∧
      (∀ g ∈ nNielsenFacList z y x κ w p q k,
        (∀ v, nFrameOrientation ha 0 (g v) = nFrameOrientation ha 0 v) ∧
          NFrameCupIsometry ha g ∧ NNielsenFacLifts ha g) ∧
      (∀ v, nNielsenFacCompose (nNielsenFacList z y x κ w p q k) v = nNielsenFacMap P v) ∧
      NNielsenFacLifts ha (nNielsenFacCompose (nNielsenFacList z y x κ w p q k))
```

```lean
theorem nNielsenFac_stabilizer_induced {alpha : ℕ} (ha : 2 ≤ alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DN alpha 0 : Type))
      (topAbelianization (DN alpha 0 : Type)))
    (hxi : IsNStab alpha (nNielsenFacRows ha (nNielsenFacTransport ha xi))) :
    ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
      (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
      (∀ x, abMk (Psi x) = xi (abMk x))
```

The M list is seven members of the seven families `mFamM1` to `mFamM7`
(`M.lean:1113-1134`); the N list is eight members of the six families `nFamN1`
to `nFamN6` (`NNielsenFactorization.lean:138-158`), the extra two slots being
the repeated block families `N2`, `N3` and a Boolean `N3(w)` correction that is
the identity when the `(1,0)` block entry is a unit.

### 2.3 Axiom pins measured by this lane

Fresh default-limit elaboration of the four modules with
`bash scripts/w361_lean_runner.sh <source>`, pinned toolchain
`leanprover/lean4:v4.31.0-rc2` against the shared dependency cache. `lake` was
not invoked and nothing was written.

| Module | `#print axioms` lines | Result | Exit |
| --- | --- | --- | --- |
| `MarkedCore/MFullStabilizerLift.lean` | 10 | all `[propext, Classical.choice, Quot.sound]` | 0 |
| `MarkedCore/NFullStabilizerLift.lean` | 6 | same | 0 |
| `MarkedCore/MNielsenGenerators.lean` | 70 | same | 0 |
| `MarkedCore/NNielsenFactorization.lean` | 94 | same | 0 |

180 pins, no exceptions, no errors, no warnings, no `sorry`, no `native_decide`.
This is an incremental re-elaboration against the shared cache, not a
source-only transitive clean build of the tree.

### 2.4 Group-level constructions, as the tree actually has them

This inventory matters only for the alternative to the proposed method
(section 5, Option B), and it is where the existing documents disagree
(section 6, item 3). What this lane verified in the Lean:

| Family | Independent group-level construction | Footprint of that construction |
| --- | --- | --- |
| M1 `Λ_k` | `mLambdaEquiv` (`MarkedCore/M.lean`, MC3) | standard |
| M2 `E_e` | `dmTauDEquiv` (HM4, `MarkedCore/HandleMixClear.lean`) | standard |
| M3 `Σ_γ` | `mScaleEquiv` / `mScalingHypothesis_zero` (`MarkedCore/MScaling.lean:497,531`), `h = 0` | `mScalingHypothesis_zero` consumes axiom **B8** `peripheralCyclotomicAction`; the parameterized form `mScalingHypothesis_zero_of_peripheral` keeps it a hypothesis |
| M5 `X_b` | `mMixFamily_coreMix` (`MarkedCore/CoreMixM.lean:304`), every `b : ℤ_[2]`, every `h`, `2 ≤ α` | standard, but its conclusion is stated on `nuFrame f` for `ℤ₂`-valued characters `f`, so it pins the `ℤ₂` coordinates only and says nothing about the `ZMod 2` torsion coordinate of the full frame |
| M4, M6, M7 | none in the tree | `CoreMixM.lean` section 5 records that the M4/M6/M7 directions are unnecessary for correcting one marking |
| N1, N2, N3 | `dnTauBEquiv`, `dnTauCEquiv` (`MarkedCore/N.lean`), `dnTauDEquiv` (`MarkedCore/HandleMixClear.lean`), exact | standard |
| N5, N6 | `nMixPairHypothesis_coreMix` (`MarkedCore/ClearWide.lean`) | standard |
| N4 | `nPlaneScalingHypothesis_general` (`MarkedCore/NPlaneGeneralScaling.lean`) | standard, but itself a compactness limit of the N-plane stages |

At N these assemble: `nStabParam_fullFrame_lift_general` gives a **second,
independent** lift of every list member
(`nNielsenFacLifts_of_param_families`), so at N each generator carries two
lifts. At M no such assembly exists in the tree, and no declaration relates
`mMixFamily_coreMix`'s `ℤ₂`-frame statement to the full torsion-sensitive
frame automorphism `mNielsenGenM5 b`.

## 3. Proposed replacement wording: the per-core assertion

**Proposed text** for the emphasized statement at lines 732-735, replacing it
in place (the surrounding definition, proposition and proof are unchanged):

> *For each standard core `P` in `{M, N}`, every `alpha >= 2` and every handle
> count `h`: a continuous automorphism of the full topological abelianization
> `D_P^ab`, torsion coordinate included, is induced by a continuous
> automorphism of `D_P` preserving the canonical orientation `chi_P` **if and
> only if** it preserves the transported canonical orientation and the full
> mod-2 cup form. The induced-map equation holds at every element of `D_P`, not
> only at the marked generators, and handles may mix arbitrarily. The torsion
> relation vector is not a hypothesis: it is fixed automatically by every frame
> automorphism, and the constructed lift fixes the corresponding head word
> literally.*

(a) **Lean statements.** `mFullStabilizer_lift_iff` and
`nFullStabilizer_lift_iff`, quoted verbatim in section 2.1, with
`mFullStabilizer_lift` and `nFullStabilizer_lift` as the sufficiency halves.

(b) **What this proves relative to the original wording.** Strictly more, in
five respects, each checked against the quoted statements:

1. **Both directions.** The original asks for sufficiency; the Lean proves an
   `iff`, so the displayed condition is exactly the image of the group-level
   stabilizer in the frame automorphism group.
2. **Torsion-sensitive.** `MFrameModel h` and `NFrameModel h` carry the
   `ZMod 2` torsion coordinate, and the cup hypothesis quantifies over all
   continuous mod-two characters of the frame, its torsion character included.
3. **All handles.** Every binder is general in `h`. The packet's own remark that
   "hyperbolic handles can then be added by standard Nielsen moves preserving
   their commutator product" is replaced by a proof at every `h`, with the
   `2h` handle coordinates carried explicitly.
4. **A smaller hypothesis set.** The original assumes preservation of the
   torsion relation vector. The Lean discharges it: on the frame every
   automorphism fixes the torsion class (the M and N frames are the same Lean
   type, and `nFrameModel_map_t` applies to both), and on the free cover the
   constructed lift fixes the head word literally, which forces the primitive
   relation vector in the original integral coordinates.
5. **The conclusion is on every element, and it is what Definition 8.1 asks
   for.** The lift preserves `chi_P`, which is the first half of that
   definition's clause (iii), and the commuting square is stated for all `x`
   directly on `abMk`, so no transport step is interposed between the theorem
   and `D_P^ab` and the reduction's own proof can feed it into the `nu_K` half
   of the clause exactly as written.

(c) **What this does not prove.** Nothing at `alpha = 1` or `alpha = 0`: the M
side has four named lemmas that are **false** at `alpha = 1`, not merely
unproved, and `MStageStep alpha h` has no producer below `alpha = 2`. The final
`Psi` is not asserted to fix any group generator literally (literal head
fixation is a property of the initial free lift only). And the M cup hypothesis
is the semantic predicate `MCupFrameCupIsometry`; no declaration in the tree
relates it to `M.lean`'s matrix-level `mCupIsometry` / `IsMStabilizer` in
general. At rank four that consumer path is now closed anyway, by
`mNielsenGen_stabilizer_induced`, which takes `IsMStabilizer` and returns the
lift; it is closed by routing through the classification and the seven
families, not by a predicate bridge.

(d) **Axiom footprint.** Standard three, measured (section 2.3). No new axiom.
The general endpoint's own footprint is unchanged by this: standard three plus
the nine standing declarations for the canonical combined endpoint, plus six
for the supplied-bundle endpoint. These core theorems neither add to nor remove
from that list.

(e) **Proof method.** A uniform filtered correction with a compactness limit:
an initial free pro-two basis fixing the head word, the literal depth-three
relator error obtained from cup preservation alone (no orientation hypothesis),
exact filtered stages at every depth retaining the whole initial coordinate
matrix, and a torsion-sensitive compact limit over nested closed stage sets,
with the generator equations lifted to the all-element square by hom
extensionality. It is uniform in `(alpha >= 2, h)`: not a rank sweep, not a
class sweep, not a finite-target test.

## 4. Proposed replacement wording: the section 14 rows

**Proposed rows**, replacing lines 1077-1082 in place:

> **MC-M** | Marked automorphism lifting for the rank-four `M_alpha` core |
> *Discharged, by two theorems with different scopes. (i) The lifting
> assertion of `prop:marked-reduction` holds at every `alpha >= 2` and every
> handle count, as an equivalence, torsion included
> (`MarkedCore.mFullStabilizer_lift_iff`). (ii) At rank four, every element of
> the Smith-Witt stabilizer is the composite of an explicit seven-member list
> drawn from the seven Nielsen families, each member of which preserves the
> orientation and the full mod-2 cup form and therefore lifts, and the
> composite of those lifts induces the given stabilizer element on the nose
> (`MarkedCore.mNielsenGen_finite_list`,
> `MarkedCore.mNielsenGen_stabilizer_induced`). The individual generators are
> lifted by (i), not by seven separate closed-form group constructions.*
>
> **MC-N** | Marked automorphism lifting for the rank-four `N_alpha` core |
> *Same, with `MarkedCore.nFullStabilizer_lift_iff`, and at rank four an
> eight-slot list drawn from six Nielsen families, complete by
> `MarkedCore.nNielsen_factorization`
> (`MarkedCore.nNielsenFac_finite_list`,
> `MarkedCore.nNielsenFac_stabilizer_induced`). At N the list members carry a
> second, independent lift assembled from the families' own constructions
> (`nNielsenFacLifts_of_param_families`), whose `N4` ingredient is itself a
> compactness limit.*

(a) **Lean statements.** Quoted verbatim in section 2.2: for MC-M,
`mNielsenGen_finite_list` and `mNielsenGen_stabilizer_induced`; for MC-N,
`nNielsen_factorization`, `nNielsenFac_finite_list` and
`nNielsenFac_stabilizer_induced`.

(b) **What this proves relative to the original wording.** The original row asks
for a finite list of orientation-preserving Nielsen generators that lifts the
Smith-Witt stabilizer, with composition giving every required marking
correction. All three clauses are now literal Lean:

1. **A literal finite list.** `mNielsenGenList` has `length = 7` by `rfl`;
   `nNielsenFacList` has `length = 8` by `rfl`. Both are explicit lists of
   continuous automorphisms of the actual full frame, not abstract generating
   sets.
2. **Orientation-preserving, and cup-preserving.** Proved for every list
   member by a finite mod-two matrix computation rather than by assuming the
   member comes from a core automorphism; at M the two clauses hold for every
   `MStabParam`, at N orientation holds for every parameter and the cup clause
   for every admissible one. This is
   the step that was previously impossible: before wave 363 the only producer
   of either semantic cup predicate was "it comes from an actual core
   automorphism", which is exactly what one lacks for a family one is trying to
   lift.
3. **Each member lifts, and composition gives the correction.** Each member
   satisfies `MNielsenGenLifts` / `NNielsenFacLifts`, which is verbatim the
   conclusion of the corresponding full-stabilizer theorem; the composite of
   the list is the parameter's frame action; and the composite of the lifts
   lifts that composite.
4. **The literal stabilizer quantifier.** Both `_stabilizer_induced` theorems
   read over every element of the Smith-Witt stabilizer of the rank-four
   abelianization, not over every parameter tuple, and conclude with the exact
   square `abMk (Psi x) = xi (abMk x)`. At M the stabilizer clause is
   `IsMStabilizer` against an abstract orientation character with four pinned
   generator values; at N it is `IsNStab` on the rows of `xi` read in the
   canonical frame.
5. **At N, completeness is new mathematics.** `nNielsen_factorization` is the
   bounded `GL_2(ℤ₂)` factorization `F(w) diag(det g, 1) E(x) F(y) E(z)` with
   `w` Boolean, plus the two admissibility couplings consumed exactly once to
   close the torsion slot. Wave 363 recorded that this did not exist in the
   repo; wave 364 supplied it.

(c) **What this does not prove.**

1. **No generator-level closed-form lifts.** In both list theorems the lifts of
   the individual generators come from the compactness theorems of section 3,
   not from seven or eight separate group-level constructions. At N there is a
   second per-family route, but its `N4` ingredient is itself a compactness
   limit, so even there not every generator is lifted by a closed formula. At M
   the tree has independent constructions for M1 and M2, for M3 only at the
   cost of axiom B8, and for the pure M5 move only on the `ℤ₂` coordinates
   (section 2.4); M4, M6 and M7 have none, and nothing assembles the ones that
   exist into a lift of the list.
2. **No finite generating set, and none is possible.** "Finite list" means
   finitely many *families*, each parameterized by a 2-adic number or unit;
   what either theorem produces for a given stabilizer element is one member of
   each slot. A literally finite generating set does not exist: the stabilizer,
   `(Z/2 x Z_2^2) semidirect GL_2(Z_2)` at N, is not finitely generated as an
   abstract group.
3. **Rank four only, for the lists.** Both list theorems are `h = 0`, because
   both classifications (`mStabilizer_classification`, `nStabilizer_classification`)
   are rank-four statements. The packet rows are themselves explicitly
   rank-four, so this matches the obligation; it is recorded because the
   lifting halves are general in `h` and the two scopes must not be conflated.
   Extending the lists would first need a classification of the handle-mixing
   stabilizer, which the repo does not have.
4. **No minimality.** Seven and eight are the lengths of these slot lists, not
   proved minima. At N it is shown only that the block cannot be done in four
   slots of the `E, F, diag(κ,1)` families uniformly.
5. **No descended orientation character at M.** `mNielsenGen_stabilizer_induced`
   takes `chi` with four pinned generator values, exactly as
   `mStabilizer_classification` does; it does not construct a descended
   `chiMab` and prove that clause redundant. This is `M.lean`'s own recorded
   finding, inherited, not a new gap.

(d) **Axiom footprint.** Standard three for all of it, measured (section 2.3):
70 pins in `MNielsenGenerators.lean`, 94 in `NNielsenFactorization.lean`, all
`[propext, Classical.choice, Quot.sound]`. The general endpoint's separate
footprint is unchanged. Note the direction of the trade in section 5: the
compactness route is std-3, while the only M3 group-level construction in the
tree consumes axiom B8.

(e) **Proof method.** Two ingredients on top of section 3(e). First, the
frame-action factorizations: `mNielsen_factorization` (unconditional, `alpha
>= 2` used once) and `nNielsen_factorization` (`alpha`-free). Second, a
reduction of the semantic cup predicate to a finite mod-two matrix identity, so
that a family with no group-level lift can still be shown to satisfy the
hypothesis of the compactness theorem: at M through the coordinate characters
and `mNielsenGen_cup_core` (a `decide` over `ZMod 2`), at N through
`nNielsenFac_mat` and wave 363's `nNielsenGen_cup_of_mat`.

## 5. The decision this amendment asks for

The mathematical target need not be weakened either way. The decision is which
*proof method* the packet's completion criterion accepts.

**Option A, accept the method.** Adopt sections 3 and 4 as written. The packet
rows are then discharged, with the qualification stated in the rows themselves
that the generators are lifted by the uniform theorem. Consequences: the
artifact exists today; its footprint is standard three; and the acceptance text
must say plainly that no finite-word decomposition of the limit automorphism is
produced, so that no later reader infers an algorithm from the row.

**Option B, require generator-level lifts.** Keep the original row and treat it
as open until each family carries its own closed-form group construction. The
outstanding work is then precisely:

- at M: families **M4**, **M6**, **M7**, with no construction in the tree;
  family **M3**, whose only construction consumes axiom **B8**
  `peripheralCyclotomicAction`, so a B8-free construction or an accepted axiom
  charge is needed; and family **M5**, where `mMixFamily_coreMix` exists but is
  stated on `ℤ₂`-valued characters only, so the torsion coordinate of the full
  frame is not pinned by it;
- at N: family **N4**, whose ingredient `nPlaneScalingHypothesis_general` is
  itself a compactness limit;
- at both: an assembly theorem composing the per-family lifts into a lift of
  the whole list. At N that assembly exists
  (`nStabParam_fullFrame_lift_general`, `nNielsenFacLifts_of_param_families`);
  at M it does not.

Option B costs at least one axiom (B8) unless M3 is rebuilt, which is the
strongest single argument for Option A.

**Sub-decisions raised by either option**, listed for the memo and itemized in
[the readiness note](w364-acceptance-readiness-mc.md):

1. Whether the packet's completion criterion for MC-M and MC-N is the proof
   method or the mathematical assertion. Owner memo wave-362 item 4 already
   frames this for both rows; this wave supplies the finite lists that item 4
   said W363-NIELSEN was attempting, so the item is now a decision on a
   delivered artifact rather than on an expected one.
2. Whether the rank-four scope of the lists is accepted as matching the rows,
   given that the lifting halves are general in `h`.
3. Whether to correct the section numbering and README citation of 1.3.
4. Whether the M docstring inventory of section 2.4 is corrected before the
   rows are adopted (section 6, item 3), since Option B's work list is read
   directly off it.

No owner decision is recorded by this note.

## 6. Where the inputs contradict each other

1. **Section number.** The lane brief and `docs/dyadic/refs/README.md:19` place
   the per-core assertion in section 7 (Def. 7.1, Prop. 7.2). It is the eighth
   numbered section of the packet, so Definition 8.1 and Proposition 8.2. The
   line ranges 732-735 are correct in both sources. See 1.3.
2. **The ledger has no MC-M or MC-N rows.** The lane brief cites
   `docs/dyadic/refs/dyadic-presentations-formalization-ledger.md` for them;
   `grep` finds neither string anywhere in that file. The MC rows exist only in
   the packet TeX, section 14. The ledger's corresponding content is section
   5.1 (`MarkedCoreCertificate`, whose `correction` field is what these
   theorems supply), section 9 item 6 ("rank-four abelian classification and
   automorphism lifting"), section 10 (merge gates) and section 11 ("The
   uploaded TeX does not yet provide the two rank-four marked-core
   certificates"). Proposed: the readiness table cites the packet for the rows
   and the ledger for the structure, and the brief's pointer is corrected.
3. **Which M families have independent group-level lifts: three sources, three
   answers.**
   - `MNielsenGenerators.lean`'s module docstring: "Families M1 and M2 do have
     honest independent group-level lifts elsewhere in the repo ...; families M3
     through M7 do not".
   - `docs/dyadic/w363-nielsen-note.md`: M1, M2 and **M3** do (M3 being
     `MScaling.lean`), and "M4, M5, M6, M7 are the S3 residue and have no
     group-level construction anywhere in the repo".
   - The Lean: `mMixFamily_coreMix` (`CoreMixM.lean:304`) is a group-level
     construction of the pure **M5** move at every `b : ℤ_[2]`, every `h`,
     `2 ≤ alpha`, so both prose claims are wrong at M5; and `MScaling.lean`'s
     M3 construction consumes axiom B8, which neither prose claim mentions.
     `mMixFamily_coreMix` is stated on `ℤ₂`-valued characters, so it does not
     by itself pin the torsion coordinate, which is presumably what the
     docstring was reaching for.

   Nothing in the Lean depends on any of these sentences; the theorems quoted
   in section 2 are unaffected. But Option B's work list is read off exactly
   this inventory, so the proposed repair is: state the inventory as section
   2.4 does, with the footprint column, before the rows are adopted.
4. **A stale hash, and a rename.** `w363-m-full-stabilizer-scope.md` and its
   companion audit pin `MFullStabilizerLift.lean` at SHA-256
   `bac55a1a...36da783`. The current file is `cf6c7bbd...45aebf3`. The two
   intervening commits are `acffa057` (which frees the public name
   `mFullStabilizer_lift` for the unconditional theorem, so the audits' subject
   `mFullStabilizer_lift_of_frame` is now a definitional alias) and `492fe22e`
   (docstrings, including the repair of that audit's FLAG-1). This lane
   verified that the statement text is unchanged. Readers of those audits
   should use the new hash and the new name; the audits' verdicts stand.
5. **A closed W361 remaining-requirement item.** The W361 amendment's section 4
   and readiness item 4 say the MC-N finite-list method "remains distinct" and
   that either the artifact or acceptance of the alternative method is needed.
   The artifact now exists at rank four. The W361 documents are not edited by
   this lane; they carry a one-line dated pointer to this note.
