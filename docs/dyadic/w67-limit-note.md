# W67: the compactness assembly - the `h >= 1` residual, one class at a time

Lane W67-LIMIT.  New module `GQ2/Dyadic/SqCore/GradedLimit.lean`; no edits to existing files.
Prefixes `lim` / `sqClassClearing` / `limFinal`.

## 0.  Headline

The inverse-limit step of the `h >= 1` residual is now committed mathematics:

> **`limFinal_markTransitivity_iff`**:
> `SqLamMarkTransitivity h  <->  forall k, SqClassClearingSupply h k`

where `SqClassClearingSupply h k` is *literally* `SqArbRelWord h` with the relator identity
`sqRelWord (sqArbFrame h nu' j a) = 1` weakened to membership in
`twoCentralSeries (DSq h) k`.  The limit machinery (compactness, closedness, tower
separation) is discharged once and for all; what remains of the residual is the per-class
family, and classes `k <= 2` are already theorems (`sqClassClearingSupply_of_le_two`), so
the honest remainder is

> **`LimFinalResidual h`** := `forall k, 3 <= k -> SqClassClearingSupply h k`,
> with **`limFinal_residual_iff`**: `SqLamMarkTransitivity h <-> LimFinalResidual h`.

The residual now begins at class 3 - exactly where the depth sweeps began measuring.
Every declaration pins to the standard three axioms.

## 1.  The compatibility analysis (the wave's first question)

The assembly needs the per-class solution sets to form an inverse system.  **Verdict:
projects by construction, in the strongest possible form - the sets are nested.**

* The class-`k` solution set is stated *upstairs*: `limClearingSet h nu' j k` is the set of
  dressings `a : Fin (sqRank h) -> DSq h` with exactly trivial `lambda`- and `nu'`-rows, a
  mod-2 independent frame, and relator value in `twoCentralSeries (DSq h) k`.  Only the
  relator clause mentions `k`; the ambient space is the same for every class; the tower is
  antitone.  Hence `limClearingSet_antitone`: a class-`(k+1)` solution *is* a class-`k`
  solution.  No inverse-system functor, no compatible-subsystem repair, no
  solutions-with-memory or tree-of-extensions variant is needed.
* Consequently the Koenig section-selection step of the committed template
  (`Instances/StageAbstractionEvenFinite.lean`, `exists_globalMarking`) collapses into the
  finite-intersection property of a nested family of closed subsets of the compact dressing
  space, run by the same mathlib lemma the template uses
  (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`).  The template's
  `OpenTuple` interface itself does not fit verbatim - it carries one `Z2^x`-valued row
  functional where the clearing problem carries two `Z2`-valued rows plus the independence
  clause - so `GradedLimit` re-instantiates the committed compactness pattern rather than
  invoking the template's theorem.  (Recorded in the module docstring, section 1.)
* **Measured vs provable.**  The sweeps' per-class sets live in the finite level quotients
  (dressings mod `gamma_k`, the torsor at level one, affine cosets deeper); `GradedLimit`'s
  sets live upstairs with exact rows.  Upstairs nonemptiness projects to finite-level
  solvability trivially.  The converse per class is a **row-lifting question** - lift a
  finite-level dressing to one whose `nuLam`- and `nu'`-rows are exactly trivial - which is
  NOT settled here and belongs to the class-`k` attack surface (section 4).  The reduction
  does not consume it: `limFinal_arbRelWord_iff` is an equivalence because a global solution
  restricts to every class.  The affine transition maps of the sweep remain measured; the
  assembly never uses them.

## 2.  The reduction theorem

`limFinal_arbRelWord : (forall k, SqClassClearingSupply h k) -> SqArbRelWord h`, with
corollaries `limFinal_clearingStep`, `limFinal_markTransitivity`, and the equivalences
`limFinal_arbRelWord_iff`, `limFinal_markTransitivity_iff`.  Ingredients, all committed:

1. **Nestedness** (section 1): `twoCentralSeries_antitone`.
2. **Closedness** (`isClosed_limClearingSet`): rows are closed by continuity of the
   characters against closed singletons; the independence clause is an intersection over
   index-two open normal subgroups of finite unions of clopen escape conditions; the relator
   clause is the preimage of the closed `twoCentralSeries (DSq h) k` under the (new,
   `limContinuous_sqRelWord_arbFrame`) continuous relator-of-frame map - the relator shape
   is a group word in the slots, and each slot is a fixed base times the dressing
   coordinate.
3. **Compactness**: the dressing space `(DSq h)^(sqRank h)` is a compact product;
   `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` meets the nested
   nonempty closed family (`limClearingSet_iInter_nonempty`).
4. **Separation**: `lim_iInf_twoCentralSeries` - the committed neighborhood-basis theorem
   `iInf_twoCentralSeries` of `GQ2/Roe/Labute/TwoCentralTower.lean`, instantiated at
   `DSq h` through `dsq_topGen` (in `Finset` form, `lim_dsq_finsetGen`) and `isProP_DSq`.
   A limit dressing's relator value lies in every tower level, hence is `1`.

No finite-quotient argument is asked to conclude on its own, so the discrete obstruction
(the amalgam's marking-transitivity failure, W44) is not in the way: compactness, not a
finite quotient, produces the pro-2 dressing.

## 3.  The committed classes

* `lim_sqRelWord_mem_twoCentralSeries_two`: the relator dies to class 2 at **every** tuple
  of **every** topological group - the core word is two commutators and two squares
  (`sqWord s x y = commP s x * ((x^2)^2)^-1 * y^2 * commP y (conjP y s)`, a free identity),
  and the handle word is a product of commutators.
* `lim_sqArbBase_modTwoIndep`: the undressed frame is mod-2 independent at every marking
  and every handle (index-two escape via the pivot, against `exists_sqGen_notMem`).
* Hence `sqClassClearingSupply_two` (witness: the trivial dressing) and
  `sqClassClearingSupply_of_le_two`.
* **No class `k >= 3` instance is committed today, and none is claimed.**  The class-3
  slice statement of `GradedContain` and the census kills of `GradedCensusAchieve` are
  proved on the *binder* (`SqU4 gr3R`), not on the tower `levelQuot (DSq h) k`; the
  binder-to-tower bridge does not exist in the tree.  Classes 3-6 remain MEASURED
  (w50/w51), exhaustively at 3-4-5 for `h = 1`, census-grade.

## 4.  The class-`k` attack surface

The remaining Prop is `LimFinalResidual h`: for every `k >= 3`, every selected marking and
every handle admit a row-trivial, mod-2 independent dressing whose relator value dies to
class `k`.  Structure of the per-class problem, as measured:

* the linear system at each level has **corank exactly `d + 1`**, `d = sqRank h = 3 + 2h`,
  uniformly in level and marking (w50 section 6.3);
* the defect map `delta_j` and its image depend on the marking **only through the parity
  class `(t mod 2, s mod 2)`** (w51 section 4, verified through class 6);
* `delta` is the **graded Fox form** of the dressing-defect map (w52 section 1), and the
  containment is this-relator-specific (w52 section 4).

What a proof of the general class-`k` step needs, in order:

1. **The graded step as a theorem** (w52 section 7, items 1-2): for the relator, the defect
   of any `K`-dressed frame lies in `im delta` at every level - the conjectured mechanism
   is w52's "the defect of a dressed relator frame is a pure dressing artefact" - together
   with the structural `d - 1` cut (power-substitution families supplying the kernel
   elements no commutator family gives).
2. **The bridge**: convert the graded per-level statement into `SqClassClearingSupply h k`.
   Concretely this is the row-lifting question of section 1: from a dressing mod `gamma_k`
   with graded row conditions, produce `a : Fin (sqRank h) -> DSq h` with *exactly* trivial
   rows and the relator still dead to class `k`.  The concrete sub-question is the joint
   image of `(nuLam, nu')` on `ker (levelMk (DSq h) k)`.
3. **The induction over `k`** then runs inside `LimFinalResidual` with no further limit
   argument - that is what this wave removed.

## 5.  Verification record

* Verification of record, from the worktree root:
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
  GQ2/Dyadic/SqCore/GradedLimit.lean` - clean, no `sorry`, no new axioms.
* Axiom pins: every declaration `[propext, Classical.choice, Quot.sound]` (the tower facts
  consumed are themselves std-3, so the assembly does not even carry fin-gen).
* Full-mirror collision test: `scripts/mirror.sh sweep` (5723 artifacts), then
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedLimit` - generated clean against the
  complete cache mirror.
* Base `1b418341`, cache `c3c62654` (4314 jobs green).
