/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.DRDemushkin
public import GQ2.Roe.CrossedDerivation
public import GQ2.DyadicPresentation
public import GQ2.BoundaryFrame
public import GQ2.Reciprocity

@[expose] public section

/-!
# The marked pro-2 identification `(D_R, ν_R) ≅ (G_{ℚ₂}(2), ν_ur)`  (Roe note §3.3)

**Skeleton (ticket R7; fills are R15, gated through R14's owner-approved B-Lab flip).**
Statements are final; proofs may be `sorry`.

The endgame of the note's §3 ⟦prop:markedpro2⟧: `D_R` carries the unramified marking
`ν_R(s, x, y) = (1, 0, 0)` (note Lemma 2.1 ⟦lem:tame⟧ restricted to the pro-2 quotient, and
eq. (3.6) ⟦eq:BRsplit⟧), and the pair `(D_R, ν_R)` is isomorphic to the fully unramified
marked pair `(G_{ℚ₂}(2), ν_ur)`.  The statement `markedPro2_R` targets **exactly the marked
vocabulary of `prop_3_10_local_marked`** (`GQ2/SectionThreeMarked.lean:60`), since the
boundary-frame layer consumes that shape: the `ℤ₂`-identification `ι : Ztwo ≅ Multiplicative ℤ₂`
is quantified and pinned by `ι(1) = ofAdd 1`, and the `ν_ur`-values are read through arbitrary
lifts as in `prop_1_1`.

## The B-Lab hypothesis (`section Draft`)

The one genuinely new literature input of Route L is Labute's odd-rank `q = 2` classification
([Labute], Théorèmes 4 and 8; note Cor. 3.4 ⟦cor:abstractD0⟧), consumed as the **single
instance** `G := D_R`.  Per the campaign safeguard (plan §3 Route L step 4; b9a `section Draft`
precedent), it enters here as an explicit *hypothesis* `BLabHypothesis : Prop` — **not** an
axiom; the axiom-insertion commit is ticket R14, owner-gated — drafted below for owner review
with its convention docstring.

## Proof route for `markedPro2_R` (fill R15; note §3.3)

1. The invariant quadruple: `isDemushkin_DR`, `demushkinRank_DR`, `demushkinQ_DR`
   (`DRDemushkin.lean`), and the canonical orientation `χ_R` with
   `im χ_R = {±1}×(1+4ℤ₂) = ℤ₂ˣ` (tickets R10/R11, from `isLabuteOrientationDatum_of_root` and
   the Hensel root `X ≡ 5 (mod 16)`).  Feed `BLabHypothesis` to get an abstract
   `f : D_R ≅ D₀`.
2. Marked correction on abelianizations: the unique `b` with `S = X^b` (`zpowZtwo`
   bijectivity; `b ≡ 3 (mod 4)`), the shear basis `k = s̄ − b·x̄`, the unique `u` with
   `η^u = X` (`u ≡ 1 (mod 4)`; `η = (−3)⁻¹`, `GQ2.norm_inv_neg_three`-side facts), and the
   ν- and χ-preserving `φ_ab : B_R ≅ D₀^{ab}`, `t ↦ t₀, k ↦ S̄₀, x̄ ↦ u·Ȳ₀` ⟦eq:desiredab⟧.
3. Correct `f` by `prop_3_8_classification` + `prop_3_8_lift`
   (`GQ2/AnabelianBridge/Classification.lean:342`, `Construction.lean:1089` — both live on the
   `D₀` side and are reused **as-is**), so the corrected isomorphism abelianizes to `φ_ab`,
   hence preserves the full `ℤ₂`-marking; finish with the marked local normalization
   `prop_1_1` (`GQ2/PropOneOneAssembly.lean:298`).

Cross-check numerics for R15 (R2 spike §2.4): `b ≡ 91367 (mod 2²⁰)`, `u ≡ 898793 (mod 2²⁰)`;
mod-2 Gram-isometry seed `s̄ ↦ S̄+Ȳ, x̄ ↦ Ȳ, ȳ ↦ Ā`.
-/

namespace GQ2

/-! ## The unramified marking `ν_R` -/

/-- **`ν_R : D_R → Z₂`** (note Lemma 2.1 ⟦lem:tame⟧ / eq. (3.6) ⟦eq:BRsplit⟧):
`ν_R(s) = 1`, `ν_R(x) = ν_R(y) = 0` — the unramified marking of the Roe pro-2 quotient,
mirroring `GQ2.nuTwo` (`GQ2/BoundaryFrame.lean:228`) with the same target
`Ztwo = maxProPQuotient 2 ℤ̂` and the same marked value `ztwoOne`.  Built by the universal
property of `D_R` (`drLiftHom` = kill the relator on the free profinite group, descend through
the presentation and the maximal pro-2 quotient): every factor of `r₂` has unramified image
zero. -/
noncomputable def nuR : ContinuousMonoidHom (DR : Type) Ztwo :=
  drLiftHom isProP_maxProPQuotient ![ztwoOne, 1, 1] (by
    show drWord ztwoOne 1 1 = 1
    simp [drWord, conjP, commP])

@[simp] theorem nuR_drS : nuR drS = ztwoOne := drLiftHom_S _ _ _

@[simp] theorem nuR_drX : nuR drX = 1 := drLiftHom_X _ _ _

@[simp] theorem nuR_drY : nuR drY = 1 := drLiftHom_Y _ _ _

/-- `ν_R` is surjective (note Lemma 2.1: "it is surjective because `σ` maps to `1`").
Fill (R15): `ztwoOne` topologically generates `Ztwo`, and the image of a continuous hom of
profinite groups is closed — the `nuTwo_surjective` argument (`GQ2/Prop32.lean`) verbatim. -/
theorem nuR_surjective : Function.Surjective nuR := by
  sorry

/-! ## The B-Lab classification hypothesis  (draft for owner review — ticket R14 flips) -/

section Draft

/-- **B-Lab (DRAFT, hypothesis form — not an axiom until the R14 owner gate).**

Labute's classification of Demushkin groups of odd rank with `q = 2`
([Labute], *Classification of Demushkin groups*, Canad. J. Math. **19** (1967), Théorème 4
(uniqueness and image classification of the canonical orientation in the `q = 2` case) and
Théorème 8 (the classification by `(rank, q, im χ)`); note Cor. 3.4 ⟦cor:abstractD0⟧),
specialized to **the single instance consumed by the Roe verification**:

> a pro-2 group that is Demushkin of rank `3` with `q = 2`, and whose canonical orientation —
> characterized à la Labute by the descent of crossed derivations through the relation
> (`IsLabuteOrientation`) — is surjective onto `ℤ₂ˣ = {±1} × (1 + 4ℤ₂)` (the secondary depth
> `f = 2`), is continuously isomorphic to `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩_pro-2`.

Conventions (per the ground rules of `docs/orchestration/formalization-plan.md`):
* `IsDemushkin`/`demushkinRank`/`demushkinQ` are the repo's `Nat.card`-encoded predicates
  (`GQ2/Demushkin.lean`; rank 3 ⟺ `#H¹ = 8`, `q = 2` ⟺ torsion count 2 in the topological
  abelianization).
* The orientation clause is stated against the **descent characterization**
  (`GQ2/Roe/CrossedDerivation.lean`), which is Labute's own definition of the canonical
  orientation for the presented group — *not* the deferred abstract dualizing-module route
  (the `GQ2/Orientation.lean` deviation note); `Continuous χ` is carried separately per the
  `ℤ₂ˣ`-character house style.
* The image invariant `{±1} × (1 + 4ℤ₂)` is the **full** unit group `ℤ₂ˣ` (the `f = 2` case),
  so it is encoded as `Function.Surjective χ` — the same encoding as B3c's
  `DyadicOrientation.surjective_chiTwo`.
* Specializing to `G := D_R` (rather than quantifying over abstract `G`) is deliberate: it
  quarantines exactly the instance used, and the descent-characterized orientation is
  concretely available for `D_R` through its presentation.  See the R7 design memo for the
  abstract-`G` alternative and its cost.

All four antecedents will be discharged by R10–R13 (`isDemushkin_DR`, `demushkinRank_DR`,
`demushkinQ_DR`, and R11's `χ_R`), so consuming code applies this to obtain the abstract
isomorphism of the note's Cor. 3.4. -/
def BLabHypothesis : Prop :=
  IsDemushkin 2 (DR : Type) →
    demushkinRank 2 (DR : Type) = 3 →
      demushkinQ (DR : Type) = 2 →
        (∃ χ : (DR : Type) →* ℤ_[2]ˣ,
          Continuous χ ∧ IsLabuteOrientation χ ∧ Function.Surjective χ) →
          Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type))

end Draft

/-! ## The marked identification -/

/-- **The marked pro-2 identification** ⟦prop:markedpro2⟧ (note Prop. 3.6), in the marked
vocabulary of `prop_3_10_local_marked` (`GQ2/SectionThreeMarked.lean:60`), which the
boundary-frame layer consumes: given the B-Lab hypothesis, there is a continuous isomorphism
`e : G_{ℚ₂}(2) ≅ D_R` matching the unramified markings — the `ℤ₂`-identification `ι` between
the two `ν`-targets is quantified explicitly and pinned by `ι(1) = ofAdd 1`, and the
`ν_ur`-values are read through arbitrary lifts, as in `prop_1_1`.

Fill (R15): the three-step route of the module docstring — B-Lab abstract isomorphism,
`φ_ab`-correction via `prop_3_8_classification`/`prop_3_8_lift` (both on the `D₀` side, reused
as-is), and the `prop_1_1`/`prop_3_10_local_marked` assembly pattern for the `ι`-bridge. -/
theorem markedPro2_R [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (R : LocalReciprocity) (hBLab : BLabHypothesis) :
    ∃ ι : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2]),
      ι ztwoOne = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]) ∧
      ∃ e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type),
        ∀ g : AbsGalQ2,
          R.nu_ur (toAb g) = ι (nuR (e (maxProPMk 2 AbsGalQ2 g))) := by
  sorry

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Prop 3.6 = ⟦prop:markedpro2⟧
  * Cor 3.4 = ⟦cor:abstractD0⟧ (`BLabHypothesis` draft)
  * eq. (3.14)–(3.16) = ⟦eq:B0⟧/⟦eq:nu0⟧/⟦eq:chi0⟧ (fill-side inputs, `GQ2/SectionThree.lean`)
  * eq. (3.17) = ⟦eq:desiredab⟧ (fill R15)
  * Lemma 2.1 = ⟦lem:tame⟧ (`ν_R` values)
-/
