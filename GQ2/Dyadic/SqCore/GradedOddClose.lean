/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedXFree
import GQ2.Dyadic.SqCore.GradedUniformGen

/-!
# W80-FINAL: the odd route closes

Wave 80's two big lanes ran blind to each other, and their outputs are the two halves of one
implication.

* `GradedXFree` (prefix `gXf`) removed the last two *interfaces* from the graded chain.  Wave
  79's separation theorem `gExt_separationAll` is internalized there, and the extraction, which
  wave 79 showed does **not** hold as quantified in `GTowerKnobRealizable h`, is replaced by the
  `x₁`-free form `GXfKnobRealizable h`, which is a theorem.  What that lane left is one family:
  `GXfKillResidual h = ∀ k, 4 ≤ k → GDeepKillAt h k`, with `gXf_markTransitivity_of_residual`
  turning it into `SqLamMarkTransitivity h`.
* `GradedUniformGen` (prefix `gGen`) proved the uniform generation record at every level and
  closed the kill ladder outright: `gGen_killAt : ∀ k, 2 ≤ k → GDeepKillAt h k`.  Its own
  composite `gGen_markTransitivity` still carried the two wave-75 interfaces, because that lane
  routed through `gDeep_markTransitivity_of_kills` and did not know the other lane had removed
  them.

The binders meet on the nose.  `GDeepKillAt h k` is a closed `Prop` in `h` and `k` alone (its
marking `ν'` and its handle-free element `g` are quantified inside the definition, and no
handle index appears at all), the `h` of both statements is the same implicit section variable,
and `gGen_killAt`'s range `k ≥ 2` contains `GXfKillResidual`'s `k ≥ 4`.  No bridge is needed
beyond weakening `2 ≤ k` to `4 ≤ k`.

## What lands

`SqLamMarkTransitivity h` at **every** `h`, unconditionally: the odd-degree row's
marking-transitivity statement, which has been the odd route's residual since wave 44 and the
graded campaign's target since wave 51, is a theorem.  With it, everything the wave-51 to
wave-67 era proved *equivalent* to it becomes a theorem too (§2), and the `K`-facing handle
stratum `SqHandleMixFixesCore h c` becomes a theorem at every `h` and every unit `c` (§3),
which is exactly the `hMix` binder of the `L`-row branch-datum producer in
`GQ2/Dyadic/GeneralAssembly.lean`.

## What does not land

Nothing here touches the even route, the quadratic flagship's ASK/CAND obligations, or the
remaining fields of the general assembly's residual record.  See
`docs/dyadic/w80-final-note.md` §4 for the field-by-field statement of what is and is not
discharged.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The composition

One weakening and one application.  `gGen_killAt` proves the ladder from rung 2 up;
`GXfKillResidual` asks for it from rung 4 up. -/

section Compose

variable (h : ℕ)

/-- **The `x₁`-free lane's residual, discharged by the uniform lane.**  `gGen_killAt` proves
`GDeepKillAt h k` for every `k ≥ 2`, and `GXfKillResidual h` asks only for `k ≥ 4`. -/
theorem gOdd_killResidual : GXfKillResidual h :=
  fun k hk => gGen_killAt k (by omega)

/-- ⭐⭐⭐ **The odd route's closing theorem**: `SqLamMarkTransitivity h` at every `h`, with no
hypothesis of any kind.

The statement: for every continuous `ν' : D_sq h → ℤ₂` with the two P3-selected core rows
`ν'(σ) = 1` and `ν'(x₀) = 0`, there is a continuous automorphism `Ψ` of `D_sq h` preserving
the χ-exponent functional `λ` with `ν' ∘ Ψ = ν_sq`.  Equivalently (`sqLamMarkTransitivity_iff`)
the stabiliser of `λ` in `Aut(D_sq h)` acts transitively on the selected markings.

The whole graded route now stands behind it: the compactness assembly of wave 67, the
per-class clearing recursion of wave 75, wave 78's and wave 79's depth-2 and depth-3 kills,
wave 79's separation theorem, this wave's `x₁`-free extraction, and this wave's uniform
generation record closing the kill ladder at every depth. -/
theorem gOdd_markTransitivity : SqLamMarkTransitivity h :=
  gXf_markTransitivity_of_residual (gOdd_killResidual h)

end Compose

/-! ## §2 The read-backs inside the graded route

Wave 67 proved `SqLamMarkTransitivity h ↔ ∀ k, SqClassClearingSupply h k` and the wave-51 era
proved `SqArbRelWord h ↔ SqLamMarkTransitivity h`; both directions of both now have a proved
left-hand side, so every member of that equivalence class is a theorem. -/

section ReadBack

/-- ⭐⭐ **The class-`k` clearing supply at every class and every `h`**, read back off §1
through wave 67's `limFinal_markTransitivity_iff`.  Wave 79 had this at `k ≤ 5` only
(`gXf_supply_five`); the classes `k ≥ 6` were the open part.

⚠ **[W81-HOUSE, as of `6f2916f3`: the citation is misattributed by one wave.**
`gXf_supply_five` is THIS wave's, not wave 79's: it lives in `SqCore/GradedXFree.lean`, whose
module docstring is headed "W80-XFREE", and its own docstring says wave 79 supplied the
separation it consumes.  What wave 79 had was the CONDITIONAL `gDeep_supply_five (hsep) (HR)`
(`SqCore/GradedDepthThree.lean`); the unconditional `k ≤ 5` statement is wave 80's.  The
substance of the sentence - that `k ≥ 6` was the open part before this file - is right.]** -/
theorem gOdd_supply (h k : ℕ) : SqClassClearingSupply h k :=
  limFinal_markTransitivity_iff.mp (gOdd_markTransitivity h) k

/-- Wave 67's residual `LimFinalResidual h = ∀ k ≥ 3, SqClassClearingSupply h k`, discharged. -/
theorem gOdd_limFinalResidual (h : ℕ) : LimFinalResidual h :=
  fun k _ => gOdd_supply h k

/-- ⭐⭐ **The arbitrary-dressing relator identity**: at every selected marking and every handle
there is a `λ`-trivial, `ν'`-trivial dressing whose frame spans `H₁` and kills the relator
outright.  This is the word-level form, and unlike `SqEichRelWord` and its variants (which are
refuted for `h ≥ 1`) it is now proved. -/
theorem gOdd_arbRelWord (h : ℕ) : SqArbRelWord h :=
  sqArbRelWord_iff_lamMarkTransitivity.mpr (gOdd_markTransitivity h)

/-- ⭐⭐ **The clearing scheme**, family-agnostically: one handle at a time, every other
handle's rows left where they were. -/
theorem gOdd_clearingStep (h : ℕ) : SqClearingStep h :=
  sqClearingStep_of_arbRelWord (gOdd_arbRelWord h)

/-- The wave-75 defect-vanishing interface, from the uniform lane's ladder and wave 79's
separation.  Recorded because it is the input shape several earlier modules quote. -/
theorem gOdd_defectVanishing (h : ℕ) : GJoinDefectVanishing h :=
  gGen_defectVanishing (gExt_separationAll h)

/-- The `x₁`-free supply clause at every class, likewise. -/
theorem gOdd_chiSupply (h k : ℕ) : GXfChiSupply h k :=
  gXf_chiSupply_of_vanishing (gOdd_defectVanishing h) k

end ReadBack

/-! ## §3 The `K`-facing read-backs

`SqLamMarkTransitivity h` is the hypothesis-free form; what the certificate machinery consumes
is the handle stratum `SqHandleMixFixesCore h c`.  The passage costs `h ≥ 1` and `IsUnit c`
(`sqHandleMixFixesCore_of_lamMarkTransitivity`), and `h = 0` is separately a theorem
(`sqHandleMixFixesCore_zero`), so the composite holds at every `h`. -/

section KFacing

/-- ⭐⭐⭐ **The handle stratum at every `h` and every unit exponent.**  This is the binder that
the `L`-row certificate producers take, and the one `genAsm_oddResidual_gives_mix` in
`GQ2/Dyadic/GeneralAssembly.lean` reads off the residual.  It is now a theorem. -/
theorem gOdd_handleMix (h : ℕ) {c : ℤ_[2]} (hc : IsUnit c) : SqHandleMixFixesCore h c := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · exact sqHandleMixFixesCore_zero c
  · exact sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (gOdd_markTransitivity h)

/-- The stratum at the canonical pivot exponent, which is the spelling the pivot lane and the
`L`-row producers use. -/
theorem gOdd_pivotFix (h : ℕ) : SqHandleMixFixesCore h sqPivotExp :=
  gOdd_handleMix h isUnit_sqPivotExp

/-- MC5's weaker handle-mixing statement, a fortiori. -/
theorem gOdd_handleMixHypothesis (h : ℕ) {c : ℤ_[2]} (hc : IsUnit c) :
    SqHandleMixHypothesis h c :=
  sqHandleMixHypothesis_of_fixesCore (gOdd_handleMix h hc)

/-- ⭐⭐ **The marked-matching statement**: at every selected marking there is a
χ-**preserving** continuous automorphism carrying it to `ν_sq`.  This is strictly the shape the
`L_sq` certificate consumes; the automorphism of §1 preserves the χ-exponent functional `λ`,
and this one preserves χ itself. -/
theorem gOdd_markedMatching (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nu' (u x) = nuSq h x :=
  sqMarkedMatching_of_fixesCore (gOdd_pivotFix h) nu' hsigma hx0

/-- The χ-free clearing target, which is what `MarkedCoreRealization (DSq h) (lNu h)` consumes
and nothing more. -/
theorem gOdd_nuClear (h : ℕ) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_fixesCore (gOdd_pivotFix h)

/-- The `λ`-refined form of the same, i.e. `SqLamMarkTransitivity` under its clearing-condition
name. -/
theorem gOdd_lamNuClear (h : ℕ) : SqLamNuClearHypothesis h :=
  (sqLamMarkTransitivity_iff h).mp (gOdd_markTransitivity h)

end KFacing

/-! ## §4 The furthest committed consequence: the `L_sq` certificate has no handle binder

`marked_matching_certificate_sq_of_fixesCore` is the one-binder production route.  With §3 its
handle binder is discharged, so on an abstract slot the marked-core certificate for the odd row
costs exactly an oriented identification and the two `ν`-normalizations, and no
correction-stratum hypothesis at all.

⚠ **[W81-HOUSE, as of `6f2916f3`: "exactly an oriented identification and the two
`ν`-normalizations" drops one binder.**  `gOdd_certificate` below also takes
`hcont : Continuous fun x => nuG (f x)`, the continuity of the transported marking, which is
data about `nuG` and not implied by the other three.  The theorem's own docstring states the
list correctly ("the oriented identification `f`, its continuity data, and the two selected
core rows"); this section header is the loose one.  The substantive claim - no
correction-stratum hypothesis - is exact.]**

This is as far as `SqCore` can carry it.  Turning the abstract slot into `G_K(2)` is
`GQ2/Dyadic/LabuteInterface.lean`'s `marked_matching_certificate_KTwoSq_of_fixesCore` and then
`GQ2/Dyadic/GeneralAssembly.lean`'s `genAsm_branch_of_oddSq`, neither of which is imported
here. -/

section Certificate

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐⭐⭐ **The odd row's marked-core certificate, with the correction stratum removed.**
Compare `marked_matching_certificate_sq_of_fixesCore`, whose `H` binder this discharges: what
remains is the oriented identification `f`, its continuity data, and the two selected core
rows. -/
theorem gOdd_certificate (h : ℕ) (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (horient : ∀ x, chiG (f x) = chiSq h x)
    (hcont : Continuous fun x : (DSq h : Type) => nuG (f x))
    (hsigma : nuG (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuG (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateSq h chiG nuG) :=
  marked_matching_certificate_sq_of_fixesCore h sqPivotExp chiG nuG f horient hcont
    (gOdd_pivotFix h) hsigma hx0

end Certificate

/-! ## §5 Axiom pins -/

section AxiomPinsOddClose

#print axioms gOdd_killResidual
#print axioms gOdd_markTransitivity
#print axioms gOdd_supply
#print axioms gOdd_limFinalResidual
#print axioms gOdd_arbRelWord
#print axioms gOdd_clearingStep
#print axioms gOdd_defectVanishing
#print axioms gOdd_chiSupply
#print axioms gOdd_handleMix
#print axioms gOdd_pivotFix
#print axioms gOdd_handleMixHypothesis
#print axioms gOdd_markedMatching
#print axioms gOdd_nuClear
#print axioms gOdd_lamNuClear
#print axioms gOdd_certificate

end AxiomPinsOddClose

end SqCore

end Dyadic

end GQ2
