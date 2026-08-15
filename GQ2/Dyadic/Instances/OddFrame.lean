/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.Instances.OddSeam
import GQ2.Dyadic.Instances.GammaLOddDegreeBridge
import GQ2.Dyadic.SqCore.PivotSeedD0

/-!
# The cup-adapted frame at odd degree  (dyadic campaign, lane W83-FRAME)

Wave 82 left the odd classification's last structural input as one Prop per field,
`LSquare.SqMarkedForwardSupply B h`, equivalent (`oddSeam_supply_iff_cupAdaptedFrame`) to ONE
cup-adapted Frattini frame killing the improved relator and carrying the two `ν`-rows.  This
module works the frame ticket: the mod-2 cup structure at odd degree (T1), the frame itself or
the smallest named residual it still costs (T2), and the acceptance composites (T3).

## T1: the form at odd degree

`H¹(G_K(2), 𝔽₂)` has odd dimension `2h + 3` at `[K : ℚ₂] = 2h + 1` (§1, from the committed
census `card_H1_zmodTwo_maxProTwoGalK`).  The cup form is the symmetric non-alternating form
with Labute diagonal `b(κ, x) = b(x, x)`; its odd normal form `⟨1⟩ ⊥ H ⊥ H^{⊥h}` (the improved
relator's quadratic initial Gram, `⟨1⟩`-slot at `x₁`, first plane at `(σ, x₀)`) is REALIZED by
actual frames: `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` produces a cup-adapted frame at
every odd-degree `K`, so the committed machinery covers the odd-dimensional case and no odd
companion is needed (§1, `oddFrame_isCupAdapted_exists`).  Against ANY cup-adapted frame the
unramified class `ν̄ = [u]` has a pinned shape, and this is the lane's T1 content:

* its `x₁`-row vanishes (`oddFrame_nuRow_x1_of_isCupAdapted`): the row IS the cup value
  `b(κ, ν̄)` by the κ-side sharpness, and that value is the isotropy `b(ν̄, ν̄) = 0`, paid by
  `nuUrKappaCupZero_of_odd`;
* its `σ`-row and `x₀`-row SUM to `1` (`oddFrame_nuRowSum_of_isCupAdapted`): the sum IS the cup
  value `b(τ, ν̄)` by the ω-side sharpness, and that value is `1` by `nuUrOmegaCupOne_of_odd`
  (the Hilbert symbol `(2, u)_K = −1` at odd ramification index);
* hence the dichotomy (`oddFrame_nuRow_dichotomy_of_isCupAdapted`): the two selected rows are
  `(1, 0)` or `(0, 1)`, never `(0, 0)` or `(1, 1)`, and `ν̄` is independent of `span{κ, τ}`
  (`oddFrame_nu_notin_kappaTau_span`).  The ramified-`i` hypothesis is automatic here: at odd
  degree both cup values are theorems over the bundle.

## T2: the frame, and the one residual that remains

The presenting frame `frameOfOrientedEquiv` of the unconditional oriented equivalence
`orientedEquiv_of_oddDegree` is cup-adapted and kills the improved relator GLOBALLY with no
hypothesis; T1's row shape applies to it.  So a cup-adapted frame with the relator and the two
mod-2 rows correct UP TO ONE SHARED BIT exists unconditionally
(§2, `oddFrame_presenting_relator_rowSum`): row sum `1` at `(σ, x₀)`, row `0` at `x₁`.

The bit is then absorbed by the pivot, and this is the lane's T2 discovery.  The pivot exponent
`sqPivotExp` is a UNIT (odd), so the parity of the transported pivot row
`ν(f(σ·x₀^{−c₀}))` equals the row SUM, which T1 pins to `1`.  Hence at EVERY oriented
equivalence the transported marking's pivot row is a unit, unconditionally
(§3, `oddFrame_isUnit_transported_sqPivot`).  This is precisely the arithmetic input that
`SqCore.SqNuOrientedClearAtUnitPivot h` consumes and that
`GammaLOddDegreeBridge` §9 proved no choice of `f` and no model automorphism can manufacture;
the cup form manufactures it.  Consequently the whole seam costs exactly the MODEL-side
clearing statement (§4, `oddFrame_supply`):

  `SqCore.SqNuOrientedClearAtUnitPivot h  →  SqMarkedForwardSupply B h`

with no other input beyond the bundle, the filtration, and the degree.  The named residual
Prop is therefore `SqCore.SqNuOrientedClearAtUnitPivot h`: a statement about `D_sq(h)`,
`χ_sq`, `ν_sq` and continuous automorphisms, with no field, no bundle, no frame and no cup
form in it.  PivotClimb §8 shows it is the strongest unrefuted statement of its shape and
derives it from the handle stratum plus the two one-parameter pivot subgroups
(`SqPivotTranslation`, `SqPivotScaling`), which at `h ≥ 1` are the graded lanes' open moves.
At `h = 0` all three families are committed theorems, so the clearing is unconditional
(§4, `oddFrame_clearAtUnitPivot_zero`) and the supply at every degree-one field reproves the
committed floor (`oddFrame_supply_degreeOne`, the n = 1 sanity check).

## T3: acceptance

§4 composes `oddFrame_supply` into wave 82's consumers: over the model clearing alone, every
odd-degree `K` carries the full standard marking, the exact-row cup-adapted frame, the `L`-row
branch datum, the pro-2 block, and `genAsm_candidate_equiv_galK`'s chain needing exactly the
two record blocks.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  §6 pins every declaration; the measured split is
recorded there.  `B` is a binder throughout; neither `B5 localReciprocity` nor
`B5-K markedRecipAt` occurs in any pin.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 Multiplicative
open ContCoh SqCore LSquare MarkedCore
open GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 T1: the mod-2 cup structure at odd degree

The dimension, the realized normal form, and the shape of the unramified class `ν̄` against
every cup-adapted frame.  The two cup values that pin `ν̄` are committed
(`nuUrKappaCupZero_of_odd`, `nuUrOmegaCupOne_of_odd`); the sharp identities that convert them
into rows are committed (`frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted`,
`frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted`); this section composes them into the
frame-facing statements the ticket names. -/

section FormStructure

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The dimension at odd degree**: `H¹(G_K(2), 𝔽₂)` has `2^{2h+3}` elements at
`[K : ℚ₂] = 2h + 1`, i.e. odd `𝔽₂`-dimension `2h + 3`.  The committed census
`card_H1_zmodTwo_maxProTwoGalK`, read at the odd degree. -/
theorem oddFrame_card_H1 {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * h + 3) := by
  rw [card_H1_zmodTwo_maxProTwoGalK (K := K), hdeg]

/-- **The odd normal form is realized by actual frames.**  A cup-adapted Frattini frame exists
at every odd-degree `K`: evaluation on its generators carries the field cup form to the
improved relator's quadratic initial Gram `⟨1⟩ ⊥ H ⊥ H^{⊥h}` (the `⟨1⟩`-slot at `x₁`, the first
hyperbolic plane at `(σ, x₀)`).  So the committed normal-form machinery covers the
odd-dimensional case: this is `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` with the handle
count normalized to the field's own `h`. -/
theorem oddFrame_isCupAdapted_exists (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : h = (Module.finrank ℚ_[2] K - 1) / 2 := by omega
  subst hh
  exact oddDegreeSqCyclotomicFrattiniFrameSupply_holds K B hodd

/-- **The `x₁`-row of `ν̄` vanishes in every cup-adapted frame.**  The row is the cup value
`b(κ, ν̄)` by the κ-side sharp identity, and that value is `0` at every odd-degree `K`: by the
Labute identity it is the isotropy `b(ν̄, ν̄)`, and `ν̄ = [u]` is represented by the norm form of
the unramified quadratic extension `K(√u)`. -/
theorem oddFrame_nuRow_x1_of_isCupAdapted (B : MarkedRecip Rec K) {h : ℕ}
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted) :
    frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 2) = 0 := by
  rw [← NuAdapted.frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted B F hcup]
  exact NuAdapted.nuUrKappaCupZero_of_odd B hodd

/-- **The `σ`- and `x₀`-rows of `ν̄` sum to `1` in every cup-adapted frame.**  The sum is the
cup value `b(τ, ν̄)` by the ω-side sharp identity, and that value is `1` at every odd-degree `K`
at level `r = 0`: the Hilbert symbol `(2, u)_K = (−1)^{e(K/ℚ₂)}` with `e` odd. -/
theorem oddFrame_nuRowSum_of_isCupAdapted (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted) :
    frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 0) +
      frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 1) = 1 := by
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  rw [← MarkedFrame.frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted B F hcup]
  exact NuKummer.nuUrOmegaCupOne_of_odd B hodd hr

/-- **The row dichotomy.**  In every cup-adapted frame at every odd-degree `K` the two selected
mod-2 rows of `ν̄` are `(1, 0)` or `(0, 1)`: the seam's row pattern is correct up to one shared
bit, and the patterns `(0, 0)` and `(1, 1)` are excluded by the cup form alone. -/
theorem oddFrame_nuRow_dichotomy_of_isCupAdapted (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted) :
    (frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 0) = 1 ∧
        frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 1) = 0) ∨
      (frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 0) = 0 ∧
        frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 1) = 1) := by
  have hz : ∀ a b : ZMod 2, a + b = 1 → (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by decide
  exact hz _ _ (oddFrame_nuRowSum_of_isCupAdapted B FF hodd F hcup)

/-- **`ν̄` is an independent direction**: at every odd-degree `K` the unramified class lies
outside `span{κ, τ}`, so the two mod-2 rows are not constrained to a degenerate position.  This
is the ticket's "ramified-`i` makes `ν̄` independent" clause; at odd degree it is a theorem over
the bundle. -/
theorem oddFrame_nu_notin_kappaTau_span (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (hodd : Odd (Module.finrank ℚ_[2] K)) (a c : ZMod 2) :
    MarkedFrame.nuUrModTwoClassKTwo B ≠
      a • cyclotomicModFourClassKTwo (K := K) +
        c • cyclotomicModEightOmegaClassKTwo (K := K) := by
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  exact MarkedFrame.nuUrModTwoClassKTwo_ne_smul_add_smul_of_cupOne B
    (NuKummer.nuUrOmegaCupOne_of_odd B hodd hr) a c

end FormStructure

/-! ## §2 T2, unconditional half: relator plus the mod-2 rows up to one bit

The presenting frame of the unconditional oriented equivalence kills the improved relator
globally and is cup-adapted, so §1's row shape applies to it: the ticket's target object,
cup-adapted frame + relator + two mod-2 rows, exists unconditionally with the rows correct up
to the single shared bit (which of `(1, 0)`, `(0, 1)` the pattern is). -/

section PresentingFrame

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The unconditional frame**: at every odd-degree `K` there is a cup-adapted Frattini frame
that kills the improved relator globally, whose `ν̄`-row sum at `(σ, x₀)` is `1` and whose
`x₁`-row is `0`.  Only the split of the row sum into `(1, 0)` is missing, and §3 shows the
pivot cannot see that split: it is the seam's entire remaining arithmetic content. -/
theorem oddFrame_presenting_relator_rowSum (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
      frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 0) +
        frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 1) = 1 ∧
      frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 2) = 0 := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree B hdeg
  exact ⟨frameOfOrientedEquiv f horient, isCupAdapted_frameOfOrientedEquiv f horient,
    sqRelWord_frameOfOrientedEquiv f horient,
    oddFrame_nuRowSum_of_isCupAdapted B FF hodd _ (isCupAdapted_frameOfOrientedEquiv f horient),
    oddFrame_nuRow_x1_of_isCupAdapted B hodd _ (isCupAdapted_frameOfOrientedEquiv f horient)⟩

end PresentingFrame

/-! ## §3 T2, the discovery: the cup form pays the unit-pivot hypothesis

`GammaLOddDegreeBridge` §9 proved the parity of the transported pivot row is an invariant of
the target that no choice of oriented equivalence and no model automorphism can arrange, and
concluded that the `h ≥ 1` bridge needs the arithmetic input carried by the marked supply
itself.  The conclusion overshot: the pivot exponent is odd, so the pivot-row parity IS the
`ν̄`-row sum, and §1 computes that sum from the cup form.  The invariant is a unit, always. -/

section PivotParity

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The transported pivot row is a unit, unconditionally.**  For every oriented equivalence
`f : D_sq(h) ≃ₜ* G_K(2)` at an odd-degree `K`, the pivot row of the transported marking
`ν_ur ∘ f` is a unit of `ℤ₂`.  Proof: the pivot row is `ν(f σ) − c₀·ν(f x₀)` with `c₀` a unit,
so its parity is the `ν̄`-row sum at the presenting frame of `f`, which is cup-adapted; the
ω-side sharp identity converts the sum into the cup value `b(τ, ν̄) = 1`.

This is exactly the hypothesis `SqCore.SqNuOrientedClearAtUnitPivot h` consumes, and the input
that `PivotClimb` §9 shows the model side cannot produce.  The cup form of the target produces
it. -/
theorem oddFrame_isUnit_transported_sqPivot (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    IsUnit (toAdd (transportedNuUr B f (sqPivot h))) := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  -- the mod-2 rows of the transported marking sum to `1`, by §1 at the presenting frame
  have hrows : MarkedFrame.redTwo (toAdd (nuUrKTwo B (f (dsqSigma h)))) +
      MarkedFrame.redTwo (toAdd (nuUrKTwo B (f (dsqX0 h)))) = 1 :=
    oddFrame_nuRowSum_of_isCupAdapted B FF hodd (frameOfOrientedEquiv f horient)
      (isCupAdapted_frameOfOrientedEquiv f horient)
  -- the pivot row in coordinates, reduced mod 2 with the unit exponent erased
  have hpiv : toAdd (transportedNuUr B f (sqPivot h)) =
      toAdd (nuUrKTwo B (f (dsqSigma h))) - sqPivotExp * toAdd (nuUrKTwo B (f (dsqX0 h))) :=
    toAdd_nu_sqPivot (transportedNuUr B f)
  rw [← MarkedFrame.redTwo_eq_one_iff, hpiv, map_sub, map_mul,
    (MarkedFrame.redTwo_eq_one_iff _).mpr isUnit_sqPivotExp, one_mul]
  have hz : ∀ a b : ZMod 2, a + b = 1 → a - b = 1 := by decide
  exact hz _ _ hrows

end PivotParity

/-! ## §4 T3: the seam over the model clearing alone

The composite: an oriented equivalence is free, its transported marking is jointly surjective,
its pivot row is a unit (§3), so the model-side clearing statement corrects it onto the whole
standard marking, and the supply follows.  Everything downstream of the supply is wave 82's. -/

section Acceptance

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The seam over the model clearing.**  `SqCore.SqNuOrientedClearAtUnitPivot h`, a statement
about `D_sq(h)` with no field in it, implies `SqMarkedForwardSupply B h` at every odd-degree
`K` over the bundle and filtration alone.  Before this lane the clearing statement was known to
suffice only TOGETHER with the supply's own rows (`GammaLOddDegreeBridge` §1′); the cup form
pays the unit-pivot input, so the clearing is now the seam's whole remaining cost. -/
theorem oddFrame_supply (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) : SqMarkedForwardSupply B h := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree B hdeg
  obtain ⟨Ψ, hchi, hnu⟩ := hclear (transportedNuUr B f)
    (fun u y => jointSurjective_transportedNuUr B hodd hr f horient u y)
    (oddFrame_isUnit_transported_sqPivot B FF hdeg f horient)
  refine ⟨Ψ.trans f, fun x => ?_, ?_, ?_⟩
  · show chiCycKTwo (K := K) (f (Ψ x)) = chiSq h x
    rw [horient (Ψ x), hchi x]
  · show nuUrKTwo B (f (Ψ (dsqSigma h))) = ofAdd (1 : ℤ_[2])
    have hval := hnu (dsqSigma h)
    rw [transportedNuUr_apply] at hval
    rw [hval]
    exact nuSq_sigma h
  · show nuUrKTwo B (f (Ψ (dsqX0 h))) = ofAdd (0 : ℤ_[2])
    have hval := hnu (dsqX0 h)
    rw [transportedNuUr_apply] at hval
    rw [hval]
    exact nuSq_x0 h

/-- The full standard marking over the model clearing: wave 82's self-improvement applied to
`oddFrame_supply`. -/
theorem oddFrame_fullMarking_of_clear (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      (∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) ∧
        ∀ x, nuUrKTwo B (f x) = nuSq h x :=
  oddSeam_fullMarking_of_supply B h (oddFrame_supply B FF hdeg hclear)

/-- **The ticket's frame, with exact rows, over the model clearing**: a cup-adapted Frattini
frame killing the improved relator and carrying the two exact `ν`-rows.  By
`oddSeam_supply_iff_cupAdaptedFrame` this is the seam on the nose. -/
theorem oddFrame_cupAdaptedFrame_of_clear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
      nuUrKTwo B (F.generators 0) = ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F.generators 1) = ofAdd (0 : ℤ_[2]) :=
  oddSeam_cupAdaptedFrame_of_supply B h (oddFrame_supply B FF hdeg hclear)

/-- The `L`-row branch datum over the model clearing. -/
theorem oddFrame_genAsmBranch_L_of_clear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    ∃ G : GenAsmBranch K B, G.pres = .L h :=
  oddId_genAsmBranch_L_of_supply B hdeg (oddFrame_supply B FF hdeg hclear)

/-- The `L`-row pro-2 block over the model clearing, with no clearing binder on the `K` side
and no frame residual. -/
theorem oddFrame_realization_of_clear (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) :=
  oddSeam_realization_of_supply B h (oddFrame_supply B FF hdeg hclear)

/-- **The full chain over the model clearing**: what the general theorem still needs at an
odd-degree `K`, beyond `SqCore.SqNuOrientedClearAtUnitPivot h`, is exactly the two record
blocks `GenAsmFieldInputs` and `GenAsmRowResidual`. -/
theorem oddFrame_candidate_equiv_galK_of_clear (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    ∃ G : GenAsmBranch K B, G.pres = .L h ∧
      ∀ F : GenAsmFieldInputs K B FF G.degree, GenAsmRowResidual G F.T →
        Nonempty (ContinuousMulEquiv
          ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  oddId_candidate_equiv_galK_of_supply B hdeg (oddFrame_supply B FF hdeg hclear)

/-- **The clearing is a theorem at `h = 0`**: the handle stratum is empty
(`sqHandleMixFixesCore_zero`) and the two one-parameter pivot families are the committed
degree-one seeds (`sqPivotTranslation_zero`, `sqPivotScaling_zero`). -/
theorem oddFrame_clearAtUnitPivot_zero : SqCore.SqNuOrientedClearAtUnitPivot 0 :=
  sqNuOrientedClearAtUnitPivot_of_families (sqHandleMixFixesCore_zero sqPivotExp)
    (fun c => sqPivotTranslation_zero c) (fun _ ha => sqPivotScaling_zero ha)

/-- **The n = 1 sanity check**: at `[K : ℚ₂] = 1` the new route is unconditional and lands on
the committed degree-one floor's statement. -/
theorem oddFrame_supply_degreeOne (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1) : SqMarkedForwardSupply B 0 :=
  oddFrame_supply B FF (h := 0) (by omega) oddFrame_clearAtUnitPivot_zero

end Acceptance

/-! ## §5 Stress pins -/

section StressTests

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Stress: the pivot exponent is odd.  This is the one bit of model arithmetic that makes the
pivot parity equal the row sum, hence makes §3 possible; if `c₀` were even the pivot argument
would instead pin the rows outright and the dichotomy would collapse. -/
example : MarkedFrame.redTwo sqPivotExp = 1 :=
  (MarkedFrame.redTwo_eq_one_iff _).mpr isUnit_sqPivotExp

/-- Stress (degree-one regression): the committed floor and the new route prove the same
statement. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1) :
    SqMarkedForwardSupply B 0 ∧ SqMarkedForwardSupply B 0 :=
  ⟨oddId_markedSupply_degreeOne B FF hdeg, oddFrame_supply_degreeOne B FF hdeg⟩

/-- Stress: at degree one the exact-row cup-adapted relator-killing frame is unconditional
through the new route as well. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1) :
    ∃ F : SqCyclotomicFrattiniFrame K 0, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
      nuUrKTwo B (F.generators 0) = ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F.generators 1) = ofAdd (0 : ℤ_[2]) :=
  oddFrame_cupAdaptedFrame_of_clear B FF (h := 0) (by omega) oddFrame_clearAtUnitPivot_zero

/-- Stress: the supply built by `oddFrame_supply` feeds wave 82's equivalence back, so the two
frame forms of the seam agree over the clearing. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) :
    ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
      nuUrKTwo B (F.generators 0) = ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F.generators 1) = ofAdd (0 : ℤ_[2]) :=
  (oddSeam_supply_iff_cupAdaptedFrame B hdeg).mp (oddFrame_supply B FF hdeg hclear)

end StressTests

end

/-! ## §6 Axiom pins

Recorded from the mirror run; the sets below are the measured ones.  Base: std-3 is
`propext`, `Classical.choice`, `Quot.sound`; the census members are
`absGalQ2_isTopologicallyFinitelyGenerated` (B1), `tateDualityAt` (B6),
`absGalQ2_localEulerCharacteristic` (B7), `hilbertSymbol_normCriterion_finiteDyadic` (B11a),
and the two Roe-side members `dyadicOrientation`, `peripheralCyclotomicAction` carried by the
degree-one seed identification `D_R ≅ D_sq(0)`.  Neither `B5 localReciprocity` nor
`B5-K markedRecipAt` occurs in any pin.  The measured split:

* `oddFrame_card_H1`: std-3 + {B6, B7}.  The census alone; no Hilbert dictionary, no B1.
* `oddFrame_isCupAdapted_exists`, `oddFrame_presenting_relator_rowSum`, `oddFrame_supply` and
  every §4 consumer over the clearing: std-3 + {B1, B6, B7, B11a}.
* the four `ν̄`-shape statements of §1 (`nuRow_x1`, `nuRowSum`, `nuRow_dichotomy`,
  `nu_notin_kappaTau_span`): std-3 + {B6, B11a} only.  The row shape is the cup dictionary and
  duality, nothing else.
* `oddFrame_isUnit_transported_sqPivot`: std-3 + {B1, B6, B11a}.  No B7: the pivot parity does
  not consume the Euler characteristic, only the frame's cup adaptation.
* `oddFrame_clearAtUnitPivot_zero`: std-3 + {dyadicOrientation, peripheralCyclotomicAction}.
  The `h = 0` clearing rides the committed degree-one pivot seeds, which identify `D_sq(0)`
  with the Roe core; no bundle-side census member appears.
* `oddFrame_supply_degreeOne`: the union, std-3 + {B1, B6, B7, B11a} +
  {dyadicOrientation, peripheralCyclotomicAction}. -/

#print axioms GQ2.Dyadic.oddFrame_card_H1
#print axioms GQ2.Dyadic.oddFrame_isCupAdapted_exists
#print axioms GQ2.Dyadic.oddFrame_nuRow_x1_of_isCupAdapted
#print axioms GQ2.Dyadic.oddFrame_nuRowSum_of_isCupAdapted
#print axioms GQ2.Dyadic.oddFrame_nuRow_dichotomy_of_isCupAdapted
#print axioms GQ2.Dyadic.oddFrame_nu_notin_kappaTau_span
#print axioms GQ2.Dyadic.oddFrame_presenting_relator_rowSum
#print axioms GQ2.Dyadic.oddFrame_isUnit_transported_sqPivot
#print axioms GQ2.Dyadic.oddFrame_supply
#print axioms GQ2.Dyadic.oddFrame_fullMarking_of_clear
#print axioms GQ2.Dyadic.oddFrame_cupAdaptedFrame_of_clear
#print axioms GQ2.Dyadic.oddFrame_genAsmBranch_L_of_clear
#print axioms GQ2.Dyadic.oddFrame_realization_of_clear
#print axioms GQ2.Dyadic.oddFrame_candidate_equiv_galK_of_clear
#print axioms GQ2.Dyadic.oddFrame_clearAtUnitPivot_zero
#print axioms GQ2.Dyadic.oddFrame_supply_degreeOne

end GQ2.Dyadic
