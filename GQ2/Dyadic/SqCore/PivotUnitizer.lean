/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotCoreMoves

/-!
# The handle input of the oriented residual is one bit: *make the pivot row odd*

`SqCore/JointClearing.lean` assembles the oriented clearing residual out of three inputs: the
banked handle stratum `SqHandleMixFixesCore h c₀`, the pivot core family, and **one
handle-to-core transfer per handle letter** (`SqHandleToCoreMove h i`, a full move statement with
four row clauses).  Reading that assembly shows the transfers are consumed in exactly one place
and for exactly one purpose: to produce, from a jointly-surjective marking, a χ-preserving
automorphism after which the *pivot row is a unit*.  Nothing else about them is used.

This file names that purpose,

  `SqPivotUnitizer h` : every jointly-surjective marking admits a χ-preserving continuous
  automorphism `Ψ` with `ν'(Ψ w)` a unit  (`w = sqPivot h`),

and re-runs the assembly over it.  Three facts make this the right shape:

* **It is implied by the transfers** (`sqPivotUnitizer_of_handleToCore`), so nothing is lost:
  the committed assembly factors through this file (`sqNuOrientedClear_of_moves'`, a regression
  against `sqNuOrientedClear_of_moves`).
* **It is strictly weaker**: no `x₀`-row clause, no handle-row clauses, no prescribed shift, and
  a *hypothesis* (joint surjectivity) rather than a bare universal quantifier over markings.
* **It is necessary** (`sqPivotUnitizer_of_orientedClear`): the oriented residual itself implies
  it, since the clearing automorphism sends the pivot row to `ν_sq(w) = 1`.  So the reduction
  cannot be weakened further along this axis, and the residual splits *exactly* into
  "unitize the pivot row" plus "normalize the two core rows".
* **At `h = 0` it is a theorem** (`sqPivotUnitizer_zero`): joint surjectivity there *is* the
  unit pivot row (`sqJointSurjective_isUnit_pivot_zero`), so the identity works and the whole
  odd-degree model residual collapses onto the pivot core family, i.e. onto the two
  one-parameter subgroups of `PivotCoreMoves` §3.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The unitizer -/

section Statement

/-- **The pivot unitizer**: every jointly-surjective marking can be moved, by a χ-preserving
continuous automorphism, to one whose **pivot row is a unit**.  This is the entire contribution
of the handle-to-core transfers to the oriented clearing assembly. -/
def SqPivotUnitizer (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    SqJointSurjective h nu' →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ IsUnit (toAdd (nu' (Ψ (sqPivot h))))

variable {h : ℕ}

/-- **The transfers imply the unitizer.**  Joint surjectivity gives a unit pivot row directly, or
a unit row at some handle letter; in the second case one transfer moves it onto the pivot. -/
theorem sqPivotUnitizer_of_handleToCore
    (hmixU : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxU j))
    (hmixV : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxV j)) : SqPivotUnitizer h := by
  intro nu' hjs
  by_cases hd : IsUnit (toAdd (nu' (sqPivot h)))
  · exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, hd⟩
  · have hdeven : (2 : ℤ_[2]) ∣ toAdd (nu' (sqPivot h)) := by
      by_contra hc
      exact hd (isUnit_iff_not_two_dvd.mpr hc)
    obtain ⟨j, hj⟩ := (sqJointSurjective_isUnit_pivot_or_handle hjs).resolve_left hd
    rcases hj with hu | hv
    · exact isUnit_pivot_of_handleToCore nu' (hmixU j) hdeven hu
    · exact isUnit_pivot_of_handleToCore nu' (hmixV j) hdeven hv

/-- **The unitizer is necessary.**  If the oriented residual holds then its clearing
automorphism already unitizes the pivot row, since `ν_sq(w) = 1`. -/
theorem sqPivotUnitizer_of_orientedClear (H : SqNuOrientedClear h) : SqPivotUnitizer h := by
  intro nu' hjs
  obtain ⟨Ψ, hchi, hnu⟩ := H nu' hjs
  refine ⟨Ψ, hchi, ?_⟩
  rw [hnu (sqPivot h)]
  exact isUnit_nuSq_sqPivot h

/-- **At `h = 0` the unitizer is a theorem**: there joint surjectivity *is* the unit pivot row,
so the identity automorphism already does it. -/
theorem sqPivotUnitizer_zero : SqPivotUnitizer 0 := fun _ hjs =>
  ⟨ContinuousMulEquiv.refl _, fun _ => rfl, sqJointSurjective_isUnit_pivot_zero hjs⟩

end Statement

/-! ## §2 The assembly over the unitizer -/

section Assembly

variable {h : ℕ}

/-- **The oriented residual over the pivot family and the unitizer.**  Same proof as
`sqNuOrientedClear_of_moves`, with the handle-to-core transfers replaced by the single bit they
were used for. -/
theorem sqNuOrientedClear_of_pivotMoves_of_unitizer
    (hfix : SqHandleMixFixesCore h sqPivotExp)
    (hmv : ∀ m k : ℤ_[2], IsUnit (sqPivotDet m k) → SqPivotCoreMove h m k)
    (hunit : SqPivotUnitizer h) : SqNuOrientedClear h := by
  intro nu' hjs
  obtain ⟨Ψ₀, hchi₀, hpiv₀⟩ := hunit nu' hjs
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₀) with hmudef
  have hmupiv : IsUnit (toAdd (mu (sqMixPivotElem h sqPivotExp))) := hpiv₀
  obtain ⟨Ψ₁, hchi₁, hU₁, hV₁, hs₁, hx₁⟩ := hfix mu hmupiv
  set rho : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    mu.comp (autHom Ψ₁) with hrhodef
  have hrhopiv : IsUnit (toAdd (rho (sqPivot h))) := by
    have hval : toAdd (rho (sqPivot h)) = toAdd (mu (sqPivot h)) := by
      show toAdd (mu (Ψ₁ (sqPivot h))) = _
      rw [toAdd_aut_sqPivot, hs₁, hx₁, toAdd_nu_sqPivot]
    rw [hval]
    exact hpiv₀
  obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hU₂, hV₂⟩ := sqCoreRows_of_pivotMove hmv rho hrhopiv
  refine ⟨Ψ₂.trans (Ψ₁.trans Ψ₀), fun x => ?_, fun x => ?_⟩
  · show chiSq h (Ψ₀ (Ψ₁ (Ψ₂ x))) = chiSq h x
    rw [hchi₀, hchi₁, hchi₂]
  · have hcore : ∀ y, (rho.comp (autHom Ψ₂)) y = nuSq h y := by
      refine nu_eq_nuSq_of_core _ hs₂ hx₂ (fun j => ?_) (fun j => ?_)
      · show rho (Ψ₂ (sqGen h (sqHandleIdxU j))) = 1
        rw [hU₂ j]
        exact hU₁ j
      · show rho (Ψ₂ (sqGen h (sqHandleIdxV j))) = 1
        rw [hV₂ j]
        exact hV₁ j
    exact hcore x

/-- **Regression**: the committed assembly factors through this file — same statement, same
hypotheses, new proof. -/
theorem sqNuOrientedClear_of_moves' (hfix : SqHandleMixFixesCore h sqPivotExp)
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove h m k)
    (hmixU : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxU j))
    (hmixV : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxV j)) : SqNuOrientedClear h :=
  sqNuOrientedClear_of_pivotMoves_of_unitizer hfix hmv
    (sqPivotUnitizer_of_handleToCore hmixU hmixV)

/-- **The residual at every handle count, in its smallest committed form**: the banked handle
stratum, the two one-parameter pivot subgroups, and the one-bit unitizer. -/
theorem sqNuOrientedClear_of_families_of_unitizer
    (hfix : SqHandleMixFixesCore h sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a)
    (hunit : SqPivotUnitizer h) : SqNuOrientedClear h :=
  sqNuOrientedClear_of_pivotMoves_of_unitizer hfix
    (fun m k hd => sqPivotCoreMove_of_translation_scaling m k (htr k) (hsc _ hd)) hunit

/-- **The `h = 0` face, over the two one-parameter subgroups alone.**  The unitizer and the
handle stratum are both theorems at `h = 0`, so this is the whole model-side input to the
odd-degree row at `[K : ℚ₂] = 1`. -/
theorem sqNuOrientedClear_zero_of_two_subgroups
    (htr : ∀ c : ℤ_[2], SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 0 a) : SqNuOrientedClear 0 :=
  sqNuOrientedClear_of_families_of_unitizer (sqHandleMixFixesCore_zero sqPivotExp) htr hsc
    sqPivotUnitizer_zero

end Assembly

/-! ## §3 Stress pins -/

section StressTests

/-- The unitizer is a theorem at `h = 0`. -/
example : SqPivotUnitizer 0 := sqPivotUnitizer_zero

/-- At one handle it follows from the two transfers. -/
example (hmixU : ∀ j : Fin 1, SqHandleToCoreMove 1 (sqHandleIdxU j))
    (hmixV : ∀ j : Fin 1, SqHandleToCoreMove 1 (sqHandleIdxV j)) : SqPivotUnitizer 1 :=
  sqPivotUnitizer_of_handleToCore hmixU hmixV

/-- …and it is implied by the target it helps prove, so the reduction is sharp. -/
example (H : SqNuOrientedClear 1) : SqPivotUnitizer 1 := sqPivotUnitizer_of_orientedClear H

/-- One handle: the residual over the three inputs. -/
example (hfix : SqHandleMixFixesCore 1 sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqPivotTranslation 1 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 1 a) (hunit : SqPivotUnitizer 1) :
    SqNuOrientedClear 1 :=
  sqNuOrientedClear_of_families_of_unitizer hfix htr hsc hunit

/-- The `h = 0` milestone shape, over the two one-parameter subgroups alone. -/
example (htr : ∀ c : ℤ_[2], SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 0 a) : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_two_subgroups htr hsc

end StressTests

/-! ## §4 Axiom pins -/

section AxiomPins

#print axioms SqPivotUnitizer
#print axioms sqPivotUnitizer_of_handleToCore
#print axioms sqPivotUnitizer_of_orientedClear
#print axioms sqPivotUnitizer_zero
#print axioms sqNuOrientedClear_of_pivotMoves_of_unitizer
#print axioms sqNuOrientedClear_of_moves'
#print axioms sqNuOrientedClear_of_families_of_unitizer
#print axioms sqNuOrientedClear_zero_of_two_subgroups

end AxiomPins

end SqCore

end Dyadic

end GQ2
