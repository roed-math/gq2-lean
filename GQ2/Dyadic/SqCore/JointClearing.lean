/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.NuSeedWide

/-!
# The clearing residual on `Aut(D_sq h)`: joint, oriented, and reduced to one move family

Two residual shapes reach the model group `D_sq(h)`, and this file prices both.

* `SqNuJointClear h` — every marking jointly surjective with `χ_sq` is carried to `ν_sq` by a
  continuous automorphism (the `Instances` statement `LSquare.SqNuJointClearing`, restated here
  so that `SqCore` need not import `Instances`; same body, so the bridge is `id`).
* `SqNuOrientedClear h` — the same with the automorphism required to **preserve `χ_sq`**.  This
  is the model face of the odd-degree *one-binder* residual `SqNuAdaptedFrameRelator`
  (`Instances/GammaLNuAdaptedFrame.lean`), which
  `sqNuAdaptedFrameRelator_iff_orientedFullNu` characterizes as: *one* equivalence
  `D_sq(h) ≃ G_K(2)` carrying **both** the orientation and the whole marking.  Over the
  unconditional `orientedEquiv_of_oddDegree` this model statement **implies** that residual, at
  every odd-degree `K` at once (bridge, one line in `Instances`: take `ν' := ν_ur ∘ f`, jointly
  surjective by `jointSurjective_transportedNuUr`; the produced `Ψ` gives the oriented full-`ν`
  equivalence `Ψ.trans f`).  It is the *uniform* form of the residual: any two oriented
  equivalences differ by a χ-preserving automorphism, so per field the residual asks for the
  single transported marking, while `SqNuOrientedClear h` asks for all jointly-surjective ones.

## The reduction

Write `a = ν'(σ)`, `b = ν'(x₀)`, `c₀ = sqPivotExp`, `w = σ·x₀^{−c₀} = sqPivot h`, so the pivot
row is `d = ν'(w) = a − c₀·b`.

* **§3–§4** (what the new precondition buys) `sqJointSurjective_isUnit_pivot_or_handle`: joint
  surjectivity says exactly that `d` is a unit **or** some handle row is.  At `h = 0` the second
  disjunct is empty, so the whole precondition is *one bit*, where the retired two-row
  hypothesis pinned two entire rows.  The engine is the committed `χ_sq² = X^{2λ}`
  (`chiSq_sq_eq_lam`): an element with `χ_sq = 1` has even `λ`-row, and in the bad shape `ν'` is
  congruent modulo `2` either to `0` or to `λ` on every generator, so it can never take an odd
  value where `χ_sq = 1` — which is what surjectivity at `(1, 1)` demands.
* **§5** `w` is **χ-trivial** (`chiSq_sqPivot`), so dressing core letters by powers of `w` is
  invisible to the orientation.  The two-parameter family

    `SqPivotCoreMove h m k` : `σ ↦ σ·w^m`, `x₀ ↦ x₀·w^k`, χ-preserving, handle rows fixed

  moves the core rows by `(a, b) ↦ (a + m·d, b + k·d)`, so its abelianized determinant is
  `1 + m − k·c₀`, and at the **single** parameter pair `m = (1 − a)·d⁻¹`, `k = −b·d⁻¹` it lands
  on `(1, 0) = (ν_sq(σ), ν_sq(x₀))` with determinant `d⁻¹` — a unit for free
  (`sqCoreRows_of_pivotMove`).  Both parity classes of `(a, b)` are covered by that one pair:
  when `m` and `k` are both odd the family realizes the mod-2 swap, which neither one-parameter
  subfamily can.
* **§6** the assembly `sqNuOrientedClear_of_moves`: the pivot family, the banked handle stratum
  `SqHandleMixFixesCore h c₀`, and one handle-to-core transfer per handle discharge the whole
  oriented residual.  At `h = 0` the handle stratum is a theorem (`sqHandleMixFixesCore_zero`)
  and there are no handles, so `sqNuOrientedClear_zero_of_pivotMoves` reduces the residual to
  the pivot family **alone**.
* **§7** `sqRelWord_of_aut`: any tuple in the `Aut(D_sq h)`-orbit of the standard generators
  kills the relator.  This is the pivot of the basis-transitivity route — an automorphism is
  all a frame ever needs in order to present.

## Honest pricing

No automorphism is constructed here.  What is established is that the odd-degree residual needs
**exactly one** family of them, of a shape the seed calculus already knows how to search: a
substitution dressing two core letters by powers of the χ-trivial pivot, with the inverse
substitution supplied by the unit determinant.

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

/-! ## §1 The two residual shapes, inside `SqCore` -/

section Statements

/-- **Joint surjectivity of `(χ_sq, ν')`**: every pair `(u, y) ∈ ℤ₂ˣ × ℤ₂` is realized at a
single element of `D_sq(h)`. -/
def SqJointSurjective (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∀ (u : ℤ_[2]ˣ) (y : ℤ_[2]), ∃ g : (DSq h : Type), chiSq h g = u ∧ nu' g = ofAdd y

/-- **The joint clearing target**, restated in `SqCore`.  Same body as
`GQ2.Dyadic.LSquare.SqNuJointClearing h`, so the bridge between the two is `id`. -/
def SqNuJointClear (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    (∀ (u : ℤ_[2]ˣ) (y : ℤ_[2]), ∃ g : (DSq h : Type), chiSq h g = u ∧ nu' g = ofAdd y) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type), ∀ x, nu' (Ψ x) = nuSq h x

/-- The joint clearing target, spelled through `SqJointSurjective`. -/
theorem sqNuJointClear_iff (h : ℕ) :
    SqNuJointClear h ↔ ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      SqJointSurjective h nu' →
        ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type), ∀ x, nu' (Ψ x) = nuSq h x :=
  Iff.rfl

/-- **The oriented clearing target** — the model face of the odd-degree one-binder residual:
the clearing automorphism must preserve `χ_sq`, so that an oriented equivalence stays
oriented. -/
def SqNuOrientedClear (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    SqJointSurjective h nu' →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x

/-- The oriented target is the stronger one.

⚠ **DEAD ROUTE at `h ≥ 1`: this implication is vacuous.**  Its hypothesis `SqNuOrientedClear h`
is refuted at every positive handle count by `PivotClimb.not_sqNuOrientedClear`: the pivot row's
parity is an invariant of the *whole* automorphism group (the Frattini cup form is, and it names
the pivot), so the `SqPivotUnitizer` factor of `PivotClimb.sqNuOrientedClear_iff` fails.  No
`h ≥ 1` instance of this implication can ever fire.

The *conclusion* `SqNuJointClear h` is **not** refuted — only this route to it is; the live
oriented statement is `PivotClimb.SqNuOrientedClearAtUnitPivot h`.  Kept because the implication
is true and `h = 0` (where joint surjectivity *is* the unit pivot row) still factors through
it. -/
theorem sqNuJointClear_of_orientedClear {h : ℕ} (H : SqNuOrientedClear h) :
    SqNuJointClear h := fun nu' hjs => (H nu' hjs).imp fun _ hΨ => hΨ.2

/-- **The core-row residual**: every jointly-surjective marking admits a continuous automorphism
installing the two P3-selected core rows.  This is what the retired two-row precondition
*assumed* and the joint precondition must *produce*. -/
def SqNuCoreRows (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    SqJointSurjective h nu' →
      ∃ Φ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        nu' (Φ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧ nu' (Φ (dsqX0 h)) = ofAdd (0 : ℤ_[2])

end Statements

/-! ## §2 The split: over the committed clearing hypothesis, joint clearing *is* core-row
normalisation -/

section Split

variable {h : ℕ}

/-- **Necessity**: joint clearing carries the two core rows, so it implies the core-row
residual. -/
theorem sqNuCoreRows_of_jointClear (H : SqNuJointClear h) : SqNuCoreRows h := by
  intro nu' hjs
  obtain ⟨Ψ, hΨ⟩ := H nu' hjs
  refine ⟨Ψ, ?_, ?_⟩
  · rw [hΨ (dsqSigma h), nuSq_sigma]
  · rw [hΨ (dsqX0 h), nuSq_x0]

/-- **Sufficiency**: the core-row residual plus the χ-free clearing hypothesis give joint
clearing.  Normalise the rows with `Φ`, then clear the handles with `Ψ`. -/
theorem sqNuJointClear_of_coreRows (hcore : SqNuCoreRows h)
    (hclear : SqNuClearHypothesis h) : SqNuJointClear h := by
  intro nu' hjs
  obtain ⟨Φ, hs, hx⟩ := hcore nu' hjs
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Φ) with hmudef
  have hmus : mu (dsqSigma h) = ofAdd (1 : ℤ_[2]) := hs
  have hmux : mu (dsqX0 h) = ofAdd (0 : ℤ_[2]) := hx
  obtain ⟨Ψ, hΨ⟩ := hclear mu hmus hmux
  exact ⟨Ψ.trans Φ, fun x => hΨ x⟩

/-- **The split**, as an equivalence over the χ-free clearing hypothesis. -/
theorem sqNuJointClear_iff_coreRows (hclear : SqNuClearHypothesis h) :
    SqNuJointClear h ↔ SqNuCoreRows h :=
  ⟨sqNuCoreRows_of_jointClear, fun hcore => sqNuJointClear_of_coreRows hcore hclear⟩

/-- **The `h = 0` face, exactly**: at `h = 0` the χ-free clearing hypothesis is a theorem, so the
joint residual there *is* the core-row normalisation. -/
theorem sqNuJointClear_zero_iff : SqNuJointClear 0 ↔ SqNuCoreRows 0 :=
  sqNuJointClear_iff_coreRows sqNuClearHypothesis_zero

end Split

/-! ## §3 The parity calculus -/

section Parity

/-- In a pro-2 group, `x^t = 1` at a **unit** exponent forces `x = 1`. -/
theorem eq_one_of_zpowZtwo_eq_one_of_isUnit {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) {t : ℤ_[2]} (ht : IsUnit t)
    (hx : zpowZtwo hP x t = 1) : x = 1 := by
  obtain ⟨v, hv⟩ := ht
  have hinv : t * ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← hv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc x = zpowZtwo hP x (t * ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by rw [hinv, zpowZtwo_one_exp]
    _ = zpowZtwo hP (zpowZtwo hP x t) ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := (zpowZtwo_zpowZtwo hP x _ _).symm
    _ = 1 := by rw [hx, zpowZtwo_one_base]

/-- **The λ-row of a χ-trivial element is even.**  `χ_sq² = X^{2λ}` and `X² ≠ 1`, so an odd
`λ`-row where `χ_sq = 1` would make `X²` trivial. -/
theorem two_dvd_toAdd_nuLam_of_chiSq_eq_one {h : ℕ} {g : (DSq h : Type)}
    (hg : chiSq h g = 1) : (2 : ℤ_[2]) ∣ toAdd (nuLam h g) := by
  by_contra hdvd
  refine rootXUnit_sq_ne_one (eq_one_of_zpowZtwo_eq_one_of_isUnit isProP_two_unitsPadicInt
    (rootXUnit ^ 2) (isUnit_iff_not_two_dvd.mpr hdvd) ?_)
  have hsq := chiSq_sq_eq_lam h g
  rw [hg, one_pow, xPowLamSq_apply] at hsq
  exact hsq.symm

/-- The **parity character** of a marking: `g ↦ (−1)^{ν'(g)}`. -/
noncomputable def sqNuParity {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  (zpowZtwoHom isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ)).comp nu'

theorem sqNuParity_apply {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (g : (DSq h : Type)) :
    sqNuParity nu' g = zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (nu' g)) := rfl

/-- `−1 ≠ 1` in `ℤ₂ˣ`. -/
theorem negOne_ne_one_unitsPadicInt : (-1 : ℤ_[2]ˣ) ≠ 1 := by
  intro hc
  have hval : ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2]) := congrArg _ hc
  rw [Units.val_neg, Units.val_one] at hval
  have h2 : (2 : ℤ_[2]) = 0 := by linear_combination -hval
  exact absurd h2 (by norm_num)

/-- `(−1)^t = 1` exactly for even `t`. -/
theorem zpowZtwo_negOne_eq_one_iff {t : ℤ_[2]} :
    zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) t = 1 ↔ (2 : ℤ_[2]) ∣ t := by
  constructor
  · intro ht
    by_contra hdvd
    exact negOne_ne_one_unitsPadicInt (eq_one_of_zpowZtwo_eq_one_of_isUnit
      isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (isUnit_iff_not_two_dvd.mpr hdvd) ht)
  · rintro ⟨s, rfl⟩
    rw [show (2 : ℤ_[2]) * s = ((2 : ℕ) : ℤ_[2]) * s by push_cast; ring, ← zpowZtwo_zpowZtwo,
      zpowZtwo_natCast]
    norm_num

/-- **Parity is decided on the generators**: two markings whose generator rows agree modulo `2`
agree modulo `2` everywhere. -/
theorem two_dvd_toAdd_sub_of_gen {h : ℕ}
    (nu' mu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h i)) - toAdd (mu' (sqGen h i)))
    (g : (DSq h : Type)) : (2 : ℤ_[2]) ∣ toAdd (nu' g) - toAdd (mu' g) := by
  have hext : sqNuParity nu' = sqNuParity mu' := by
    refine dsq_hom_ext _ _ fun i => ?_
    obtain ⟨s, hs⟩ := hgen i
    have hsplit : toAdd (nu' (sqGen h i))
        = toAdd (mu' (sqGen h i)) + (2 : ℤ_[2]) * s := by linear_combination hs
    show zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (nu' (sqGen h i)))
      = zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (mu' (sqGen h i)))
    rw [hsplit, zpowZtwo_add, zpowZtwo_negOne_eq_one_iff.mpr ⟨s, rfl⟩, mul_one]
  have hg : zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (nu' g))
      = zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (mu' g)) :=
    DFunLike.congr_fun hext g
  refine zpowZtwo_negOne_eq_one_iff.mp ?_
  rw [show toAdd (nu' g) - toAdd (mu' g) = toAdd (nu' g) + (-(toAdd (mu' g))) by ring,
    zpowZtwo_add, hg, ← zpowZtwo_add, add_neg_cancel, zpowZtwo_zero_exp]

/-- A marking with even generator rows is even everywhere. -/
theorem two_dvd_toAdd_of_gen {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h i))) (g : (DSq h : Type)) :
    (2 : ℤ_[2]) ∣ toAdd (nu' g) := by
  have hext : sqNuParity nu'
      = (zpowZtwoHom isProP_two_unitsPadicInt (1 : ℤ_[2]ˣ)).comp nu' := by
    refine dsq_hom_ext _ _ fun i => ?_
    show zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) (toAdd (nu' (sqGen h i)))
      = zpowZtwo isProP_two_unitsPadicInt (1 : ℤ_[2]ˣ) (toAdd (nu' (sqGen h i)))
    rw [zpowZtwo_one_base, zpowZtwo_negOne_eq_one_iff.mpr (hgen i)]
  refine zpowZtwo_negOne_eq_one_iff.mp ?_
  have hg := DFunLike.congr_fun hext g
  rw [show sqNuParity nu' g = zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ)
    (toAdd (nu' g)) from rfl] at hg
  rw [hg]
  show zpowZtwo isProP_two_unitsPadicInt (1 : ℤ_[2]ˣ) (toAdd (nu' g)) = 1
  rw [zpowZtwo_one_base]

end Parity

/-! ## §4 What joint surjectivity buys -/

section Buys

variable {h : ℕ}

/-- The pivot row of a marking, in coordinates. -/
theorem toAdd_nu_sqPivot (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (sqPivot h))
      = toAdd (nu' (dsqSigma h)) - sqPivotExp * toAdd (nu' (dsqX0 h)) :=
  toAdd_nu_sqMixPivotElem nu' sqPivotExp

/-- **The bad shape**: if the pivot row and every handle row are even then `(χ_sq, ν')` misses
`(1, 1)`.  Either `ν'` is even on every generator, or it agrees with the χ-exponent row `λ`
modulo `2` on every generator — and `λ` is even wherever `χ_sq` is trivial. -/
theorem not_sqJointSurjective_of_even
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hpiv : (2 : ℤ_[2]) ∣ toAdd (nu' (sqPivot h)))
    (hU : ∀ j : Fin h, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h (sqHandleIdxU j))))
    (hV : ∀ j : Fin h, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h (sqHandleIdxV j)))) :
    ¬ SqJointSurjective h nu' := by
  intro H
  obtain ⟨g, hchi, hnu⟩ := H 1 1
  have hone : toAdd (nu' g) = 1 := by rw [hnu, toAdd_ofAdd]
  have hnotdvd : ¬ (2 : ℤ_[2]) ∣ (1 : ℤ_[2]) := isUnit_iff_not_two_dvd.mp isUnit_one
  rw [toAdd_nu_sqPivot] at hpiv
  obtain ⟨p, hp⟩ := hpiv
  have hx1 : toAdd (nu' (dsqX1 h)) = 2 * toAdd (nu' (dsqX0 h)) := toAdd_nu_dsqX1 nu'
  by_cases hbpar : (2 : ℤ_[2]) ∣ toAdd (nu' (dsqX0 h))
  · obtain ⟨t, ht⟩ := hbpar
    have hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h i)) := by
      intro i
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨p + sqPivotExp * t, by
          rw [show sqGen h 0 = dsqSigma h from rfl]; linear_combination hp + sqPivotExp * ht⟩
      · exact ⟨t, by rw [show sqGen h 1 = dsqX0 h from rfl]; exact ht⟩
      · exact ⟨2 * t, by rw [show sqGen h 2 = dsqX1 h from rfl, hx1, ht]⟩
      · exact hU j
      · exact hV j
    exact hnotdvd (hone ▸ two_dvd_toAdd_of_gen nu' hgen g)
  · have hbu : IsUnit (toAdd (nu' (dsqX0 h))) := isUnit_iff_not_two_dvd.mpr hbpar
    obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit hbu isUnit_one
    have hgen : ∀ i, (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h i)) - toAdd (nuLam h (sqGen h i)) := by
      intro i
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · refine ⟨p + sqPivotExp * q, ?_⟩
        rw [show sqGen h 0 = dsqSigma h from rfl, nuLam_sigma, toAdd_ofAdd]
        linear_combination hp + sqPivotExp * hq
      · refine ⟨q, ?_⟩
        rw [show sqGen h 1 = dsqX0 h from rfl, nuLam_x0, toAdd_ofAdd]
        linear_combination hq
      · refine ⟨2 * q, ?_⟩
        rw [show sqGen h 2 = dsqX1 h from rfl, hx1, nuLam_x1, toAdd_ofAdd]
        linear_combination 2 * hq
      · rw [nuLam_handleU, toAdd_one, sub_zero]; exact hU j
      · rw [nuLam_handleV, toAdd_one, sub_zero]; exact hV j
    obtain ⟨r, hr⟩ := two_dvd_toAdd_sub_of_gen nu' (nuLam h) hgen g
    obtain ⟨l, hl⟩ := two_dvd_toAdd_nuLam_of_chiSq_eq_one hchi
    exact hnotdvd ⟨r + l, by linear_combination hr - hone + hl⟩

/-- **What joint surjectivity buys**: the pivot row is a unit, or some handle row is. -/
theorem sqJointSurjective_isUnit_pivot_or_handle
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (H : SqJointSurjective h nu') :
    IsUnit (toAdd (nu' (sqPivot h))) ∨
      ∃ j : Fin h, IsUnit (toAdd (nu' (sqGen h (sqHandleIdxU j))))
        ∨ IsUnit (toAdd (nu' (sqGen h (sqHandleIdxV j)))) := by
  by_contra hcon
  refine not_sqJointSurjective_of_even nu' ?_ (fun j => ?_) (fun j => ?_) H
  · by_contra hc
    exact hcon (Or.inl (isUnit_iff_not_two_dvd.mpr hc))
  · by_contra hc
    exact hcon (Or.inr ⟨j, Or.inl (isUnit_iff_not_two_dvd.mpr hc)⟩)
  · by_contra hc
    exact hcon (Or.inr ⟨j, Or.inr (isUnit_iff_not_two_dvd.mpr hc)⟩)

/-- At `h = 0` joint surjectivity **is** the unit pivot row: one bit. -/
theorem sqJointSurjective_isUnit_pivot_zero
    {nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])}
    (H : SqJointSurjective 0 nu') : IsUnit (toAdd (nu' (sqPivot 0))) := by
  rcases sqJointSurjective_isUnit_pivot_or_handle H with hp | ⟨j, _⟩
  · exact hp
  · exact absurd j.isLt (by omega)

end Buys

/-! ## §5 The pivot core move, and the normalisation of the core rows -/

section Moves

variable {h : ℕ}

/-- **The pivot core move at `(m, k)`**: a χ-preserving automorphism dressing `σ` by `w^m` and
`x₀` by `w^k` (`w = sqPivot h`, χ-trivial), so that the two core rows move by multiples of the
pivot row and every handle row is fixed. -/
def SqPivotCoreMove (h : ℕ) (m k : ℤ_[2]) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ toAdd (nu' (Ψ (dsqSigma h)))
            = toAdd (nu' (dsqSigma h)) + m * toAdd (nu' (sqPivot h))
        ∧ toAdd (nu' (Ψ (dsqX0 h)))
            = toAdd (nu' (dsqX0 h)) + k * toAdd (nu' (sqPivot h))
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = nu' (sqGen h (sqHandleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = nu' (sqGen h (sqHandleIdxV j)))

/-- **The handle-to-core transfer at the letter `i`**: a χ-preserving automorphism dressing `σ`
by the (χ-trivial) handle letter `sqGen h i`, so that the `σ`-row absorbs that handle row. -/
def SqHandleToCoreMove (h : ℕ) (i : Fin (sqRank h)) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ toAdd (nu' (Ψ (dsqSigma h)))
            = toAdd (nu' (dsqSigma h)) + toAdd (nu' (sqGen h i))
        ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = nu' (sqGen h (sqHandleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = nu' (sqGen h (sqHandleIdxV j)))

/-- **One move normalizes both core rows.**  With `d = ν'(w)` a unit, the parameters
`m = (1 − a)·d⁻¹`, `k = −b·d⁻¹` land the core rows on `(1, 0)`, and the family's abelianized
determinant `1 + m − k·c₀` equals `d⁻¹` — a unit for free.  Both parity classes of `(a, b)` are
covered: at `(a, b) ≡ (0, 1)` both parameters are odd and the move is the mod-2 swap. -/
theorem sqCoreRows_of_pivotMove
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove h m k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hd : IsUnit (toAdd (nu' (sqPivot h)))) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
        ∧ nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = nu' (sqGen h (sqHandleIdxU j)))
        ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = nu' (sqGen h (sqHandleIdxV j))) := by
  obtain ⟨e, he⟩ := hd
  set d : ℤ_[2] := toAdd (nu' (sqPivot h)) with hdd
  set a : ℤ_[2] := toAdd (nu' (dsqSigma h)) with haa
  set b : ℤ_[2] := toAdd (nu' (dsqX0 h)) with hbb
  set einv : ℤ_[2] := ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hei
  have hde : d * einv = 1 := by
    rw [hei, ← he, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hpivot : d = a - sqPivotExp * b := toAdd_nu_sqPivot nu'
  have hdet : 1 + (1 - a) * einv - (-b * einv) * sqPivotExp = einv := by
    linear_combination (-1 : ℤ_[2]) * hde + einv * hpivot
  obtain ⟨Ψ, hchi, hs, hx, hU, hV⟩ :=
    hmv ((1 - a) * einv) (-b * einv) (by rw [hdet, hei]; exact (e⁻¹).isUnit) nu'
  refine ⟨Ψ, hchi, ?_, ?_, hU, hV⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [hs, toAdd_ofAdd]
    linear_combination (1 - a) * hde
  · refine Multiplicative.toAdd.injective ?_
    rw [hx, toAdd_ofAdd]
    linear_combination (-b) * hde

end Moves


/-! ## §6 The assembly -/

section Assembly

variable {h : ℕ}

/-- The pivot row of a marking pushed through an automorphism, in core-row coordinates. -/
theorem toAdd_aut_sqPivot (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    toAdd (nu' (Ψ (sqPivot h)))
      = toAdd (nu' (Ψ (dsqSigma h))) - sqPivotExp * toAdd (nu' (Ψ (dsqX0 h))) :=
  toAdd_nu_sqPivot (nu'.comp (autHom Ψ))

/-- **The transfer step**: an even pivot row plus a unit row at a χ-trivial letter `i` gives, via
one handle-to-core move, a marking with a **unit** pivot row.

⚠ **DEAD at `h ≥ 1` at every letter its consumers use: no instance can fire.**  The hypothesis
`SqHandleToCoreMove h i` is refuted at `i = sqHandleIdxU j` by
`PivotClimb.not_sqHandleToCoreMove_handleU` and at `i = sqHandleIdxV j` by
`PivotClimb.not_sqHandleToCoreMove_handleV` — and those handle letters are the only values of
`i` any consumer instantiates (`sqNuOrientedClear_of_moves` below, and
`PivotCoreMoves.sqNuOrientedClear_of_families`).  The refuting mechanism is the display in this
very proof: the transfer shifts the pivot row by *exactly* the transferred letter's row, and
that row's parity is fixed by every χ-preserving automorphism.

Kept because the implication is true, because it states the transfer's exact arithmetic
(`d ↦ d + ν'(g_i)`), and because it is what made the refutation possible: it is precisely
because the transfers' whole contribution is this one parity bit that refuting the bit refutes
the transfers. -/
theorem isUnit_pivot_of_handleToCore
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {i : Fin (sqRank h)} (hmix : SqHandleToCoreMove h i)
    (hdeven : (2 : ℤ_[2]) ∣ toAdd (nu' (sqPivot h)))
    (hiu : IsUnit (toAdd (nu' (sqGen h i)))) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ IsUnit (toAdd (nu' (Ψ (sqPivot h)))) := by
  obtain ⟨Ψ, hchi, hs, hx, _, _⟩ := hmix nu'
  refine ⟨Ψ, hchi, ?_⟩
  have hx' : toAdd (nu' (Ψ (dsqX0 h))) = toAdd (nu' (dsqX0 h)) := by rw [hx]
  have hval : toAdd (nu' (Ψ (sqPivot h)))
      = toAdd (nu' (sqPivot h)) + toAdd (nu' (sqGen h i)) := by
    rw [toAdd_aut_sqPivot, hs, hx', toAdd_nu_sqPivot]
    ring
  rw [hval]
  refine isUnit_iff_not_two_dvd.mpr fun hc => ?_
  obtain ⟨s, hs'⟩ := hdeven
  obtain ⟨u, hu'⟩ := hc
  exact (isUnit_iff_not_two_dvd.mp hiu) ⟨u - s, by linear_combination hu' - hs'⟩

/-- **The oriented residual over the move families.**  Three inputs: the banked χ-preserving
handle stratum at the canonical exponent, the pivot core family, and one handle-to-core transfer
per handle letter.  Joint surjectivity supplies the unit pivot row (§4) — directly, or after one
transfer.

⚠ **DEAD at `h ≥ 1`, on both sides: this theorem is vacuous, and its conclusion is false.**
This is the committed assembly, so the annotation matters most here.

* *Hypotheses refuted*: `hmixU` by `PivotClimb.not_sqHandleToCoreMove_handleU`, `hmixV` by
  `PivotClimb.not_sqHandleToCoreMove_handleV` (and jointly by
  `PivotClimb.not_sqHandleToCoreMove_families`).  So no `h ≥ 1` instance can fire.
* *Conclusion refuted*: `SqNuOrientedClear h` is itself false at every `h ≥ 1`
  (`PivotClimb.not_sqNuOrientedClear`), with the explicit witness `nuHandleU h 0 0 j` — a
  jointly-surjective marking whose pivot row is **even**.  So this implication cannot be
  repaired by strengthening its hypotheses: only the target can change.

The live `h ≥ 1` replacements, both of which drop the transfers entirely: the corrected target
`PivotClimb.SqNuOrientedClearAtUnitPivot h` with
`PivotClimb.sqNuOrientedClearAtUnitPivot_of_pivotMoves`, and — on the model side — the
unit-pivot row supplied arithmetically by P3 rather than by a move
(`PivotClimb` §9).  `PivotUnitizer.sqNuOrientedClear_of_moves'` is the regression pin that keeps
this statement's shape reachable from the reduced supply list.

The two remaining hypotheses are untouched by all of this: `hfix`
(`SqHandleMixFixesCore h sqPivotExp`, cut to `HandleEichler.SqChiNuClearHypothesis h`) and `hmv`
(the pivot core family) are open, not refuted.  `h = 0` is fully live. -/
theorem sqNuOrientedClear_of_moves
    (hfix : SqHandleMixFixesCore h sqPivotExp)
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove h m k)
    (hmixU : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxU j))
    (hmixV : ∀ j : Fin h, SqHandleToCoreMove h (sqHandleIdxV j)) :
    SqNuOrientedClear h := by
  intro nu' hjs
  obtain ⟨Ψ₀, hchi₀, hpiv₀⟩ :
      ∃ Ψ₀ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ₀ x) = chiSq h x) ∧ IsUnit (toAdd (nu' (Ψ₀ (sqPivot h)))) := by
    by_cases hd : IsUnit (toAdd (nu' (sqPivot h)))
    · exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, hd⟩
    · have hdeven : (2 : ℤ_[2]) ∣ toAdd (nu' (sqPivot h)) := by
        by_contra hc
        exact hd (isUnit_iff_not_two_dvd.mpr hc)
      obtain ⟨j, hj⟩ := (sqJointSurjective_isUnit_pivot_or_handle hjs).resolve_left hd
      rcases hj with hu | hv
      · exact isUnit_pivot_of_handleToCore nu' (hmixU j) hdeven hu
      · exact isUnit_pivot_of_handleToCore nu' (hmixV j) hdeven hv
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

/-- **The `h = 0` face**: no handles, and the χ-preserving handle stratum is a theorem there, so
the oriented residual reduces to the pivot core family **alone**. -/
theorem sqNuOrientedClear_zero_of_pivotMoves
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove 0 m k) :
    SqNuOrientedClear 0 :=
  sqNuOrientedClear_of_moves (sqHandleMixFixesCore_zero sqPivotExp) hmv
    (fun j => j.elim0) (fun j => j.elim0)

/-- The same, forgetting the orientation: the joint residual over the pivot family. -/
theorem sqNuJointClear_zero_of_pivotMoves
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove 0 m k) :
    SqNuJointClear 0 :=
  sqNuJointClear_of_orientedClear (sqNuOrientedClear_zero_of_pivotMoves hmv)

end Assembly

/-! ## §7 The basis-transitivity pivot -/

section Transitivity

/-- **An automorphism is all a frame ever needs.**  A tuple in the `Aut(D_sq h)`-orbit of the
standard generators kills the relator, by naturality of the relator word.  So any route that
exhibits a `ν`-adapted frame as the automorphic image of a presenting one — the uniqueness half
of the Demushkin classification — closes the odd-degree relator clause outright. -/
theorem sqRelWord_of_aut {h : ℕ} (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (m : Fin (sqRank h) → (DSq h : Type)) (hm : ∀ i, m i = Ψ (sqGen h i)) :
    sqRelWord m = 1 := by
  have hfun : m = fun i => (autHom Ψ) (sqGen h i) := funext hm
  rw [hfun, ← map_sqRelWord (autHom Ψ) (sqGen h), dsq_relation h, map_one]

end Transitivity

/-! ## §8 Stress pins -/

section StressTests

/-- The joint statement, spelled through the named precondition. -/
example (h : ℕ) (H : SqNuJointClear h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hjs : SqJointSurjective h nu') :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type), ∀ x, nu' (Ψ x) = nuSq h x :=
  H nu' hjs

/-- The standard marking has a unit pivot row, so the precondition of §5 is satisfiable. -/
example (h : ℕ) : IsUnit (toAdd (nuSq h (sqPivot h))) := isUnit_nuSq_sqPivot h

/-- The pivot is χ-trivial — the reason the core moves preserve the orientation. -/
example (h : ℕ) : chiSq h (sqPivot h) = 1 := chiSq_sqPivot h

/-- One handle: the residual over the three families.

⚠ **VACUOUS as stated**: `hmixU 0` and `hmixV 0` are both refuted at `h = 1`
(`PivotClimb.not_sqHandleToCoreMove_handleU`/`_handleV`), and the conclusion
`SqNuOrientedClear 1` is refuted too (`PivotClimb.not_sqNuOrientedClear`).  Kept as the shape
pin for `sqNuOrientedClear_of_moves`; the live `h = 1` reading is the unit-pivot target
`PivotClimb.SqNuOrientedClearAtUnitPivot 1`. -/
example (hfix : SqHandleMixFixesCore 1 sqPivotExp)
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove 1 m k)
    (hmixU : ∀ j : Fin 1, SqHandleToCoreMove 1 (sqHandleIdxU j))
    (hmixV : ∀ j : Fin 1, SqHandleToCoreMove 1 (sqHandleIdxV j)) :
    SqNuOrientedClear 1 :=
  sqNuOrientedClear_of_moves hfix hmv hmixU hmixV

/-- At `h = 0` the pivot family alone suffices. -/
example (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqPivotCoreMove 0 m k) :
    SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_pivotMoves hmv

/-- The standard generators kill the relator — `sqRelWord_of_aut` at the identity. -/
example (h : ℕ) : sqRelWord (sqGen h) = 1 :=
  sqRelWord_of_aut (ContinuousMulEquiv.refl _) (sqGen h) fun _ => rfl

end StressTests

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms SqJointSurjective
#print axioms SqNuJointClear
#print axioms SqNuOrientedClear
#print axioms SqNuCoreRows
#print axioms sqNuCoreRows_of_jointClear
#print axioms sqNuJointClear_of_coreRows
#print axioms sqNuJointClear_iff_coreRows
#print axioms sqNuJointClear_zero_iff
#print axioms eq_one_of_zpowZtwo_eq_one_of_isUnit
#print axioms two_dvd_toAdd_nuLam_of_chiSq_eq_one
#print axioms zpowZtwo_negOne_eq_one_iff
#print axioms two_dvd_toAdd_sub_of_gen
#print axioms two_dvd_toAdd_of_gen
#print axioms not_sqJointSurjective_of_even
#print axioms sqJointSurjective_isUnit_pivot_or_handle
#print axioms sqJointSurjective_isUnit_pivot_zero
#print axioms SqPivotCoreMove
#print axioms SqHandleToCoreMove
#print axioms sqCoreRows_of_pivotMove
#print axioms isUnit_pivot_of_handleToCore
#print axioms sqNuOrientedClear_of_moves
#print axioms sqNuOrientedClear_zero_of_pivotMoves
#print axioms sqNuJointClear_zero_of_pivotMoves
#print axioms sqRelWord_of_aut

end AxiomPins

end SqCore

end Dyadic

end GQ2
