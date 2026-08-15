/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.PivotClimb
import GQ2.Dyadic.SqCore.GradedOddClose
import GQ2.Dyadic.Instances.OddFrame

/-!
# W84-CLEAR: the model clearing collapses onto the row plane

The odd route's last item is the model-only Prop `SqNuOrientedClearAtUnitPivot h`: every
jointly-surjective marking of `D_sq(h)` with a unit pivot row is corrected onto `nu_sq` by a
chi-preserving automorphism.  The committed producers ask for automorphism families at EVERY
marking: `sqNuOrientedClearAtUnitPivot_of_pivotMoves` wants the whole unit-determinant pivot
family `SqPivotCoreMove h m k`, and `_of_families` wants the two one-parameter subgroups, each a
`forall nu'` statement.

This module proves that the wave-80 closure already pays for everything EXCEPT the row plane.

## The engine (section 2)

`gClear_transport`: for every marking `nu'` with a unit pivot row `d`, there is a
chi-preserving automorphism `u` with `nu' o u = nuSqOf h a b` - the MODEL marking carrying the
same two core rows `(a, b) = (nu'(sigma), nu'(x0))`, trivial handle rows, and the forced
`x1`-row.  The proof is three committed pieces snapped together:

* the lambda-twist `mu := nuTwist nu' d⁻¹ b = d⁻¹(nu' - b·lambda)` (`HandleEichler` section 2)
  is a SELECTED marking - `mu(sigma) = 1`, `mu(x0) = 0` - because the pivot `w` is
  lambda-trivial;
* wave 80's `gOdd_lamNuClear` hands a lambda-preserving `u` with `mu o u = nu_sq`;
* since `nu' = d·mu + b·lambda` pointwise and `u` preserves `lambda` exactly, `nu' o u` is the
  explicit combination `d·nu_sq + b·lambda`, which IS `nuSqOf h a b`
  (`gClear_nuSqOf_eq_twist`).

So the graded closure quotients the clearing by everything except the two-parameter row datum:
the marking quantifier of the residual collapses onto the EXPLICIT family `nuSqOf h a b`.

## What the residual becomes (sections 1, 3)

`GClearModelMove h a b`: a chi-preserving automorphism putting the two core rows of the single
explicit marking `nuSqOf h a b` at `(1, 0)`.  Two rows only - no handle clause, no clause at
`x1`, no marking binder: `gOdd_markedMatching` upgrades the two rows to the full correction
(`gClear_modelMove_full`), and `gClear_clearing_of_model` closes the loop:

* `gClear_clearing_of_model : (forall a b, IsUnit (a - c0·b) -> GClearModelMove h a b) ->
  SqNuOrientedClearAtUnitPivot h`.

Against the committed reductions this changes the residual's shape twice over.  The `forall
nu'` binder is GONE: what remains is a family of single-marking instances indexed by the row
plane, and at the model markings every handle letter and every commutator is invisible, so a
future word-level construction has the handle block available as correction material - the
uniform moves never did.  And the handle stratum binder is gone too: the committed
`_of_families` route asks for `hfix` plus two families; here `hfix` is wave 80's
`gOdd_pivotFix`, a theorem, so the subsumption `gClear_clearing_of_families` needs the two
families alone (section 4) - strictly fewer binders than the committed producer.

## The ray decomposition (section 4)

`gClear_modelMove_of_ray`: the model moves on the whole unit locus follow from the two
one-parameter rays through it - the translations `GClearModelTranslate h c` (pivot row `1`,
rows `(1 + c0·c, c)`) and the scalings `GClearModelScale h d` (rows `(d, 0)`).  The scaling
identity `nuSqOf h (d·a') (d·b') = d · nuSqOf h a' b'` is an instance of the lambda-twist at
`s = 0`, so the splitting costs two `dsq_hom_ext` computations and nothing else.

## What this does NOT do

No unconditional `gClear_clearing h`.  The model moves at `h >= 1` are genuinely open: they are
the first row-moving automorphisms the model side would ever produce (the h = 0 instances ride
the committed arithmetic affine family of `D_0`, axioms B8 + B3c - see the pins), and nothing
in the tree at `h >= 1` moves rows.  The honest landing is the reduction: the odd route's last
item is now `forall (a b) on the unit locus, GClearModelMove h a b` - one two-parameter family
of explicit single-marking instances, with `gClear_supply_of_model` and
`gClear_candidateEquiv_of_model` (section 5) carrying it through wave 83's seam to the
`L`-row branch datum and the general theorem at every odd-degree field.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  The model-side chain (sections 1-4 headline
theorems) prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`) - the wave-80 closure
is axiom-free and so is everything here built on it.  The `h = 0` pins add the committed census
members `dyadicOrientation` (B3c) and `peripheralCyclotomicAction` (B8) they always cost.  The
section 5 seam composites print std-3 + {`hilbertSymbol_normCriterion_finiteDyadic`,
`tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
`Foundations.absGalQ2_localEulerCharacteristic`}; `localReciprocity` and `markedRecipAt` do not
appear because `Rec` and `B` are binders here.  Census unchanged.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The residual as a row-plane family -/

section ModelMove

/-- **The model move at `(a, b)`**: a chi-preserving automorphism carrying the two core rows of
the single explicit marking `nuSqOf h a b` onto the P3-selected values `(1, 0)`.  Two rows and
one marking: no handle clause, no `x1` clause, no marking quantifier.  This is the exact shape
`gClear_clearing_of_model` consumes, and by `gClear_modelMove_full` it upgrades itself to the
full correction `nuSqOf h a b o Psi = nu_sq` through wave 80's matching. -/
def GClearModelMove (h : ℕ) (a b : ℤ_[2]) : Prop :=
  ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
    (∀ x, chiSq h (Ψ x) = chiSq h x)
      ∧ nuSqOf h a b (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
      ∧ nuSqOf h a b (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])

/-- The base point `(1, 0)` is free: `nuSqOf h 1 0` already carries the selected rows. -/
theorem gClear_modelMove_one_zero (h : ℕ) : GClearModelMove h 1 0 := by
  refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, ?_, ?_⟩
  · show nuSqOf h 1 0 (dsqSigma h) = ofAdd (1 : ℤ_[2])
    exact nuSqOf_sigma h 1 0
  · show nuSqOf h 1 0 (dsqX0 h) = ofAdd (0 : ℤ_[2])
    exact nuSqOf_x0 h 1 0

end ModelMove

/-! ## §2 The wave-80 transport: the marking quantifier collapses onto the row plane -/

section Transport

variable {h : ℕ}

/-- **The model marking is a lambda-twist of the standard one**: whenever `d·e = 1` and
`d = a - c0·b`, the marking `nuSqOf h a b` is `d·nu_sq + b·lambda`, spelled through the
committed twist `nuTwist (nu_sq) d (-(e·b)) = d·(nu_sq + e·b·lambda)`.  Four generator rows,
one `dsq_hom_ext`. -/
theorem gClear_nuSqOf_eq_twist {a b d e : ℤ_[2]} (hde : d * e = 1)
    (hd : d = a - sqPivotExp * b) :
    nuSqOf h a b = nuTwist (nuSq h) d (-(e * b)) := by
  refine dsq_hom_ext _ _ fun i => ?_
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show sqGen h 0 = dsqSigma h from rfl, nuSqOf_sigma, toAdd_ofAdd, toAdd_nuTwist,
      nuSq_sigma, nuLam_sigma, toAdd_ofAdd, toAdd_ofAdd]
    linear_combination -hd - sqPivotExp * b * hde
  · rw [show sqGen h 1 = dsqX0 h from rfl, nuSqOf_x0, toAdd_ofAdd, toAdd_nuTwist,
      nuSq_x0, nuLam_x0, toAdd_ofAdd, toAdd_ofAdd]
    linear_combination -b * hde
  · rw [show sqGen h 2 = dsqX1 h from rfl, nuSqOf_x1, toAdd_ofAdd, toAdd_nuTwist,
      nuSq_x1, nuLam_x1, toAdd_ofAdd, toAdd_ofAdd]
    linear_combination -2 * b * hde
  · rw [nuSqOf_handleU, toAdd_one, toAdd_nuTwist, nuSq_handleU, nuLam_handleU, toAdd_one]
    ring
  · rw [nuSqOf_handleV, toAdd_one, toAdd_nuTwist, nuSq_handleV, nuLam_handleV, toAdd_one]
    ring

/-- ⭐⭐⭐ **The transport**: every marking with a unit pivot row is chi-equivalent to the model
marking carrying its own two core rows.  The lambda-twist `d⁻¹(nu' - b·lambda)` is a selected
marking, wave 80's `gOdd_lamNuClear` corrects it onto `nu_sq` by a lambda-preserving
automorphism `u`, and untwisting along the SAME `u` - legitimate exactly because `u` preserves
`lambda` on the nose - lands `nu' o u` on `d·nu_sq + b·lambda = nuSqOf h a b`.

This is the statement that the wave-80 dividend DOES reach arbitrary unit-pivot markings: the
graded closure quotients the clearing residual by everything except the row plane. -/
theorem gClear_transport (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {a b : ℤ_[2]} (ha : toAdd (nu' (dsqSigma h)) = a) (hb : toAdd (nu' (dsqX0 h)) = b)
    (hpiv : IsUnit (toAdd (nu' (sqPivot h)))) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nu' (u x) = nuSqOf h a b x := by
  obtain ⟨e, he⟩ := hpiv
  set einv : ℤ_[2] := ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hei
  have hed : einv * toAdd (nu' (sqPivot h)) = 1 := by
    rw [hei, ← he, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hde : toAdd (nu' (sqPivot h)) * einv = 1 := by rw [mul_comm]; exact hed
  have hpivrow : toAdd (nu' (sqPivot h)) = a - sqPivotExp * b := by
    rw [toAdd_nu_sqPivot nu', ha, hb]
  -- the normalizing lambda-twist is a selected marking
  have hsig : nuTwist nu' einv (toAdd (nu' (dsqX0 h))) (dsqSigma h) = ofAdd (1 : ℤ_[2]) :=
    nuTwist_sigma_eq_one nu' hed
  have hx0 : nuTwist nu' einv (toAdd (nu' (dsqX0 h))) (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
    nuTwist_x0_eq_zero nu' einv
  -- wave 80 corrects it onto the standard marking, preserving lambda exactly
  obtain ⟨u, hlam, hval⟩ := gOdd_lamNuClear h (nuTwist nu' einv (toAdd (nu' (dsqX0 h)))) hsig hx0
  refine ⟨u, (chiSq_preserving_iff_nuLam u).mpr hlam, fun x => ?_⟩
  -- untwist along u
  refine Multiplicative.toAdd.injective ?_
  have h1 : toAdd (nuTwist nu' einv (toAdd (nu' (dsqX0 h))) (u x))
      = einv * (toAdd (nu' (u x)) - toAdd (nu' (dsqX0 h)) * toAdd (nuLam h (u x))) :=
    toAdd_nuTwist nu' einv (toAdd (nu' (dsqX0 h))) (u x)
  have h2 : toAdd (nuTwist nu' einv (toAdd (nu' (dsqX0 h))) (u x)) = toAdd (nuSq h x) :=
    congrArg toAdd (hval x)
  have h3 : toAdd (nuLam h (u x)) = toAdd (nuLam h x) := congrArg toAdd (hlam x)
  have h4 : toAdd (nuSqOf h a b x)
      = toAdd (nu' (sqPivot h)) * (toAdd (nuSq h x) + einv * b * toAdd (nuLam h x)) := by
    rw [gClear_nuSqOf_eq_twist hde hpivrow, toAdd_nuTwist]
    ring
  rw [h4, ← h2, h1, h3, hb]
  linear_combination -(toAdd (nu' (u x))) * hde

end Transport

/-! ## §3 The upgrade and the reduction -/

section Reduction

variable {h : ℕ}

/-- **Two rows buy the whole correction**: a model move composes with wave 80's marked matching
(applied to the transported marking, whose two core rows the move has just selected) into the
full statement `nuSqOf h a b o Psi = nu_sq`. -/
theorem gClear_modelMove_full {a b : ℤ_[2]} (H : GClearModelMove h a b) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ ∀ x, nuSqOf h a b (Ψ x) = nuSq h x := by
  obtain ⟨Θ, hchi, hs, hx⟩ := H
  obtain ⟨u, hchi₂, hval₂⟩ := gOdd_markedMatching h ((nuSqOf h a b).comp (autHom Θ)) hs hx
  refine ⟨u.trans Θ, fun x => ?_, fun x => ?_⟩
  · show chiSq h (Θ (u x)) = chiSq h x
    rw [hchi, hchi₂]
  · show nuSqOf h a b (Θ (u x)) = nuSq h x
    exact hval₂ x

/-- ⭐⭐⭐ **The reduction**: the model moves on the unit locus discharge the odd route's last
item.  Compare the committed producers, whose family binders quantify over EVERY marking: here
the marking quantifier is spent by `gClear_transport`, and what remains is the two-parameter
family of explicit single-marking instances. -/
theorem gClear_clearing_of_model
    (H : ∀ a b : ℤ_[2], IsUnit (a - sqPivotExp * b) → GClearModelMove h a b) :
    SqNuOrientedClearAtUnitPivot h := by
  intro nu' _ hpiv
  obtain ⟨u, hchi₁, hval₁⟩ := gClear_transport nu' rfl rfl hpiv
  have hd : IsUnit (toAdd (nu' (dsqSigma h)) - sqPivotExp * toAdd (nu' (dsqX0 h))) := by
    rw [← toAdd_nu_sqPivot nu']
    exact hpiv
  obtain ⟨Θ, hchi₂, hval₂⟩ := gClear_modelMove_full (H _ _ hd)
  refine ⟨Θ.trans u, fun x => ?_, fun x => ?_⟩
  · show chiSq h (u (Θ x)) = chiSq h x
    rw [hchi₁, hchi₂]
  · show nu' (u (Θ x)) = nuSq h x
    rw [hval₁ (Θ x), hval₂ x]

end Reduction

/-! ## §4 The rays, and the subsumption of the committed routes -/

section Rays

variable {h : ℕ}

/-- **The translation ray**: the model moves along the pivot-row-one line, rows
`(1 + c0·c, c)`. -/
def GClearModelTranslate (h : ℕ) (c : ℤ_[2]) : Prop :=
  GClearModelMove h (1 + sqPivotExp * c) c

/-- **The scaling ray**: the model moves along the `x0`-row-zero line, rows `(d, 0)`. -/
def GClearModelScale (h : ℕ) (d : ℤ_[2]) : Prop := GClearModelMove h d 0

/-- The scaling identity behind the ray splitting: `nuSqOf h (d·a') (d·b')` is the
`s = 0` lambda-twist (i.e. the plain rescaling) of `nuSqOf h a' b'` by `d`. -/
theorem gClear_nuSqOf_smul (h : ℕ) (d a' b' : ℤ_[2]) :
    nuSqOf h (d * a') (d * b') = nuTwist (nuSqOf h a' b') d 0 := by
  refine dsq_hom_ext _ _ fun i => ?_
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show sqGen h 0 = dsqSigma h from rfl, nuSqOf_sigma, toAdd_ofAdd, toAdd_nuTwist,
      nuSqOf_sigma, toAdd_ofAdd]
    ring
  · rw [show sqGen h 1 = dsqX0 h from rfl, nuSqOf_x0, toAdd_ofAdd, toAdd_nuTwist,
      nuSqOf_x0, toAdd_ofAdd]
    ring
  · rw [show sqGen h 2 = dsqX1 h from rfl, nuSqOf_x1, toAdd_ofAdd, toAdd_nuTwist,
      nuSqOf_x1, toAdd_ofAdd]
    ring
  · rw [nuSqOf_handleU, toAdd_one, toAdd_nuTwist, nuSqOf_handleU, toAdd_one]
    ring
  · rw [nuSqOf_handleV, toAdd_one, toAdd_nuTwist, nuSqOf_handleV, toAdd_one]
    ring

/-- **The rays generate**: one translation instance and one scaling instance per point of the
unit locus produce every model move, mirroring `sqPivotCoreMove_of_translation_scaling` one
level down.  Both inputs enter through their full (`gClear_modelMove_full`) forms, so the
composite costs wave 80's matching twice and the two `dsq_hom_ext` identities above. -/
theorem gClear_modelMove_of_ray (htr : ∀ c : ℤ_[2], GClearModelTranslate h c)
    (hsc : ∀ d : ℤ_[2], IsUnit d → GClearModelScale h d) {a b : ℤ_[2]}
    (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b := by
  obtain ⟨e, he⟩ := hd
  set einv : ℤ_[2] := ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hei
  have hde : (a - sqPivotExp * b) * einv = 1 := by
    rw [hei, ← he, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- the translation instance at the scaled rows
  have htr' : GClearModelMove h (einv * a) (einv * b) := by
    have hrw : (1 : ℤ_[2]) + sqPivotExp * (einv * b) = einv * a := by
      linear_combination -hde
    have := htr (einv * b)
    rwa [GClearModelTranslate, hrw] at this
  obtain ⟨Θt, hchit, hvt⟩ := gClear_modelMove_full htr'
  obtain ⟨Θs, hchis, hvs⟩ := gClear_modelMove_full (hsc (a - sqPivotExp * b) ⟨e, he⟩)
  -- the two rescaling identities
  have e1 : nuSqOf h a b = nuTwist (nuSqOf h (einv * a) (einv * b)) (a - sqPivotExp * b) 0 := by
    have := gClear_nuSqOf_smul h (a - sqPivotExp * b) (einv * a) (einv * b)
    have hra : (a - sqPivotExp * b) * (einv * a) = a := by linear_combination a * hde
    have hrb : (a - sqPivotExp * b) * (einv * b) = b := by linear_combination b * hde
    rwa [hra, hrb] at this
  have e2 : nuSqOf h (a - sqPivotExp * b) 0 = nuTwist (nuSq h) (a - sqPivotExp * b) 0 := by
    have := gClear_nuSqOf_smul h (a - sqPivotExp * b) 1 0
    have hra : (a - sqPivotExp * b) * 1 = a - sqPivotExp * b := mul_one _
    have hrb : (a - sqPivotExp * b) * 0 = 0 := mul_zero _
    rw [hra, hrb] at this
    rw [this]
    congr 1
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show sqGen h 0 = dsqSigma h from rfl, nuSqOf_sigma, nuSq_sigma]
    · rw [show sqGen h 1 = dsqX0 h from rfl, nuSqOf_x0, nuSq_x0]
    · rw [show sqGen h 2 = dsqX1 h from rfl, nuSqOf_x1, nuSq_x1]
      norm_num
    · rw [nuSqOf_handleU, nuSq_handleU]
    · rw [nuSqOf_handleV, nuSq_handleV]
  -- translate, then scale
  have hkey : ∀ x, nuSqOf h a b (Θt x) = nuSqOf h (a - sqPivotExp * b) 0 x := by
    intro x
    refine Multiplicative.toAdd.injective ?_
    rw [e1, e2, toAdd_nuTwist, toAdd_nuTwist, congrArg toAdd (hvt x)]
    ring
  refine ⟨Θs.trans Θt, fun x => ?_, ?_, ?_⟩
  · show chiSq h (Θt (Θs x)) = chiSq h x
    rw [hchit, hchis]
  · show nuSqOf h a b (Θt (Θs (dsqSigma h))) = ofAdd (1 : ℤ_[2])
    rw [hkey, hvs, nuSq_sigma]
  · show nuSqOf h a b (Θt (Θs (dsqX0 h))) = ofAdd (0 : ℤ_[2])
    rw [hkey, hvs, nuSq_x0]

/-- **The committed families overpay**: the two one-parameter pivot families (each a statement
at EVERY marking) restrict to the model moves.  One application of the committed row
normalization `sqCoreRows_of_pivotMove` at the single marking `nuSqOf h a b`. -/
theorem gClear_modelMove_of_families (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a) {a b : ℤ_[2]}
    (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b := by
  have hpiv : IsUnit (toAdd (nuSqOf h a b (sqPivot h))) := by
    rw [toAdd_nuSqOf_sqPivot]
    exact hd
  obtain ⟨Ψ, hchi, hs, hx, -, -⟩ := sqCoreRows_of_pivotMove
    (fun m k hu => sqPivotCoreMove_of_translation_scaling m k (htr k) (hsc _ hu))
    (nuSqOf h a b) hpiv
  exact ⟨Ψ, hchi, hs, hx⟩

/-- **The clearing over the two families alone** - the committed producer's `hfix` binder is
wave 80's `gOdd_pivotFix`, so it is gone: two binders against
`sqNuOrientedClearAtUnitPivot_of_families`' three, and the two survivors are consumed only at
the model markings. -/
theorem gClear_clearing_of_families (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a) : SqNuOrientedClearAtUnitPivot h :=
  gClear_clearing_of_model fun _ _ hd => gClear_modelMove_of_families htr hsc hd

section DegreeOne

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The `h = 0` model moves are theorems**, riding the committed degree-one pivot seeds (the
arithmetic affine family of `D_0`; axioms B8 + B3c enter here and only here). -/
theorem gClear_modelMove_zero {a b : ℤ_[2]} (hd : IsUnit (a - sqPivotExp * b)) :
    GClearModelMove 0 a b :=
  gClear_modelMove_of_families (fun c => sqPivotTranslation_zero c)
    (fun _ ha => sqPivotScaling_zero ha) hd

/-- The new route reproves the committed `h = 0` clearing end to end. -/
theorem gClear_clearing_zero : SqNuOrientedClearAtUnitPivot 0 :=
  gClear_clearing_of_model fun _ _ hd => gClear_modelMove_zero hd

end DegreeOne

end Rays

/-! ## §5 The seam: the row-plane family carries the odd-degree classification -/

section Seam

open ContCoh LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The seam over the model moves**: the row-plane family implies `SqMarkedForwardSupply B h`
at every odd-degree `K`, through `gClear_clearing_of_model` and wave 83's `oddFrame_supply`. -/
theorem gClear_supply_of_model (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : ∀ a b : ℤ_[2], IsUnit (a - sqPivotExp * b) → GClearModelMove h a b) :
    SqMarkedForwardSupply B h :=
  oddFrame_supply B FF hdeg (gClear_clearing_of_model H)

/-- The `L`-row branch datum over the model moves. -/
theorem gClear_branchL_of_model (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : ∀ a b : ℤ_[2], IsUnit (a - sqPivotExp * b) → GClearModelMove h a b) :
    ∃ G : GenAsmBranch K B, G.pres = .L h :=
  oddFrame_genAsmBranch_L_of_clear B FF hdeg (gClear_clearing_of_model H)

/-- **The general theorem over the model moves**: at every odd-degree `K`, what remains beyond
the row-plane family is exactly the two record blocks `GenAsmFieldInputs` and
`GenAsmRowResidual`. -/
theorem gClear_candidateEquiv_of_model (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : ∀ a b : ℤ_[2], IsUnit (a - sqPivotExp * b) → GClearModelMove h a b) :
    ∃ G : GenAsmBranch K B, G.pres = .L h ∧
      ∀ F : GenAsmFieldInputs K B FF G.degree, GenAsmRowResidual G F.T →
        Nonempty (ContinuousMulEquiv
          ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  oddFrame_candidate_equiv_galK_of_clear B hdeg (gClear_clearing_of_model H)

/-- The seam over the two rays, the sharpest conditional form this wave leaves. -/
theorem gClear_supply_of_ray (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (htr : ∀ c : ℤ_[2], GClearModelTranslate h c)
    (hsc : ∀ d : ℤ_[2], IsUnit d → GClearModelScale h d) : SqMarkedForwardSupply B h :=
  gClear_supply_of_model B FF hdeg fun _ _ hd => gClear_modelMove_of_ray htr hsc hd

end Seam

/-! ## §6 Stress pins -/

section StressPins

/-- The transport at the standard marking itself is available and lands where it must. -/
example (h : ℕ) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nuSq h (u x) = nuSqOf h 1 0 x :=
  gClear_transport (nuSq h) (by rw [nuSq_sigma, toAdd_ofAdd]) (by rw [nuSq_x0, toAdd_ofAdd])
    (by rw [nuSq_sqPivot, toAdd_ofAdd]; exact isUnit_one)

/-- The base point of each ray is free. -/
example (h : ℕ) : GClearModelTranslate h 0 ∧ GClearModelScale h 1 := by
  constructor
  · have h0 : (1 : ℤ_[2]) + sqPivotExp * 0 = 1 := by ring
    rw [GClearModelTranslate, h0]
    exact gClear_modelMove_one_zero h
  · exact gClear_modelMove_one_zero h

/-- The committed three-binder route and the new two-binder route land on the same statement. -/
example (h : ℕ) (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a) :
    SqNuOrientedClearAtUnitPivot h ∧ SqNuOrientedClearAtUnitPivot h :=
  ⟨sqNuOrientedClearAtUnitPivot_of_families (gOdd_pivotFix h) htr hsc,
    gClear_clearing_of_families htr hsc⟩

/-- The `h = 0` landing agrees with wave 83's. -/
example [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    SqNuOrientedClearAtUnitPivot 0 ∧ SqNuOrientedClearAtUnitPivot 0 :=
  ⟨oddFrame_clearAtUnitPivot_zero, gClear_clearing_zero⟩

end StressPins

/-! ## §7 Axiom pins

Verified at generation time (`scripts/mirror.sh gen`):

* `GClearModelMove`, `gClear_modelMove_one_zero`, `gClear_nuSqOf_eq_twist`,
  `gClear_transport`, `gClear_modelMove_full`, `gClear_clearing_of_model`,
  `GClearModelTranslate`, `GClearModelScale`, `gClear_nuSqOf_smul`,
  `gClear_modelMove_of_ray`, `gClear_modelMove_of_families`, `gClear_clearing_of_families`
  print **std-3** (`propext`, `Classical.choice`, `Quot.sound`): the whole model-side chain,
  wave-80 closure included, is axiom-free beyond the standard three.
* `gClear_modelMove_zero`, `gClear_clearing_zero` print std-3 + {`dyadicOrientation` (B3c),
  `peripheralCyclotomicAction` (B8)}: the committed price of the `h = 0` arithmetic affine
  family, and nothing else.
* `gClear_supply_of_model`, `gClear_branchL_of_model`, `gClear_candidateEquiv_of_model`,
  `gClear_supply_of_ray` print std-3 + {`hilbertSymbol_normCriterion_finiteDyadic` (B11a),
  `tateDualityAt` (B7), `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`}.  `localReciprocity` (B1) and
  `markedRecipAt` (B6) are absent because `Rec` and `B` are binders of these statements; they
  re-enter only when a caller instantiates the bundle.
-/

section AxiomPins

#print axioms GClearModelMove
#print axioms gClear_modelMove_one_zero
#print axioms gClear_nuSqOf_eq_twist
#print axioms gClear_transport
#print axioms gClear_modelMove_full
#print axioms gClear_clearing_of_model
#print axioms GClearModelTranslate
#print axioms GClearModelScale
#print axioms gClear_nuSqOf_smul
#print axioms gClear_modelMove_of_ray
#print axioms gClear_modelMove_of_families
#print axioms gClear_clearing_of_families
#print axioms gClear_modelMove_zero
#print axioms gClear_clearing_zero
#print axioms gClear_supply_of_model
#print axioms gClear_branchL_of_model
#print axioms gClear_candidateEquiv_of_model
#print axioms gClear_supply_of_ray

end AxiomPins

end SqCore

end Dyadic

end GQ2
