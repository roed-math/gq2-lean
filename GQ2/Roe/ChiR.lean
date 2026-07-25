/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.CrossedDerivation
public import GQ2.Roe.OrientationRoot
public import GQ2.SectionThree
public import GQ2.FrattiniCriterion

@[expose] public section

/-!
# The canonical orientation `χ_R` of `D_R` and its image  (Roe note §3.3, ⟦prop:orientation⟧)

Assembles the canonical Demushkin orientation `χ_R : D_R → ℤ₂ˣ` of the Roe pro-2 group
(`GQ2/Roe/DRPresentation.lean`) out of the two halves that were kept parallel:

* the **crossed-derivation descent** (`GQ2/Roe/CrossedDerivation.lean`, ticket R9), which
  characterises the orientation datum `(S, X, Y)` abstractly as an `IsLabuteOrientationDatum`,
  and
* the **arithmetic solution** (`GQ2/Roe/OrientationRoot.lean`, ticket R10), which pins the
  values `X = χ_R x`, `S = χ_R s`, `Y = χ_R y` to the unique Hensel root of `Z³ + 2Z² + 1`.

The note's display eq. (orientationvalues) reads
```
Y = -X²,      X³ + 2X² + 1 = 0,      S = -X³ / (X² + X + 1),
X ≡ 5 (mod 16),      S ≡ 13 (mod 16),      im χ_R = {±1} × (1 + 4ℤ₂).
```

## Main definitions

* `rootXUnit`, `SvalUnit`, `YvalUnit : ℤ₂ˣ` — the orientation values `X, S, Y` bundled as
  units (`Sval = -X³·(X²+X+1)⁻¹` is a product of units; `Yval = -X²`);
* `chiR : ContinuousMonoidHom D_R ℤ₂ˣ` — the orientation character, built by the universal
  property `drLiftHom` (`GQ2/Roe/DRPresentation.lean`) at the triple `(S, X, Y)`; the relator
  dies because in the abelian target `drWord` collapses to `(X⁴)⁻¹Y²` and `Y² = X⁴`.

## Main results

* `chiR_drS`/`chiR_drX`/`chiR_drY` — the generator values `S, X, Y`;
* `isLabuteOrientation_chiR : IsLabuteOrientation χ_R.toMonoidHom` — `χ_R` *is* Labute's
  canonical orientation, discharged from `isLabuteOrientationDatum_of_root` with R10's
  `rootX_isRoot`/`Sval_mul_denom`/`Yval_eq`;
* `chiR_torsion : χ_R(y)·χ_R(x)⁻² = -1` — the note's `χ_R(t) = YX⁻² = -1` (eq. (tR)),
  phrased on the generator word `y·x⁻²` so it needs no abelianization;
* `chiR_surjective : Function.Surjective χ_R` — the **image statement** `im χ_R = ℤ₂ˣ`.
  Because every `2`-adic unit is `≡ ±1 (mod 4)`, the note's `{±1}×(1+4ℤ₂)` is *all* of `ℤ₂ˣ`,
  so the image equality is surjectivity — the same encoding as B3c's `surjective_chiTwo`
  (`GQ2/Orientation.lean`).

## The surjectivity proof

Rather than build the `2`-adic logarithm `1+4ℤ₂ ≅ 4ℤ₂` from the note, we run the pro-`2`
**Burnside / Frattini criterion** (`surjective_of_forall_not_le_index_p`,
`GQ2/FrattiniCriterion.lean`): a continuous hom into a pro-`2` group is surjective once its
range escapes every index-`2` open normal subgroup `M`.  Such an `M` contains all squares (its
quotient has order `2`); the image contains `χ_R(x) = X ≡ 5` and `χ_R(y·x⁻²) = -1 ≡ 7`, and
by the mod-`8` square decomposition `mod8_sq` (every unit is `s·w²` with `s ∈ {1,-1,±(-3)}`,
and `-3 ≡ 5 ≡ X (mod 8)`) the classes `{X, -1}` with the squares generate `ℤ₂ˣ`, so
`M = ⊤` — impossible at index `2`.

Cross-checked against ⟦prop:orientation⟧'s last display and the R2 spike
(`docs/orchestration/roe-r2-spike.md`).  All std-3.
-/

namespace GQ2.Roe

open GQ2.SectionThree

/-! ## Unit packaging of the orientation values

R10's `rootX`, `Sval`, `Yval` are `ℤ₂` elements; the character universal property and Labute
datum both need them as `ℤ₂ˣ` units.  (`Sval_isUnit`/`Yval_isUnit` are the "R10-side
nice-to-haves" flagged in the R7 design memo §R10.) -/

/-- `Y = -X²` is a unit (a negated power of the unit `X`). -/
theorem Yval_isUnit : IsUnit Yval := by
  rw [Yval_eq]; exact (rootX_isUnit.pow 2).neg

/-- `S = -X³/(X²+X+1)` is a unit: `S·(X²+X+1) = -X³` is a unit and `X²+X+1` is a unit
(`denom_isUnit`), so `S` is. -/
theorem Sval_isUnit : IsUnit Sval := by
  have h : IsUnit (Sval * (rootX ^ 2 + rootX + 1)) := by
    rw [Sval_mul_denom]; exact (rootX_isUnit.pow 3).neg
  exact (IsUnit.mul_iff.mp h).1

/-- `X = χ_R(x)` as a `2`-adic unit. -/
noncomputable def rootXUnit : ℤ_[2]ˣ := rootX_isUnit.unit

/-- `S = χ_R(s)` as a `2`-adic unit. -/
noncomputable def SvalUnit : ℤ_[2]ˣ := Sval_isUnit.unit

/-- `Y = χ_R(y)` as a `2`-adic unit. -/
noncomputable def YvalUnit : ℤ_[2]ˣ := Yval_isUnit.unit

@[simp] theorem val_rootXUnit : (rootXUnit : ℤ_[2]) = rootX := rootX_isUnit.unit_spec
@[simp] theorem val_SvalUnit : (SvalUnit : ℤ_[2]) = Sval := Sval_isUnit.unit_spec
@[simp] theorem val_YvalUnit : (YvalUnit : ℤ_[2]) = Yval := Yval_isUnit.unit_spec

/-- The character relation ⟦eq:charrelation⟧ in unit form: `Y² = X⁴` (from `Y = -X²`). -/
theorem YvalUnit_sq_eq : YvalUnit ^ 2 = rootXUnit ^ 4 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, val_YvalUnit, val_rootXUnit, Yval_eq]
  ring

/-- `Y = -X²` in unit form (the shape `χ_R(t) = YX⁻²` consumes). -/
theorem YvalUnit_eq_neg_sq : YvalUnit = -rootXUnit ^ 2 := by
  apply Units.ext
  rw [val_YvalUnit, Units.val_neg, Units.val_pow_eq_pow_val, val_rootXUnit, Yval_eq]

/-! ## The orientation character `χ_R` -/

/-- **The canonical orientation `χ_R : D_R → ℤ₂ˣ`** ⟦prop:orientation⟧, built by the
universal property of `D_R` (`drLiftHom`) at the triple
`(S, X, Y) = (SvalUnit, rootXUnit, YvalUnit)`.  The relator `r₂` dies because `ℤ₂ˣ` is
abelian: `drWord` collapses to `(X⁴)⁻¹Y²` (`drWord_comm`) and `Y² = X⁴` (`YvalUnit_sq_eq`). -/
noncomputable def chiR : ContinuousMonoidHom (DR : Type) ℤ_[2]ˣ :=
  drLiftHom isProP_two_unitsPadicInt ![SvalUnit, rootXUnit, YvalUnit] (by
    show drWord SvalUnit rootXUnit YvalUnit = 1
    rw [drWord_comm, YvalUnit_sq_eq, inv_mul_cancel])

@[simp] theorem chiR_drS : chiR drS = SvalUnit := drLiftHom_S _ _ _
@[simp] theorem chiR_drX : chiR drX = rootXUnit := drLiftHom_X _ _ _
@[simp] theorem chiR_drY : chiR drY = YvalUnit := drLiftHom_Y _ _ _

/-! ## `χ_R` is the Labute orientation -/

/-- **`χ_R` is Labute's canonical orientation** ⟦prop:orientation⟧: its generator values
`(S, X, Y)` form a Labute orientation datum.  Discharged from `isLabuteOrientationDatum_of_root`
with R10's cubic root facts. -/
theorem isLabuteOrientation_chiR : IsLabuteOrientation chiR.toMonoidHom := by
  show IsLabuteOrientationDatum (chiR drS) (chiR drX) (chiR drY)
  rw [chiR_drS, chiR_drX, chiR_drY]
  exact isLabuteOrientationDatum_of_root rootXUnit SvalUnit YvalUnit
    (by rw [val_rootXUnit]; exact rootX_isRoot)
    (by rw [val_SvalUnit, val_rootXUnit]; exact Sval_mul_denom)
    (by rw [val_YvalUnit, val_rootXUnit]; exact Yval_eq)

/-- **The torsion value** ⟦eq:tR⟧: `χ_R(y)·χ_R(x)⁻² = -1`.  Since `Y = -X²`, this is
`(-X²)·X⁻² = -1`.  Phrased on the generators `y, x` (not on the abelianized `t̄`), so it is
available before ticket R8's abelianization; ticket R15 transports it to `t̄`. -/
theorem chiR_torsion : chiR drY * (chiR drX)⁻¹ ^ 2 = -1 := by
  rw [chiR_drY, chiR_drX, YvalUnit_eq_neg_sq, inv_pow, neg_mul, mul_inv_cancel]

/-! ## Surjectivity: `im χ_R = ℤ₂ˣ` -/

/-- **Surjectivity of `χ_R`** ⟦prop:orientation⟧, the image statement `im χ_R = ℤ₂ˣ`.
Because every `2`-adic unit is `≡ ±1 (mod 4)`, the note's `{±1}×(1+4ℤ₂)` is all of `ℤ₂ˣ`,
so this is the same encoding as B3c's `surjective_chiTwo`.

Proof by the pro-`2` Burnside/Frattini criterion (`surjective_of_forall_not_le_index_p`):
fix an index-`2` open normal `M ≤ ℤ₂ˣ`.  Its quotient has order `2`, so `M` contains every
square.  The range of `χ_R` contains `χ_R(x) = X` and `χ_R(y·x⁻²) = -1`; if `M` also
contained the range then, by `mod8_sq` (every unit is `s·w²` with `s ∈ {1,-1,±(-3)}` and
`-3 ≡ 5 ≡ X (mod 8)` is `X` times a square), `M` would be all of `ℤ₂ˣ`, contradicting
index `2`. -/
theorem chiR_surjective : Function.Surjective chiR := by
  refine surjective_of_forall_not_le_index_p (p := 2) isProP_two_unitsPadicInt chiR ?_
  intro M hM hle
  -- The order-`2` quotient kills squares: `u² ∈ M` for every unit `u`.
  haveI : Finite (ℤ_[2]ˣ ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hsq : ∀ u : ℤ_[2]ˣ, u ^ 2 ∈ M.toSubgroup := by
    intro u
    have hpow : (QuotientGroup.mk' M.toSubgroup u) ^ 2 = 1 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' M.toSubgroup u)
      rw [← Subgroup.index_eq_card, hM] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have h2 : QuotientGroup.mk' M.toSubgroup (u ^ 2) = 1 := by rw [map_pow]; exact hpow
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  -- `X = χ_R x` and `-1 = χ_R (y·x⁻²)` are in the range, hence in `M`.
  have hrootX : rootXUnit ∈ M.toSubgroup := hle ⟨drX, chiR_drX⟩
  have hchiTors : chiR (drY * (drX ^ 2)⁻¹) = -1 := by
    rw [map_mul, map_inv, map_pow, ← inv_pow]; exact chiR_torsion
  have hneg1 : (-1 : ℤ_[2]ˣ) ∈ M.toSubgroup := hle ⟨drY * (drX ^ 2)⁻¹, hchiTors⟩
  -- `-3 ≡ X (mod 8)`, so `-3 = X · square ∈ M`.
  have hrootX3 : PadicInt.toZModPow 3 rootX = 5 := by
    have h := congrArg (PadicInt.toZModPow (p := 2) 3) rootX_isRoot
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h
    exact (by decide : ∀ r : ZMod (2 ^ 3), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 5) _ h
  have hn3v : (neg3Int : ℤ_[2]) = -3 := by simp only [neg3Int]; exact IsUnit.unit_spec _
  have hn3val3 : PadicInt.toZModPow 3 (neg3Int : ℤ_[2]) = 5 := by
    rw [hn3v, show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]; decide
  have hres : PadicInt.toZModPow 3 (neg3Int : ℤ_[2])
      = PadicInt.toZModPow 3 (rootXUnit : ℤ_[2]) := by
    rw [hn3val3, val_rootXUnit, hrootX3]
  have hdvd : (8 : ℤ_[2]) ∣ ((neg3Int : ℤ_[2]) - rootXUnit) := by
    rw [← toZModPow3_eq_zero_iff, map_sub, hres, sub_self]
  have hs1 : (rootXUnit : ℤ_[2]) * ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have heq : ((neg3Int * rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = ((neg3Int : ℤ_[2]) - rootXUnit) * ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [Units.val_mul, sub_mul, hs1]
  obtain ⟨t, ht⟩ := hensel_sq (neg3Int * rootXUnit⁻¹) (by rw [heq]; exact hdvd.mul_right _)
  have hn3eq : neg3Int = rootXUnit * t ^ 2 := by
    rw [← ht, mul_comm neg3Int rootXUnit⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hn3 : neg3Int ∈ M.toSubgroup := by
    rw [hn3eq]; exact M.toSubgroup.mul_mem hrootX (hsq t)
  -- Then `mod8_sq` forces `M = ⊤`, contradicting index `2`.
  have htop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro v
    obtain ⟨s₂, hs₂, w, hvw⟩ := mod8_sq v
    have hs₂mem : s₂ ∈ M.toSubgroup := by
      rcases hs₂ with rfl | rfl | rfl | rfl
      · exact M.toSubgroup.one_mem
      · exact hneg1
      · exact hn3
      · rw [show (-neg3Int : ℤ_[2]ˣ) = (-1) * neg3Int from (neg_one_mul neg3Int).symm]
        exact M.toSubgroup.mul_mem hneg1 hn3
    rw [hvw]; exact M.toSubgroup.mul_mem hs₂mem (hsq w)
  rw [htop, Subgroup.index_top] at hM
  omega

/-! ## Stress tests -/

/-- **Stress test** (mod-`16` value of `χ_R(x)`): `χ_R(x) ≡ 5 (mod 16)` (eq. orientationvalues).
Catches a sign/branch slip in the value assignment. -/
theorem chiR_drX_toZModPow_four : PadicInt.toZModPow 4 (chiR drX : ℤ_[2]) = 5 := by
  rw [chiR_drX, val_rootXUnit]; exact rootX_toZModPow_four

/-- **Stress test** (mod-`16` value of `χ_R(s)`): `χ_R(s) ≡ 13 (mod 16)`. -/
theorem chiR_drS_toZModPow_four : PadicInt.toZModPow 4 (chiR drS : ℤ_[2]) = 13 := by
  rw [chiR_drS, val_SvalUnit]; exact Sval_toZModPow_four

/-- **Stress test** (the relator dies): `χ_R(r₂) = 1`.  It holds already as `χ_R(1)` since
`r₂ = 1` in `D_R` (`dr_relation`); this checks the value assignment is consistent with the
presentation. -/
theorem chiR_drWord : chiR (drWord drS drX drY) = 1 := by
  rw [dr_relation, map_one]

end GQ2.Roe

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Prop 3.3 = ⟦prop:orientation⟧
    - `χ_R` construction + values `(S, X, Y)` = `chiR`, `chiR_drS`/`chiR_drX`/`chiR_drY`
    - Labute orientation = `isLabuteOrientation_chiR`
    - eq. (tR) `χ_R(t) = YX⁻² = -1` = `chiR_torsion`
    - `im χ_R = {±1}×(1+4ℤ₂) = ℤ₂ˣ` = `chiR_surjective`
-/
