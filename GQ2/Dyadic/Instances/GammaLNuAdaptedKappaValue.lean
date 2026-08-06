/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLNuAdaptedPlacement
import GQ2.Dyadic.Instances.GammaLNuKummerIdentification

/-!
# The second `𝔽₂` datum is free: `b_K([−1], ν̄) = 0`

`GammaLNuAdaptedPlacement` §3 names the second cup value the fully `ν`-adapted frame costs,
`NuUrKappaCupZero B : b_K(κ, ν̄) = 0`, and §2 there shows it is exactly the `x₁`-row of `ν̄` in
*any* cup-adapted frame, hence necessary.  This file discharges it for every odd-degree `K`,
with no new arithmetic input at all.

## The argument

By the Labute identity `b(κ, x) = b(x, x)` the datum is the **isotropy** `b(ν̄, ν̄) = 0`, and
`ν̄ = [u]` for `u = −3` (`NuKummer.nuUrUnramifiedKummerClass_of_odd`), so what has to be shown is
that `u` is represented by its own norm form `x² − u y²`.  It is, and the two ingredients are
already in the repository:

* `−u = 0² − u · 1²` is the norm of `√u` — free;
* `−1 = x² − u y²` is **B11b** (`unramifiedQuadratic_units_are_norms`) applied to the norm-one
  unit `−1`, legitimate because `K(√u)/K` is unramified in the repository's
  `HasEqualNormValueGroups` sense — the same hypothesis `NuUrUnramifiedKummerClass` already
  carries.

The norm form is multiplicative, `(x₁² − a y₁²)(x₂² − a y₂²) = (x₁x₂ + a y₁y₂)² − a(x₁y₂ +
x₂y₁)²`, and `u = (−1) · (−u)`; the specialization at `(x₂, y₂) = (0, 1)` is the single
`linear_combination` of `normForm_self_of_normForm_neg_one`.

Contrast the `ω`-side datum `NuUrOmegaCupOne`: there the value is `1`, and proving it needed the
sharp *negative* computation `not_normForm_two_of_unramified` (`2` has odd valuation, so it is
not a norm).  Here the value is `0` and B11b alone settles it, which is why this datum never had
to be named as a residual.

## What is proved

* **§1 `cupFormK_kummer_self_eq_zero_of_unramified`** — `b_K([u],[u]) = 0` for every unit `u`
  cutting out an unramified quadratic extension, at every `K` (no degree hypothesis).
* **§2 `nuUrKappaCupZero_of_odd`** — `NuUrKappaCupZero B` for every odd-degree `K`, through the
  Kummer identification `ν̄ = [−3]`.

## Axioms

Std-3 + `tateDualityAt` (**B6**, definitional through `FieldData.cupFormK`) +
`hilbertSymbol_normCriterion_finiteDyadic` (**B11a**, the cup ⟺ Hilbert dictionary).  B11b is a
theorem in-repository, so it contributes nothing.  No `sorry`, no new axiom, no `native_decide`.
Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

/-! ## §1 A unit is a norm from its own quadratic extension, when that extension is unramified -/

section NormSide

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- `−1` has norm one, so B11b applies to it. -/
theorem norm_negOne_eq_one (K : IntermediateField ℚ_[2] ℚ̄₂) :
    ‖(((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ = 1 := by
  have hval : (((-1 : (↥K)ˣ) : ↥K) : ℚ̄₂) = -1 := by
    show ((-1 : ↥K) : ℚ̄₂) = -1
    rw [show ((-1 : ↥K) : ℚ̄₂) = algebraMap (↥K) ℚ̄₂ (-1) from rfl, map_neg, map_one]
  rw [hval, norm_neg, norm_one]

omit [FiniteDimensional ℚ_[2] K] in
/-- **Multiplicativity, at the one instance needed.**  If `−1 = x² − a y²` then `a` itself is
represented: `a = (a y)² − a x²`, because `a = (−1) · (−a)` and `−a = 0² − a · 1²`. -/
theorem normForm_self_of_normForm_neg_one {a : (↥K)ˣ} {x y : ↥K}
    (hxy : (-1 : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2) :
    (a : ↥K) = ((a : ↥K) * y) ^ 2 - (a : ↥K) * x ^ 2 := by
  linear_combination (-(a : ↥K)) * hxy

/-- **The isotropy of an unramified Kummer class.**  For a unit `a` whose square root generates an
unramified quadratic extension of `K`, `b_K([a], [a]) = 0`: the norm group of `K(√a)` contains
every norm-one unit (B11b), in particular `−1`, and it contains `−a = N(√a)`, so it contains
their product `a`. -/
theorem cupFormK_kummer_self_eq_zero_of_unramified (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (a : (↥K)ˣ) (δa : ℚ̄₂) (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂))
    (hunram : HasEqualNormValueGroups K δa) :
    FieldData.cupFormK K (kummerClassK K a) (kummerClassK K a) = 0 := by
  refine (MarkedFrame.cupFormK_kummer_eq_zero_iff K a a).mpr ?_
  obtain ⟨x, y, hxy⟩ :=
    unramifiedQuadratic_units_are_norms K a δa hδ2 hunram (-1) (norm_negOne_eq_one K)
  have hneg : (-1 : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
    rw [← hxy]
    show (-1 : ↥K) = ((-1 : (↥K)ˣ) : ↥K)
    rw [Units.val_neg, Units.val_one]
  exact ⟨(a : ↥K) * y, x, normForm_self_of_normForm_neg_one hneg⟩

end NormSide

/-! ## §2 The datum, discharged in odd degree -/

section Assembly

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- **The `κ`-cup value from the Kummer identification.**  `b_K(κ, ν̄) = b_K(ν̄, ν̄)` is the Labute
identity, and §1 makes the right-hand side vanish. -/
theorem nuUrKappaCupZero_of_unramifiedKummerClass (B : MarkedRecip R K) {u : (↥K)ˣ} {δu : ℚ̄₂}
    (hδ2 : δu ^ 2 = ((u : ↥K) : ℚ̄₂)) (hunram : HasEqualNormValueGroups K δu)
    (hclass : h1MaxProTwoEquivGalK (K := K) (MarkedFrame.nuUrModTwoClassKTwo B) =
      kummerClassK K u) :
    NuUrKappaCupZero B := by
  show frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
    (MarkedFrame.nuUrModTwoClassKTwo B) = 0
  rw [frattiniFrameCup_kappa (K := K), frattiniFrameCup, hclass]
  exact cupFormK_kummer_self_eq_zero_of_unramified K u δu hδ2 hunram

omit [T2Space (GalK K)] in
/-- **The second datum is a theorem in odd degree.**  `ν̄ = [−3]` and `K(√−3)/K` is unramified
(`NuKummer.nuUrUnramifiedKummerClass_of_odd`), so §1 applies.  Unlike the `ω`-side value, this
one costs no ramification input: it is B11b and nothing else. -/
theorem nuUrKappaCupZero_of_odd (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K)) :
    NuUrKappaCupZero B := by
  obtain ⟨u, δu, hδ2, hunram, hclass⟩ := NuKummer.nuUrUnramifiedKummerClass_of_odd B hodd
  exact nuUrKappaCupZero_of_unramifiedKummerClass B hδ2 hunram hclass

end Assembly

end NuAdapted

end

#print axioms NuAdapted.norm_negOne_eq_one
#print axioms NuAdapted.normForm_self_of_normForm_neg_one
#print axioms NuAdapted.cupFormK_kummer_self_eq_zero_of_unramified
#print axioms NuAdapted.nuUrKappaCupZero_of_unramifiedKummerClass
#print axioms NuAdapted.nuUrKappaCupZero_of_odd

end GQ2.Dyadic.LSquare
