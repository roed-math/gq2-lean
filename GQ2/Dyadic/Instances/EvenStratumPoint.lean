/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NFrameAlphaOneInvariants
import GQ2.Dyadic.Instances.EvenParityModel

/-!
# W71-STRATUM: the even stage layer is refuted on the third stratum

Wave 69 (`Instances/EvenUnramified.lean`) showed the presented even cores meet the third stratum
of the range identity in exactly one point, `imChiN 1 = evenRangePrin 2`, with model field
`ℚ₂(i)`.  Wave 70 supplied the group-side invariant there, `demushkinQ (D_N 1 h) = 4`
(`MarkedCore/NFrameAlphaOne.lean`), and proved both `α = 1` cores Demushkin
(`Instances/EvenAlphaOne.lean`).  The wave-69 note priced two further replacements before the
classification could be stated at that point: a `q = 4` frame at the stage level, and a
substitute for the relator-shift factorization at an even half-exponent.

## Which replacement is binding

**Neither.**  Both are mis-priced, in opposite directions, and a third obstruction sits upstream
of both.

1. The `q = 4` frame at the stage level is a **non-item**.  `MarkedCore.NFrame` is an object of
   the abelianization layer, and no file in the stage layer consumes one: the stage layer's frame
   is `StageGeneric.Frame`, whose fields are generators in the target group, their character rows,
   and level-two generation, with no torsion slot anywhere.  So there is nothing for wave 70's
   `NFrame4` to lift to, and the emptiness of `NFrame 1 h` was never a stage-level obstruction.
   `NFrame4` remains what wave 70 built it for, the `q`-invariant, and this file does not use it.
2. The relator-shift factorization at an even half-exponent is **not reached**, because the frame
   step that precedes it fails first.
3. What is binding is a single arithmetical fact, `4 ∣ nUnit α + 1`, equivalently
   `nUnit α ≡ -1 (mod 4)`.  §1 shows it holds **exactly** on `α ≥ 2`: at `α = 1` the value is
   `nUnit 1 ≡ 1 (mod 4)`.  Every `2 ≤ α` binder in the `N` stage layer is carrying this one fact,
   through the parity table, the shadow determination, the deep row supply, the derivation-kernel
   diagonal row, and the `κ ≠ 0` binder.

## The refutation

The consequence is not a missing lemma.  On the third stratum the range lies in the principal
units, so the mod-four cyclotomic character is trivial and `κ = 0` (§3).  The committed
`frattiniFrameCup_kappa` says, with no hypothesis, that the diagonal of the field cup form is
cupping with `κ`; hence on this stratum **the field cup form is alternating** (§4).  The even
coordinate model's Gram is not alternating, and the tree says so in its own docstring
(`evenFrameGramModel_self`: the diagonal is the `x₀` coordinate).  Two forms one of which is
alternating and one of which is not are not isomorphic, so:

> **`evenStratum_no_adaptedModelEquiv`**: at every field whose cyclotomic range lies in
> `evenRangePrin 2`, and at every handle count, there is **no** linear isomorphism carrying the
> field cup form to `evenFrameGramModel h`.

That is the conclusion of `evenFrameAdaptedModelEquiv`, which is the shared step of all three
even frame producers in the tree (`evenEndpoint_nFrame_of_range` on the `N` row,
`StageAbstractionEvenFrattiniFrameM.lean` on the `M` row, and `StageAbstractionEvenFrameCore`'s
own).  So the even stage layer's frame step is refuted on the whole third stratum, at `ℚ₂(i)`
included (§7), and not only at the surviving point.

## What is NOT claimed

The classification at the surviving point is **neither proved nor refuted here**, and nothing
below should be read as either.  What is refuted is one route's frame step, not the existence of
an oriented equivalence: no declaration in this file, or anywhere in the tree, asserts or denies
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)` at a third-stratum field.  Wave
70's invariant match `(rank, q) = (4 + 2h, 4)` remains a match of invariants and is not an
isomorphism; it is not used below.

## The reduction that survives

§6 records what the point now costs.  Of the three inputs of
`nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData`, two are discharged at `α = 1`: the
depth binder is `1 ≤ 1`, and the model-side package is wave 70's `evenAlphaOne_nModelDemushkin`.
So the classification at the surviving point follows from the forward-generator datum alone:

> **`evenStratum_orientedEquivN_one_of_forwardGeneratorData`**: given
> `Nonempty (NForwardGeneratorData 1 h χ_cyc)` and the degree, the oriented equivalence follows.

Read against the refutation, this says precisely where a future lane must attack: the datum has
to be produced by some route other than the committed frame-and-climb, because that route's frame
step is unavailable on this stratum.

## Contents

* **§1** The mod-four alignment and its sharpness, `evenStratum_four_dvd_nUnit_add_one_iff`.
* **§2** The `α = 1` parity table is the zero table.
* **§3** `κ = 0` on the third stratum.
* **§4** The cup form is alternating there, and the adapted model equivalence is refuted.
* **§5** The same at the surviving point, with the hypothesis shape of `evenEndpoint_kappa_of_rangeN`.
* **§6** The reduction of the classification at the surviving point to one `Prop`.
* **§7** The model field `ℚ₂(i)`.
* **§8** Axiom pins.

## Axiom scope (measured)

§1, §2, §3 and §5's range lemma are std-3.  §4 and §7 add `tateDualityAt` and
`hilbertSymbol_normCriterion_finiteDyadic`, and §6 adds `tateDualityAt` and
`Foundations.absGalQ2_localEulerCharacteristic`.  Every one of these sets is a **subset** of the
set printed by the `α ≥ 2` analogue it stands against; §8 prints them side by side.
-/

namespace GQ2.Dyadic.EvenStratum

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenCyclotomicRange

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The mod-four alignment, and where it is sharp -/

/-- The defining equation in additive form: `v + 1 = -v · 2^α`. -/
theorem evenStratum_nUnit_add_one {α : ℕ} (hα : 1 ≤ α) :
    ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 1 = -((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) * 2 ^ α := by
  have hmul := nUnit_mul (α := α) hα
  linear_combination hmul

/-- **`nUnit 1 ≡ 1 (mod 4)`.**  The `N` twisted value at the surviving parameter reduces to `1`,
not to `-1`: from `nUnit 1 · 3 = -1` the residue `x` satisfies `3x = 3` in `ZMod 4`, whose only
solution is `x = 1`.  Every `α ≥ 2` statement in the even stage layer wants `-1` here. -/
theorem evenStratum_nUnit_one_toZModPow :
    PadicInt.toZModPow 2 ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  have hmul := nUnit_mul (α := 1) (le_refl 1)
  have himg := congrArg (PadicInt.toZModPow (p := 2) 2) hmul
  rw [map_mul, map_neg, map_one] at himg
  have h3 : PadicInt.toZModPow (p := 2) 2 ((1 : ℤ_[2]) + 2 ^ 1) = 3 := by
    rw [show ((1 : ℤ_[2]) + 2 ^ 1) = ((3 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
    decide
  rw [h3] at himg
  revert himg
  generalize PadicInt.toZModPow (p := 2) 2 ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) = x
  revert x
  decide

/-- **The `N` diagonal alignment fails at `α = 1`.**  `evenKernel_vN_diagonal_add_one_dvd_four`
asks for `4 ∣ nUnit α + 1`; at `α = 1` the residue is `1`, so the sum is `2` mod `4`. -/
theorem evenStratum_not_four_dvd_nUnit_one_add_one :
    ¬ (2 : ℤ_[2]) ^ 2 ∣ ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  intro hdvd
  have hsub : ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1 = ((nUnit 1 : ℤ_[2]ˣ) : ℤ_[2]) - (-1) := by ring
  rw [hsub, ← evenRange_toZModPow_eq_iff, evenStratum_nUnit_one_toZModPow] at hdvd
  rw [map_neg, map_one] at hdvd
  exact absurd hdvd (by decide)

/-- **The alignment is sharp.**  `4 ∣ nUnit α + 1` holds exactly on `α ≥ 2`.  This one
arithmetical fact is what every `2 ≤ α` binder in the `N` stage layer is carrying. -/
theorem evenStratum_four_dvd_nUnit_add_one_iff {α : ℕ} (hα : 1 ≤ α) :
    (2 : ℤ_[2]) ^ 2 ∣ ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 1 ↔ 2 ≤ α := by
  refine ⟨fun hdvd => ?_, fun h2 => StageGeneric.evenKernel_nUnit_add_one_dvd_four h2⟩
  by_contra hlt
  have hone : α = 1 := by omega
  subst hone
  exact evenStratum_not_four_dvd_nUnit_one_add_one hdvd

/-! ## §2 The `α = 1` parity table is the zero table -/

/-- **The `N` row's mod-four parity vanishes at `α = 1`.**  Contrast `evenDegreeN_parity_nUnit`,
which is `= 1` for `α ≥ 2`; the twisted index of the parity table loses its mark here. -/
theorem evenStratum_parity_nUnit_one :
    Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom (nUnit 1))) = 0 := by
  have hone : Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom (nUnit 1) = 1 :=
    Units.ext (by simpa using evenStratum_nUnit_one_toZModPow)
  rw [hone, map_one]
  rfl

/-! ## §3 The mod-four cyclotomic class vanishes on the third stratum -/

section Kappa

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance evenStratumScalar :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _

local instance evenStratumContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The mod-four cyclotomic character is trivial on the third stratum.**  Every value is a
principal unit at level `2`, and `evenRangePrin 2` is by definition the kernel of the mod-four
reduction, so the parity character is constant. -/
theorem evenStratum_modFourCharacter_eq_one
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2) :
    cyclotomicModFourCharacterKTwo (K := K) = 1 := by
  ext g
  have hmem : chiCycKTwo (K := K) g ∈ evenRangePrin 2 := hle ⟨g, rfl⟩
  have hker : Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom
      (chiCycKTwo (K := K) g) = 1 := hmem
  show unitsModFourParity (Units.map (PadicInt.toZModPow (p := 2) 2).toMonoidHom
    (chiCycKTwo (K := K) g)) = 1
  rw [hker, map_one]

/-- **`κ = 0` on the third stratum.**  The standing ramified-`i` binder of the even stage layer,
`cyclotomicModFourClassKTwo ≠ 0`, is not merely unproved at a third-stratum field: it is false
there.  Every producer of the cup-adapted even frame takes it as a hypothesis. -/
theorem evenStratum_kappa_eq_zero
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2) :
    cyclotomicModFourClassKTwo (K := K) = 0 := by
  have hchar := evenStratum_modFourCharacter_eq_one (K := K) hle
  show ContCoh.H1mk _ _ (Count.homEquivZ1 (cyclotomicModFourCharacterKTwo (K := K))) = 0
  rw [hchar]
  have hz : Count.homEquivZ1 (Γ := maxProPQuotient 2 (GalK K)) 1 = 0 := by
    apply Subtype.ext
    funext g
    rfl
  rw [hz, map_zero]

end Kappa

/-! ## §4 The stage-level frame is refuted on the stratum -/

section Frame

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenStratumFrameScalar :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _

local instance evenStratumFrameContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The cup form vanishes against `0` in the first slot. -/
theorem evenStratum_cup_zero_left (x : ContCoh.H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    LSquare.FrattiniFrameSupply.frattiniFrameCup (K := K) 0 x = 0 := by
  have hadd := (LSquare.FrattiniFrameSupply.isCupFormFp2_frattiniFrameCup (K := K)).add_left 0 0 x
  rw [add_zero] at hadd
  linear_combination -hadd

/-- **The field cup form is ALTERNATING on the third stratum.**  `frattiniFrameCup_kappa` is
committed with no hypothesis: the diagonal of the cup form is cupping with `κ`.  On this stratum
`κ = 0`, so the diagonal is identically zero. -/
theorem evenStratum_cup_self_eq_zero
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (x : ContCoh.H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    LSquare.FrattiniFrameSupply.frattiniFrameCup (K := K) x x = 0 := by
  rw [← LSquare.FrattiniFrameSupply.frattiniFrameCup_kappa (K := K) x,
    evenStratum_kappa_eq_zero hle]
  exact evenStratum_cup_zero_left x

/-- The model vector whose self-pairing is `1`: the even head is not alternating. -/
def evenStratumHeadVec (h : ℕ) : StageGeneric.evenFrameModel h := (((1 : ZMod 2), (0 : ZMod 2)), 0)

/-- The head vector has self-pairing `1` against the even frame Gram. -/
theorem evenStratum_gramModel_headVec (h : ℕ) :
    StageGeneric.evenFrameGramModel h (evenStratumHeadVec h) (evenStratumHeadVec h) = 1 := by
  rw [StageGeneric.evenFrameGramModel_self, StageGeneric.evenFrameCoord_zero]
  rfl

/-- **THE STAGE-LEVEL FRAME IS REFUTED ON THE THIRD STRATUM.**  `evenFrameAdaptedModelEquiv`,
the step every even frame producer runs through, asks for a linear isomorphism carrying the
field cup form to `evenFrameGramModel h`.  On this stratum no such isomorphism exists at any
handle count: the source form is alternating (§4) and the target has a vector of self-pairing
`1` (`evenFrameGramModel_self`, whose own docstring says the model Gram is not alternating).

This is a refutation, not a gap.  The obstruction is not that a lemma is missing at `α = 1`; it
is that the two forms are not isomorphic. -/
theorem evenStratum_no_adaptedModelEquiv
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2) (h : ℕ) :
    ¬ ∃ Φ : ContCoh.H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2]
        StageGeneric.evenFrameModel h,
      ∀ x y, LSquare.FrattiniFrameSupply.frattiniFrameCup (K := K) x y =
        StageGeneric.evenFrameGramModel h (Φ x) (Φ y) := by
  rintro ⟨Φ, hΦ⟩
  have hx := hΦ (Φ.symm (evenStratumHeadVec h)) (Φ.symm (evenStratumHeadVec h))
  rw [Φ.apply_symm_apply, evenStratum_gramModel_headVec,
    evenStratum_cup_self_eq_zero hle] at hx
  exact zero_ne_one hx

/-! ## §5 The surviving point: same hypothesis shape, opposite conclusion -/

omit [FiniteDimensional ℚ_[2] K] in
/-- The `N` branch identification at the surviving parameter puts the range inside the principal
units, by wave 69's `evenUnram_imChiN_one_eq_prin_two`. -/
theorem evenStratum_range_le_prin_of_rangeN_one
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 1) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2 := by
  rw [hrange, EvenUnram.evenUnram_imChiN_one_eq_prin_two]

omit [FiniteDimensional ℚ_[2] K] in
/-- **`κ = 0` at the surviving point.**  Compare `evenEndpoint_kappa_of_rangeN`, which reads
`κ ≠ 0` off exactly this hypothesis for `α ≥ 2`.  At the one parameter where the presented `N`
images meet the third stratum the same hypothesis gives the opposite conclusion, because the
value `nUnit 1` that supplies the nonzero parity for `α ≥ 2` is `≡ 1 (mod 4)` here (§1). -/
theorem evenStratum_kappa_eq_zero_of_rangeN_one
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 1) :
    cyclotomicModFourClassKTwo (K := K) = 0 :=
  evenStratum_kappa_eq_zero (evenStratum_range_le_prin_of_rangeN_one hrange)

/-- **The frame refutation at the surviving point**, at every handle count. -/
theorem evenStratum_no_adaptedModelEquiv_of_rangeN_one
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 1) (h : ℕ) :
    ¬ ∃ Φ : ContCoh.H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2]
        StageGeneric.evenFrameModel h,
      ∀ x y, LSquare.FrattiniFrameSupply.frattiniFrameCup (K := K) x y =
        StageGeneric.evenFrameGramModel h (Φ x) (Φ y) :=
  evenStratum_no_adaptedModelEquiv (evenStratum_range_le_prin_of_rangeN_one hrange) h

end Frame

/-! ## §6 What the classification at the surviving point now costs -/

section Reduction

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **THE REDUCTION AT THE SURVIVING POINT.**  The even classification at branch parameter `1`
follows from the forward-generator datum ALONE.  Both other inputs of
`nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData` are discharged here: the depth
binder is `1 ≤ 1`, and the model-side package is wave 70's `evenAlphaOne_nModelDemushkin`.

So the model layer at the surviving point is fully paid, and what remains is exactly one `Prop`.
This is a reduction, not a classification: no declaration in the tree asserts that
`G_{ℚ₂(i)}(2)` is isomorphic to any `DN 1 h`, and none is asserted here. -/
theorem evenStratum_orientedEquivN_one_of_forwardGeneratorData {h : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hdata : Nonempty (EvenForward.NForwardGeneratorData 1 h (chiCycKTwo (K := K)))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 1 h) (chiCycKTwo (K := K))) :=
  EvenForward.nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData 1 h (le_refl 1) hev
    (EvenAlphaOne.evenAlphaOne_nModelDemushkin h) hdata

end Reduction

/-! ## §7 The model field `ℚ₂(i)` -/

section ModelField

open GQ2.Dyadic.Fields GQ2.Dyadic.EvenParity

variable [CompactSpace (GalK EvenUnram.evenUnramKNegOne)]
  [TotallyDisconnectedSpace (GalK EvenUnram.evenUnramKNegOne)]

local instance evenStratumKScalar :
    DistribMulAction (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenStratumKContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **`κ = 0` at `ℚ₂(i)`**, over the standing profinite binders and nothing else: no reciprocity
bundle is needed, because the range bound comes from the square root of `-1` directly. -/
theorem evenStratum_kappa_eq_zero_KNegOne :
    cyclotomicModFourClassKTwo (K := EvenUnram.evenUnramKNegOne) = 0 :=
  evenStratum_kappa_eq_zero
    (EvenUnram.evenUnram_range_le_prin_two_of_sqrt_neg_one (sqrtIn_mem_quadField (-1))
      evenParity_sqrtIn_neg_one_sq)

/-- **THE FRAME IS REFUTED AT `ℚ₂(i)`**, at every handle count.  This is the tree's first named
field at which the even stage layer's frame step is known to be unavailable, as opposed to
unproved. -/
theorem evenStratum_no_adaptedModelEquiv_KNegOne (h : ℕ) :
    ¬ ∃ Φ : ContCoh.H1 (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) ≃ₗ[ZMod 2]
        StageGeneric.evenFrameModel h,
      ∀ x y, LSquare.FrattiniFrameSupply.frattiniFrameCup
          (K := EvenUnram.evenUnramKNegOne) x y =
        StageGeneric.evenFrameGramModel h (Φ x) (Φ y) :=
  evenStratum_no_adaptedModelEquiv
    (EvenUnram.evenUnram_range_le_prin_two_of_sqrt_neg_one (sqrtIn_mem_quadField (-1))
      evenParity_sqrtIn_neg_one_sq) h

end ModelField

end

/-! ## §8 Axiom pins

Every declaration is expected std-3 (`propext`, `Classical.choice`, `Quot.sound`).  Each block is
printed beside the `α ≥ 2` analogue it stands against, so that the two are read together. -/

#print axioms evenStratum_nUnit_add_one
#print axioms evenStratum_nUnit_one_toZModPow
#print axioms evenStratum_not_four_dvd_nUnit_one_add_one
#print axioms evenStratum_four_dvd_nUnit_add_one_iff
#print axioms GQ2.Dyadic.StageGeneric.evenKernel_nUnit_add_one_dvd_four

#print axioms evenStratum_parity_nUnit_one
#print axioms GQ2.Dyadic.StageGeneric.evenDegreeN_parity_nUnit

#print axioms evenStratum_modFourCharacter_eq_one
#print axioms evenStratum_kappa_eq_zero
#print axioms evenStratum_kappa_eq_zero_of_rangeN_one
#print axioms evenStratum_kappa_eq_zero_KNegOne
#print axioms GQ2.Dyadic.EvenEndpoint.evenEndpoint_kappa_of_rangeN

#print axioms evenStratum_cup_zero_left
#print axioms evenStratum_cup_self_eq_zero
#print axioms evenStratum_gramModel_headVec
#print axioms evenStratum_no_adaptedModelEquiv
#print axioms evenStratum_no_adaptedModelEquiv_of_rangeN_one
#print axioms evenStratum_no_adaptedModelEquiv_KNegOne
#print axioms GQ2.Dyadic.EvenEndpoint.evenEndpoint_nFrame_of_range

#print axioms evenStratum_range_le_prin_of_rangeN_one
#print axioms evenStratum_orientedEquivN_one_of_forwardGeneratorData
#print axioms GQ2.Dyadic.EvenAlphaOne.evenAlphaOne_nModelDemushkin
#print axioms GQ2.Dyadic.EvenRouteModel.evenRouteModel_orientedEquivN_atDepth

end GQ2.Dyadic.EvenStratum
