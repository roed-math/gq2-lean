/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenStratumPoint
import GQ2.Dyadic.Instances.StageAbstractionEvenFinite
import GQ2.Dyadic.Instances.StageAbstractionEvenStageClimb

/-!
# W72-STRATUM: no cup-adapted stage frame on the third stratum

Wave 71 (`Instances/EvenStratumPoint.lean`) proved that on the third stratum of the range
identity the field cup form is alternating (`evenStratum_cup_self_eq_zero`, from `κ = 0`), and
deduced that no linear isomorphism carries it to `evenFrameGramModel h`
(`evenStratum_no_adaptedModelEquiv`).  That refutes the *coordinate* step of the even frame
producers.  This file refutes the object those producers are built to deliver.

## The statement

> **`evenStratum_no_cupAdaptedFrame`**: at a field whose cyclotomic range lies in
> `evenRangePrin 2` and whose degree is `2 + 2h`, there is **no** `StageGeneric.Frame` at any
> row table `v : Fin (coreRank h) → ℤ_[2]ˣ` that is cup-adapted for the even quadratic-initial
> Gram `evenFrameGram h`.

`Frame.IsCupAdapted` is what `EvenDegreeNCyclotomicFrattiniFrameSupply` and its `M` twin
produce, and what `evenFrame_of_adapted` assembles; the model equivalence is only the route
wave 71 could see through.  So this is the frame step itself, not one implementation of it, and
it is refuted at every row table, not only at the two committed ones.

## The argument

Three steps, none of them arithmetic.

1. **The Gram's diagonal is the `x₀` entry** (§1).  `evenFrameGram h` contracts a matrix as
   `M 0 0 + (M 0 1 + M 1 0) + (M 2 3 + M 3 2) + ∑ⱼ (handle plane)`.  On the rank-one matrix
   `M i j = f i * f j` every bracket cancels in characteristic two and `M 0 0 = f 0 * f 0 =
   f 0`.  So cup-adaptedness forces `P c c = ` the value of `c` at the *zeroth generator*, for
   every continuous mod-two character `c`.
2. **Hence every character kills the zeroth generator** (§3).  `P c c` is the field cup form on
   the diagonal, which wave 71 proved is `0` on this stratum.  Through this file's own
   `evenStratumFrame_exists_character` (§2, class to character) this says: every degree-one
   class evaluates to `0` at `F.generators 0`.
3. **Counting** (§4).  A class evaluating to zero at all of `F.generators` is zero: characters
   kill `λ₂`, so `Frame.levelTwoGen` promotes vanishing on the generators to vanishing
   everywhere (§2).  So the coordinate map `H¹ → (Fin (coreRank h) → 𝔽₂)` is injective; both
   sides have `2 ^ (4 + 2h)` elements by `card_H1_zmodTwo_maxProTwoGalK`, so it is a bijection,
   so *some* class has coordinate `1` at index `0`, contradicting step 2.

Nondegeneracy of the cup form is **not** used; `Frame.levelTwoGen` does that work, which is why
the conclusion needs no reciprocity bundle and no ramification binder.

## What is NOT claimed

Nothing here refutes `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`, and §6 does
not prove it: §6 states an implication *into* it and names its two unproved hypotheses.  What
§4 refutes is the availability of one *route*: a frame cup-adapted for `evenFrameGram h`.  That
Gram is the `α ≥ 2` shape, whose model is non-alternating; the surviving point's cup form is
alternating, so a forward-generator tuple there is not required to be cup-adapted for it, and
§6's reduction is untouched by §4.  The two live side by side deliberately, and
`evenStratum_baseN_frame_not_cupAdapted` is the exact seam between them.

## Contents

* **§1** The diagonal of `evenFrameGram`.
* **§2** Characters, and the duality that `Frame.levelTwoGen` supplies.
* **§3** On the stratum every class evaluates to zero at the zeroth generator.
* **§4** The refutation, and its surviving-point instantiation.
* **§5** The model field `ℚ₂(i)`, and `[ℚ₂(i) : ℚ₂] = 2`.
* **§6** The surviving point, unfolded into a base and a climb.
* **§7** The `demushkinQ`-invariant of the `N` family stops at `4`.
* **§8** Axiom pins.
-/

namespace GQ2.Dyadic.EvenStratumFrame

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.ContCoh GQ2.Roe.Labute
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The diagonal of the even quadratic-initial Gram -/

/-- **The even Gram's diagonal is its `x₀` entry.**  Contracting `evenFrameGram h` against the
rank-one matrix of products of a single coordinate vector returns that vector's zeroth
coordinate: the two off-diagonal brackets of the head and of the `σ`, `x₂` plane cancel in
characteristic two, every handle plane cancels, and `f 0 * f 0 = f 0` in `𝔽₂`.

This is the frame-level shadow of `evenFrameGramModel_self`, and it is the step that turns
cup-adaptedness into a statement about one generator. -/
theorem evenStratumFrame_gram_diag {h : ℕ} (f : Fin (MarkedCore.coreRank h) → ZMod 2) :
    StageGeneric.evenFrameGram h (fun i j ↦ f i * f j) = f 0 := by
  have hsq : ∀ a : ZMod 2, a * a = a := by decide
  have hsym : ∀ a b : ZMod 2, a * b + b * a = 0 := by decide
  simp only [StageGeneric.evenFrameGram_expand, hsq, hsym, Finset.sum_const_zero, add_zero]

section Field

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenStratumFrameScalar :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _

local instance evenStratumFrameContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §2 Characters and the duality supplied by `Frame.levelTwoGen` -/

omit [FiniteDimensional ℚ_[2] K] in
/-- Evaluation is additive in the class, in subtracted form. -/
theorem evenStratumFrame_eval_sub (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (x - y) g = frattiniFrameEval x g - frattiniFrameEval y g := by
  unfold frattiniFrameEval
  rw [map_sub]
  rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- **Every degree-one class is a character.**  The trivial-action cocycle representative of a
class *is* a continuous mod-two character, so evaluation of the class is evaluation of that
character.  (This is the `hcz` step inside `frattiniFrameEval_eq_of_levelMk_eq`, extracted.) -/
theorem evenStratumFrame_exists_character (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    ∃ c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      ∀ g, frattiniFrameEval x g = Multiplicative.toAdd (c g) := by
  set z := (H1equivZ1OfTrivial (M := ZMod 2) (fun _ _ => rfl)) x with hz
  refine ⟨Count.homEquivZ1.symm z, fun g => ?_⟩
  show z.1 g = _
  conv_lhs => rw [← Count.homEquivZ1.apply_symm_apply z]
  rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- **A character trivial on a frame's generators is trivial.**  Mod-two characters kill `λ₂`
(`twoCentralSeries_two_le_continuousCharacter_ker`), so the kernel is a union of Frattini
cosets; `Frame.levelTwoGen` says the generators' cosets generate, hence the kernel is
everything.  No cup form and no nondegeneracy enter. -/
theorem evenStratumFrame_character_eq_one {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
    (F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (hgen : ∀ i, c (F.generators i) = 1) (g : maxProPQuotient 2 (GalK K)) : c g = 1 := by
  have hmap : Subgroup.map (levelMk (maxProPQuotient 2 (GalK K)) 2) c.toMonoidHom.ker = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← F.levelTwoGen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F.generators i, MonoidHom.mem_ker.mpr (hgen i), rfl⟩
  have hmem : levelMk (maxProPQuotient 2 (GalK K)) 2 g ∈
      Subgroup.map (levelMk (maxProPQuotient 2 (GalK K)) 2) c.toMonoidHom.ker := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hlevel⟩ := hmem
  have hcentral : k⁻¹ * g ∈ twoCentralSeries (maxProPQuotient 2 (GalK K)) 2 :=
    (QuotientGroup.eq_one_iff _).mp (by
      show levelMk (maxProPQuotient 2 (GalK K)) 2 (k⁻¹ * g) = 1
      rw [map_mul, map_inv, hlevel, inv_mul_cancel])
  have hker : c (k⁻¹ * g) = 1 :=
    MonoidHom.mem_ker.mp (twoCentralSeries_two_le_continuousCharacter_ker c hcentral)
  have hsplit : g = k * (k⁻¹ * g) := by group
  rw [hsplit, map_mul, hker, mul_one]
  exact MonoidHom.mem_ker.mp hk

omit [FiniteDimensional ℚ_[2] K] in
/-- **The frame coordinates are faithful on `H¹`.**  A class evaluating to zero at every
generator of a `StageGeneric.Frame` is zero. -/
theorem evenStratumFrame_eq_zero_of_eval_gens {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
    (F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2))
    (hall : ∀ i, frattiniFrameEval x (F.generators i) = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := evenStratumFrame_exists_character x
  have hgen : ∀ i, c (F.generators i) = 1 := by
    intro i
    apply Multiplicative.toAdd.injective
    rw [← hc, hall i]
    rfl
  refine frattiniFrameEval_eq_zero x fun g => ?_
  rw [hc g, evenStratumFrame_character_eq_one F c hgen g]
  rfl

/-! ## §3 On the stratum, every class dies at the zeroth generator -/

/-- **Cup-adaptedness reads the diagonal off one generator.**  For every continuous mod-two
character, the field cup form's value on the diagonal is the character's value at
`F.generators 0`.  This holds at every field; it is §1 composed with the definition of
`Frame.IsCupAdapted`. -/
theorem evenStratumFrame_pairing_self {h : ℕ} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (hF : F.IsCupAdapted (StageGeneric.evenFrameGram h) (StageGeneric.evenFramePairing (K := K)))
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    StageGeneric.evenFramePairing (K := K) c c =
      Multiplicative.toAdd (c (F.generators 0)) := by
  rw [hF c c]
  exact evenStratumFrame_gram_diag (fun i ↦ Multiplicative.toAdd (c (F.generators i)))

/-- **Every degree-one class evaluates to zero at the zeroth generator**, on the third stratum.
The cup form is alternating there (wave 71), so §3's diagonal identity forces the value. -/
theorem evenStratumFrame_eval_gen_zero {h : ℕ} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (hF : F.IsCupAdapted (StageGeneric.evenFrameGram h) (StageGeneric.evenFramePairing (K := K)))
    (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    frattiniFrameEval x (F.generators 0) = 0 := by
  obtain ⟨c, hc⟩ := evenStratumFrame_exists_character x
  rw [hc, ← evenStratumFrame_pairing_self F hF c]
  exact EvenStratum.evenStratum_cup_self_eq_zero hle _

/-! ## §4 The refutation -/

/-- **THERE IS NO CUP-ADAPTED STAGE FRAME ON THE THIRD STRATUM.**  At a field of degree
`2 + 2h` whose cyclotomic range lies in `evenRangePrin 2`, and at *every* row table
`v : Fin (coreRank h) → ℤ_[2]ˣ`, no `StageGeneric.Frame` at `v` is cup-adapted for the even
quadratic-initial Gram `evenFrameGram h`.

This is the object every even frame producer delivers (`evenFrame_of_adapted`, and through it
`EvenDegreeNCyclotomicFrattiniFrameSupply` and its `M` twin), so the even stage layer's frame
step is refuted on the stratum as a *statement about frames*, not only about the coordinate
model of wave 71.

It says nothing about the existence of an oriented equivalence at the surviving point: the Gram
refuted here is the `α ≥ 2` shape. -/
theorem evenStratum_no_cupAdaptedFrame {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) :
    ¬ ∃ F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (StageGeneric.evenFrameGram h)
        (StageGeneric.evenFramePairing (K := K)) := by
  classical
  rintro ⟨F, hF⟩
  have hinj : Function.Injective
      (fun (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) (i : Fin (MarkedCore.coreRank h)) ↦
        frattiniFrameEval x (F.generators i)) := by
    intro x y hxy
    have hsub : x - y = 0 := by
      refine evenStratumFrame_eq_zero_of_eval_gens F _ fun i => ?_
      have hi : frattiniFrameEval x (F.generators i) = frattiniFrameEval y (F.generators i) :=
        congrFun hxy i
      rw [evenStratumFrame_eval_sub, hi, sub_self]
    exact sub_eq_zero.mp hsub
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
      2 ^ MarkedCore.coreRank h := by
    rw [card_H1_zmodTwo_maxProTwoGalK, hev]
    congr 1
    simp only [MarkedCore.coreRank]
    omega
  haveI : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := Fintype.ofFinite _
  have hcards : Fintype.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
      Fintype.card (Fin (MarkedCore.coreRank h) → ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, hcards⟩).surjective (fun _ => (1 : ZMod 2))
  have hone : frattiniFrameEval x (F.generators 0) = 1 := congrFun hx 0
  exact one_ne_zero (hone.symm.trans (evenStratumFrame_eval_gen_zero hle F hF x))

/-- **The refutation at the surviving point**, at every handle count and every row table. -/
theorem evenStratum_no_cupAdaptedFrame_of_rangeN_one {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 1)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) :
    ¬ ∃ F : StageGeneric.Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (StageGeneric.evenFrameGram h)
        (StageGeneric.evenFramePairing (K := K)) :=
  evenStratum_no_cupAdaptedFrame
    (EvenStratum.evenStratum_range_le_prin_of_rangeN_one hrange) hev v

end Field

/-! ## §5 The model field `ℚ₂(i)`

Wave 71 could state its `ℚ₂(i)` corollaries with no degree hypothesis; the counting step of §4
needs one, so the degree is computed here.  `finrank_quadField` wants `−1` to be a non-square,
which the committed row list does not contain: the five committed rows are `±2, 5, ±10`, and
`−1` is a unit, so the valuation criterion says nothing.  The mod-eight criterion of
`not_isSquare_five` applies verbatim. -/

section ModelField

open GQ2.Dyadic.Fields GQ2.Dyadic.EvenParity

/-- **`−1` is not a square in `ℚ₂`.**  A square of a `2`-adic integer is `0`, `1` or `4` mod
`8`, and `−1` is `7`.  This is `not_isSquare_five`'s criterion at the one remaining unit the
campaign needs. -/
theorem evenStratumFrame_not_isSquare_neg_one : ¬ IsSquare (-1 : ℚ_[2]) := by
  rintro ⟨b, hb⟩
  have hb1 : ‖b‖ ≤ 1 := by
    have hn : ‖b‖ * ‖b‖ = 1 := by rw [← norm_mul, ← hb, norm_neg, norm_one]
    nlinarith [norm_nonneg b]
  set bz : ℤ_[2] := ⟨b, hb1⟩ with hbz
  have hcoe : bz * bz = (-1 : ℤ_[2]) := by
    apply Subtype.ext
    push_cast [hbz]
    exact hb.symm
  have himg := congrArg (PadicInt.toZModPow (p := 2) 3) hcoe
  rw [map_mul, map_neg, map_one] at himg
  revert himg
  exact (by decide : ∀ x : ZMod (2 ^ 3), x * x ≠ -1) _

/-- **`[ℚ₂(i) : ℚ₂] = 2`**, in the even lane's `2 + 2h` spelling with `h = 0`. -/
theorem evenStratumFrame_finrank_KNegOne :
    Module.finrank ℚ_[2] EvenUnram.evenUnramKNegOne = 2 + 2 * 0 :=
  finrank_quadField evenStratumFrame_not_isSquare_neg_one

variable [CompactSpace (GalK EvenUnram.evenUnramKNegOne)]
  [TotallyDisconnectedSpace (GalK EvenUnram.evenUnramKNegOne)]

local instance evenStratumFrameKScalar :
    DistribMulAction (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenStratumFrameKContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **NO CUP-ADAPTED STAGE FRAME AT `ℚ₂(i)`**, at every row table.  Over the standing profinite
binders and nothing else: no reciprocity bundle, since the range bound comes from the square
root of `−1` directly, and no ramification binder, since §4 uses none.

Wave 71 refuted the coordinate model here; this refutes the frame. -/
theorem evenStratum_no_cupAdaptedFrame_KNegOne (v : Fin (MarkedCore.coreRank 0) → ℤ_[2]ˣ) :
    ¬ ∃ F : StageGeneric.Frame v (maxProPQuotient 2 (GalK EvenUnram.evenUnramKNegOne))
        (chiCycKTwo (K := EvenUnram.evenUnramKNegOne)),
      F.IsCupAdapted (StageGeneric.evenFrameGram 0)
        (StageGeneric.evenFramePairing (K := EvenUnram.evenUnramKNegOne)) :=
  evenStratum_no_cupAdaptedFrame
    (EvenUnram.evenUnram_range_le_prin_two_of_sqrt_neg_one (sqrtIn_mem_quadField (-1))
      evenParity_sqrtIn_neg_one_sq) evenStratumFrame_finrank_KNegOne v

end ModelField

/-! ## §6 The surviving point, reduced to a base and a climb

Wave 71 reduced the classification at the surviving point to one `Prop`,
`Nonempty (NForwardGeneratorData 1 h χ_cyc)`.  That `Prop` is a *structure* with nine fields, so
"one `Prop`" understates what is owed; this section unfolds it against the committed tree.

Of the nine fields, the six row fields (`x0`, `x1`, `sigma`, `x2`, `handleU`, `handleV`) are the
row table `vN 1` entry by entry, and every one of its values is attained by `χ_cyc` as soon as
the range is `imChiN 1`: `evenClimb_vN_mem_range` carries **no** `2 ≤ α`, so it applies at the
surviving parameter unchanged (`evenStratum_vN_one_mem_range`).  What is not free is the
interaction of the rows with the other three fields (`generators`, `relation`, `topGen`): a
tuple must have those values *and* generate *and* kill the relator.

The committed assembly of exactly that is `evenForwardGeneratorDataN_of_base_and_corrections`,
whose own binder is `1 ≤ α`.  Its two inputs are a level-three stage tuple and defect
reachability from level three up, and a level-three stage tuple is a `StageGeneric.Frame` whose
relator dies modulo `λ₃` (`Frame.toLevelThree`, which converts Frattini generation into
topological generation).  So `section Reduction` below names those two (`EvenStratumBaseN` and
`EvenStratumClimbN`, in source order *before* the row-field theorem just cited) and then
composes them:

> **`evenStratum_orientedEquivN_one_of_base_and_climb`**: at degree `2 + 2h`, a frame at the
> `vN 1` row table whose relator dies modulo `λ₃`, plus defect reachability at every level
> `≥ 3`, give the oriented equivalence.

The section closes with the seam against §4: the frame in that base is exactly the kind of
object §4 refutes cup-adaptedness of, so a lane building it must build it by other means.  That
is a statement about how the base may be *built*, not about whether it holds.  (`section
Reduction` carries no `§6.x` headers; the pointers above are by declaration name because the
source order does not match any numbering.) -/

section Reduction

/-- **The level-three base at the surviving parameter.**  A `StageGeneric.Frame` at the `N` row
table `vN 1` (actual elements with the exact cyclotomic values, and Frattini generation)
whose relator dies modulo `λ₃`.  This is `Frame.toLevelThree`'s input, hence a level-three
stage tuple. -/
def EvenStratumBaseN (K : IntermediateField ℚ_[2] ℚ̄₂) [CompactSpace (GalK K)]
    [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ) : Prop :=
  ∃ F : StageGeneric.Frame (StageGeneric.vN (h := h) 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)),
    F.LevelThreeRelation (StageGeneric.nStageWord 1 h (le_refl 1))

/-- **The climb at the surviving parameter.**  Defect reachability for every level-`k` stage
tuple at the `N_1` word datum, `k ≥ 3`.  This is the `Hcorr` input of
`evenForwardGeneratorDataN_of_base_and_corrections`.

The committed producer is `evenClimb_defectReachable`, and all three of its inputs are supplied
on the `N` row only under `2 ≤ α`: the residual supply at depth `α − 1`, the `d̄`-shift supply
`evenSharpDbarShiftSupply_n`, and the deep row supply `evenClimb_deepRowSupply_n`.  The middle
one is the sharpest obstruction: it is `evenRawStageShift_n`, whose own file records in prose
that the factorization's coordinate-`0` row is false at `α = 1`.  So this `Prop` is not merely
unproved at the surviving parameter; the committed route to it is blocked, exactly as the
committed route to `EvenStratumBaseN` is blocked by §4. -/
def EvenStratumClimbN (K : IntermediateField ℚ_[2] ℚ̄₂) [CompactSpace (GalK K)]
    [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ T : StageGeneric.Tuple (StageGeneric.nStageWord 1 h (le_refl 1))
      (StageGeneric.vN (h := h) 1) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
    StageGeneric.Tuple.DefectReachable T

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The six row fields of the datum are free at the surviving parameter.**  Every value of
the `vN 1` table is attained by `χ_cyc` once the range is `imChiN 1`.  The committed
`evenClimb_vN_mem_range` carries no lower bound on `α`, so nothing has to be re-proved here;
naming it records that the obstruction at `α = 1` is not in the values. -/
theorem evenStratum_vN_one_mem_range {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 1)
    (i : Fin (MarkedCore.coreRank h)) :
    StageGeneric.vN 1 i ∈ Set.range (chiCycKTwo (K := K)) :=
  StageGeneric.evenClimb_vN_mem_range hrange i

omit [FiniteDimensional ℚ_[2] K] in
/-- **What the base demands, unfolded.**  A tuple of actual elements of `G_K(2)` with the exact
`vN 1` cyclotomic values, generating the Frattini quotient, whose `N_1` relator dies at level
three.  Nothing is hidden in the structure: these three conditions are its three fields. -/
theorem evenStratumBaseN_iff {h : ℕ} :
    EvenStratumBaseN K h ↔
      ∃ g : Fin (MarkedCore.coreRank h) → maxProPQuotient 2 (GalK K),
        (∀ i, chiCycKTwo (K := K) (g i) = StageGeneric.vN 1 i) ∧
        Subgroup.closure
            (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2 (g i)) = ⊤ ∧
        MarkedCore.nRelWord 1
          (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3 (g i)) = 1 := by
  constructor
  · rintro ⟨F, hrel⟩
    exact ⟨F.generators, F.rows, F.levelTwoGen, hrel⟩
  · rintro ⟨g, hrows, hgen, hrel⟩
    exact ⟨{ generators := g, rows := hrows, levelTwoGen := hgen }, hrel⟩

/-- **The forward-generator datum at `α = 1`, from the base and the climb.**  The committed
inverse-limit endpoint at its own binder `1 ≤ α`, fed by `Frame.toLevelThree`. -/
theorem evenStratum_forwardGeneratorDataN_one_of_base_and_climb {h : ℕ}
    (Hbase : EvenStratumBaseN K h) (Hclimb : EvenStratumClimbN K h) :
    Nonempty (EvenForward.NForwardGeneratorData 1 h (chiCycKTwo (K := K))) := by
  obtain ⟨F, hrel⟩ := Hbase
  exact StageGeneric.evenForwardGeneratorDataN_of_base_and_corrections (le_refl 1)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    (F.toLevelThree hrel (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
      isProP_maxProPQuotient)
    Hclimb

/-- **THE REDUCTION AT THE SURVIVING POINT, UNFOLDED.**  At degree `2 + 2h`, the base and the
climb at `α = 1` give the oriented equivalence `chiN 1 h ≃ χ_cyc`.

Composed with wave 71's `evenStratum_orientedEquivN_one_of_forwardGeneratorData`, whose other
two inputs (the depth binder and the model-side package) are already discharged at `α = 1`.
This is a reduction, not a classification: neither this file nor any other asserts or denies
the existence of that equivalence. -/
theorem evenStratum_orientedEquivN_one_of_base_and_climb {h : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hbase : EvenStratumBaseN K h) (Hclimb : EvenStratumClimbN K h) :
    Nonempty (OrientedContinuousMulEquiv (chiN 1 h) (chiCycKTwo (K := K))) :=
  EvenStratum.evenStratum_orientedEquivN_one_of_forwardGeneratorData hev
    (evenStratum_forwardGeneratorDataN_one_of_base_and_climb Hbase Hclimb)

omit [T2Space (GalK K)] in
/-- **The seam with §4.**  On the third stratum, the frame witnessing a base is never
cup-adapted for `evenFrameGram h`.  So the base is not refuted, but the committed route to it
is: any lane producing the base must produce its frame by some means other than the
cup-adaptation step that all three even frame producers share.

Read with §4: the Gram whose adaptation is impossible here is the `α ≥ 2` shape, whose model is
non-alternating, while this stratum's cup form is alternating. -/
theorem evenStratum_baseN_frame_not_cupAdapted {h : ℕ}
    (hle : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≤ evenRangePrin 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (F : StageGeneric.Frame (StageGeneric.vN (h := h) 1) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))) :
    ¬ F.IsCupAdapted (StageGeneric.evenFrameGram h)
      (StageGeneric.evenFramePairing (K := K)) :=
  fun hF ↦ evenStratum_no_cupAdaptedFrame hle hev _ ⟨F, hF⟩

end Reduction

/-! ## §7 The `q`-invariant of the `N` family stops at `4`

Wave 69's queue item 4 and wave 71's queue item 4 both record that `q ≥ 8` is out of reach for
the committed core families because no `2 + 2^a` is a power of two above `4`.  Four theorems
here, of which two are the arithmetic and two the invariant.

**The arithmetic half was already committed**, and both cited queue items call it a theorem
rather than prose: `evenUnram_head_eq_two_pow_iff` (`EvenUnramified.lean:274`) has said
`2 + 2^a = 2^b ↔ (a = 1 ∧ b = 2)` since wave 69, under the same headline this section reuses.
`evenStratum_two_add_two_pow_eq_two_pow` is its `mp` direction and
`evenStratum_pAlpha_eq_pow_two_iff` is it again modulo unfolding `pAlpha α = 2 + 2^α`, the `x₀`
exponent of the `N_α` core.  The de-duplication would be a statement change and is not made
here.  **What this section genuinely supplies is the invariant half**, composed from the two
committed computations (`nFrame4_demushkinQ_DN_one` at `α = 1` and
`nFrameExists_demushkinQ_DN` at `α ≥ 2`), which needs no arithmetic at all.  Neither says
anything about fields: `ℚ₂(ζ₈)` has `demushkinQ = 8` (not `q_K`, which is `2` there, the
extension being totally ramified), and the content here is that no member of the
present `N` family is isomorphic to its maximal pro-`2` quotient. -/

section QInvariant

/-- **If `2 + 2^a` is a power of two then `a = 1`**, where it is `4`.  (One direction only; the
`iff` is `evenStratum_pAlpha_eq_pow_two_iff` below, and wave 69's
`evenUnram_head_eq_two_pow_iff`.)  Both `2 ≤ a` and
`a = 0` are excluded by a mod-four count: `2 + 2^a` is `2` mod `4` in the first case and odd in
the second, while a power of two above `2` is `0` mod `4`. -/
theorem evenStratum_two_add_two_pow_eq_two_pow {a b : ℕ} (hab : 2 + 2 ^ a = 2 ^ b) :
    a = 1 ∧ b = 2 := by
  have hfour : ∀ n : ℕ, 2 ≤ n → (4 : ℕ) ∣ 2 ^ n := fun n hn =>
    dvd_trans (by norm_num) (pow_dvd_pow 2 hn)
  have hsmall : ∀ n : ℕ, n ≤ 1 → (2 : ℕ) ^ n ≤ 2 := by
    intro n hn
    interval_cases n <;> norm_num
  have hpos : ∀ n : ℕ, 0 < (2 : ℕ) ^ n := fun n => pow_pos (by norm_num) n
  have ha : a ≤ 1 := by
    by_contra hlt
    have h4a := hfour a (by omega)
    have hge : (4 : ℕ) ≤ 2 ^ a := Nat.le_of_dvd (hpos a) h4a
    have hb : 2 ≤ b := by
      by_contra hb1
      have := hsmall b (by omega)
      omega
    have h4b := hfour b hb
    omega
  interval_cases a
  · exfalso
    simp only [pow_zero] at hab
    rcases Nat.lt_or_ge b 2 with hb | hb
    · have := hsmall b (by omega)
      omega
    · have := hfour b hb
      omega
  · refine ⟨rfl, ?_⟩
    simp only [pow_one] at hab
    have h2 : (2 : ℕ) ^ b = 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 from rfl]
      omega
    exact Nat.pow_right_injective (le_refl 2) h2

/-- The same for the campaign's named exponent `pAlpha α = 2 + 2^α`, the `x₀` exponent of the
`N_α` core `x₀^{p_α}[x₀,x₁][σ,x₂]`. -/
theorem evenStratum_pAlpha_eq_pow_two_iff {a b : ℕ} :
    pAlpha a = 2 ^ b ↔ (a = 1 ∧ b = 2) := by
  constructor
  · exact fun h => evenStratum_two_add_two_pow_eq_two_pow h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The `N` family's `q`-invariant never exceeds `4`.**  Wave 70's `α = 1` computation and the
committed `α ≥ 2` one, side by side.  Nothing else in the range `1 ≤ α` is left. -/
theorem evenStratum_demushkinQ_DN_le_four {α : ℕ} (hα : 1 ≤ α) (h : ℕ) :
    demushkinQ (MarkedCore.DN α h : Type) ≤ 4 := by
  rcases Nat.lt_or_ge α 2 with hlt | hge
  · have hone : α = 1 := by omega
    subst hone
    rw [MarkedCore.nFrame4_demushkinQ_DN_one]
  · rw [MarkedCore.nFrameExists_demushkinQ_DN hge]
    omega

/-- **`q ≥ 8` is out of reach for the present `N` family**, at every parameter `α ≥ 1` and every
handle count.  This is a statement about the family, not about fields: a field whose maximal
pro-`2` quotient has `q = 2^b` with `b ≥ 3` is simply not one of these cores, and reaching it
needs a new core family. -/
theorem evenStratum_demushkinQ_DN_ne_pow_two {α h b : ℕ} (hα : 1 ≤ α) (hb : 3 ≤ b) :
    demushkinQ (MarkedCore.DN α h : Type) ≠ 2 ^ b := by
  intro heq
  have hle := evenStratum_demushkinQ_DN_le_four hα h
  rw [heq] at hle
  have hge : (8 : ℕ) ≤ 2 ^ b := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  omega

end QInvariant

end

/-! ## §8 Axiom pins -/

#print axioms evenStratumFrame_gram_diag
#print axioms evenStratumFrame_eval_sub
#print axioms evenStratumFrame_exists_character
#print axioms evenStratumFrame_character_eq_one
#print axioms evenStratumFrame_eq_zero_of_eval_gens
#print axioms evenStratumFrame_pairing_self
#print axioms evenStratumFrame_eval_gen_zero
#print axioms evenStratum_no_cupAdaptedFrame
#print axioms evenStratum_no_cupAdaptedFrame_of_rangeN_one
#print axioms evenStratumFrame_not_isSquare_neg_one
#print axioms evenStratumFrame_finrank_KNegOne
#print axioms evenStratum_no_cupAdaptedFrame_KNegOne

#print axioms evenStratum_vN_one_mem_range
#print axioms EvenStratumBaseN
#print axioms EvenStratumClimbN
#print axioms evenStratumBaseN_iff
#print axioms evenStratum_forwardGeneratorDataN_one_of_base_and_climb
#print axioms evenStratum_orientedEquivN_one_of_base_and_climb
#print axioms evenStratum_baseN_frame_not_cupAdapted

#print axioms evenStratum_two_add_two_pow_eq_two_pow
#print axioms evenStratum_pAlpha_eq_pow_two_iff
#print axioms evenStratum_demushkinQ_DN_le_four
#print axioms evenStratum_demushkinQ_DN_ne_pow_two

-- The three statements §6 stands against, printed beside it.  They are not three `α ≥ 2`
-- analogues: the first carries `1 ≤ α`, only the second carries `2 ≤ α`, and the third is
-- wave 71's own statement fixed at `α = 1`.
#print axioms GQ2.Dyadic.StageGeneric.evenForwardGeneratorDataN_of_base_and_corrections
#print axioms GQ2.Dyadic.EvenAlphaTwo.evenAlphaTwo_forwardGeneratorDataN_of_residual
#print axioms GQ2.Dyadic.EvenStratum.evenStratum_orientedEquivN_one_of_forwardGeneratorData

end GQ2.Dyadic.EvenStratumFrame
