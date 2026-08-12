/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenStratumPoint

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
   the diagonal, which wave 71 proved is `0` on this stratum.  Through
   `frattiniFrameEval_characterClass` this says: every degree-one class evaluates to `0` at
   `F.generators 0`.
3. **Counting** (§4).  A class evaluating to zero at all of `F.generators` is zero: characters
   kill `λ₂`, so `Frame.levelTwoGen` promotes vanishing on the generators to vanishing
   everywhere (§2).  So the coordinate map `H¹ → (Fin (coreRank h) → 𝔽₂)` is injective; both
   sides have `2 ^ (4 + 2h)` elements by `card_H1_zmodTwo_maxProTwoGalK`, so it is a bijection,
   so *some* class has coordinate `1` at index `0`, contradicting step 2.

Nondegeneracy of the cup form is **not** used; `Frame.levelTwoGen` does that work, which is why
the conclusion needs no reciprocity bundle and no ramification binder.

## What is NOT claimed

Nothing here bears on `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)` in either
direction, and no declaration below mentions it.  What is refuted is the availability of one
*route*: a frame cup-adapted for `evenFrameGram h`.  That Gram is the `α ≥ 2` shape, whose
model is non-alternating; the surviving point's cup form is alternating, so a forward-generator
tuple there is not required to be cup-adapted for it, and §5's reduction is untouched by §4.
The two live side by side deliberately.

## Contents

* **§1** The diagonal of `evenFrameGram`.
* **§2** Characters, and the duality that `Frame.levelTwoGen` supplies.
* **§3** On the stratum every class evaluates to zero at the zeroth generator.
* **§4** The refutation, and its two instantiations.
* **§5** Axiom pins.
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

end

/-! ## §5 Axiom pins -/

#print axioms evenStratumFrame_gram_diag
#print axioms evenStratumFrame_eval_sub
#print axioms evenStratumFrame_exists_character
#print axioms evenStratumFrame_character_eq_one
#print axioms evenStratumFrame_eq_zero_of_eval_gens
#print axioms evenStratumFrame_pairing_self
#print axioms evenStratumFrame_eval_gen_zero
#print axioms evenStratum_no_cupAdaptedFrame
#print axioms evenStratum_no_cupAdaptedFrame_of_rangeN_one

end GQ2.Dyadic.EvenStratumFrame
