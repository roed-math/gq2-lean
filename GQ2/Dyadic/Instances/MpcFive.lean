/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcLadder

/-!
# W87-FIVE: the `M6` word at class five, and the class-five decision

Wave 86 (`GQ2/Dyadic/Instances/MpcLadder.lean`) made every rung of the `M6` ladder an iff
(`mpcLad_nonempty_iff`), gave a rung its exact shape as an `𝔽₂`-linear membership test inside a
`λ_j`-orbit (`mpcLad_defect_orbit`), and computed **one** of the four factors of `mWord` at class
five (`mpcLad_pow_letC_five`).  It left the other three factors and the decision open.

This module computes the three remaining factors, assembles the class-five defect in closed form,
evaluates it at the wave-84 class-four witness, and decides the class-five rung.

## What lands

1. **The three remaining factors** (§1-§3).  `mpcFv_sq_letA` (the `Ā`-letter square, whose
   `z = (B̄⁴)⁻¹` is no longer central at class five), `mpcFv_comm_letAB`, `mpcFv_comm_letCD`.
   Each is the class-four lemma of `MpcBuild.lean` times an explicit product of central
   corrections, and each correction vanishes at class four for a stated reason.

2. **The class-five defect in closed form** (§4).  `mpcFv_mWord_five`, the analogue of
   `mpcBld_mWord_four` one class up, and `mpcFv_defect_five`, its reading on `D_M 2 0`.  The
   assembly is clean for a reason worth recording: every correction factor lies in `λ₃/λ₅`, and
   `λ₃/λ₅` commutes with both `λ₂/λ₅` and itself in `Q₅`, so nothing has to be moved past the
   three trailing letters of `mWord`.

3. **The witness's class-five defect** (§5).  `mpcFv_witness_defect`: at the wave-84 witness
   `s = t = ⁅D̄, B̄⁆`, `m = n = 1`, every `λ₃`-valued term cancels and exactly three central
   involutions survive:

       ⁅B̄⁴, Ā⁆ · ⁅C̄₀, B̄²⁆² · ⁅⁅B̄², D̄⁆, C̄₀⁆ .

4. ⭐⭐⭐ **The class-five rung is climbed** (§6).  `mpcFv_supply_witness` exhibits a reachable
   `λ₃`-move killing that defect - `us = 1`, `ut = B̄⁴`, `um = 1`, `un = B̄⁴·⁅B̄², D̄⁆` - and
   `mpcFv_nonempty_five : (mpcWordSet 5).Nonempty` follows, with the explicit class-five witness
   `mpcFvW5`.  So the residue of `MpcPivShift 2` starts at class **six**, not five.

## What does not land

**`MpcPivShift 2` is still open**, and this module makes no negative claim of any kind.  What is
decided here is one rung: the class-five solution set of the `M6` **ansatz** is nonempty.  Wave
86's structural gap is untouched - the orbit space of `mpcWordSet (j+1)` under `λ_j`-moves is
still not shown to be a point - but the class-five rung did not need it, because the rung was hit
inside the wave-84 witness's own orbit.

Declaration prefix `mpcFv` (namespace `GQ2.Dyadic.Instances.MpcFv`).  No `sorry`, no new axiom,
no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcFv

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld GQ2.Dyadic.Instances.MpcLad
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-! ## §0 The class-five layer calculus, in the form the three factors need

Everything is read in `Q₅ = G/λ₅`, with three layers in play:

* `Y = λ₂/λ₅` (`lambdaImage G 2 5`), where every bracket lands;
* `L = λ₃/λ₅` (`lambdaImage G 3 5`), where `⁅Y, G⁆`, `Y²` and `p⁴` land;
* `Z = λ₄/λ₅` (`zLayer G 4`), central of exponent two, where `⁅L, G⁆`, `⁅Y, Y⁆`, `L²` and `p⁸`
  land.

The two facts that drive every cancellation below are `⁅Y, L⁆ = 1` (wave 86's
`mpcLad_five_vanish`, which is `cfive_commutator_lambdaTwo` at `k = 3`) and `L ⊆ Y`, which
together give `⁅L, L⁆ = 1`: **`L` is a central-enough layer that it commutes with everything a
correction can produce.**  That is why the assembly in §4 costs nothing. -/

section Calculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Moving a central factor one place to the right. -/
private theorem mpcFv_cmove {Q : Type*} [Group Q] {z : Q} (hz : ∀ x : Q, z * x = x * z)
    (x y : Q) : x * z * y = x * y * z := by
  rw [mul_assoc, hz, ← mul_assoc]

/-- A `Z`-element commutes with everything in `Q₅`. -/
private theorem mpcFv_zcomm {z : levelQuot G 5} (hz : z ∈ zLayer G 4) (x : levelQuot G 5) :
    z * x = x * z := (zLayer_commute hz x).eq

/-- The bracket swap, in any group. -/
private theorem mpcFv_swap {Q : Type*} [Group Q] (x y : Q) : commP x y = (commP y x)⁻¹ := by
  simp only [commP]; group

/-- Every bracket of `Q₅` is a `Y`-element. -/
theorem mpcFv_commP_mem_two (x y : levelQuot G 5) : commP x y ∈ lambdaImage G 2 5 :=
  mpcLad_commP_mem_two (j := 3) x y

/-- A bracket with a `Y`-slot on the left lands in `L`. -/
theorem mpcFv_commP_mem_three_left {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (x : levelQuot G 5) : commP y x ∈ lambdaImage G 3 5 :=
  cfive_commP_lambdaTwo_mem_lambdaThree hy x

/-- A bracket with a `Y`-slot on the right lands in `L`. -/
theorem mpcFv_commP_mem_three_right (x : levelQuot G 5) {y : levelQuot G 5}
    (hy : y ∈ lambdaImage G 2 5) : commP x y ∈ lambdaImage G 3 5 :=
  mpcLad_five_commP_mem_three_right x hy

/-- A bracket with an `L`-slot on the left is central. -/
theorem mpcFv_commP_mem_zLayer_left {ε : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5)
    (x : levelQuot G 5) : commP ε x ∈ zLayer G 4 :=
  cfive_commP_mem_zLayer_left (k := 3) hε x

/-- A bracket with an `L`-slot on the right is central. -/
theorem mpcFv_commP_mem_zLayer_right (x : levelQuot G 5) {ε : levelQuot G 5}
    (hε : ε ∈ lambdaImage G 3 5) : commP x ε ∈ zLayer G 4 :=
  cfive_commP_mem_zLayer_right (k := 3) x hε

/-- A bracket of two `Y`-elements is central. -/
theorem mpcFv_commP_mem_zLayer_two {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) : commP y y' ∈ zLayer G 4 :=
  cfive_commP_lambdaTwo_mem_zLayer hy hy'

/-- A `Z`-element kills a bracket from the left. -/
theorem mpcFv_commP_zLayer_left {z : levelQuot G 5} (hz : z ∈ zLayer G 4) (x : levelQuot G 5) :
    commP z x = 1 := cfive_commP_zLayer_left (k := 3) hz x

/-- A `Z`-element kills a bracket from the right. -/
theorem mpcFv_commP_zLayer_right (x : levelQuot G 5) {z : levelQuot G 5} (hz : z ∈ zLayer G 4) :
    commP x z = 1 := by
  rw [mpcFv_swap, mpcFv_commP_zLayer_left hz x, inv_one]

/-- `⁅Y, L⁆ = 1` in `Q₅`. -/
theorem mpcFv_vanish {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : commP y ε = 1 := mpcLad_five_vanish hy hε

/-- `⁅L, Y⁆ = 1` in `Q₅`. -/
theorem mpcFv_vanish' {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : commP ε y = 1 := mpcLad_five_vanish' hy hε

/-- `⁅L, L⁆ = 1` in `Q₅`: the layer `L` is abelian, because it sits inside `Y`. -/
theorem mpcFv_vanish33 {ε ε' : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5)
    (hε' : ε' ∈ lambdaImage G 3 5) : commP ε ε' = 1 :=
  mpcFv_vanish (mpcLad_five_three_le_two hε) hε'

/-- An `L`-element commutes with a `Y`-element. -/
theorem mpcFv_lycomm {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : ε * y = y * ε :=
  (cfour_commute_of_comm (mpcFv_vanish' hy hε)).eq

/-- The square of a `Y`-element is an `L`-element. -/
theorem mpcFv_sq_mem_three {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    y ^ 2 ∈ lambdaImage G 3 5 := mpcLad_five_sq_mem_three hy

/-- The square of an `L`-element is central. -/
theorem mpcFv_sq_mem_zLayer {ε : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5) :
    ε ^ 2 ∈ zLayer G 4 := mpcLad_sq_mem_zLayer (j := 3) hε

/-- `L ⊆ Y`. -/
theorem mpcFv_three_le_two {ε : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5) :
    ε ∈ lambdaImage G 2 5 := mpcLad_five_three_le_two hε

/-- `Z ⊆ L`. -/
theorem mpcFv_zLayer_le_three {z : levelQuot G 5} (hz : z ∈ zLayer G 4) :
    z ∈ lambdaImage G 3 5 := by
  obtain ⟨v, hv, rfl⟩ := hz
  exact ⟨v, twoCentralSeries_antitone (G := G) (by omega : (3 : ℕ) ≤ 4) hv, rfl⟩

/-- **Left-slot additivity against an `L`-element**, the right slot unrestricted. -/
theorem mpcFv_commP_left_add {ε ε' : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5)
    (x : levelQuot G 5) : commP (ε * ε') x = commP ε x * commP ε' x :=
  mpcLad_commP_left_add (j := 3) hε x

/-- **Right-slot additivity against two `L`-elements.** -/
theorem mpcFv_commP_right_add (x : levelQuot G 5) {ε ε' : levelQuot G 5}
    (hε : ε ∈ lambdaImage G 3 5) (hε' : ε' ∈ lambdaImage G 3 5) :
    commP x (ε * ε') = commP x ε * commP x ε' :=
  mpcLad_commP_right_add (j := 3) x hε hε'

/-- **The left slot of a bracket inverts on `L`.** -/
theorem mpcFv_commP_inv_left {ε : levelQuot G 5} (hε : ε ∈ lambdaImage G 3 5)
    (x : levelQuot G 5) : commP ε⁻¹ x = (commP ε x)⁻¹ := by
  have h : commP (ε⁻¹ * ε) x = commP ε⁻¹ x * commP ε x :=
    mpcFv_commP_left_add (Subgroup.inv_mem _ hε) x
  rw [inv_mul_cancel, cfour_one_comm] at h
  exact mul_eq_one_iff_eq_inv.mp h.symm

/-- **Both slots of a bracket against `Y` are additive when the other slot is a `Y`-element**:
the correction is a bracket of a `Z`-element. -/
theorem mpcFv_commP_two_add_left {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) (x : levelQuot G 5) :
    commP (y * x) y' = commP y y' * commP x y' :=
  cfive_commP_lambdaTwo_hom_left hy hy' x

end Calculus

/-! ## §1 The `Ā`-letter's square

`mpcBld_sq_letA` reads `(p·z·σ)² = p²·(σ²·⁅σ,p⁆)` in `Q₄`, where the ansatz's `z = (q⁴)⁻¹` is a
central involution and so contributes nothing.  At class five `q⁴` is only an `L`-element
(`cfive_pow_four_mem_lambdaThree`), so `z² = q⁻⁸` and `⁅z,p⁆` both survive.  They are central,
so they can be collected at the right, and the class-four statement is the case `z ∈ Z`. -/

section LetterA

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **THE `Ā`-LETTER'S SQUARE AT CLASS FIVE.**  `(p·z·σ)² = p²·(σ²·⁅σ,p⁆)·(z²·⁅z,p⁆)` with
`z` an `L`-element and `σ` a `Y`-correction.  The two extra factors `z²` and `⁅z,p⁆` are central
of order dividing two; both are `1` in `Q₄`, where `z` is itself central, which is
`mpcBld_sq_letA`. -/
theorem mpcFv_sq_letA {p σ z : levelQuot G 5} (hσ : σ ∈ lambdaImage G 2 5)
    (hz : z ∈ lambdaImage G 3 5) :
    (p * z * σ) ^ 2 = p ^ 2 * (σ ^ 2 * commP σ p) * (z ^ 2 * commP z p) := by
  have hzp : commP z p ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_left hz p
  have hz2 : z ^ 2 ∈ zLayer G 4 := mpcFv_sq_mem_zLayer hz
  have hζ : z ^ 2 * commP z p ∈ zLayer G 4 := Subgroup.mul_mem _ hz2 hzp
  have hσp : commP σ p ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_left hσ p
  -- the square of the `z`-shifted head
  have h1 : (p * z) ^ 2 = p ^ 2 * (z ^ 2 * commP z p) := by
    rw [cfour_sq_mul, mpcFv_commP_zLayer_left hzp z, mul_one, mul_assoc]
  -- the correction sees only the head
  have h2 : commP σ (p * z) = commP σ p := by
    rw [cfour_commP_mul_right, mpcFv_vanish hσ hz, mpcFv_vanish33 hσp hz, mul_one, one_mul]
  have h3 : commP (commP σ (p * z)) σ = 1 := by
    rw [h2]; exact mpcFv_vanish' hσ hσp
  calc (p * z * σ) ^ 2
      = (p * z) ^ 2 * σ ^ 2 * commP σ (p * z) * commP (commP σ (p * z)) σ := cfour_sq_mul _ _
    _ = p ^ 2 * (z ^ 2 * commP z p) * σ ^ 2 * commP σ p := by rw [h3, h2, h1, mul_one]
    _ = p ^ 2 * σ ^ 2 * (z ^ 2 * commP z p) * commP σ p := by
        rw [mpcFv_cmove (mpcFv_zcomm hζ) (p ^ 2) (σ ^ 2)]
    _ = p ^ 2 * σ ^ 2 * commP σ p * (z ^ 2 * commP z p) := by
        rw [mpcFv_cmove (mpcFv_zcomm hζ) (p ^ 2 * σ ^ 2) (commP σ p)]
    _ = p ^ 2 * (σ ^ 2 * commP σ p) * (z ^ 2 * commP z p) := by group

end LetterA

/-! ## §2 Axiom pins

One line per public declaration, in declaration order, measured against the mirror. -/

section AxiomPins

#print axioms mpcFv_commP_mem_two
#print axioms mpcFv_commP_mem_three_left
#print axioms mpcFv_commP_mem_three_right
#print axioms mpcFv_commP_mem_zLayer_left
#print axioms mpcFv_commP_mem_zLayer_right
#print axioms mpcFv_commP_mem_zLayer_two
#print axioms mpcFv_commP_zLayer_left
#print axioms mpcFv_commP_zLayer_right
#print axioms mpcFv_vanish
#print axioms mpcFv_vanish'
#print axioms mpcFv_vanish33
#print axioms mpcFv_lycomm
#print axioms mpcFv_sq_mem_three
#print axioms mpcFv_sq_mem_zLayer
#print axioms mpcFv_three_le_two
#print axioms mpcFv_zLayer_le_three
#print axioms mpcFv_commP_left_add
#print axioms mpcFv_commP_right_add
#print axioms mpcFv_commP_inv_left
#print axioms mpcFv_commP_two_add_left
#print axioms mpcFv_sq_letA

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcFv
