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

/-- Moving an `L`-factor one place to the right past a `Y`-factor. -/
private theorem mpcFv_lmove {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) (x : levelQuot G 5) : x * ε * y = x * y * ε := by
  rw [mul_assoc, mpcFv_lycomm hy hε, ← mul_assoc]

/-- **The left slot of a bracket doubles up**, exactly as at class four: the correction
`⁅⁅q,w⁆,q⁆` is an `L`-element and commutes with the `Y`-element `⁅q,w⁆`.  This is the identity
that turns `⁅q², w⁆` into the class-four shape `⁅q,w⁆²·⁅⁅q,w⁆,q⁆`. -/
theorem mpcFv_commP_sq_left (q w : levelQuot G 5) :
    commP (q ^ 2) w = commP q w ^ 2 * commP (commP q w) q := by
  have hqw : commP q w ∈ lambdaImage G 2 5 := mpcFv_commP_mem_two q w
  have hk : commP (commP q w) q ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_left hqw q
  rw [pow_two q, cfour_commP_mul_left q q w, mpcFv_lmove hqw hk (commP q w),
    ← pow_two (commP q w)]

/-- A product `m₁·z₁·(m₂·z₂)·z₃` with `z₁` central collects into `m₁·m₂·(z₁·z₂·z₃)`. -/
private theorem mpcFv_join3 {Q : Type*} [Group Q] {z₁ : Q} (h₁ : ∀ x : Q, z₁ * x = x * z₁)
    (m₁ m₂ z₂ z₃ : Q) : m₁ * z₁ * (m₂ * z₂) * z₃ = m₁ * m₂ * (z₁ * z₂ * z₃) := by
  calc m₁ * z₁ * (m₂ * z₂) * z₃ = m₁ * z₁ * m₂ * z₂ * z₃ := by group
    _ = m₁ * m₂ * z₁ * z₂ * z₃ := by rw [mpcFv_cmove h₁ m₁ m₂]
    _ = m₁ * m₂ * (z₁ * z₂ * z₃) := by group

/-- Exchanging the first and third factors of a four-term product, all three commutations
supplied. -/
private theorem mpcFv_swap4 {Q : Type*} [Group Q] {x y u : Q} (hxy : x * y = y * x)
    (hxu : x * u = u * x) (hyu : y * u = u * y) (v : Q) : x * y * u * v = u * y * x * v := by
  calc x * y * u * v = y * x * u * v := by rw [hxy]
    _ = y * u * x * v := by rw [mul_assoc y x u, hxu, ← mul_assoc]
    _ = u * y * x * v := by rw [hyu]

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

/-! ## §2 The `Ā`/`B̄` bracket

`mpcBld_comm_letAB` reads `⁅p·z·σ, q·τ⁆ = ⁅p,q⁆·(⁅p,τ⁆·⁅σ,q⁆)` in `Q₄`: only the two
first-order terms survive, because at class four a correction of a correction is a bracket of two
`Y`-elements and dies.  At class five `⁅Y,Y⁆` is central but not trivial, so three such terms
survive - `⁅σ,τ⁆` and the two `⁅⁅p,q⁆, ·⁆` - and `z` contributes `⁅z,q⁆`.  All four are central
of order dividing two. -/

section LetterAB

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **THE `Ā`/`B̄` BRACKET AT CLASS FIVE.**

    ⁅p·z·σ, q·τ⁆ = ⁅p,q⁆ · (⁅p,τ⁆·⁅σ,q⁆) · (⁅σ,τ⁆·⁅z,q⁆·⁅⁅p,q⁆,σ⁆·⁅⁅p,q⁆,τ⁆) .

The first two groups are `mpcBld_comm_letAB`; the third is central of exponent two and is `1` in
`Q₄`, where `⁅Y,Y⁆ = 1` kills the three bracket-of-bracket terms and `z ∈ Z` kills `⁅z,q⁆`. -/
theorem mpcFv_comm_letAB {p q σ τ z : levelQuot G 5} (hσ : σ ∈ lambdaImage G 2 5)
    (hτ : τ ∈ lambdaImage G 2 5) (hz : z ∈ lambdaImage G 3 5) :
    commP (p * z * σ) (q * τ)
      = commP p q * (commP p τ * commP σ q) *
        (commP σ τ * commP z q * commP (commP p q) σ * commP (commP p q) τ) := by
  have hpq : commP p q ∈ lambdaImage G 2 5 := mpcFv_commP_mem_two p q
  have hpτ : commP p τ ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_right p hτ
  have hσq : commP σ q ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_left hσ q
  have hzq : commP z q ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_left hz q
  have hστ : commP σ τ ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_two hσ hτ
  have hpqσ : commP (commP p q) σ ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_two hpq hσ
  -- the `Ā`-letter against the `B̄`-correction: `z` is invisible, `σ` is not
  have h1 : commP (p * z) τ = commP p τ := by
    rw [cfour_commP_mul_left p z τ, mpcFv_vanish33 hpτ hz, mpcFv_vanish' hτ hz, mul_one, mul_one]
  have h2 : commP (p * z * σ) τ = commP p τ * commP σ τ := by
    rw [cfour_commP_mul_left (p * z) σ τ, h1, mpcFv_vanish' hσ hpτ, mul_one]
  -- the `Ā`-letter against the marked `B̄`
  have h3 : commP (p * z) q = commP p q * commP z q := by
    rw [cfour_commP_mul_left p z q, mpcFv_vanish hpq hz, mul_one]
  have h4 : commP (p * z * σ) q
      = commP p q * commP σ q * (commP z q * commP (commP p q) σ) := by
    rw [cfour_commP_mul_left (p * z) σ q, h3,
      mpcFv_commP_two_add_left hpq hσ (commP z q),
      mpcFv_commP_zLayer_left hzq σ, mul_one,
      mpcFv_cmove (mpcFv_zcomm hpqσ) (commP p q * commP z q) (commP σ q),
      mpcFv_cmove (mpcFv_zcomm hzq) (commP p q) (commP σ q), mul_assoc]
  -- the second-order correction sees only the marked bracket
  have h5 : commP (commP (p * z * σ) q) τ = commP (commP p q) τ := by
    have hY : commP p q * commP σ q ∈ lambdaImage G 2 5 :=
      Subgroup.mul_mem _ hpq (mpcFv_three_le_two hσq)
    rw [h4, mpcFv_commP_two_add_left hY hτ (commP z q * commP (commP p q) σ),
      mpcFv_commP_zLayer_left (Subgroup.mul_mem _ hzq hpqσ) τ, mul_one,
      mpcFv_commP_two_add_left hpq hτ (commP σ q), mpcFv_vanish' hτ hσq, mul_one]
  calc commP (p * z * σ) (q * τ)
      = commP (p * z * σ) τ * commP (p * z * σ) q * commP (commP (p * z * σ) q) τ :=
        cfour_commP_mul_right _ _ _
    _ = commP p τ * commP σ τ *
          (commP p q * commP σ q * (commP z q * commP (commP p q) σ)) *
        commP (commP p q) τ := by rw [h5, h4, h2]
    _ = commP p τ * (commP p q * commP σ q) *
          (commP σ τ * (commP z q * commP (commP p q) σ) * commP (commP p q) τ) :=
        mpcFv_join3 (mpcFv_zcomm hστ) _ _ _ _
    _ = commP p q * (commP p τ * commP σ q) *
          (commP σ τ * commP z q * commP (commP p q) σ * commP (commP p q) τ) := by
        rw [← mul_assoc (commP p τ) (commP p q) (commP σ q), mpcFv_lycomm hpq hpτ]
        group

end LetterAB

/-! ## §3 The `C̄₀`/`D̄` bracket

`mpcBld_comm_letCD` reads

    ⁅q²·r·μ, w·ν⁆ = ⁅r,w⁆ · (⁅q,w⁆²·⁅⁅q,w⁆,q⁆·⁅r,ν⁆·⁅μ,w⁆)

in `Q₄`, and calls the first two factors of the second group "the `B̄²` prefix's own cost".  At
class five five more terms survive, all central of order dividing two, and all of them
bracket-of-bracket or `⁅Y,Y⁆` terms that class four kills for the same single reason. -/

section LetterCD

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **THE `C̄₀`/`D̄` BRACKET AT CLASS FIVE.**

    ⁅q²·r·μ, w·ν⁆ = ⁅r,w⁆ · (⁅q,w⁆²·⁅⁅q,w⁆,q⁆·⁅r,ν⁆·⁅μ,w⁆)
                          · (⁅q²,ν⁆·⁅μ,ν⁆·⁅⁅q²,w⁆,r⁆·⁅⁅r,w⁆,μ⁆·⁅⁅r,w⁆,ν⁆) .

The first two groups are `mpcBld_comm_letCD`; the third is central of exponent two and vanishes
at class four, where `⁅Y,Y⁆ = 1` kills `⁅q²,ν⁆` and `⁅μ,ν⁆` and the last two, and `⁅q²,w⁆ ∈ Z`
kills the middle one. -/
theorem mpcFv_comm_letCD {q r w μ ν : levelQuot G 5} (hμ : μ ∈ lambdaImage G 2 5)
    (hν : ν ∈ lambdaImage G 2 5) :
    commP (q ^ 2 * r * μ) (w * ν)
      = commP r w * (commP q w ^ 2 * commP (commP q w) q * commP r ν * commP μ w) *
        (commP (q ^ 2) ν * commP μ ν * commP (commP (q ^ 2) w) r * commP (commP r w) μ *
          commP (commP r w) ν) := by
  rw [← mpcFv_commP_sq_left q w]
  have hq2 : q ^ 2 ∈ lambdaImage G 2 5 := mpcLad_five_sq_mem_two q
  have hq2w : commP (q ^ 2) w ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_left hq2 w
  have hq2ν : commP (q ^ 2) ν ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_two hq2 hν
  have hrν : commP r ν ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_right r hν
  have hμν : commP μ ν ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_two hμ hν
  have hrw : commP r w ∈ lambdaImage G 2 5 := mpcFv_commP_mem_two r w
  have hμw : commP μ w ∈ lambdaImage G 3 5 := mpcFv_commP_mem_three_left hμ w
  have hq2wr : commP (commP (q ^ 2) w) r ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_left hq2w r
  have hrwμ : commP (commP r w) μ ∈ zLayer G 4 := mpcFv_commP_mem_zLayer_two hrw hμ
  -- the pivot letter against the `D̄`-correction
  have h1 : commP (q ^ 2 * r) ν = commP (q ^ 2) ν * commP r ν := by
    rw [cfour_commP_mul_left (q ^ 2) r ν, mpcFv_commP_zLayer_left hq2ν r, mul_one]
  have h2 : commP (q ^ 2 * r * μ) ν = commP r ν * (commP (q ^ 2) ν * commP μ ν) := by
    rw [cfour_commP_mul_left (q ^ 2 * r) μ ν, h1,
      mpcFv_vanish' hμ (Subgroup.mul_mem _ (mpcFv_zLayer_le_three hq2ν) hrν), mul_one,
      mpcFv_zcomm hq2ν (commP r ν), mul_assoc]
  -- the pivot letter against the marked `D̄`
  have h3 : commP (q ^ 2 * r) w
      = commP (q ^ 2) w * commP r w * commP (commP (q ^ 2) w) r := by
    rw [cfour_commP_mul_left (q ^ 2) r w,
      mpcFv_cmove (mpcFv_zcomm hq2wr) (commP (q ^ 2) w) (commP r w)]
  have h4 : commP (q ^ 2 * r * μ) w
      = commP (q ^ 2) w * commP r w * commP μ w *
        (commP (commP (q ^ 2) w) r * commP (commP r w) μ) := by
    have hY : commP (q ^ 2) w * commP r w ∈ lambdaImage G 2 5 :=
      Subgroup.mul_mem _ (mpcFv_three_le_two hq2w) hrw
    rw [cfour_commP_mul_left (q ^ 2 * r) μ w, h3,
      mpcFv_commP_two_add_left hY hμ (commP (commP (q ^ 2) w) r),
      mpcFv_commP_zLayer_left hq2wr μ, mul_one,
      mpcFv_commP_two_add_left (mpcFv_three_le_two hq2w) hμ (commP r w),
      mpcFv_vanish' hμ hq2w, one_mul,
      mpcFv_cmove (mpcFv_zcomm hrwμ) (commP (q ^ 2) w * commP r w *
        commP (commP (q ^ 2) w) r) (commP μ w),
      mpcFv_cmove (mpcFv_zcomm hq2wr) (commP (q ^ 2) w * commP r w) (commP μ w), mul_assoc]
  -- the second-order correction sees only the marked bracket
  have h5 : commP (commP (q ^ 2 * r * μ) w) ν = commP (commP r w) ν := by
    have hY : commP (q ^ 2) w * commP r w * commP μ w ∈ lambdaImage G 2 5 :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (mpcFv_three_le_two hq2w) hrw)
        (mpcFv_three_le_two hμw)
    have hY' : commP (q ^ 2) w * commP r w ∈ lambdaImage G 2 5 :=
      Subgroup.mul_mem _ (mpcFv_three_le_two hq2w) hrw
    rw [h4, mpcFv_commP_two_add_left hY hν (commP (commP (q ^ 2) w) r * commP (commP r w) μ),
      mpcFv_commP_zLayer_left (Subgroup.mul_mem _ hq2wr hrwμ) ν, mul_one,
      mpcFv_commP_two_add_left hY' hν (commP μ w), mpcFv_vanish' hν hμw, mul_one,
      mpcFv_commP_two_add_left (mpcFv_three_le_two hq2w) hν (commP r w),
      mpcFv_vanish' hν hq2w, one_mul]
  calc commP (q ^ 2 * r * μ) (w * ν)
      = commP (q ^ 2 * r * μ) ν * commP (q ^ 2 * r * μ) w *
          commP (commP (q ^ 2 * r * μ) w) ν := cfour_commP_mul_right _ _ _
    _ = commP r ν * (commP (q ^ 2) ν * commP μ ν) *
          (commP (q ^ 2) w * commP r w * commP μ w *
            (commP (commP (q ^ 2) w) r * commP (commP r w) μ)) *
        commP (commP r w) ν := by rw [h5, h4, h2]
    _ = commP r ν * (commP (q ^ 2) w * commP r w * commP μ w) *
          (commP (q ^ 2) ν * commP μ ν *
            (commP (commP (q ^ 2) w) r * commP (commP r w) μ) * commP (commP r w) ν) :=
        mpcFv_join3 (mpcFv_zcomm (Subgroup.mul_mem _ hq2ν hμν)) _ _ _ _
    _ = commP r w * (commP (q ^ 2) w * commP r ν * commP μ w) *
          (commP (q ^ 2) ν * commP μ ν * commP (commP (q ^ 2) w) r *
            commP (commP r w) μ * commP (commP r w) ν) := by
        rw [← mul_assoc (commP r ν) (commP (q ^ 2) w * commP r w) (commP μ w),
          ← mul_assoc (commP r ν) (commP (q ^ 2) w) (commP r w),
          mpcFv_swap4 (mpcFv_lycomm (mpcFv_three_le_two hq2w) hrν)
            (mpcFv_lycomm hrw hrν) (mpcFv_lycomm hrw hq2w) (commP μ w)]
        group

end LetterCD

/-! ## §4 Axiom pins

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
#print axioms mpcFv_commP_sq_left
#print axioms mpcFv_sq_letA
#print axioms mpcFv_comm_letAB
#print axioms mpcFv_comm_letCD

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcFv
