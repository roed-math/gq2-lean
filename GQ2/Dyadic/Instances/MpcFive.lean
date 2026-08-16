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

2. **The class-five defect in closed form** (§4-§5).  `mpcFv_mWord_five`, the analogue of
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

/-- Moving one factor one place to the right past another it commutes with. -/
private theorem mpcFv_mv {Q : Type*} [Group Q] {e x : Q} (h : e * x = x * e) (u v : Q) :
    u * e * x * v = u * x * e * v := by rw [mul_assoc u e x, h, ← mul_assoc]

/-- Moving a central factor one place to the left. -/
private theorem mpcFv_cmoveL {Q : Type*} [Group Q] {z : Q} (hz : ∀ x : Q, z * x = x * z)
    (x y : Q) : x * y * z = x * z * y := (mpcFv_cmove hz x y).symm

/-- A bracket of an element with itself is trivial. -/
theorem mpcFv_commP_self {Q : Type*} [Group Q] (x : Q) : commP x x = 1 := by
  simp only [commP]; group

/-- **The left slot of a bracket inverts on `Y`**: the correction is a bracket of an `L`-element
against a `Y`-element. -/
theorem mpcFv_commP_inv_left_two {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (x : levelQuot G 5) : commP y⁻¹ x = (commP y x)⁻¹ := by
  have hyi : y⁻¹ ∈ lambdaImage G 2 5 := Subgroup.inv_mem _ hy
  have h : commP (y⁻¹ * y) x
      = commP y⁻¹ x * commP (commP y⁻¹ x) y * commP y x := cfour_commP_mul_left _ _ _
  rw [inv_mul_cancel, cfour_one_comm,
    mpcFv_vanish' hy (mpcFv_commP_mem_three_left hyi x), mul_one] at h
  exact mul_eq_one_iff_eq_inv.mp h.symm

/-- Three central involutions in the pattern the class-five kill produces multiply to `1`. -/
private theorem mpcFv_kill3 {Q : Type*} [Group Q] {a b c : Q}
    (ha : ∀ x : Q, a * x = x * a) (hb : ∀ x : Q, b * x = x * b)
    (ea : a * a = 1) (eb : b * b = 1) (ec : c * c = 1) : a * b * c * (a * (b * c)) = 1 := by
  calc a * b * c * (a * (b * c)) = a * b * c * a * b * c := by group
    _ = a * b * a * c * b * c := by rw [mpcFv_cmoveL ha (a * b) c]
    _ = a * a * b * c * b * c := by rw [mpcFv_cmoveL ha a b]
    _ = a * a * b * b * c * c := by rw [mpcFv_cmoveL hb (a * a * b) c]
    _ = 1 := by rw [ea, one_mul, eb, one_mul, ec]

/-- **The cancellation at the class-four witness.**  Three `L`-valued pairs cancel - the two
`⁅W, Ā⁆`-brackets, the two `B̄⁸`-factors, and the pair `W²·⁅q,w⁆²` together with `⁅W,B̄⁆·⁅⁅q,w⁆,B̄⁆`
- and the three central survivors are left in order. -/
private theorem mpcFv_witness_kill {Q : Type*} [Group Q] {x y zc dc f gc jc : Q}
    (hz : ∀ u : Q, zc * u = u * zc) (hd : ∀ u : Q, dc * u = u * dc)
    (hg : ∀ u : Q, gc * u = u * gc) (hzz : zc * zc = 1) (hxf : x * f = f * x) :
    x * y * (zc * dc) * (y⁻¹ * f) * (zc * gc) * (x⁻¹ * f⁻¹ * jc) = dc * gc * jc := by
  have hcomm : x * f * x⁻¹ * f⁻¹ = 1 := by rw [hxf]; group
  calc x * y * (zc * dc) * (y⁻¹ * f) * (zc * gc) * (x⁻¹ * f⁻¹ * jc)
      = x * y * zc * dc * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by group
    _ = x * zc * y * dc * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by rw [mpcFv_cmoveL hz x y]
    _ = x * zc * dc * y * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by
        rw [mpcFv_cmoveL hd (x * zc) y]
    _ = x * zc * dc * f * zc * gc * x⁻¹ * f⁻¹ * jc := by group
    _ = x * zc * dc * zc * f * gc * x⁻¹ * f⁻¹ * jc := by rw [mpcFv_cmoveL hz (x * zc * dc) f]
    _ = x * zc * dc * zc * gc * f * x⁻¹ * f⁻¹ * jc := by
        rw [mpcFv_cmoveL hg (x * zc * dc * zc) f]
    _ = x * zc * zc * dc * gc * f * x⁻¹ * f⁻¹ * jc := by rw [mpcFv_cmove hd (x * zc) zc]
    _ = x * dc * gc * f * x⁻¹ * f⁻¹ * jc := by rw [mul_assoc x zc zc, hzz, mul_one]
    _ = dc * x * gc * f * x⁻¹ * f⁻¹ * jc := by rw [← hd x]
    _ = dc * gc * x * f * x⁻¹ * f⁻¹ * jc := by rw [mpcFv_cmoveL hg dc x]
    _ = dc * gc * (x * f * x⁻¹ * f⁻¹) * jc := by group
    _ = dc * gc * jc := by rw [hcomm, mul_one]

/-- **The four-letter shuffle.**  Each of `mWord`'s four factors splits as a marked part times a
correction, and every correction commutes with every marked part to its right, so the four
corrections collect at the end with nothing incurred. -/
private theorem mpcFv_shuffle4 {Q : Type*} [Group Q] {x₁ x₂ x₃ x₄ e₁ e₂ e₃ e₄ : Q}
    (h₁₂ : e₁ * x₂ = x₂ * e₁) (h₁₃ : e₁ * x₃ = x₃ * e₁) (h₁₄ : e₁ * x₄ = x₄ * e₁)
    (h₂₃ : e₂ * x₃ = x₃ * e₂) (h₂₄ : e₂ * x₄ = x₄ * e₂) (h₃₄ : e₃ * x₄ = x₄ * e₃) :
    x₁ * e₁ * (x₂ * e₂) * (x₃ * e₃) * (x₄ * e₄)
      = x₁ * x₂ * x₃ * x₄ * (e₁ * e₂ * e₃ * e₄) := by
  calc x₁ * e₁ * (x₂ * e₂) * (x₃ * e₃) * (x₄ * e₄)
      = x₁ * e₁ * x₂ * e₂ * x₃ * e₃ * x₄ * e₄ := by group
    _ = x₁ * x₂ * e₁ * e₂ * x₃ * e₃ * x₄ * e₄ := by rw [mpcFv_mv h₁₂ x₁ e₂]
    _ = x₁ * x₂ * e₁ * x₃ * e₂ * e₃ * x₄ * e₄ := by rw [mpcFv_mv h₂₃ (x₁ * x₂ * e₁) e₃]
    _ = x₁ * x₂ * x₃ * e₁ * e₂ * e₃ * x₄ * e₄ := by rw [mpcFv_mv h₁₃ (x₁ * x₂) e₂]
    _ = x₁ * x₂ * x₃ * e₁ * e₂ * x₄ * e₃ * e₄ := by
        rw [mpcFv_mv h₃₄ (x₁ * x₂ * x₃ * e₁ * e₂) e₄]
    _ = x₁ * x₂ * x₃ * e₁ * x₄ * e₂ * e₃ * e₄ := by rw [mpcFv_mv h₂₄ (x₁ * x₂ * x₃ * e₁) e₃]
    _ = x₁ * x₂ * x₃ * x₄ * e₁ * e₂ * e₃ * e₄ := by rw [mpcFv_mv h₁₄ (x₁ * x₂ * x₃) e₂]
    _ = x₁ * x₂ * x₃ * x₄ * (e₁ * e₂ * e₃ * e₄) := by group

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

/-! ## §4 The class-five defect of the `M6` ansatz, in closed form

The four factors assemble with nothing incurred, and the reason is the one recorded in §0: every
correction lies in `L = λ₃/λ₅`, `L` is abelian, and `L` commutes with `Y = λ₂/λ₅`.  The three
marked parts a correction has to pass are `⁅p,q⁆ ∈ Y`, `r⁴ ∈ L` and `⁅r,w⁆ ∈ Y`, so each pass is
free.  At class four the same statement is `mpcBld_mWord_four`, where all four corrections are
central and the assembly is free for the cruder reason. -/

section Assembly

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐⭐⭐ **THE CLASS-FIVE DEFECT OF THE `M6` ANSATZ, IN CLOSED FORM.**  In `Q₅`, for `Y`-
corrections `σ, τ, μ, ν` and an `L`-element `z` (the ansatz uses `z = (q⁴)⁻¹`, which at class four
was central and here is not),

    mWord 2 (p·z·σ) (q·τ) (q²·r·μ) (w·ν) = mWord 2 p q r w · (E₁·E₂·E₃·E₄)

with the four corrections

    E₁ = σ²·⁅σ,p⁆ · (z²·⁅z,p⁆)
    E₂ = ⁅p,τ⁆·⁅σ,q⁆ · (⁅σ,τ⁆·⁅z,q⁆·⁅⁅p,q⁆,σ⁆·⁅⁅p,q⁆,τ⁆)
    E₃ = q⁸·(μ⁴·(⁅μ,r⁆²·⁅r,q²⁆²))
    E₄ = ⁅q,w⁆²·⁅⁅q,w⁆,q⁆·⁅r,ν⁆·⁅μ,w⁆ · (⁅q²,ν⁆·⁅μ,ν⁆·⁅⁅q²,w⁆,r⁆·⁅⁅r,w⁆,μ⁆·⁅⁅r,w⁆,ν⁆) .

Setting `z ∈ Z` and dropping every term that `⁅Y,Y⁆ = 1` kills recovers `mpcBld_mWord_four`
exactly, where the whole defect is central and the rung is one `𝔽₂`-linear equation.  **At class
five the defect is only `L`-valued**, so the rung is not linear in the same cheap sense; what
makes it linear again is `mpcLad_defect_orbit`, which is a statement about increments and not
about defects. -/
theorem mpcFv_mWord_five {p q r w σ τ μ ν z : levelQuot G 5}
    (hσ : σ ∈ lambdaImage G 2 5) (hτ : τ ∈ lambdaImage G 2 5)
    (hμ : μ ∈ lambdaImage G 2 5) (hν : ν ∈ lambdaImage G 2 5)
    (hz : z ∈ lambdaImage G 3 5) :
    mWord 2 (p * z * σ) (q * τ) (q ^ 2 * r * μ) (w * ν)
      = mWord 2 p q r w *
        (σ ^ 2 * commP σ p * (z ^ 2 * commP z p) *
          (commP p τ * commP σ q *
            (commP σ τ * commP z q * commP (commP p q) σ * commP (commP p q) τ)) *
          (q ^ 8 * (μ ^ 4 * (commP μ r ^ 2 * commP r (q ^ 2) ^ 2))) *
          (commP q w ^ 2 * commP (commP q w) q * commP r ν * commP μ w *
            (commP (q ^ 2) ν * commP μ ν * commP (commP (q ^ 2) w) r *
              commP (commP r w) μ * commP (commP r w) ν))) := by
  have hpq : commP p q ∈ lambdaImage G 2 5 := mpcFv_commP_mem_two p q
  have hrw : commP r w ∈ lambdaImage G 2 5 := mpcFv_commP_mem_two r w
  have hr4 : r ^ 4 ∈ lambdaImage G 3 5 := cfive_pow_four_mem_lambdaThree r
  have hq2 : q ^ 2 ∈ lambdaImage G 2 5 := mpcLad_five_sq_mem_two q
  have hμsq : (μ ^ 2) ^ 2 = μ ^ 4 := by rw [← pow_mul]
  have hE₁ : σ ^ 2 * commP σ p * (z ^ 2 * commP z p) ∈ lambdaImage G 3 5 :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ (mpcFv_sq_mem_three hσ) (mpcFv_commP_mem_three_left hσ p))
      (Subgroup.mul_mem _ (mpcFv_zLayer_le_three (mpcFv_sq_mem_zLayer hz))
        (mpcFv_zLayer_le_three (mpcFv_commP_mem_zLayer_left hz p)))
  have hE₂ : commP p τ * commP σ q *
      (commP σ τ * commP z q * commP (commP p q) σ * commP (commP p q) τ)
        ∈ lambdaImage G 3 5 :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ (mpcFv_commP_mem_three_right p hτ)
        (mpcFv_commP_mem_three_left hσ q))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (mpcFv_zLayer_le_three (mpcFv_commP_mem_zLayer_two hσ hτ))
        (mpcFv_zLayer_le_three (mpcFv_commP_mem_zLayer_left hz q)))
        (mpcFv_zLayer_le_three (mpcFv_commP_mem_zLayer_two hpq hσ)))
        (mpcFv_zLayer_le_three (mpcFv_commP_mem_zLayer_two hpq hτ)))
  have hE₃ : q ^ 8 * (μ ^ 4 * (commP μ r ^ 2 * commP r (q ^ 2) ^ 2)) ∈ lambdaImage G 3 5 :=
    Subgroup.mul_mem _ (mpcFv_zLayer_le_three (cfive_pow_eight_mem_zLayer q))
      (Subgroup.mul_mem _
        (mpcFv_zLayer_le_three (hμsq ▸ mpcFv_sq_mem_zLayer (mpcFv_sq_mem_three hμ)))
        (Subgroup.mul_mem _
          (mpcFv_zLayer_le_three (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_left hμ r)))
          (mpcFv_zLayer_le_three (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right r hq2)))))
  have hA : (p * z * σ) ^ 2 = p ^ 2 * (σ ^ 2 * commP σ p * (z ^ 2 * commP z p)) := by
    rw [mpcFv_sq_letA hσ hz, mul_assoc]
  have hB : commP (p * z * σ) (q * τ)
      = commP p q * (commP p τ * commP σ q *
          (commP σ τ * commP z q * commP (commP p q) σ * commP (commP p q) τ)) := by
    rw [mpcFv_comm_letAB hσ hτ hz, mul_assoc]
  have hD : commP (q ^ 2 * r * μ) (w * ν)
      = commP r w * (commP q w ^ 2 * commP (commP q w) q * commP r ν * commP μ w *
          (commP (q ^ 2) ν * commP μ ν * commP (commP (q ^ 2) w) r *
            commP (commP r w) μ * commP (commP r w) ν)) := by
    rw [mpcFv_comm_letCD hμ hν, mul_assoc]
  simp only [mWord, show (2 : ℕ) ^ 2 = 4 from rfl]
  rw [hA, hB, mpcLad_pow_letC_five q r hμ, hD]
  exact mpcFv_shuffle4 (mpcFv_lycomm hpq hE₁) (mpcFv_lycomm (mpcFv_three_le_two hr4) hE₁)
    (mpcFv_lycomm hrw hE₁) (mpcFv_lycomm (mpcFv_three_le_two hr4) hE₂)
    (mpcFv_lycomm hrw hE₂) (mpcFv_lycomm hrw hE₃)

/-- The ansatz's head shift `z = (q⁴)⁻¹` squares to `q⁸`, because `q⁸` is a central
involution. -/
theorem mpcFv_z_sq (q : levelQuot G 5) : ((q ^ 4)⁻¹) ^ 2 = q ^ 8 := by
  have e : (q ^ 4) ^ 2 = q ^ 8 := by rw [← pow_mul]
  rw [inv_pow, e]
  exact zLayer_inv_self (cfive_pow_eight_mem_zLayer q)

/-- The head shift is invisible to inversion inside a bracket: `⁅z, x⁆ = ⁅q⁴, x⁆`, both being
central involutions. -/
theorem mpcFv_z_commP (q x : levelQuot G 5) : commP (q ^ 4)⁻¹ x = commP (q ^ 4) x := by
  have h4 : q ^ 4 ∈ lambdaImage G 3 5 := cfive_pow_four_mem_lambdaThree q
  rw [mpcFv_commP_inv_left h4 x]
  exact zLayer_inv_self (mpcFv_commP_mem_zLayer_left h4 x)

/-- A power commutes with its own base, so the head shift is invisible against `B̄`. -/
theorem mpcFv_pow_four_commP_self (q : levelQuot G 5) : commP (q ^ 4) q = 1 :=
  bridge_comm_of_commute ((Commute.refl q).pow_left 4).eq

end Assembly

/-! ## §5 The defect on `D_M 2 0`, and the class-four witness

§4 transported through `levelMk` and with the marked relator killed by `mpcOrb_relation`, exactly
as `mpcBld_defect_four` does one class down.  The head shift `z = (B̄⁴)⁻¹` is simplified on the
way: `z² = B̄⁸`, `⁅z, Ā⁆ = ⁅B̄⁴, Ā⁆`, and `⁅z, B̄⁆ = 1` because a power commutes with its base.

Evaluated at the wave-84 witness `s = t = ⁅D̄, B̄⁆`, `m = n = 1`, every `λ₃`-valued term cancels -
as it must, the witness being a class-four solution - and three central involutions survive. -/

section Downstairs

/-- ⭐⭐ **THE CLASS-FIVE DEFECT ON `D_M 2 0`.**  The analogue of `mpcBld_defect_four`: the `M6`
ansatz's core word, modulo `λ₅`, is exactly this twenty-two-term product.  Dropping every factor
that dies at class four leaves `mpcBld_defect_four`'s eight-term product. -/
theorem mpcFv_defect_five (s t m n : (DM 2 0 : Type))
    (hs : s ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hm : m ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    levelMk (DM 2 0 : Type) 5
        (mWord 2 (mpcWordLetA s) (mpcWordLetB t) (mpcWordLetC m) (mpcWordLetD n))
      = levelMk (DM 2 0 : Type) 5
        (s ^ 2 * commP s (dmA 2 0) * (dmB 2 0 ^ 8 * commP (dmB 2 0 ^ 4) (dmA 2 0)) *
          (commP (dmA 2 0) t * commP s (dmB 2 0) *
            (commP s t * commP (commP (dmA 2 0) (dmB 2 0)) s *
              commP (commP (dmA 2 0) (dmB 2 0)) t)) *
          (dmB 2 0 ^ 8 *
            (m ^ 4 * (commP m (dmC 2 0) ^ 2 * commP (dmC 2 0) (dmB 2 0 ^ 2) ^ 2))) *
          (commP (dmB 2 0) (dmD 2 0) ^ 2 * commP (commP (dmB 2 0) (dmD 2 0)) (dmB 2 0) *
            commP (dmC 2 0) n * commP m (dmD 2 0) *
            (commP (dmB 2 0 ^ 2) n * commP m n *
              commP (commP (dmB 2 0 ^ 2) (dmD 2 0)) (dmC 2 0) *
              commP (commP (dmC 2 0) (dmD 2 0)) m *
              commP (commP (dmC 2 0) (dmD 2 0)) n))) := by
  have hrel : mWord 2 (levelMk (DM 2 0 : Type) 5 (dmA 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      (levelMk (DM 2 0 : Type) 5 (dmC 2 0)) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) = 1 := by
    rw [← map_mWord, mpcOrb_relation, map_one]
  have hz : (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4)⁻¹ ∈ lambdaImage (DM 2 0 : Type) 3 5 :=
    Subgroup.inv_mem _ (cfive_pow_four_mem_lambdaThree _)
  have hA : levelMk (DM 2 0 : Type) 5 (mpcWordLetA s)
      = levelMk (DM 2 0 : Type) 5 (dmA 2 0) * (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4)⁻¹ *
        levelMk (DM 2 0 : Type) 5 s := by
    rw [mpcWordLetA, map_mul, map_mul, map_inv, map_pow]
  have hB : levelMk (DM 2 0 : Type) 5 (mpcWordLetB t)
      = levelMk (DM 2 0 : Type) 5 (dmB 2 0) * levelMk (DM 2 0 : Type) 5 t := by
    rw [mpcWordLetB, map_mul]
  have hC : levelMk (DM 2 0 : Type) 5 (mpcWordLetC m)
      = levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2 * levelMk (DM 2 0 : Type) 5 (dmC 2 0) *
        levelMk (DM 2 0 : Type) 5 m := by
    rw [mpcWordLetC, map_mul, map_mul, map_pow]
  have hD : levelMk (DM 2 0 : Type) 5 (mpcWordLetD n)
      = levelMk (DM 2 0 : Type) 5 (dmD 2 0) * levelMk (DM 2 0 : Type) 5 n := by
    rw [mpcWordLetD, map_mul]
  rw [map_mWord, hA, hB, hC, hD,
    mpcFv_mWord_five (G := (DM 2 0 : Type)) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
      hz, hrel, one_mul, mpcFv_z_sq]
  simp only [mpcFv_z_commP, mpcFv_pow_four_commP_self, mul_one]
  simp only [map_mul, map_pow, commP, map_inv]

/-- ⭐⭐⭐ **THE CLASS-FIVE DEFECT OF THE CLASS-FOUR WITNESS.**  At `s = t = ⁅D̄, B̄⁆`, `m = n = 1`
the twenty-two terms of `mpcFv_defect_five` collapse to three central involutions:

    ⁅B̄⁴, Ā⁆ · ⁅C̄₀, B̄²⁆² · ⁅⁅B̄², D̄⁆, C̄₀⁆ .

Every `λ₃`-valued term cancels, as it must: the witness is a class-four solution, so its defect
already lies in `λ₄/λ₅`.  The three cancelling pairs are the two `Ā`-brackets against `W`, the
`W`-square against `⁅B̄,D̄⁆²`, and `⁅W, B̄⁆` against `⁅⁅B̄,D̄⁆, B̄⁆`.

Which survivors wave 86 could see.  `mpcLad_pow_letC_five` predicted two terms present already
at `m = 1`, namely `B̄⁸` and `⁅C̄₀, B̄²⁆²`.  Only the second survives: `B̄⁸` cancels against the
head letter's `z² = ((B̄⁴)⁻¹)²`, which is the same central involution.  The other two survivors
come from factors wave 86 did not compute, the head's `⁅z, Ā⁆ = ⁅B̄⁴, Ā⁆` and the `C̄₀`/`D̄`
bracket's `⁅⁅B̄², D̄⁆, C̄₀⁆`. -/
theorem mpcFv_witness_defect :
    levelMk (DM 2 0 : Type) 5
        (mWord 2 (mpcWordLetA mpcBldW) (mpcWordLetB mpcBldW) (mpcWordLetC 1) (mpcWordLetD 1))
      = levelMk (DM 2 0 : Type) 5
          (commP (dmB 2 0 ^ 4) (dmA 2 0) * commP (dmC 2 0) (dmB 2 0 ^ 2) ^ 2 *
            commP (commP (dmB 2 0 ^ 2) (dmD 2 0)) (dmC 2 0)) := by
  rw [mpcFv_defect_five mpcBldW mpcBldW 1 1 mpcBld_w_mem mpcBld_w_mem (one_mem _) (one_mem _)]
  simp only [mpcBldW, map_mul, map_pow, mpcBld_map_commP, cfour_comm_one,
    cfour_one_comm, mpcFv_commP_self, one_pow, one_mul, mul_one]
  have hq2 : levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2 ∈ lambdaImage (DM 2 0 : Type) 2 5 :=
    mpcLad_five_sq_mem_two _
  have hq4 : levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4 ∈ lambdaImage (DM 2 0 : Type) 3 5 :=
    cfive_pow_four_mem_lambdaThree _
  have hW : commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      ∈ lambdaImage (DM 2 0 : Type) 2 5 := mpcFv_commP_mem_two _ _
  have hpq : commP (levelMk (DM 2 0 : Type) 5 (dmA 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      ∈ lambdaImage (DM 2 0 : Type) 2 5 := mpcFv_commP_mem_two _ _
  have hWsq : commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      ^ 2 ∈ lambdaImage (DM 2 0 : Type) 3 5 := mpcFv_sq_mem_three hW
  have hWq : commP (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0))
      (levelMk (DM 2 0 : Type) 5 (dmB 2 0))) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      ∈ lambdaImage (DM 2 0 : Type) 3 5 := mpcFv_commP_mem_three_left hW _
  -- the two `⁅⁅Ā,B̄⁆, W⁆` factors are one central involution squared
  have hK : commP (commP (levelMk (DM 2 0 : Type) 5 (dmA 2 0))
        (levelMk (DM 2 0 : Type) 5 (dmB 2 0)))
        (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))) *
      commP (commP (levelMk (DM 2 0 : Type) 5 (dmA 2 0))
        (levelMk (DM 2 0 : Type) 5 (dmB 2 0)))
        (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0)))
      = 1 := by
    rw [← pow_two]
    exact zLayer_sq _ (mpcFv_commP_mem_zLayer_two hpq hW)
  -- the two `Ā`-brackets are inverse to each other
  have hY : commP (levelMk (DM 2 0 : Type) 5 (dmA 2 0))
      (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0)))
      = (commP (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0))
          (levelMk (DM 2 0 : Type) 5 (dmB 2 0))) (levelMk (DM 2 0 : Type) 5 (dmA 2 0)))⁻¹ :=
    mpcFv_swap _ _
  -- the `⁅B̄, D̄⁆`-terms are inverse to the `W`-terms
  have hH : commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0)) (levelMk (DM 2 0 : Type) 5 (dmD 2 0))
      ^ 2 = (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0))
        (levelMk (DM 2 0 : Type) 5 (dmB 2 0)) ^ 2)⁻¹ := by
    rw [mpcFv_swap (levelMk (DM 2 0 : Type) 5 (dmB 2 0)) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)),
      inv_pow]
  have hI : commP (commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
        (levelMk (DM 2 0 : Type) 5 (dmD 2 0))) (levelMk (DM 2 0 : Type) 5 (dmB 2 0))
      = (commP (commP (levelMk (DM 2 0 : Type) 5 (dmD 2 0))
          (levelMk (DM 2 0 : Type) 5 (dmB 2 0))) (levelMk (DM 2 0 : Type) 5 (dmB 2 0)))⁻¹ := by
    rw [mpcFv_swap (levelMk (DM 2 0 : Type) 5 (dmB 2 0)) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)),
      mpcFv_commP_inv_left_two hW]
  rw [hK, mul_one, hY, hH, hI]
  exact mpcFv_witness_kill (mpcFv_zcomm (cfive_pow_eight_mem_zLayer _))
    (mpcFv_zcomm (mpcFv_commP_mem_zLayer_left hq4 _))
    (mpcFv_zcomm (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right _ hq2)))
    (by rw [← pow_two]; exact zLayer_sq _ (cfive_pow_eight_mem_zLayer _))
    (mpcFv_lycomm (mpcFv_three_le_two hWq) hWsq)

end Downstairs

/-! ## §6 The class-five rung, climbed

The defect of §5 is hit by an explicit `λ₃`-move, so the class-five rung of the ladder is
climbed and the residue of `MpcPivShift 2` starts at class six.

The move is read straight off the three survivors.  `mpcBldIncr`'s `B̄`-slot buys `⁅Ā, u⁆` and
its `D̄`-slot buys `⁅C̄₀, v⁆`, so it suffices that

* `⁅B̄⁴, Ā⁆ = ⁅Ā, B̄⁴⁆`, giving `ut = B̄⁴`;
* `⁅C̄₀, B̄²⁆² = ⁅C̄₀, B̄⁴⁆` and `⁅⁅B̄², D̄⁆, C̄₀⁆ = ⁅C̄₀, ⁅B̄², D̄⁆⁆`, giving
  `un = B̄⁴·⁅B̄², D̄⁆`;

with the head and pivot slots left alone.  Both `ut` and `un` are legal corrections: they lie in
`λ₃`, and they are χ-trivial because `χ_M(B̄) = -1` has order two, so `χ_M(B̄⁴) = 1`, and every
bracket is χ-trivial. -/

section Decision

/-- The class-five `B̄`-slot move: `B̄⁴`, which is exactly what `⁅Ā, -⁆` needs to hit `⁅B̄⁴, Ā⁆`. -/
def mpcFvUt : (DM 2 0 : Type) := dmB 2 0 ^ 4

/-- The class-five `D̄`-slot move: `B̄⁴·⁅B̄², D̄⁆`, whose `⁅C̄₀, -⁆`-bracket is the product of the
two remaining survivors. -/
def mpcFvUn : (DM 2 0 : Type) := dmB 2 0 ^ 4 * commP (dmB 2 0 ^ 2) (dmD 2 0)

theorem mpcFv_b2_mem_two : dmB 2 0 ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
  sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top _)

theorem mpcFv_ut_mem_three : mpcFvUt ∈ twoCentralSeries (DM 2 0 : Type) 3 := by
  have h : mpcFvUt = (dmB 2 0 ^ 2) ^ 2 := by rw [mpcFvUt, ← pow_mul]
  rw [h]
  exact sq_mem_twoCentralSeries_succ _ mpcFv_b2_mem_two

theorem mpcFv_chi_b4 : chiM 2 0 (dmB 2 0 ^ 4) = 1 := by
  rw [map_pow, chiM_dmB, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]

theorem mpcFv_chi_ut : chiM 2 0 mpcFvUt = 1 := mpcFv_chi_b4

theorem mpcFv_chi_un : chiM 2 0 mpcFvUn = 1 := by
  rw [mpcFvUn, map_mul, mpcFv_chi_b4, mpcBld_chi_commP, one_mul]

theorem mpcFv_ut_mem_corr : mpcFvUt ∈ mpcWordCorr :=
  ⟨twoCentralSeries_antitone (G := (DM 2 0 : Type)) (by omega : (2 : ℕ) ≤ 3)
    mpcFv_ut_mem_three, mpcFv_chi_ut⟩

theorem mpcFv_un_mem_three : mpcFvUn ∈ twoCentralSeries (DM 2 0 : Type) 3 :=
  Subgroup.mul_mem _ mpcFv_ut_mem_three (cfour_commP_mem_three mpcFv_b2_mem_two _)

theorem mpcFv_un_mem_corr : mpcFvUn ∈ mpcWordCorr :=
  ⟨twoCentralSeries_antitone (G := (DM 2 0 : Type)) (by omega : (2 : ℕ) ≤ 3)
    mpcFv_un_mem_three, mpcFv_chi_un⟩

/-- The class-five move of the four corrections: identity in the head and pivot slots, `B̄⁴` in
the `B̄`-slot and `B̄⁴·⁅B̄², D̄⁆` in the `D̄`-slot. -/
theorem mpcFv_move : MpcLadMove 3 1 mpcFvUt 1 mpcFvUn :=
  ⟨⟨one_mem _, one_mem _⟩, ⟨mpcFv_ut_mem_corr, mpcFv_ut_mem_three⟩, ⟨one_mem _, one_mem _⟩,
    ⟨mpcFv_un_mem_corr, mpcFv_un_mem_three⟩⟩

/-- `⁅C̄₀, B̄⁴⁆ = ⁅C̄₀, B̄²⁆²` in `Q₅`: the second-order term of the expansion is a bracket of an
`L`-element against a `Y`-element. -/
theorem mpcFv_commP_pow_four_right (r q : levelQuot (DM 2 0 : Type) 5) :
    commP r (q ^ 4) = commP r (q ^ 2) ^ 2 := by
  have hq2 : q ^ 2 ∈ lambdaImage (DM 2 0 : Type) 2 5 := mpcLad_five_sq_mem_two q
  have e : q ^ 4 = q ^ 2 * q ^ 2 := by rw [← pow_add]
  rw [e, cfour_commP_mul_right, mpcFv_vanish' hq2 (mpcFv_commP_mem_three_right r hq2), mul_one,
    ← pow_two]

/-- ⭐⭐ **THE MOVE KILLS THE DEFECT.**  All six factors are central involutions and they pair
off: `⁅Ā, B̄⁴⁆` against `⁅B̄⁴, Ā⁆`, and the two halves of `⁅C̄₀, B̄⁴·⁅B̄²,D̄⁆⁆` against
`⁅C̄₀, B̄²⁆²` and `⁅⁅B̄², D̄⁆, C̄₀⁆`. -/
theorem mpcFv_supply_kill :
    mpcLadDefect mpcLadW4 * mpcBldIncr mpcLadW4.2.1 mpcLadW4.2.2.2 1 mpcFvUt 1 mpcFvUn
      ∈ twoCentralSeries (DM 2 0 : Type) 5 := by
  rw [mpcWord_mem_iff_levelMk]
  have hdef : mpcLadDefect mpcLadW4
      = mWord 2 (mpcWordLetA mpcBldW) (mpcWordLetB mpcBldW) (mpcWordLetC 1) (mpcWordLetD 1) :=
    rfl
  rw [hdef, map_mul, mpcFv_witness_defect]
  simp only [mpcBldIncr, mpcFvUt, mpcFvUn, map_mul, map_pow, mpcBld_map_commP,
    cfour_one_comm, one_pow, one_mul, mul_one]
  have hq2 : levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2 ∈ lambdaImage (DM 2 0 : Type) 2 5 :=
    mpcLad_five_sq_mem_two _
  have hq4 : levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4 ∈ lambdaImage (DM 2 0 : Type) 3 5 :=
    cfive_pow_four_mem_lambdaThree _
  have hbr : commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2)
      (levelMk (DM 2 0 : Type) 5 (dmD 2 0)) ∈ lambdaImage (DM 2 0 : Type) 3 5 :=
    mpcFv_commP_mem_three_left hq2 _
  -- the `Ā`-slot bracket is the first survivor
  have hA : commP (levelMk (DM 2 0 : Type) 5 (dmA 2 0)) (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4)
      = commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4)
        (levelMk (DM 2 0 : Type) 5 (dmA 2 0)) := by
    rw [mpcFv_swap (levelMk (DM 2 0 : Type) 5 (dmA 2 0))
      (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4)]
    exact zLayer_inv_self (mpcFv_commP_mem_zLayer_left hq4 _)
  have hbrswap : commP (levelMk (DM 2 0 : Type) 5 (dmC 2 0))
        (commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)))
      = commP (commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2)
          (levelMk (DM 2 0 : Type) 5 (dmD 2 0))) (levelMk (DM 2 0 : Type) 5 (dmC 2 0)) := by
    rw [mpcFv_swap (levelMk (DM 2 0 : Type) 5 (dmC 2 0))
      (commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)))]
    exact zLayer_inv_self (mpcFv_commP_mem_zLayer_left hbr _)
  -- the `D̄`-slot bracket is the product of the other two
  have hC : commP (levelMk (DM 2 0 : Type) 5 (dmC 2 0))
        (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 4 *
          commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2) (levelMk (DM 2 0 : Type) 5 (dmD 2 0)))
      = commP (levelMk (DM 2 0 : Type) 5 (dmC 2 0))
          (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2) ^ 2 *
        commP (commP (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2)
          (levelMk (DM 2 0 : Type) 5 (dmD 2 0))) (levelMk (DM 2 0 : Type) 5 (dmC 2 0)) := by
    rw [mpcFv_commP_right_add _ hq4 hbr, mpcFv_commP_pow_four_right, hbrswap]
  rw [hA, hC]
  exact mpcFv_kill3 (mpcFv_zcomm (mpcFv_commP_mem_zLayer_left hq4 _))
    (mpcFv_zcomm (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right _ hq2)))
    (by rw [← pow_two]; exact zLayer_sq _ (mpcFv_commP_mem_zLayer_left hq4 _))
    (by rw [← pow_two]
        exact zLayer_sq _ (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right _ hq2)))
    (by rw [← pow_two]; exact zLayer_sq _ (mpcFv_commP_mem_zLayer_left hbr _))

/-- ⭐⭐⭐ **THE CLASS-FIVE RUNG IS CLIMBED.**  The wave-84 class-four witness has one-step supply
at class three, witnessed by `mpcFv_move`.  Combined with `mpcLad_nonempty_five_iff` this decides
wave 86's open question in the affirmative. -/
theorem mpcFv_supply_witness : MpcLadSupply 3 mpcLadW4 :=
  ⟨1, mpcFvUt, 1, mpcFvUn, mpcFv_move, mpcFv_supply_kill⟩

/-- The class-five correction quadruple: the wave-84 witness moved by `mpcFv_move`. -/
def mpcFvW5 : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) :=
  (mpcBldW * 1, mpcBldW * mpcFvUt, 1 * 1, 1 * mpcFvUn)

/-- ⭐⭐⭐ **THE CLASS-FIVE SOLUTION SET OF THE `M6` ANSATZ IS NONEMPTY**, with the explicit
witness `mpcFvW5`.  Wave 86's `mpcLad_nonempty_five_iff` asked whether some class-four solution's
defect lies in the reachable `𝔽₂`-subspace `mpcLadReach 3`; it does, at the wave-84 witness's own
orbit, so no orbit-space input was needed.

[Scope, following W86-HOUSE.  This is a statement about the **ansatz**: `mpcWordSet 5` is the
class-five solution set of the fixed shape `(Ā·B̄⁻⁴·s, B̄·t, B̄²·C̄₀·m, D̄·n)`.  It says nothing
about `MpcPivShift 2` on its own; the ladder's only shift-producer is
`mpcLad_shift_of_exists_supply`, which needs supply at **every** class from three up.] -/
theorem mpcFv_nonempty_five : (mpcWordSet 5).Nonempty :=
  mpcLad_nonempty_five_iff.mpr ⟨mpcLadW4, mpcLad_w4_mem, mpcFv_supply_witness⟩

/-- The class-five witness, explicitly: `s = ⁅D̄,B̄⁆`, `t = ⁅D̄,B̄⁆·B̄⁴`, `m = 1`,
`n = B̄⁴·⁅B̄², D̄⁆`. -/
theorem mpcFv_w5_mem : mpcFvW5 ∈ mpcWordSet 5 :=
  mpcBld_step (j := 3) mpcLad_w4_mem 1 mpcFvUt 1 mpcFvUn mpcFv_move.1.1 mpcFv_move.1.2
    mpcFv_move.2.1.1 mpcFv_move.2.1.2 mpcFv_move.2.2.1.1 mpcFv_move.2.2.1.2
    mpcFv_move.2.2.2.1 mpcFv_move.2.2.2.2 mpcFv_supply_kill

end Decision

/-! ## §7 Axiom pins

One line per public declaration, in declaration order, measured against the mirror.

**The honest split.**  Forty-eight of the forty-nine public declarations are on the standard
three (`propext`, `Classical.choice`, `Quot.sound`).  The forty-ninth, `mpcFv_commP_self`, is on
`propext` alone, which is a strict subset: it is a `group`-closed identity in an abstract group
and touches no quotient.  **This lane introduces no axiom.** -/

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
#print axioms mpcFv_commP_self
#print axioms mpcFv_commP_inv_left_two
#print axioms mpcFv_sq_letA
#print axioms mpcFv_comm_letAB
#print axioms mpcFv_comm_letCD
#print axioms mpcFv_mWord_five
#print axioms mpcFv_z_sq
#print axioms mpcFv_z_commP
#print axioms mpcFv_pow_four_commP_self
#print axioms mpcFv_defect_five
#print axioms mpcFv_witness_defect
#print axioms mpcFvUt
#print axioms mpcFvUn
#print axioms mpcFv_b2_mem_two
#print axioms mpcFv_ut_mem_three
#print axioms mpcFv_chi_b4
#print axioms mpcFv_chi_ut
#print axioms mpcFv_chi_un
#print axioms mpcFv_ut_mem_corr
#print axioms mpcFv_un_mem_three
#print axioms mpcFv_un_mem_corr
#print axioms mpcFv_move
#print axioms mpcFv_commP_pow_four_right
#print axioms mpcFv_supply_kill
#print axioms mpcFv_supply_witness
#print axioms mpcFvW5
#print axioms mpcFv_nonempty_five
#print axioms mpcFv_w5_mem

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcFv
