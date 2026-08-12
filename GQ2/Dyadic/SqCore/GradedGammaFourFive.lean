/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFive
import GQ2.Dyadic.SqCore.GradedClassFourIdentity

/-!
# W71-FIVE: the graded layer `γ₄/γ₅`, on the tower

Wave 70 built `γ₃/γ₄` on the tower (`SqCore/GradedGammaThreeFour.lean`) and recorded two of its
fourteen declarations as **layer-agnostic standing tooling**: `gThreeFour_hallWitt`, an identity in
an arbitrary group, and `gThreeFour_jacobi_of`, the passage from Hall-Witt to Jacobi over an
arbitrary group taking its two reductions as hypotheses.  This file is the next layer up, and it
is the first test of that record.

Throughout `Q₅ = levelQuot G 5`, `Y = lambdaImage G 2 5`, `T = lambdaImage G 3 5` and
`Z = zLayer G 4 = lambdaImage G 4 5` is the top layer, central in `Q₅` and of exponent two.  The
class-five map (`SqCore/GradedClassFive.lean`) supplies the calculus: a bracket with a `T`-slot
lands in `Z` (`cfive_commP_mem_zLayer_left` at `k = 3`), a bracket with a `Y`-slot lands in `T`
(`cfive_commP_lambdaTwo_mem_lambdaThree`), and `⁅γ_k, γ₂⁆ ≤ γ_{k+2}` at every `k`.

## §1 The vanishing that runs the layer

⭐ `gFourFive_commP_vanish`: in `Q₅`, `commP z y = 1` for `z ∈ T` and `y ∈ Y`, and symmetrically
`gFourFive_commP_vanish'`.  This is `cfive_commutator_lambdaTwo` at `k = 3` read downstairs, and
it is what kills the correction terms of the additivity laws.  It is **not** what kills every
correction term of §4: `gFourFive_drop_right`, `gFourFive_sq_dress` and
`gFourFive_sq_zLayer_dress` run on the **centrality** of `Z` instead
(`cfive_commP_zLayer_left`, `gFourFive_commP_zLayer_right`) and never cite the vanishing at all.
The additivity laws `gFourFive_ad_left` / `gFourFive_ad_right` and the two inverse laws are wave
70's, with the `T`-element in the near slot for `ad_left` and in the **far** slot for `ad_right`
(the convention, fixed at `GradedGammaThreeFour.lean` §1, is near = left slot, far = right slot).

## §2 Jacobi, and what the layer-agnostic tooling actually covers

**The Hall-Witt half transferred; the passage half did not, and it is the quantifier that
fails.**  `gThreeFour_jacobi_of` asks for its two reductions as **unrestricted** universals over
the ambient group.  At `γ₃/γ₄` that is right, because a triple bracket is already in the top
layer there.  At `γ₄/γ₅` a triple bracket lies in `T`, one layer short of `Z`
(`cfive_commP_lambdaTwo_mem_lambdaThree`), so its `hcentral` is not available: ⭐
`gFourFive_hcentral_iff` proves that `hcentral` read in `Q₅` is **equivalent** to the vanishing
of every **left-normed** fourfold bracket in `Q₅`.  Nothing here refutes that vanishing; what is
committed is that the class-five calculus does not supply it.

The repair keeps the tooling and weakens the hypotheses to the six words the Hall-Witt reduction
actually rewrites:

⭐⭐ `gFourFive_jacobi_of`: over an **arbitrary** group, six pointwise equations give Jacobi at
`p, q, r`.  It subsumes wave 70's version, and `gFourFive_jacobi_of_forall` re-derives that
version from it as the check.

⭐⭐ `gFourFive_jacobi`: in `Q₅`, for `p ∈ Y` and arbitrary `q, r`,

```text
  commP (commP p q) r * commP (commP q r) p * commP (commP r p) q = 1 .
```

The side condition `p ∈ Y` is the weight bookkeeping: all three rotations then lie in `Z`, so
this is the Jacobi identity of the layer `γ₄/γ₅` at weights `2 + 1 + 1`.  Since a bracket of two
`Q₅`-elements lies in `Y`, the fourfold form `gFourFive_jacobi_iter` is an instance, which is the
form a spanning argument for `L₄(V)` consumes.

## §3 Generation

⭐⭐ `gFourFive_zLayer_le_gen`: for `1 ≤ k`, a **closed** subgroup of `Q_{k+2}` containing `y ^ 2`
and `commP y q` for every `y ∈ lambdaImage G k (k + 2)` and every `q` contains `zLayer G (k + 1)`.
Wave 70's `gThreeFour_zLayer_le` is the case `k = 2`; the class-five instance is `k = 3`
(`gFourFive_zLayer_le`), where the side condition is on `T` rather than on `Y`, as the class-five
map predicts.

## §4 The knob inventory at class five

The class-four knobs are computed from `cfour_sqRelWord`, which is class-four-only, so §4 redoes
them from `relBase_sqWord_free` (`gFourFive_sqRelWord`, an identity in any group).  With the
correction moved from `γ₂` to `γ₃` the five slots buy exactly the class-four expressions:

| slot | knob | name |
| --- | --- | --- |
| `σ` | `commP c (m 1)` | `cfiveKnob_dress_zero` |
| `x₀` | `commP (m 0) c` | `cfiveKnob_dress_one` |
| `x₁` | `c² · commP c (m 2)` | `cfiveKnob_dress_two` |
| `u_{j'}` | `commP c (m (sqHandleIdxV j'))` | `cfiveKnob_dress_handleU` |
| `v_{j'}` | `commP (m (sqHandleIdxU j')) c` | `cfiveKnob_dress_handleV` |

Two entries are not the class-four proof one class up.  The `x₀`-slot's fourth power is blind for
a new reason (`gFourFive_pow_four_dress`): `cfour_pow_four_mul` needs `Y` abelian, whereas at
class five `(p·c)² = p²·(c²·commP c p)` with the correction central of exponent two, and the
outer square kills it.  And the `x₁`-slot's `conjP` factor, which at class four had already been
collapsed away, contributes `commP (m 2) c · commP c (conjP (m 2) (m 0))` here; the second term
reduces to `commP c (m 2)` by the §1 vanishing and the two then cancel in an exponent-two layer,
so the `x₁` knob is unchanged (`gFourFive_dress_two_conj_factor` records the cancelling factor).

## §5 The class-five obligation

⭐⭐ `cfiveKnob_supply_of_reach` states it in wave 70's shape: `SqClassClearingSupply h 5` follows
as soon as, at every selected marking, some frame which is exactly row-trivial and mod-2
independent admits a `γ₃`-valued, exactly row-trivial correction killing the relator in `Q₅`.
No class-four witness is presupposed, since class four is open.  `cfiveKnob_dress_core` composes
the three core knobs, and `cfiveKnob_kills` is the identity form: the amount to be killed is the
relator value of the base frame, and it is reached by the knob product.

## Scope

No instance of `SqClassClearingSupply` is discharged, at class four or at class five, and nothing
is refuted.  In particular `gFourFive_hcentral_iff` is an equivalence, not a refutation: no
witness for the failure of the left-normed fourfold-bracket vanishing in `Q₅` is committed
anywhere, and none is claimed here.

Lane W71-FIVE.  New file; no edits to existing files.  Prefixes `gFourFive` / `cfiveKnob`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The vanishing that runs the layer, and the additivity laws -/

section Vanishing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A bracket of two `Q₅`-elements lies in `Y`.  The class-four statement is
`cfour_commP_mem_lambdaTwo`. -/
theorem gFourFive_commP_mem_lambdaTwo (p q : levelQuot G 5) : commP p q ∈ lambdaImage G 2 5 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 5 p
  obtain ⟨b, rfl⟩ := levelMk_surjective G 5 q
  exact ⟨commP a b, cfour_commP_mem_two a b, by simp only [commP, map_mul, map_inv]⟩

/-- `T ≤ Y`, by antitonicity of the tower. -/
theorem gFourFive_lambdaThree_le : lambdaImage G 3 5 ≤ lambdaImage G 2 5 := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, twoCentralSeries_antitone (G := G) (by norm_num) hv, rfl⟩

/-- `Z ≤ T`, by antitonicity of the tower.  The class-four statement is
`cfour_zLayer_le_lambdaTwo`. -/
theorem gFourFive_zLayer_le_lambdaThree : zLayer G 4 ≤ lambdaImage G 3 5 := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, twoCentralSeries_antitone (G := G) (by norm_num) hv, rfl⟩

/-- A square of a `T`-element lies in `Z`.  The class-four statement is `cfour_sq_mem_zLayer`. -/
theorem gFourFive_sq_mem_zLayer {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5) :
    y ^ 2 ∈ zLayer G 4 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ (G := G) hv, by rw [map_pow]⟩

/-- ⭐ **`⁅T, Y⁆` is trivial in `Q₅`**: a bracket of a `γ₃`-image against a `γ₂`-image dies,
because upstairs it lands in `γ₅`.  This is `cfive_commutator_lambdaTwo` at `k = 3`, read
downstairs, and it is the fact the additivity laws below are killed by.  Not every correction
term of §4: the square and drop lemmas run on the centrality of `Z` instead. -/
theorem gFourFive_commP_vanish {z y : levelQuot G 5} (hz : z ∈ lambdaImage G 3 5)
    (hy : y ∈ lambdaImage G 2 5) : commP z y = 1 := by
  obtain ⟨v, hv, rfl⟩ := hz
  obtain ⟨w, hw, rfl⟩ := hy
  have hb : commP (levelMk G 5 v) (levelMk G 5 w) = levelMk G 5 (commP v w) := by
    simp only [commP, map_mul, map_inv]
  rw [hb]
  exact (lim_mem_twoCentralSeries_iff_levelMk 5 _).mp (cfive_commutator_lambdaTwo hv hw)

/-- ⭐ The same with the two slots exchanged. -/
theorem gFourFive_commP_vanish' {y z : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hz : z ∈ lambdaImage G 3 5) : commP y z = 1 := by
  have h : commP y z = (commP z y)⁻¹ := by simp only [commP]; group
  rw [h, gFourFive_commP_vanish hz hy, inv_one]

/-- A central-layer element commutes with everything.  The class-four statement is
`cfour_zLayer_comm`. -/
theorem gFourFive_zLayer_comm {z : levelQuot G 5} (hz : z ∈ zLayer G 4) (x : levelQuot G 5) :
    z * x = x * z := (zLayer_commute hz x).eq

/-- A central-layer element kills a bracket from the right.  The class-four statement is
`cfour_commP_zLayer_right`. -/
theorem gFourFive_commP_zLayer_right {z : levelQuot G 5} (hz : z ∈ zLayer G 4)
    (q : levelQuot G 5) : commP q z = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq.symm

/-- **Left additivity with a `T`-element in the near slot**: the correction term of
`cfour_commP_mul_left` is a bracket against the `Z`-element `commP y q`, so it dies.  Wave 70's
`gThreeFour_ad_left` is the same statement with the near slot in `Y`, one class down. -/
theorem gFourFive_ad_left {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5)
    (p q : levelQuot G 5) : commP (y * p) q = commP y q * commP p q := by
  rw [cfour_commP_mul_left, cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hy q) p, mul_one]

/-- **Right additivity with a `T`-element in the far slot.**  The `T`-element `y` is the right
entry of `commP`, which is the far slot by the convention of `GradedGammaThreeFour.lean` §1;
compare `gThreeFour_ad_right`, docstring'd the same way one class down. -/
theorem gFourFive_ad_right (p : levelQuot G 5) {y : levelQuot G 5}
    (hy : y ∈ lambdaImage G 3 5) (q : levelQuot G 5) :
    commP p (y * q) = commP p q * commP p y := by
  rw [cfour_commP_mul_right,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_right p hy) q, mul_one]

/-- A bracket with a `T`-slot is its own inverse: it lies in the exponent-two layer `Z`. -/
theorem gFourFive_ad_inv_self {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5)
    (q : levelQuot G 5) : (commP y q)⁻¹ = commP y q :=
  zLayer_inv_self (cfive_commP_mem_zLayer_left hy q)

/-- **An inverse in the near slot is invisible**: `commP y⁻¹ q = commP y q` for `y ∈ T`. -/
theorem gFourFive_ad_inv_left {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5)
    (q : levelQuot G 5) : commP y⁻¹ q = commP y q := by
  have h := gFourFive_ad_left hy y⁻¹ q
  rw [mul_inv_cancel, cfour_one_comm] at h
  have h3 : (commP y q)⁻¹ = commP y⁻¹ q := inv_eq_iff_mul_eq_one.mpr h.symm
  rw [← h3, gFourFive_ad_inv_self hy]

/-- **An inverse in the near slot of a `Y × Y` bracket is invisible.**  The values lie in `Z`,
where inversion is trivial, and `cfive_commP_lambdaTwo_hom_left` supplies the additivity. -/
theorem gFourFive_lambdaTwo_inv_left {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) : commP y⁻¹ y' = commP y y' := by
  have h := cfive_commP_lambdaTwo_hom_left hy hy' y⁻¹
  rw [mul_inv_cancel, cfour_one_comm] at h
  have h3 : (commP y y')⁻¹ = commP y⁻¹ y' := inv_eq_iff_mul_eq_one.mpr h.symm
  rw [← h3, zLayer_inv_self (cfive_commP_lambdaTwo_mem_zLayer hy hy')]

/-- A bracket with a `Y`-slot on the right lies in `T`.  The left-slot statement is
`cfive_commP_lambdaTwo_mem_lambdaThree`. -/
theorem gFourFive_commP_mem_lambdaThree_right (q : levelQuot G 5) {y : levelQuot G 5}
    (hy : y ∈ lambdaImage G 2 5) : commP q y ∈ lambdaImage G 3 5 := by
  have h : commP q y = (commP y q)⁻¹ := by simp only [commP]; group
  rw [h]
  exact (lambdaImage G 3 5).inv_mem (cfive_commP_lambdaTwo_mem_lambdaThree hy q)

end Vanishing

/-! ## §2 Jacobi at `γ₄/γ₅`

Wave 70's `gThreeFour_hallWitt` is used unchanged.  What is rebuilt is the passage from it to
Jacobi, because `gThreeFour_jacobi_of` quantifies its two reductions over the whole group. -/

section Passage

variable {Q : Type*} [Group Q]

/-- **Conjugation is invisible exactly when the bracket dies**, in any group.  This is the
identity `conjP z t = z * commP z t` read as an equivalence, and it is what makes
`gFourFive_hcentral_iff` below a computation rather than an estimate. -/
theorem gFourFive_conj_iff (z t : Q) : conjP z t = z ↔ commP z t = 1 := by
  have h : conjP z t = z * commP z t := by simp only [conjP, commP]; group
  rw [h]
  refine ⟨fun hh => mul_left_cancel (a := z) (by rw [hh, mul_one]), fun hh => ?_⟩
  rw [hh, mul_one]

/-- ⭐⭐ **Jacobi from Hall-Witt at six pointwise equations.**  Wave 70's `gThreeFour_jacobi_of`
takes its two reductions as universals over the ambient group; the Hall-Witt reduction rewrites
exactly six words, so those six equations suffice.  This is the form the next layer up needs,
where the reductions hold only when one slot is restricted (`gFourFive_jacobi`). -/
theorem gFourFive_jacobi_of {p q r : Q}
    (hc₁ : conjP (commP (commP p q⁻¹) r) q = commP (commP p q⁻¹) r)
    (hc₂ : conjP (commP (commP q r⁻¹) p) r = commP (commP q r⁻¹) p)
    (hc₃ : conjP (commP (commP r p⁻¹) q) p = commP (commP r p⁻¹) q)
    (hi₁ : commP (commP p q⁻¹) r = commP (commP p q) r)
    (hi₂ : commP (commP q r⁻¹) p = commP (commP q r) p)
    (hi₃ : commP (commP r p⁻¹) q = commP (commP r p) q) :
    commP (commP p q) r * commP (commP q r) p * commP (commP r p) q = 1 := by
  have h := gThreeFour_hallWitt p q r
  rw [hc₁, hc₂, hc₃, hi₁, hi₂, hi₃] at h
  exact h

/-- **The check that the pointwise form subsumes wave 70's.**  `gThreeFour_jacobi_of`'s
conclusion is re-derived from `gFourFive_jacobi_of` by instantiating its two universals. -/
theorem gFourFive_jacobi_of_forall
    (hcentral : ∀ p q r t : Q, conjP (commP (commP p q) r) t = commP (commP p q) r)
    (hinvmid : ∀ p q r : Q, commP (commP p q⁻¹) r = commP (commP p q) r) (p q r : Q) :
    commP (commP p q) r * commP (commP q r) p * commP (commP r p) q = 1 :=
  gFourFive_jacobi_of (hcentral _ _ _ _) (hcentral _ _ _ _) (hcentral _ _ _ _)
    (hinvmid _ _ _) (hinvmid _ _ _) (hinvmid _ _ _)

end Passage

section JacobiFive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **What wave 70's `hcentral` says at `Q₅`.**  Its hypothesis `hcentral`, read in `Q₅`, is
equivalent to the statement that every **left-normed** fourfold bracket `⁅⁅⁅p, q⁆, r⁆, t⁆` of
`Q₅`-elements is trivial.  Left-normed only: the right-hand side below says nothing about, say,
`⁅⁅p, q⁆, ⁅r, t⁆⁆`.  This locates the failure of `gThreeFour_jacobi_of` to instantiate here: the
class-five calculus places a triple bracket in `T` (`cfive_commP_lambdaTwo_mem_lambdaThree`), one
layer short of the central `Z`, and supplies no vanishing for the left-normed fourfold bracket.
No such vanishing is refuted here. -/
theorem gFourFive_hcentral_iff :
    (∀ p q r t : levelQuot G 5, conjP (commP (commP p q) r) t = commP (commP p q) r) ↔
      ∀ p q r t : levelQuot G 5, commP (commP (commP p q) r) t = 1 := by
  constructor <;> intro H p q r t
  · exact (gFourFive_conj_iff _ _).mp (H p q r t)
  · exact (gFourFive_conj_iff _ _).mpr (H p q r t)

/-- A triple bracket whose outermost near slot descends from a `Y`-element lies in `Z`. -/
theorem gFourFive_triple_mem_one {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP p q⁻¹) r ∈ zLayer G 4 :=
  cfive_commP_mem_zLayer_left (cfive_commP_lambdaTwo_mem_lambdaThree hp q⁻¹) r

/-- The second rotation lies in `Z`, by `⁅Y, Y⁆ ≤ Z`. -/
theorem gFourFive_triple_mem_two {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP q r⁻¹) p ∈ zLayer G 4 :=
  cfive_commP_lambdaTwo_mem_zLayer (gFourFive_commP_mem_lambdaTwo q r⁻¹) hp

/-- The third rotation lies in `Z`. -/
theorem gFourFive_triple_mem_three {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP r p⁻¹) q ∈ zLayer G 4 :=
  cfive_commP_mem_zLayer_left
    (gFourFive_commP_mem_lambdaThree_right r ((lambdaImage G 2 5).inv_mem hp)) q

/-- **First inverse-in-the-middle reduction**, with the near slot in `Y`.  The two inner brackets
differ by a `Z`-element and by an inversion, and the outer bracket sees neither. -/
theorem gFourFive_inv_mid_one {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP p q⁻¹) r = commP (commP p q) r := by
  have hB : commP p q ∈ lambdaImage G 3 5 := cfive_commP_lambdaTwo_mem_lambdaThree hp q
  have hz : commP (commP p q) q⁻¹ ∈ zLayer G 4 := cfive_commP_mem_zLayer_left hB q⁻¹
  have hid := cfour_commP_mul_right p q q⁻¹
  rw [mul_inv_cancel, cfour_comm_one] at hid
  have hC : commP p q⁻¹ = (commP p q * commP (commP p q) q⁻¹)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, ← hid])
  rw [hC, mul_inv_rev, gFourFive_ad_left (gFourFive_zLayer_le_lambdaThree ((zLayer G 4).inv_mem hz)),
    cfive_commP_zLayer_left ((zLayer G 4).inv_mem hz) r, one_mul, gFourFive_ad_inv_left hB]

/-- **Second inverse-in-the-middle reduction**, with the far slot in `Y`.  The extra term this
reduction picks up over the class-four one is a bracket of a `T`-element against a `Y`-element,
and it dies by `gFourFive_commP_vanish`. -/
theorem gFourFive_inv_mid_two {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP q r⁻¹) p = commP (commP q r) p := by
  have hA : commP q r ∈ lambdaImage G 2 5 := gFourFive_commP_mem_lambdaTwo q r
  have hB : commP (commP q r) r⁻¹ ∈ lambdaImage G 3 5 :=
    cfive_commP_lambdaTwo_mem_lambdaThree hA r⁻¹
  have hid := cfour_commP_mul_right q r r⁻¹
  rw [mul_inv_cancel, cfour_comm_one] at hid
  have hC : commP q r⁻¹ = (commP q r * commP (commP q r) r⁻¹)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, ← hid])
  rw [hC, mul_inv_rev, gFourFive_ad_left ((lambdaImage G 3 5).inv_mem hB),
    gFourFive_commP_vanish ((lambdaImage G 3 5).inv_mem hB) hp, one_mul,
    gFourFive_lambdaTwo_inv_left hA hp]

/-- **Third inverse-in-the-middle reduction**, with the inverted slot in `Y`.  Here the
correction term of `cfour_commP_mul_right` dies outright by `gFourFive_commP_vanish`, so the
inner bracket is exactly inverted. -/
theorem gFourFive_inv_mid_three {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) : commP (commP r p⁻¹) q = commP (commP r p) q := by
  have hA : commP r p ∈ lambdaImage G 3 5 := gFourFive_commP_mem_lambdaThree_right r hp
  have hid := cfour_commP_mul_right r p p⁻¹
  rw [mul_inv_cancel, cfour_comm_one, gFourFive_commP_vanish hA ((lambdaImage G 2 5).inv_mem hp),
    mul_one] at hid
  have hC : commP r p⁻¹ = (commP r p)⁻¹ := eq_inv_of_mul_eq_one_left hid.symm
  rw [hC, gFourFive_ad_inv_left hA]

/-- ⭐⭐ **Jacobi in the layer `γ₄/γ₅`**: for `p ∈ Y` and arbitrary `q, r` in `Q₅` the three
rotations of the triple bracket multiply to `1`.  All three rotations lie in `Z`
(`gFourFive_triple_mem_one` and its two companions), so this is an identity in the top layer at
weights `2 + 1 + 1`.  The side condition on `p` is what wave 70's version did not carry, and
`gFourFive_hcentral_iff` says why it cannot be dropped by the class-five calculus. -/
theorem gFourFive_jacobi {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5) (q r : levelQuot G 5) :
    commP (commP p q) r * commP (commP q r) p * commP (commP r p) q = 1 :=
  gFourFive_jacobi_of
    ((gFourFive_conj_iff _ _).mpr
      (cfive_commP_zLayer_left (gFourFive_triple_mem_one hp q r) q))
    ((gFourFive_conj_iff _ _).mpr
      (cfive_commP_zLayer_left (gFourFive_triple_mem_two hp q r) r))
    ((gFourFive_conj_iff _ _).mpr
      (cfive_commP_zLayer_left (gFourFive_triple_mem_three hp q r) p))
    (gFourFive_inv_mid_one hp q r) (gFourFive_inv_mid_two hp q r)
    (gFourFive_inv_mid_three hp q r)

/-- ⭐⭐ **The fourfold form.**  A bracket of two `Q₅`-elements lies in `Y`, so Jacobi applies with
`p = commP a b` and no hypothesis at all.  This is the form in which a spanning argument for the
fourfold-bracket part of `γ₄/γ₅` rewrites an outer slot. -/
theorem gFourFive_jacobi_iter (a b q r : levelQuot G 5) :
    commP (commP (commP a b) q) r * commP (commP q r) (commP a b) *
      commP (commP r (commP a b)) q = 1 :=
  gFourFive_jacobi (gFourFive_commP_mem_lambdaTwo a b) q r

end JacobiFive

/-! ## §3 The layer is generated by squares and brackets one layer down -/

section Generation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The mathlib bracket, written out and read in `Q_k`, is a `commP` bracket of the inverted
entries.  Wave 70's `gThreeFour_levelMk_commutator` is the case `k = 4`; the level is free here
because nothing in it is about a level. -/
theorem gFourFive_levelMk_commutator (k : ℕ) (a b : G) :
    levelMk G k (a * b * a⁻¹ * b⁻¹) = commP (levelMk G k a⁻¹) (levelMk G k b⁻¹) := by
  simp only [commP, map_mul, map_inv]
  group

/-- ⭐⭐ **The layer `γ_{k+1}/γ_{k+2}` is generated by the squares and the brackets of the image of
`γ_k`.**  A closed subgroup of `Q_{k+2}` containing `y ^ 2` for every `y ∈ lambdaImage G k (k+2)`
and `commP y q` for every such `y` and every `q` contains the whole central layer
`zLayer G (k+1)`.

The proof is the recursion `γ_{k+1} = twoCentralSucc γ_k` pulled back along `levelMk`, so the
closedness hypothesis is what pays for the topological closure in `twoCentralSucc`, and `1 ≤ k`
is what makes that recursion available.  Wave 70's `gThreeFour_zLayer_le` is the case `k = 2` and
`Levelwise`'s `zLayer_two_le_of_gens` is the case `k = 1` in a different packaging. -/
theorem gFourFive_zLayer_le_gen {k : ℕ} (hk : 1 ≤ k) {S : Subgroup (levelQuot G (k + 2))}
    (hS : IsClosed ((S : Subgroup (levelQuot G (k + 2))) : Set (levelQuot G (k + 2))))
    (hsq : ∀ y ∈ lambdaImage G k (k + 2), y ^ 2 ∈ S)
    (hcomm : ∀ y ∈ lambdaImage G k (k + 2), ∀ q, commP y q ∈ S) :
    zLayer G (k + 1) ≤ S := by
  rintro _ ⟨v, hv, rfl⟩
  have hpre : IsClosed ((Subgroup.comap (levelMk G (k + 2)) S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_comap]
    exact hS.preimage (continuous_levelMk G (k + 2))
  have hsub : twoCentralSeries G (k + 1) ≤ Subgroup.comap (levelMk G (k + 2)) S := by
    rw [twoCentralSeries_succ (G := G) hk, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      show levelMk G (k + 2) (g ^ 2) ∈ S
      rw [map_pow]
      exact hsq _ ⟨g, hg, rfl⟩
    · refine Subgroup.commutator_le.2 fun a ha b _ => ?_
      rw [commutatorElement_def]
      show levelMk G (k + 2) (a * b * a⁻¹ * b⁻¹) ∈ S
      rw [gFourFive_levelMk_commutator]
      exact hcomm _ ⟨a⁻¹, (twoCentralSeries G k).inv_mem ha, rfl⟩ _
  exact hsub hv

/-- ⭐⭐ **The class-five instance**: a closed subgroup of `Q₅` holding `y ^ 2` for every `y ∈ T`
and `commP y q` for every `y ∈ T` and every `q` holds all of `Z = γ₄/γ₅`.  The side condition is
on `T = lambdaImage G 3 5`, where wave 70's class-four statement had `Y`, which is the move the
class-five map predicts. -/
theorem gFourFive_zLayer_le {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hsq : ∀ y ∈ lambdaImage G 3 5, y ^ 2 ∈ S)
    (hcomm : ∀ y ∈ lambdaImage G 3 5, ∀ q, commP y q ∈ S) :
    zLayer G 4 ≤ S :=
  gFourFive_zLayer_le_gen (by norm_num) hS hsq hcomm

end Generation

/-! ## §4 The knob inventory at class five

`cfour_sqRelWord` is class-four-only, so the relator is expanded here by the free-group calculus
of `relBase_sqWord_free` instead, and every correction term is killed either by §1 or by the
centrality of `Z` rather than by the abelianness of `Y`. -/

section FreeShapes

variable {Q : Type*} [Group Q]

/-- Conjugation by a product is conjugation twice, in any group. -/
theorem gFourFive_conj_mul_right (z t s : Q) : conjP z (t * s) = conjP (conjP z t) s := by
  simp only [conjP]; group

/-- Conjugation of a product, in any group. -/
theorem gFourFive_conj_mul_left (a b t : Q) : conjP (a * b) t = conjP a t * conjP b t := by
  simp only [conjP]; group

/-- Conjugation as a bracket correction, in any group. -/
theorem gFourFive_conj_eq (a t : Q) : conjP a t = a * commP a t := by
  simp only [conjP, commP]; group

/-- **The relator in the free-group calculus alone**: `relBase_sqWord_free` substituted into
`sqRelWord`.  This holds in every group, and it is the shape a class-five knob computation
starts from, `cfour_sqRelWord` being class-four-only. -/
theorem gFourFive_sqRelWord {n : ℕ} (m : Fin (sqRank n) → Q) :
    sqRelWord m = commP (m 0) (m 1) * ((m 1 ^ 2) ^ 2)⁻¹ * m 2 ^ 2 *
      commP (m 2) (conjP (m 2) (m 0)) *
      handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) := by
  rw [sqRelWord, relBase_sqWord_free]

end FreeShapes

section Knobs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Moving a central factor from the first slot of a five-fold product to the end.  The
class-four statement is `cfour_shuffle`. -/
theorem gFourFive_shuffle {z : levelQuot G 5} (hz : z ∈ zLayer G 4)
    (A B C D E : levelQuot G 5) : A * z * B * C * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [gFourFive_zLayer_comm hz]
  simp only [mul_assoc]

/-- Moving a central factor from the third slot of a five-fold product to the end.  The
class-four statement is `cfour_shuffle_mid`. -/
theorem gFourFive_shuffle_mid {z : levelQuot G 5} (hz : z ∈ zLayer G 4)
    (A B C D E : levelQuot G 5) : A * B * (C * z) * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [gFourFive_zLayer_comm hz]
  simp only [mul_assoc]

/-- A central right factor in the far slot of a bracket is invisible. -/
theorem gFourFive_drop_right (p q : levelQuot G 5) {z : levelQuot G 5} (hz : z ∈ zLayer G 4) :
    commP p (q * z) = commP p q := by
  rw [cfour_commP_mul_right, gFourFive_commP_zLayer_right hz p, one_mul,
    gFourFive_commP_zLayer_right hz (commP p q), mul_one]

/-- ⭐ **A square with a `T`-valued correction**: `(p·c)² = p²·(c²·commP c p)`, the correction
being central of exponent two.  At class four the same slot was corrected inside `Y` and the
correction was `cfour_sq_mul`'s, killed by `Y` being abelian; here it survives as a `Z`-element
and is killed one step later, by the outer square. -/
theorem gFourFive_sq_dress {p c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) :
    (p * c) ^ 2 = p ^ 2 * (c ^ 2 * commP c p) := by
  rw [cfour_sq_mul, cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hc p) c, mul_one,
    mul_assoc]

/-- A central correction is invisible to a square. -/
theorem gFourFive_sq_zLayer_dress {p z : levelQuot G 5} (hz : z ∈ zLayer G 4) :
    (p * z) ^ 2 = p ^ 2 := by
  rw [cfour_sq_mul, cfive_commP_zLayer_left hz p, cfour_one_comm, zLayer_sq G hz, mul_one,
    mul_one, mul_one]

/-- ⭐ **The fourth power is blind to a `T`-valued correction**, in the shape `((·)²)²` in which
the relator carries it.  The class-four proof (`cfour_pow_four_dress`) runs through
`cfour_pow_four_mul`, which needs `Y` abelian; here the inner square already collects the whole
correction into `Z` (`gFourFive_sq_dress`) and the outer square kills it. -/
theorem gFourFive_pow_four_dress {p c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) :
    ((p * c) ^ 2) ^ 2 = (p ^ 2) ^ 2 := by
  rw [gFourFive_sq_dress hc,
    gFourFive_sq_zLayer_dress
      (Subgroup.mul_mem _ (gFourFive_sq_mem_zLayer hc) (cfive_commP_mem_zLayer_left hc p))]

/-- ⭐ **The `σ`-slot knob**: a `γ₃`-valued correction of the `σ`-slot moves the class-five
relator by the single bracket `commP c (m 1)`.  Same expression as `cfour_dress_zero`, one class
up, with the correction one layer down. -/
theorem cfiveKnob_dress_zero {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) {c : levelQuot G 5}
    (hc : c ∈ lambdaImage G 3 5) (h0 : m' 0 = m 0 * c) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m 1) := by
  have hA : commP (m' 0) (m' 1) = commP (m 0) (m 1) * commP c (m 1) := by
    rw [h0, h1, cfour_commP_mul_left,
      gFourFive_commP_vanish' (gFourFive_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one]
  have hD : commP (m' 2) (conjP (m' 2) (m' 0)) = commP (m 2) (conjP (m 2) (m 0)) := by
    rw [h0, h2, gFourFive_conj_mul_right, gFourFive_conj_eq (conjP (m 2) (m 0)) c,
      gFourFive_drop_right _ _ (cfive_commP_mem_zLayer_right (conjP (m 2) (m 0)) hc)]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hA, hD, h1, h2]
  simp only [hU, hV]
  exact gFourFive_shuffle (cfive_commP_mem_zLayer_left hc (m 1)) _ _ _ _ _

/-- ⭐ **The `x₀`-slot knob**: a `γ₃`-valued correction of the `x₀`-slot moves the class-five
relator by `commP (m 0) c`.  The fourth power contributes nothing
(`gFourFive_pow_four_dress`). -/
theorem cfiveKnob_dress_one {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) {c : levelQuot G 5}
    (hc : c ∈ lambdaImage G 3 5) (h0 : m' 0 = m 0) (h1 : m' 1 = m 1 * c) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP (m 0) c := by
  have hz : commP (m 0) c ∈ zLayer G 4 := cfive_commP_mem_zLayer_right (m 0) hc
  have hA : commP (m' 0) (m' 1) = commP (m 0) (m 1) * commP (m 0) c := by
    rw [h0, h1, cfour_commP_mul_right,
      gFourFive_commP_vanish' (gFourFive_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one,
      gFourFive_zLayer_comm hz]
  have hB : ((m' 1 ^ 2) ^ 2)⁻¹ = ((m 1 ^ 2) ^ 2)⁻¹ := by rw [h1, gFourFive_pow_four_dress hc]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hA, hB, h0, h2]
  simp only [hU, hV]
  exact gFourFive_shuffle hz _ _ _ _ _

/-- ⭐ **The `conjP` factor of the relator is blind to a `γ₃`-valued correction of the `x₁`-slot.**
Unlike at class four, where the factor had already been collapsed to a triple bracket, the two
terms this correction produces are `commP (m 2) c` and `commP c (conjP (m 2) (m 0))`; the second
reduces to `commP c (m 2)` because `conjP (m 2) (m 0)` differs from `m 2` by a `Y`-element and
`⁅T, Y⁆` is trivial, and the two are then mutually inverse in an exponent-two layer. -/
theorem gFourFive_dress_two_conj_factor {p s c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) :
    commP (p * c) (conjP (p * c) s) = commP p (conjP p s) := by
  have hz2 : commP p c ∈ zLayer G 4 := cfive_commP_mem_zLayer_right p hc
  have hzc : commP c p ∈ zLayer G 4 := cfive_commP_mem_zLayer_left hc p
  have hinvXY : commP p c * commP c p = 1 := by
    have hi : commP p c = (commP c p)⁻¹ := by simp only [commP]; group
    rw [hi, inv_mul_cancel]
  have hcP : commP c (conjP p s) = commP c p := by
    rw [gFourFive_conj_eq p s, cfive_commP_right_hom hc,
      gFourFive_commP_vanish hc (gFourFive_commP_mem_lambdaTwo p s), one_mul]
  have hinner : conjP (p * c) s = conjP p s * c * commP c s := by
    rw [gFourFive_conj_mul_left, gFourFive_conj_eq c s, ← mul_assoc]
  have hmid : commP p (conjP p s * c) = commP p c * commP p (conjP p s) := by
    rw [cfour_commP_mul_right,
      gFourFive_commP_vanish' (gFourFive_commP_mem_lambdaTwo p (conjP p s)) hc, mul_one]
  have hkill : commP (commP p c * commP p (conjP p s)) c = 1 := by
    rw [cfour_commP_mul_left (commP p c) (commP p (conjP p s)) c,
      cfive_commP_zLayer_left hz2 c, cfour_one_comm, one_mul, one_mul,
      gFourFive_commP_vanish' (gFourFive_commP_mem_lambdaTwo p (conjP p s)) hc]
  have hlast : commP c (conjP p s * c) = commP c p := by
    rw [cfour_commP_mul_right, cfour_comm_self, one_mul,
      cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hc (conjP p s)) c, mul_one, hcP]
  rw [hinner, gFourFive_drop_right _ _ (cfive_commP_mem_zLayer_left hc s),
    cfour_commP_mul_left, hmid, hkill, hlast, mul_one, gFourFive_zLayer_comm hz2, mul_assoc,
    hinvXY, mul_one]

/-- ⭐ **The `x₁`-slot knob**: a `γ₃`-valued correction of the `x₁`-slot moves the class-five
relator by `c²·commP c (m 2)`.  This is the only knob producing a square, `m 2 ^ 2` being the
only square in the relator, and the square arrives bundled with a bracket against `m 2`, exactly
as at class four (`cfour_dress_two`).  What is not the class-four proof is the `conjP` factor,
which is handled by `gFourFive_dress_two_conj_factor`. -/
theorem cfiveKnob_dress_two {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) {c : levelQuot G 5}
    (hc : c ∈ lambdaImage G 3 5) (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2 * c)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * (c ^ 2 * commP c (m 2)) := by
  have hzc : commP c (m 2) ∈ zLayer G 4 := cfive_commP_mem_zLayer_left hc (m 2)
  have hC : (m' 2) ^ 2 = m 2 ^ 2 * (c ^ 2 * commP c (m 2)) := by rw [h2, gFourFive_sq_dress hc]
  have hD : commP (m' 2) (conjP (m' 2) (m' 0)) = commP (m 2) (conjP (m 2) (m 0)) := by
    rw [h0, h2, gFourFive_dress_two_conj_factor hc]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hC, hD, h0, h1]
  simp only [hU, hV]
  exact gFourFive_shuffle_mid (Subgroup.mul_mem _ (gFourFive_sq_mem_zLayer hc) hzc) _ _ _ _ _

/-- **A relator whose only change is one handle bracket, changed by a central factor.**  The core
slots are untouched, so the first four factors agree and the whole move is the handle surgery of
`cfour_handleWord_update`, whose `Commute` hypothesis a `Z`-element discharges.  The class-four
statement is `cfourId_dress_handle`. -/
theorem cfiveKnob_dress_handle {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) (j' : Fin n)
    {z : levelQuot G 5} (hz : z ∈ zLayer G 4)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hne : ∀ i, i ≠ j' → commP (m' (sqHandleIdxU i)) (m' (sqHandleIdxV i))
        = commP (m (sqHandleIdxU i)) (m (sqHandleIdxV i)))
    (hj : commP (m' (sqHandleIdxU j')) (m' (sqHandleIdxV j'))
        = commP (m (sqHandleIdxU j')) (m (sqHandleIdxV j')) * z) :
    sqRelWord m' = sqRelWord m * z := by
  have hhandle := cfour_handleWord_update (fun i => m' (sqHandleIdxU i))
    (fun i => m' (sqHandleIdxV i)) (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i))
    j' z (fun i => (zLayer_commute hz _).symm) hne hj
  rw [sqRelWord, sqRelWord, h0, h1, h2, hhandle, ← mul_assoc]

/-- ⭐ **The `u_{j'}`-slot knob**: `commP c (m (sqHandleIdxV j'))`, as at class four
(`cfourId_dress_handleU`). -/
theorem cfiveKnob_dress_handleU {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) (j' : Fin n)
    {c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hUj : m' (sqHandleIdxU j') = m (sqHandleIdxU j') * c)
    (hUne : ∀ i, i ≠ j' → m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m (sqHandleIdxV j')) := by
  refine cfiveKnob_dress_handle m m' j' (cfive_commP_mem_zLayer_left hc _) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hUne i hi, hV i]
  · rw [hUj, hV j', cfour_commP_mul_left,
      gFourFive_commP_vanish'
        (gFourFive_commP_mem_lambdaTwo (m (sqHandleIdxU j')) (m (sqHandleIdxV j'))) hc, mul_one]

/-- ⭐ **The `v_{j'}`-slot knob**: `commP (m (sqHandleIdxU j')) c`, as at class four
(`cfourId_dress_handleV`). -/
theorem cfiveKnob_dress_handleV {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5) (j' : Fin n)
    {c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hVj : m' (sqHandleIdxV j') = m (sqHandleIdxV j') * c)
    (hVne : ∀ i, i ≠ j' → m' (sqHandleIdxV i) = m (sqHandleIdxV i))
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i)) :
    sqRelWord m' = sqRelWord m * commP (m (sqHandleIdxU j')) c := by
  refine cfiveKnob_dress_handle m m' j' (cfive_commP_mem_zLayer_right _ hc) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hU i, hVne i hi]
  · rw [hVj, hU j', cfour_commP_mul_right,
      gFourFive_commP_vanish'
        (gFourFive_commP_mem_lambdaTwo (m (sqHandleIdxU j')) (m (sqHandleIdxV j'))) hc, mul_one,
      gFourFive_zLayer_comm (cfive_commP_mem_zLayer_right (m (sqHandleIdxU j')) hc)]

/-- ⭐ **The three core knobs, composed.**  Correcting the `σ`-, `x₀`- and `x₁`-slots by
`γ₃`-elements at once moves the class-five relator by the product of the three knobs, each read
at the **undressed** frame: the only cross term is `commP c0 c1`, and it dies because `T ≤ Y` and
`⁅T, Y⁆` is trivial.  The class-four statement is `cfourId_dress_core`. -/
theorem cfiveKnob_dress_core {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5)
    {c0 c1 c2 : levelQuot G 5} (hc0 : c0 ∈ lambdaImage G 3 5) (hc1 : c1 ∈ lambdaImage G 3 5)
    (hc2 : c2 ∈ lambdaImage G 3 5)
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m *
      (commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2))) := by
  classical
  obtain ⟨mA, hA0, hA1, hA2, hAU, hAV⟩ :
      ∃ mA : Fin (sqRank n) → levelQuot G 5,
        mA 0 = m 0 * c0 ∧ mA 1 = m 1 ∧ mA 2 = m 2 ∧
          (∀ i, mA (sqHandleIdxU i) = m (sqHandleIdxU i)) ∧
            (∀ i, mA (sqHandleIdxV i) = m (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 0 then m 0 * c0 else m i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero, if_pos]
    · simp only [sqVal_one]; norm_num
    · simp only [sqVal_two]; norm_num
    · intro i; simp only [sqHandleIdxU_val]; rw [if_neg (by omega)]
    · intro i; simp only [sqHandleIdxV_val]; rw [if_neg (by omega)]
  obtain ⟨mB, hB0, hB1, hB2, hBU, hBV⟩ :
      ∃ mB : Fin (sqRank n) → levelQuot G 5,
        mB 0 = mA 0 ∧ mB 1 = mA 1 * c1 ∧ mB 2 = mA 2 ∧
          (∀ i, mB (sqHandleIdxU i) = mA (sqHandleIdxU i)) ∧
            (∀ i, mB (sqHandleIdxV i) = mA (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 1 then mA 1 * c1 else mA i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero]; norm_num
    · simp only [sqVal_one, if_pos]
    · simp only [sqVal_two]; norm_num
    · intro i; simp only [sqHandleIdxU_val]; rw [if_neg (by omega)]
    · intro i; simp only [sqHandleIdxV_val]; rw [if_neg (by omega)]
  have step0 := cfiveKnob_dress_zero m mA hc0 hA0 hA1 hA2 hAU hAV
  have step1 := cfiveKnob_dress_one mA mB hc1 hB0 hB1 hB2 hBU hBV
  have step2 := cfiveKnob_dress_two mB m' hc2 (by rw [h0, ← hA0, ← hB0])
    (by rw [h1, ← hA1, ← hB1]) (by rw [h2, ← hA2, ← hB2])
    (fun i => by rw [hU i, ← hAU i, ← hBU i]) (fun i => by rw [hV i, ← hAV i, ← hBV i])
  have hknob1 : commP (mA 0) c1 = commP (m 0) c1 := by
    rw [hA0, cfive_commP_left_hom_five (m 0) c0 hc1,
      gFourFive_commP_vanish' (gFourFive_lambdaThree_le hc0) hc1, mul_one]
  rw [step2, step1, step0, hknob1, hB2, hA2]
  simp only [mul_assoc]

end Knobs

/-! ## §5 The class-five obligation

Wave 70 reached, at class four, "some `γ₂`-valued exactly row-trivial correction of wave 68's
frame kills the relator in `Q₄`".  The class-five statement is the same shape one class up, with
the correction inside `γ₃` and with the base frame left as a parameter, since class four is open
and no frame clearing it is committed. -/

section Obligation

variable {h : ℕ}

/-- ⭐⭐ **The class-five supply from a `γ₃`-valued correction.**  `SqClassClearingSupply h 5`
follows as soon as, at every selected marking and handle, there is an exactly row-trivial,
mod-2 independent frame admitting a `γ₃`-valued exactly row-trivial correction whose corrected
relator is trivial in `Q₅`.  Rows multiply, so the corrected dressing stays exactly row-trivial;
mod-2 independence is blind to a `γ₂`-factor and `γ₃ ≤ γ₂`; and the relator clause is the
membership `sqRelWord ... ∈ γ₅` read in `Q₅`.

No class-four witness is presupposed: the base dressing is existentially quantified, so a later
wave supplies whatever frame its class-four argument produces. -/
theorem cfiveKnob_supply_of_reach
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ a d : Fin (sqRank h) → (DSq h : Type),
          (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
            SqModTwoIndep (sqArbFrame h nu' j a) ∧
              (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 3) ∧
                (∀ i, nuLam h (d i) = 1) ∧ (∀ i, nu' (d i) = 1) ∧
                  sqRelWord (fun i => levelMk (DSq h : Type) 5
                      (sqArbFrame h nu' j a i * d i)) = 1) :
    SqClassClearingSupply h 5 := by
  intro nu' j hs hx
  obtain ⟨a, d, hal, han, hai, hd3, hdl, hdn, hrel⟩ := H nu' j hs hx
  have hfr : sqArbFrame h nu' j (fun i => a i * d i)
      = fun i => sqArbFrame h nu' j a i * d i := by
    funext i
    simp only [sqArbFrame, mul_assoc]
  refine ⟨fun i => a i * d i, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [map_mul, hal i, hdl i, one_mul]
  · intro i
    rw [map_mul, han i, hdn i, one_mul]
  · rw [hfr]
    exact cfourId_modTwoIndep_mul hai
      (fun i => twoCentralSeries_antitone (G := (DSq h : Type)) (by norm_num) (hd3 i))
  · rw [hfr, lim_mem_twoCentralSeries_iff_levelMk 5, map_sqRelWord]
    exact hrel

end Obligation

section ObligationIdentity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐⭐ **The class-five obligation, as an identity.**  If a `γ₃`-valued correction of the three
core slots has knob product inverse to the base relator value, the corrected relator is trivial
in `Q₅`.  With `cfiveKnob_supply_of_reach` this is the whole of the core-slot route: the amount
to be killed is one element, and the knobs available to kill it are the three of
`cfiveKnob_dress_core` together with the two handle families. -/
theorem cfiveKnob_kills {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5)
    {c0 c1 c2 : levelQuot G 5} (hc0 : c0 ∈ lambdaImage G 3 5) (hc1 : c1 ∈ lambdaImage G 3 5)
    (hc2 : c2 ∈ lambdaImage G 3 5)
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i))
    (hkill : commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2))
      = (sqRelWord m)⁻¹) :
    sqRelWord m' = 1 := by
  rw [cfiveKnob_dress_core m m' hc0 hc1 hc2 h0 h1 h2 hU hV, hkill, mul_inv_cancel]

end ObligationIdentity

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms gFourFive_commP_mem_lambdaTwo
#print axioms gFourFive_lambdaThree_le
#print axioms gFourFive_zLayer_le_lambdaThree
#print axioms gFourFive_sq_mem_zLayer
#print axioms gFourFive_commP_vanish
#print axioms gFourFive_commP_vanish'
#print axioms gFourFive_zLayer_comm
#print axioms gFourFive_commP_zLayer_right
#print axioms gFourFive_ad_left
#print axioms gFourFive_ad_right
#print axioms gFourFive_ad_inv_self
#print axioms gFourFive_ad_inv_left
#print axioms gFourFive_lambdaTwo_inv_left
#print axioms gFourFive_commP_mem_lambdaThree_right
#print axioms gFourFive_conj_iff
#print axioms gFourFive_jacobi_of
#print axioms gFourFive_jacobi_of_forall
#print axioms gFourFive_hcentral_iff
#print axioms gFourFive_triple_mem_one
#print axioms gFourFive_triple_mem_two
#print axioms gFourFive_triple_mem_three
#print axioms gFourFive_inv_mid_one
#print axioms gFourFive_inv_mid_two
#print axioms gFourFive_inv_mid_three
#print axioms gFourFive_jacobi
#print axioms gFourFive_jacobi_iter
#print axioms gFourFive_levelMk_commutator
#print axioms gFourFive_zLayer_le_gen
#print axioms gFourFive_zLayer_le
#print axioms gFourFive_conj_mul_right
#print axioms gFourFive_conj_mul_left
#print axioms gFourFive_conj_eq
#print axioms gFourFive_sqRelWord
#print axioms gFourFive_shuffle
#print axioms gFourFive_shuffle_mid
#print axioms gFourFive_drop_right
#print axioms gFourFive_sq_dress
#print axioms gFourFive_sq_zLayer_dress
#print axioms gFourFive_pow_four_dress
#print axioms cfiveKnob_dress_zero
#print axioms cfiveKnob_dress_one
#print axioms gFourFive_dress_two_conj_factor
#print axioms cfiveKnob_dress_two
#print axioms cfiveKnob_dress_handle
#print axioms cfiveKnob_dress_handleU
#print axioms cfiveKnob_dress_handleV
#print axioms cfiveKnob_dress_core
#print axioms cfiveKnob_supply_of_reach
#print axioms cfiveKnob_kills

end AxiomPins

end SqCore

end Dyadic

end GQ2
