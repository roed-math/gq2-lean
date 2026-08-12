/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFourKnob

/-!
# W72-DEFECTS: the class-four leftover, reduced to the two defects

Wave 71 evaluated the class-four leftover of wave 68's frame to

```text
  LEFTOVER = ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu' j · (A⁴ · ⁅A, x₀⁆²) · ⁅x₁, ⁅x₁, A⁆⁆
```

with `A = bridgeDress nu' j`, and moved `A⁴` and `⁅x₁, ⁅x₁, A⁆⁆` by one admissible correction of
the `x₁`-slot (`cfourKnob_pair_correction`).  It left three things: the square `⁅A, x₀⁆²`, the
residue `⁅⁅A, x₁⁆, A⁆` of that pairing, and the two defects.

## §2 The square, and §7 the residue

`cfourDef_commSq_correction`: `⁅A, x₀⁆` is a legal `x₁`-slot correction whose knob is
`⁅A, x₀⁆² · ⁅⁅A, x₀⁆, x₁⁆`, and `cfourDef_jacobi_solve` rewrites the residue into two brackets
with outer slots `A` and `x₀`.  `cfourDef_comm_dress_mem`: the far slot of the dressing resolves
into the two handle generators, the pivot factor being an even `ℤ₂`-power and so invisible to a
bracket with a `Y`-element in the near slot.

## §4 The two defects, split

⭐⭐⭐ `cfourDef_defect_eq`.  Expanding `⁅σA, x₀A⁆` by class-four bilinearity
(`cfourDef_common_dress`) gives five factors, the term `⁅⁅σ, x₀⁆, A⁆` occurring twice and
cancelling.  Stripping `⁅σ, x₀⁆` leaves

```text
  ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect = cfourDefCore · cfourDefTriple ,
```

where `cfourDefCore = ⁅σ, A⁆ · ⁅A, x₀⁆ · cfourEichDefect` lies in `Z` and `cfourDefTriple` is the
two triple brackets whose outer slot is the dressing.  **The expansion has no term outside these
five brackets**, which is the wave-71 §4.1 question answered.

## §6 The reduction

⭐⭐⭐ `cfourDef_leftover_reduce_merged`.  The single admissible correction `cfourDefCorr` -
`⁅x₁, A⁆` on the `σ`-slot, `A² · ⁅A, x₁⁆ · ⁅A, x₀⁆` on the `x₁`-slot, `1` elsewhere - turns the
class-four relator of wave 68's frame into

```text
  cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆ .
```

Five of the leftover's factors annihilate against the knob (`cfourDef_assemble`).  The relator
identity itself needs **no** hypothesis on the marking; only admissibility does.

## §8 What is left

`CfourDefResidual` names it, and `cfourDef_supply_of_residual` shows it discharges
`SqClassClearingSupply h 4`.  The residue is `x₁`-free apart from the near slot `⁅x₀, x₁⁆`, and
its second factor is a bracket whose far slot is the dressing, which §7 resolves into the frame's
own letters.  **What is not committed** is the frame surgery composing a handle-slot correction
with a core-slot correction, without which the second factor is an expression rather than a
knob.

**Honesty marker.**  Nothing here is evidence that no dressing works.  All of it concerns one
sufficient route - `γ₂`-valued corrections of wave 68's frame, wave 70's `CfourIdReachable` - and
a failure of that route would not touch `SqClassClearingSupply h 4` itself.

Lane W72-DEFECTS.  New file; no edits to existing files.  Prefix `cfourDef`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 Jacobi, solved for one rotation -/

section JacobiSolved

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **Jacobi, solved for one rotation.**  `gThreeFour_jacobi` says the three rotations of a
triple bracket multiply to `1`; since all three lie in the exponent-two central layer `Z`, any
one of them is the product of the other two.  This is the form a rewriting step consumes: a
bracket whose **outer** slot is `r` becomes a product of two brackets whose outer slots are `p`
and `q`. -/
theorem cfourDef_jacobi_solve (p q r : levelQuot G 4) :
    commP (commP p q) r = commP (commP q r) p * commP (commP r p) q := by
  have hz : commP (commP q r) p * commP (commP r p) q ∈ zLayer G 3 :=
    Subgroup.mul_mem _ (gThreeFour_triple_mem q r p) (gThreeFour_triple_mem r p q)
  have h1 : commP (commP p q) r * (commP (commP q r) p * commP (commP r p) q) = 1 := by
    rw [← mul_assoc]
    exact gThreeFour_jacobi p q r
  have h2 : commP (commP p q) r = (commP (commP q r) p * commP (commP r p) q)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  rw [h2, zLayer_inv_self hz]

/-- **The inner slots of a triple bracket may be swapped.**  The two inner brackets are inverse
to one another and an inverse in a `Y`-slot is invisible. -/
theorem cfourDef_swap_inner (p q r : levelQuot G 4) :
    commP (commP p q) r = commP (commP q p) r := by
  have hsw : ∀ a b : levelQuot G 4, commP a b = (commP b a)⁻¹ := by
    intro a b; simp only [commP]; group
  rw [hsw q p, gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo p q) r]

end JacobiSolved

/-! ## §2 The square `⁅A, x₀⁆²`, delivered -/

section CommSquare

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- ⭐⭐ **The leftover's remaining square is a legal `x₁`-slot correction, and its residue is
Jacobi-reducible.**  The correction is the commutator `⁅A, x₀⁆` itself, which is exactly
row-trivial (`cfourKnob_comm_admissible`), so it is admissible with no repair.  Its `x₁`-slot
knob (`cfour_dress_two` at `m 2 = x₁`) is `⁅A, x₀⁆² · ⁅⁅A, x₀⁆, x₁⁆`, and the residue - a bracket
whose outer slot is `x₁` - is rewritten by `cfourDef_jacobi_solve` into two brackets whose outer
slots are `A` and `x₀`.

This is wave 71 §4.2, committed. -/
theorem cfourDef_commSq_correction :
    ∃ c ∈ twoCentralSeries (DSq h : Type) 2, nuLam h c = 1 ∧ nu' c = 1 ∧
      (levelMk (DSq h : Type) 4 c) ^ 2 *
          commP (levelMk (DSq h : Type) 4 c) (levelMk (DSq h : Type) 4 (dsqX1 h))
        = commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
              (levelMk (DSq h : Type) 4 (dsqX0 h)) ^ 2 *
            (commP (commP (levelMk (DSq h : Type) 4 (dsqX0 h))
                  (levelMk (DSq h : Type) 4 (dsqX1 h)))
                (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
              commP (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
                  (levelMk (DSq h : Type) 4 (bridgeDress nu' j)))
                (levelMk (DSq h : Type) 4 (dsqX0 h))) := by
  obtain ⟨hm, hl, hn⟩ := cfourKnob_comm_admissible nu' (bridgeDress nu' j) (dsqX0 h)
  refine ⟨_, hm, hl, hn, ?_⟩
  rw [cfourKnob_levelMk_commP, cfourDef_jacobi_solve]

end CommSquare

/-! ## §3 The core bracket under a common dressing -/

section CommonDress

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The shuffle the expansion below ends in: two `Y`-factors reorder freely, two `Z`-factors are
central, and the repeated `Z`-factor squares away. -/
theorem cfourDef_shuffle {y1 y2 y3 z1 z2 z3 : levelQuot G 4}
    (hy1 : y1 ∈ lambdaImage G 2 4) (hy2 : y2 ∈ lambdaImage G 2 4)
    (hz1 : z1 ∈ zLayer G 3) (hz2 : z2 ∈ zLayer G 3) :
    y1 * y2 * z1 * (z2 * z1) * (y3 * z3) = y2 * (y1 * y3) * (z2 * z3) := by
  have hz11 : z1 * z1 = 1 := by rw [← pow_two]; exact zLayer_sq G hz1
  have step : z1 * (z2 * z1) = z2 := by
    rw [← mul_assoc, cfour_zLayer_comm hz1 z2, mul_assoc, hz11, mul_one]
  calc y1 * y2 * z1 * (z2 * z1) * (y3 * z3)
      = y1 * y2 * (z1 * (z2 * z1)) * (y3 * z3) := by rw [mul_assoc (y1 * y2) z1 (z2 * z1)]
    _ = y1 * y2 * z2 * (y3 * z3) := by rw [step]
    _ = y1 * y2 * y3 * (z2 * z3) := by
        rw [mul_assoc (y1 * y2) z2 (y3 * z3), ← mul_assoc z2 y3 z3, cfour_zLayer_comm hz2 y3,
          mul_assoc y3 z2 z3, ← mul_assoc (y1 * y2) y3 (z2 * z3)]
    _ = y2 * (y1 * y3) * (z2 * z3) := by
        rw [(cfour_commute_lambdaTwo hy1 hy2).eq, mul_assoc y2 y1 y3]

/-- ⭐⭐⭐ **The core bracket under a common dressing, at class four.**  Wave 68's
`bridge_comm_common_dress` reads `⁅s·a, x·a⁆ = ⁅s, x⁆ · ⁅s·x, a⁆` in `Q₃`.  One class up the
expansion has five surviving factors and no `⁅s·x, a⁆`:

```text
  ⁅s·a, x·a⁆ = ⁅s, x⁆ · (⁅s, a⁆ · ⁅a, x⁆) · (⁅⁅s, a⁆, a⁆ · ⁅⁅a, x⁆, a⁆) .
```

The term `⁅⁅s, x⁆, a⁆` occurs **twice** - once from the free identity in the far slot and once
from the correction term in the near slot - and the two cancel, `Z` having exponent two.  This is
what makes the class-four core defect depend on `s` and `x` only through the two brackets against
the dressing. -/
theorem cfourDef_common_dress (s x a : levelQuot G 4) :
    commP (s * a) (x * a)
      = commP s x * (commP s a * commP a x) *
        (commP (commP s a) a * commP (commP a x) a) := by
  have hY1 : commP s a ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo s a
  have hY2 : commP s x ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo s x
  have hZ1 : commP (commP s x) a ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hY2 a
  have hZ2 : commP (commP s a) a ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hY1 a
  have hii : commP s (x * a) = commP s a * commP s x * commP (commP s x) a :=
    cfour_commP_mul_right s x a
  have hiii : commP a (x * a) = commP a x * commP (commP a x) a := by
    rw [cfour_commP_mul_right a x a, cfour_comm_self, one_mul]
  have hiv : commP (commP s (x * a)) a = commP (commP s a) a * commP (commP s x) a := by
    rw [hii, gThreeFour_ad_left (Subgroup.mul_mem _ hY1 hY2) _ a,
      cfour_commP_zLayer_left hZ1 a, mul_one, gThreeFour_ad_left hY1 _ a]
  rw [cfour_commP_mul_left s a (x * a), hiv, hii, hiii]
  exact cfourDef_shuffle hY1 hY2 hZ1 hZ2

/-- Stripping the undressed bracket off the dressed one: the `Y`-factors reorder and cancel, the
`Z`-factor is central. -/
theorem cfourDef_strip {y1 y2 y3 t : levelQuot G 4} (hy1 : y1 ∈ lambdaImage G 2 4)
    (hy2 : y2 ∈ lambdaImage G 2 4) (hy3 : y3 ∈ lambdaImage G 2 4) (ht : t ∈ zLayer G 3)
    (e : levelQuot G 4) :
    y2 * (y1 * y3) * t * y2⁻¹ * e = y1 * y3 * e * t := by
  have hcom : Commute y2 (y1 * y3) :=
    cfour_commute_lambdaTwo hy2 (Subgroup.mul_mem _ hy1 hy3)
  calc y2 * (y1 * y3) * t * y2⁻¹ * e
      = y1 * y3 * y2 * t * y2⁻¹ * e := by rw [hcom.eq]
    _ = y1 * y3 * y2 * y2⁻¹ * t * e := by
        rw [mul_assoc (y1 * y3 * y2) t y2⁻¹, cfour_zLayer_comm ht y2⁻¹,
          ← mul_assoc (y1 * y3 * y2) y2⁻¹ t]
    _ = y1 * y3 * t * e := by rw [mul_assoc (y1 * y3) y2 y2⁻¹, mul_inv_cancel, mul_one]
    _ = y1 * y3 * e * t := by
        rw [mul_assoc (y1 * y3) t e, cfour_zLayer_comm ht e, ← mul_assoc (y1 * y3) e t]

end CommonDress

/-! ## §4 The two class-four defects, split -/

section Defects

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- ⭐⭐ **The core defect**: the part of the two class-four defects that is not a triple bracket.
It is the product of the two brackets of the frame's odd-row generators against wave 68's
dressing with the class-four Eichler defect,

```text
  cfourDefCore = ⁅σ, A⁆ · ⁅A, x₀⁆ · cfourEichDefect nu' j ,
```

a product of three `Y`-elements which lies in `Z` (`cfourDef_core_mem_zLayer`) because the three
class-three images cancel: `⁅σ, A⁆ · ⁅A, x₀⁆` projects to `⁅σ·x₀, A⁆ = bridgeDefect nu' j`,
`σ·x₀` being the pivot modulo `γ₂` (`bridge_sigma_x0_eq_pivot`), and `cfourEichDefect` projects to
`bridgeDefect nu' j` as well (`cfourId_eichDefect_levelProj`).

**This is the wave-72 residue.**  It is `x₁`-free: every letter in it is `σ`, `x₀`, a handle
letter or the pivot. -/
noncomputable def cfourDefCore : levelQuot (DSq h : Type) 4 :=
  commP (levelMk (DSq h : Type) 4 (dsqSigma h)) (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
      commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) (levelMk (DSq h : Type) 4 (dsqX0 h)) *
    cfourEichDefect nu' j

/-- **The triple part of the two class-four defects**: the two iterated brackets whose **outer**
slot is the dressing.  Both are `Z`-elements on the nose. -/
noncomputable def cfourDefTriple : levelQuot (DSq h : Type) 4 :=
  commP (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
        (levelMk (DSq h : Type) 4 (bridgeDress nu' j)))
      (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
    commP (commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
        (levelMk (DSq h : Type) 4 (dsqX0 h)))
      (levelMk (DSq h : Type) 4 (bridgeDress nu' j))

/-- The triple part is a `Z`-element. -/
theorem cfourDef_triple_mem_zLayer : cfourDefTriple nu' j ∈ zLayer (DSq h : Type) 3 :=
  Subgroup.mul_mem _
    (cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) _)
    (cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) _)

/-- ⭐⭐⭐ **The two class-four defects, split into a core and a triple part.**  Expanding
`⁅σA, x₀A⁆` by `cfourDef_common_dress` and cancelling the undressed bracket leaves exactly

```text
  ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu' j = cfourDefCore nu' j · cfourDefTriple nu' j ,
```

so the whole `x₁`-free part of the leftover is one `Y`-valued core defect (which lies in `Z`)
times two triple brackets whose outer slot is the dressing.  This answers the first half of the
wave-71 §4.1 ticket: the expansion has **no** term outside these five brackets. -/
theorem cfourDef_defect_eq :
    commP (levelMk (DSq h : Type) 4 (dsqSigma h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j))
          (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
        (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
          (levelMk (DSq h : Type) 4 (dsqX0 h)))⁻¹ *
        cfourEichDefect nu' j
      = cfourDefCore nu' j * cfourDefTriple nu' j := by
  rw [cfourDef_common_dress, cfourDefCore, cfourDefTriple]
  exact cfourDef_strip (cfour_commP_mem_lambdaTwo _ _) (cfour_commP_mem_lambdaTwo _ _)
    (cfour_commP_mem_lambdaTwo _ _) (cfourDef_triple_mem_zLayer nu' j) _

/-- **The two class-four defects lie in `Z`.**  Their class-three images are both
`bridgeDefect nu' j` and cancel; formally this is `cfourId_leftover_mem_zLayer` read through
`cfourKnob_leftover_eq`, whose other three factors are `Z`-elements outright. -/
theorem cfourDef_defect_mem_zLayer :
    commP (levelMk (DSq h : Type) 4 (dsqSigma h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j))
          (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
        (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
          (levelMk (DSq h : Type) 4 (dsqX0 h)))⁻¹ *
        cfourEichDefect nu' j ∈ zLayer (DSq h : Type) 3 := by
  have hP : levelMk (DSq h : Type) 4 (bridgeDress nu' j) ^ 4 *
      commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
        (levelMk (DSq h : Type) 4 (dsqX0 h)) ^ 2 ∈ zLayer (DSq h : Type) 3 :=
    Subgroup.mul_mem _ (cfour_pow_four_mem_zLayer _)
      (cfour_sq_mem_zLayer (cfour_commP_mem_lambdaTwo _ _))
  have hQ : commP (levelMk (DSq h : Type) 4 (dsqX1 h))
      (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
        (levelMk (DSq h : Type) 4 (bridgeDress nu' j))) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right _ (cfour_commP_mem_lambdaTwo _ _)
  have hL := cfourKnob_leftover_eq nu' j
  have hEq : commP (levelMk (DSq h : Type) 4 (dsqSigma h) *
          levelMk (DSq h : Type) 4 (bridgeDress nu' j))
        (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
        (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
          (levelMk (DSq h : Type) 4 (dsqX0 h)))⁻¹ *
        cfourEichDefect nu' j
      = cfourIdLeftover nu' j *
          (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
            (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
              (levelMk (DSq h : Type) 4 (bridgeDress nu' j))))⁻¹ *
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j) ^ 4 *
            commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
              (levelMk (DSq h : Type) 4 (dsqX0 h)) ^ 2)⁻¹ := by
    rw [hL]; group
  rw [hEq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (cfourId_leftover_mem_zLayer nu' j)
    (Subgroup.inv_mem _ hQ)) (Subgroup.inv_mem _ hP)

/-- ⭐⭐ **The core defect lies in `Z`.**  It is the product of the two defects with the inverse
of the triple part, and both of those lie in `Z`. -/
theorem cfourDef_core_mem_zLayer : cfourDefCore nu' j ∈ zLayer (DSq h : Type) 3 := by
  have hsplit := cfourDef_defect_eq nu' j
  have hcore : cfourDefCore nu' j
      = (commP (levelMk (DSq h : Type) 4 (dsqSigma h) *
              levelMk (DSq h : Type) 4 (bridgeDress nu' j))
            (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
          (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
            (levelMk (DSq h : Type) 4 (dsqX0 h)))⁻¹ *
          cfourEichDefect nu' j) * (cfourDefTriple nu' j)⁻¹ := by
    rw [hsplit, mul_inv_cancel_right]
  rw [hcore]
  exact Subgroup.mul_mem _ (cfourDef_defect_mem_zLayer nu' j)
    (Subgroup.inv_mem _ (cfourDef_triple_mem_zLayer nu' j))

end Defects

/-! ## §5 The assembly, as an identity among central involutions -/

section Involutions

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A `Z`-element moves one step to the right through a product. -/
theorem cfourDef_z_push {z : levelQuot G 4} (hz : z ∈ zLayer G 3) (a x : levelQuot G 4) :
    z * (a * x) = a * (z * x) := by
  rw [← mul_assoc, cfour_zLayer_comm hz a, mul_assoc]

/-- A `Z`-element is an involution. -/
theorem cfourDef_z_sq {z : levelQuot G 4} (hz : z ∈ zLayer G 3) : z * z = 1 := by
  rw [← pow_two]
  exact zLayer_sq G hz

/-- Two adjacent copies of a `Z`-element annihilate. -/
theorem cfourDef_z_cancel {z : levelQuot G 4} (hz : z ∈ zLayer G 3) (x : levelQuot G 4) :
    z * (z * x) = x := by
  rw [← mul_assoc, cfourDef_z_sq hz, one_mul]

/-- ⭐ **The wave-72 assembly.**  Five of the eight factors of the corrected relator occur twice
and annihilate, `Z` being central of exponent two: the fourth power `q`, the commutator square
`s`, the `ad(x₁)²`-term `t`, the residue `r` of the pairing, and the `x₀`-slot bracket `p`.  What
survives is the triple part `tri` and the Jacobi term `n`.  Stated with named atoms so the
bookkeeping is separated from the identification of the atoms. -/
theorem cfourDef_assemble {q s t r p : levelQuot G 4} (hq : q ∈ zLayer G 3)
    (hs : s ∈ zLayer G 3) (ht : t ∈ zLayer G 3) (hr : r ∈ zLayer G 3) (hp : p ∈ zLayer G 3)
    (c tri n : levelQuot G 4) :
    c * tri * (q * s) * t * (r * p * (q * (r * t) * (s * (n * p)))) = c * (tri * n) := by
  simp only [mul_assoc]
  rw [cfourDef_z_push hq, cfourDef_z_push hq, cfourDef_z_push hq, cfourDef_z_push hq,
    cfourDef_z_cancel hq,
    cfourDef_z_push ht, cfourDef_z_push ht, cfourDef_z_push ht, cfourDef_z_cancel ht,
    cfourDef_z_push hs, cfourDef_z_push hs, cfourDef_z_push hs, cfourDef_z_cancel hs,
    cfourDef_z_push hr, cfourDef_z_cancel hr,
    cfourDef_z_push hp, cfourDef_z_sq hp, mul_one]

end Involutions

/-! ## §6 The wave-72 correction, and the reduction -/

section Correction

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The wave-72 correction** of wave 68's frame: `⁅x₁, A⁆` on the `σ`-slot,
`A² · ⁅A, x₁⁆ · ⁅A, x₀⁆` on the `x₁`-slot, and nothing anywhere else.  Every entry is a product
of a square of the dressing and commutators, so every entry is exactly row-trivial. -/
noncomputable def cfourDefCorr : Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = 0 then commP (dsqX1 h) (bridgeDress nu' j)
    else if (i : ℕ) = 2 then
      bridgeDress nu' j ^ 2 * commP (bridgeDress nu' j) (dsqX1 h) *
        commP (bridgeDress nu' j) (dsqX0 h)
    else 1

@[simp] theorem cfourDefCorr_zero :
    cfourDefCorr nu' j 0 = commP (dsqX1 h) (bridgeDress nu' j) := by
  simp only [cfourDefCorr, sqVal_zero, if_pos]

@[simp] theorem cfourDefCorr_one : cfourDefCorr nu' j 1 = 1 := by
  simp only [cfourDefCorr, sqVal_one]
  norm_num

@[simp] theorem cfourDefCorr_two :
    cfourDefCorr nu' j 2 = bridgeDress nu' j ^ 2 * commP (bridgeDress nu' j) (dsqX1 h) *
      commP (bridgeDress nu' j) (dsqX0 h) := by
  simp only [cfourDefCorr, sqVal_two]
  norm_num

@[simp] theorem cfourDefCorr_handleU (i : Fin h) : cfourDefCorr nu' j (sqHandleIdxU i) = 1 := by
  simp only [cfourDefCorr, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega)]

@[simp] theorem cfourDefCorr_handleV (i : Fin h) : cfourDefCorr nu' j (sqHandleIdxV i) = 1 := by
  simp only [cfourDefCorr, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

/-- **The correction is admissible**: `γ₂`-valued with both rows exactly trivial, slot by slot.
The `σ`-slot entry is a commutator (`cfourKnob_comm_admissible`); the `x₁`-slot entry is the
square of wave 68's dressing (`cfourKnob_dressSq_admissible`) times two commutators; every other
slot is `1`. -/
theorem cfourDefCorr_admissible (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (i : Fin (sqRank h)) :
    cfourDefCorr nu' j i ∈ twoCentralSeries (DSq h : Type) 2 ∧
      nuLam h (cfourDefCorr nu' j i) = 1 ∧ nu' (cfourDefCorr nu' j i) = 1 := by
  obtain ⟨hm1, hl1, hn1⟩ := cfourKnob_dressSq_admissible nu' j hsigma hx0
  obtain ⟨hm2, hl2, hn2⟩ := cfourKnob_comm_admissible nu' (bridgeDress nu' j) (dsqX1 h)
  obtain ⟨hm3, hl3, hn3⟩ := cfourKnob_comm_admissible nu' (bridgeDress nu' j) (dsqX0 h)
  obtain ⟨hm4, hl4, hn4⟩ := cfourKnob_mul_admissible nu' hm1 hm2 hl1 hl2 hn1 hn2
  simp only [cfourDefCorr]
  split_ifs
  · exact cfourKnob_comm_admissible nu' (dsqX1 h) (bridgeDress nu' j)
  · exact cfourKnob_mul_admissible nu' hm4 hm3 hl4 hl3 hn4 hn3
  · exact ⟨Subgroup.one_mem _, map_one _, map_one _⟩

/-- ⭐⭐⭐ **The wave-68 leftover, reduced to the two defects.**  One admissible correction of
wave 68's class-three witness - `cfourDefCorr`, supported on the `σ`-slot and the `x₁`-slot -
turns the class-four relator into

```text
  cfourDefCore nu' j · (cfourDefTriple nu' j · ⁅⁅x₀, x₁⁆, A⁆) .
```

Five of the leftover's factors annihilate against the knob (`cfourDef_assemble`): the fourth
power `A⁴` and the commutator square `⁅A, x₀⁆²` against the `x₁`-slot bundle of `A²·⁅A, x₁⁆` and
of `⁅A, x₀⁆`, the `ad(x₁)²`-term `⁅x₁, ⁅x₁, A⁆⁆` against the same bundle, the pairing residue
`⁅⁅A, x₁⁆, A⁆` against the `σ`-slot bracket `⁅⁅x₁, A⁆, A⁆` (the same element of `Z`,
`cfourDef_swap_inner`), and the Jacobi residue `⁅⁅x₁, A⁆, x₀⁆` against the `σ`-slot's second
bracket.

**No hypothesis on the marking is needed**: admissibility of the correction needs `hsigma` and
`hx0` (`cfourDefCorr_admissible`), the relator identity does not.

What is left is the two class-four defects, plus one bracket whose **outer** slot is the
dressing: by `cfourDef_triple_mul_jacobi` the whole tail is `⁅y, A⁆` for a single `Y`-element
`y`, and every other slot of the frame is still free. -/
theorem cfourDef_relator_step :
    sqRelWord (fun i => levelMk (DSq h : Type) 4
        (sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i))
      = cfourIdLeftover nu' j *
        (commP (levelMk (DSq h : Type) 4 (cfourDefCorr nu' j 0))
              (levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) 1)) *
            commP (levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) 0)) 1 *
          ((levelMk (DSq h : Type) 4 (cfourDefCorr nu' j 2)) ^ 2 *
            commP (levelMk (DSq h : Type) 4 (cfourDefCorr nu' j 2))
              (levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) 2)))) := by
  have hc0mem : levelMk (DSq h : Type) 4 (cfourDefCorr nu' j 0)
      ∈ lambdaImage (DSq h : Type) 2 4 := by
    rw [cfourDefCorr_zero]
    exact ⟨_, cfour_commP_mem_two _ _, rfl⟩
  have hc2mem : levelMk (DSq h : Type) 4 (cfourDefCorr nu' j 2)
      ∈ lambdaImage (DSq h : Type) 2 4 := by
    rw [cfourDefCorr_two]
    exact ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (cfourKnob_sq_mem _)
      (cfour_commP_mem_two _ _)) (cfour_commP_mem_two _ _), rfl⟩
  have hstep := cfourId_dress_core
    (fun i => levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) i))
    (fun i => levelMk (DSq h : Type) 4
      (sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i))
    hc0mem (Subgroup.one_mem _) hc2mem (map_mul _ _ _)
    (by rw [cfourDefCorr_one, mul_one, mul_one]) (map_mul _ _ _)
    (fun i => by rw [cfourDefCorr_handleU, mul_one])
    (fun i => by rw [cfourDefCorr_handleV, mul_one])
  rw [hstep, cfourId_leftover_eq]

theorem cfourDef_leftover_reduce :
    sqRelWord (fun i => levelMk (DSq h : Type) 4
        (sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i))
      = cfourDefCore nu' j *
        (cfourDefTriple nu' j *
          commP (commP (levelMk (DSq h : Type) 4 (dsqX0 h))
              (levelMk (DSq h : Type) 4 (dsqX1 h)))
            (levelMk (DSq h : Type) 4 (bridgeDress nu' j))) := by
  rw [cfourDef_relator_step]
  simp only [bridge_frame_zero, bridge_frame_one, bridge_frame_two, map_mul, cfourDefCorr_zero,
    cfourDefCorr_two, cfourKnob_levelMk_commP, map_pow]
  rw [cfourKnob_leftover_eq, cfourDef_defect_eq, cfour_comm_one, mul_one,
    cfour_commP_right_hom (cfour_commP_mem_lambdaTwo (levelMk (DSq h : Type) 4 (dsqX1 h))
      (levelMk (DSq h : Type) 4 (bridgeDress nu' j))),
    cfourKnob_dress_two_mul (Subgroup.mul_mem _ (cfour_sq_mem_lambdaTwo _)
      (cfour_commP_mem_lambdaTwo _ _)) (cfour_commP_mem_lambdaTwo _ _),
    cfourKnob_dress_two_mul (cfour_sq_mem_lambdaTwo _) (cfour_commP_mem_lambdaTwo _ _),
    cfourKnob_dress_pair,
    cfourDef_jacobi_solve (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
      (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)),
    cfourDef_swap_inner (levelMk (DSq h : Type) 4 (dsqX1 h))
      (levelMk (DSq h : Type) 4 (bridgeDress nu' j))]
  have hq : levelMk (DSq h : Type) 4 (bridgeDress nu' j) ^ 4 ∈ zLayer (DSq h : Type) 3 :=
    cfour_pow_four_mem_zLayer _
  have hs : commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
      (levelMk (DSq h : Type) 4 (dsqX0 h)) ^ 2 ∈ zLayer (DSq h : Type) 3 :=
    cfour_sq_mem_zLayer (cfour_commP_mem_lambdaTwo _ _)
  have ht : commP (levelMk (DSq h : Type) 4 (dsqX1 h))
      (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
        (levelMk (DSq h : Type) 4 (bridgeDress nu' j))) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right _ (cfour_commP_mem_lambdaTwo _ _)
  have hr : commP (commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
        (levelMk (DSq h : Type) 4 (dsqX1 h))) (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
      ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) _
  have hp : commP (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
        (levelMk (DSq h : Type) 4 (bridgeDress nu' j))) (levelMk (DSq h : Type) 4 (dsqX0 h))
      ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) _
  exact cfourDef_assemble hq hs ht hr hp _ _ _

/-- ⭐ **The tail is one bracket.**  The two triple brackets of `cfourDefTriple` and the Jacobi
term have a common outer slot, the dressing, so they merge: the whole tail of
`cfourDef_leftover_reduce` is `⁅y, A⁆` for the single `Y`-element
`y = ⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆`. -/
theorem cfourDef_triple_mul_jacobi :
    cfourDefTriple nu' j *
        commP (commP (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)))
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
      = commP (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
                (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
              commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
                (levelMk (DSq h : Type) 4 (dsqX0 h)) *
            commP (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)))
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) := by
  rw [cfourDefTriple, gThreeFour_ad_left (Subgroup.mul_mem _ (cfour_commP_mem_lambdaTwo _ _)
      (cfour_commP_mem_lambdaTwo _ _)) _ _,
    gThreeFour_ad_left (cfour_commP_mem_lambdaTwo _ _) _ _]

/-- ⭐⭐⭐ **The wave-68 leftover, reduced: the two defects and one bracket.**  This is
`cfourDef_leftover_reduce` with its tail merged by `cfourDef_triple_mul_jacobi`:

```text
  sqRelWord (wave 68's frame corrected by cfourDefCorr)
    = cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆ .
```

Both factors are `Z`-elements.  The first is the two class-four defects, `x₁`-free; the second is
a bracket with a `Y`-element in the near slot and **the dressing** in the far slot, which
`cfourDef_comm_dress_mem` decomposes into brackets against the two handle generators. -/
theorem cfourDef_leftover_reduce_merged :
    sqRelWord (fun i => levelMk (DSq h : Type) 4
        (sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i))
      = cfourDefCore nu' j *
        commP (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
                (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
              commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
                (levelMk (DSq h : Type) 4 (dsqX0 h)) *
            commP (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)))
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) := by
  rw [cfourDef_leftover_reduce, cfourDef_triple_mul_jacobi]

end Correction

/-! ## §7 The far slot of the dressing -/

section FarSlot

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **An inverse in the far slot is invisible to a `Y`-element in the near slot.**  For `y ∈ Y`
the map `commP y ·` is a homomorphism into the exponent-two layer `Z`, so it kills inverses. -/
theorem cfourDef_comm_inv_right {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (z : levelQuot G 4) : commP y z⁻¹ = commP y z := by
  have hz := cfour_commP_right_hom hy z z⁻¹
  rw [mul_inv_cancel, cfour_comm_one] at hz
  rw [eq_inv_of_mul_eq_one_left hz.symm, zLayer_inv_self (cfour_commP_mem_zLayer_left hy z)]

/-- **A bracket with a `Y`-element in one slot is symmetric**: it lies in the exponent-two layer
`Z`, where inversion is the identity. -/
theorem cfourDef_comm_swap {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (p : levelQuot G 4) : commP p y = commP y p := by
  have hsw : commP p y = (commP y p)⁻¹ := by simp only [commP]; group
  rw [hsw, zLayer_inv_self (cfour_commP_mem_zLayer_left hy p)]

end FarSlot

section DressFarSlot

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **A bracket against a `ℤ₂`-power reads only the exponent's parity.**  An even power is a
`γ₂`-element and dies against a `Y`-slot; an odd power is its base times a `γ₂`-element.  Stated
against an arbitrary subgroup so that no decidability of `2 ∣ k` in `ℤ₂` is needed. -/
theorem cfourDef_comm_zpow_mem {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) (g : (DSq h : Type)) (k : ℤ_[2])
    {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hg : commP y (levelMk (DSq h : Type) 4 g) ∈ S) :
    commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g k)) ∈ S := by
  by_cases hk : (2 : ℤ_[2]) ∣ k
  · have hone : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g k)) = 1 :=
      cfour_commP_lambdaTwo hy ⟨_, bridge_zpow_even g hk, rfl⟩
    rw [hone]
    exact Subgroup.one_mem _
  · obtain ⟨u, hu, hug⟩ := bridge_zpow_odd_eq g hk
    have hstep : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g k))
        = commP y (levelMk (DSq h : Type) 4 g) := by
      rw [hug, map_mul, cfour_commP_right_hom hy, cfour_commP_lambdaTwo hy ⟨u, hu, rfl⟩, mul_one]
    rw [hstep]
    exact hg

/-- ⭐⭐ **The far slot of wave 68's dressing, resolved into the two handle generators.**  The
dressing is `A = u_j^{ν'(v_j)} · v_j^{ν'(u_j)} · w^{-2ν'(u_j)ν'(v_j)}`.  The pivot factor has an
even exponent, hence lies in `γ₂` and is invisible to a bracket with a `Y`-element in the near
slot; the two handle powers are read through their exponents' parity only.  So `⁅y, A⁆` lies in
any subgroup containing `⁅y, u_j⁆` and `⁅y, v_j⁆`.

This is exactly the step the wave-71 note listed as missing for the pairing's residue
`⁅⁅A, x₁⁆, A⁆`: bilinearity in the far slot plus the `zpowZtwo` bookkeeping of `bridgeDress`. -/
theorem cfourDef_comm_dress_mem {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hu : commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j))) ∈ S)
    (hv : commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j))) ∈ S) :
    commP y (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ∈ S := by
  have hdvd : (2 : ℤ_[2]) ∣ -(2 * bridgeRowU nu' j * bridgeRowV nu' j) :=
    ⟨-(bridgeRowU nu' j * bridgeRowV nu' j), by ring⟩
  rw [bridgeDress, map_mul, map_mul, cfour_commP_right_hom hy,
    cfour_commP_lambdaTwo hy ⟨_, bridge_zpow_even (sqPivot h) hdvd, rfl⟩, one_mul,
    cfour_commP_right_hom hy]
  exact Subgroup.mul_mem _ (cfourDef_comm_zpow_mem hy _ _ hv)
    (cfourDef_comm_zpow_mem hy _ _ hu)

/-- **From the cleared `u`-letter to the generator.**  `U_j = w^{-ν'(u_j)} · u_j`, so the two
brackets differ by a bracket against a pivot power, which the parity lemma reads off the pivot
itself.  The cleared letters are what the frame's handle slots carry, so this is the step that
turns a handle knob into a bracket against a handle generator. -/
theorem cfourDef_comm_genU_mem {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hw : commP y (levelMk (DSq h : Type) 4 (sqPivot h)) ∈ S)
    (he : commP y (levelMk (DSq h : Type) 4 (sqEichU h nu' j)) ∈ S) :
    commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j))) ∈ S := by
  have hz : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxU j)))))) ∈ S := cfourDef_comm_zpow_mem hy _ _ hw
  have hzz : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxU j)))))) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hy _
  have hsplit : commP y (levelMk (DSq h : Type) 4 (sqEichU h nu' j))
      = commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j))) *
        commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
          (toAdd (nu' (sqGen h (sqHandleIdxU j)))))) := by
    rw [sqEichU, map_mul, map_inv, cfour_commP_right_hom hy, cfourDef_comm_inv_right hy]
  have hgen : commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j)))
      = commP y (levelMk (DSq h : Type) 4 (sqEichU h nu' j)) *
        commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
          (toAdd (nu' (sqGen h (sqHandleIdxU j)))))) := by
    rw [hsplit, mul_assoc, cfourDef_z_sq hzz, mul_one]
  rw [hgen]
  exact Subgroup.mul_mem _ he hz

/-- **From the cleared `v`-letter to the generator.**  `V_j = v_j · w^{-ν'(v_j)}`. -/
theorem cfourDef_comm_genV_mem {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hw : commP y (levelMk (DSq h : Type) 4 (sqPivot h)) ∈ S)
    (he : commP y (levelMk (DSq h : Type) 4 (sqEichV h nu' j)) ∈ S) :
    commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j))) ∈ S := by
  have hz : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxV j)))))) ∈ S := cfourDef_comm_zpow_mem hy _ _ hw
  have hzz : commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
      (toAdd (nu' (sqGen h (sqHandleIdxV j)))))) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hy _
  have hsplit : commP y (levelMk (DSq h : Type) 4 (sqEichV h nu' j))
      = commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
          (toAdd (nu' (sqGen h (sqHandleIdxV j)))))) *
        commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j))) := by
    rw [sqEichV, map_mul, map_inv, cfour_commP_right_hom hy, cfourDef_comm_inv_right hy]
  have hgen : commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j)))
      = commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) (sqPivot h)
          (toAdd (nu' (sqGen h (sqHandleIdxV j)))))) *
        commP y (levelMk (DSq h : Type) 4 (sqEichV h nu' j)) := by
    rw [hsplit, ← mul_assoc, cfourDef_z_sq hzz, one_mul]
  rw [hgen]
  exact Subgroup.mul_mem _ hz he

/-- ⭐⭐ **The tail's far slot, in the frame's own letters.**  Chaining the three lemmas above:
`⁅y, A⁆` lies in any subgroup holding the bracket of `y` against the pivot and against the two
**cleared** handle letters at `j`, which are the letters wave 68's frame actually carries in its
`j`-th handle slots.

Those three brackets are the knob **expressions** of the frame's remaining slots: `⁅y, V_j⁆` is
the `u_j`-slot knob of `cfourId_dress_handleU`, `⁅U_j, y⁆ = ⁅y, U_j⁆` (`cfourDef_comm_swap`) is
the `v_j`-slot knob of `cfourId_dress_handleV`, and `⁅y, w⁆` is the product of the two core knobs
by `cfourDef_core_knob_pair`.  What is **not** committed here is the frame surgery that composes
a handle-slot correction with a core-slot correction: `cfourId_dress_core` composes the three
core slots only, and `cfourId_dress_handleU`/`cfourId_dress_handleV` move one handle slot with
the core slots fixed. -/
theorem cfourDef_comm_dress_frame_mem {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hw : commP y (levelMk (DSq h : Type) 4 (sqPivot h)) ∈ S)
    (hU : commP y (levelMk (DSq h : Type) 4 (sqEichU h nu' j)) ∈ S)
    (hV : commP y (levelMk (DSq h : Type) 4 (sqEichV h nu' j)) ∈ S) :
    commP y (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ∈ S :=
  cfourDef_comm_dress_mem nu' j hy (cfourDef_comm_genU_mem nu' j hy hw hU)
    (cfourDef_comm_genV_mem nu' j hy hw hV)

/-- ⭐⭐⭐ **The two core knobs at a common correction deliver the pivot bracket.**  On wave 68's
frame the `σ`-slot knob at `c` is `⁅c, x₀·A⁆` and the `x₀`-slot knob at `c` is `⁅σ·A, c⁆`.  Each
carries a copy of `⁅c, A⁆`, and the two cancel because `Z` has exponent two; what survives is
`⁅c, x₀⁆ · ⁅c, σ⁆ = ⁅c, σ·x₀⁆`, and `σ·x₀` is the pivot modulo `γ₂`
(`bridge_sigma_x0_eq_pivot`), which the bracket does not see.

So the pivot bracket, which `cfourDef_comm_dress_frame_mem` needs, is the knob of **one**
correction used on **two** core slots - and `cfourId_dress_core` does compose those two slots, so
this one is available as a correction and not only as an expression.  It is the class-four shadow
of wave 68's own `bridgeDefect`, which is `⁅w, A⁆` in `Q₃`. -/
theorem cfourDef_core_knob_pair {c : levelQuot (DSq h : Type) 4}
    (hc : c ∈ lambdaImage (DSq h : Type) 2 4) :
    commP c (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
        commP (levelMk (DSq h : Type) 4 (dsqSigma h) *
          levelMk (DSq h : Type) 4 (bridgeDress nu' j)) c
      = commP c (levelMk (DSq h : Type) 4 (sqPivot h)) := by
  obtain ⟨u, hu, hup⟩ := bridge_sigma_x0_eq_pivot (h := h)
  have hA : commP c (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left hc _
  have hpiv : commP c (levelMk (DSq h : Type) 4 (dsqX0 h)) *
      commP c (levelMk (DSq h : Type) 4 (dsqSigma h))
      = commP c (levelMk (DSq h : Type) 4 (sqPivot h)) := by
    have h1 : commP c (levelMk (DSq h : Type) 4 (dsqSigma h * dsqX0 h))
        = commP c (levelMk (DSq h : Type) 4 (dsqX0 h)) *
          commP c (levelMk (DSq h : Type) 4 (dsqSigma h)) := by
      rw [map_mul, cfour_commP_right_hom hc]
    rw [← h1, hup, map_mul, cfour_commP_right_hom hc,
      cfour_commP_lambdaTwo hc ⟨u, hu, rfl⟩, mul_one]
  rw [cfour_commP_right_hom hc, cfour_commP_left_hom _ _ hc,
    cfourDef_comm_swap hc (levelMk (DSq h : Type) 4 (dsqSigma h)),
    cfourDef_comm_swap hc (levelMk (DSq h : Type) 4 (bridgeDress nu' j))]
  simp only [mul_assoc]
  rw [cfourDef_z_push hA, cfourDef_z_push hA, cfourDef_z_sq hA, mul_one]
  exact hpiv

end DressFarSlot

/-! ## §8 The residual -/

section Residual

variable {h : ℕ}

/-- ⭐⭐⭐ **The wave-72 residual.**  Everything wave 68's leftover carries except the two
class-four defects and one bracket against the dressing is moved by the single admissible
correction `cfourDefCorr` (`cfourDef_leftover_reduce_merged`).  What remains is exactly this: a
further admissible correction of the already-corrected frame must kill

```text
  cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆ ,
```

one element of the elementary abelian 2-group `Z = γ₃/γ₄`.

**Honesty marker.**  This is a residual of one *route* - `γ₂`-valued corrections of wave 68's
frame, wave 70's `CfourIdReachable` - not of `SqClassClearingSupply h 4` itself.  A failure of
this Prop would not refute the supply. -/
def CfourDefResidual (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ d : Fin (sqRank h) → (DSq h : Type),
        (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧ (∀ i, nuLam h (d i) = 1) ∧
          (∀ i, nu' (d i) = 1) ∧
          sqRelWord (fun i => levelMk (DSq h : Type) 4
              (sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i * d i)) = 1

/-- ⭐⭐ **The residual discharges the class-four supply.**  `cfourDefCorr` is admissible and
admissible corrections compose, so a further correction of the corrected frame is a correction of
wave 68's frame, and `cfourId_supply_of_reach` applies. -/
theorem cfourDef_supply_of_residual (H : CfourDefResidual h) : SqClassClearingSupply h 4 := by
  refine cfourId_supply_of_reach fun nu' j hs hx => ?_
  obtain ⟨d, hd2, hdl, hdn, hrel⟩ := H nu' j hs hx
  refine ⟨fun i => cfourDefCorr nu' j i * d i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Subgroup.mul_mem _ ((cfourDefCorr_admissible nu' j hs hx i).1) (hd2 i)
  · intro i
    rw [map_mul, (cfourDefCorr_admissible nu' j hs hx i).2.1, hdl i, one_mul]
  · intro i
    rw [map_mul, (cfourDefCorr_admissible nu' j hs hx i).2.2, hdn i, one_mul]
  · simpa only [← mul_assoc] using hrel

/-- **The residual holds wherever the residue simply vanishes**: take the trivial further
correction.  This is the sufficient condition a wave-73 run would most like to have; nothing here
says it holds. -/
theorem cfourDef_residual_of_vanish
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      cfourDefCore nu' j *
        commP (commP (levelMk (DSq h : Type) 4 (dsqSigma h))
                (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
              commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
                (levelMk (DSq h : Type) 4 (dsqX0 h)) *
            commP (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)))
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) = 1) :
    CfourDefResidual h := by
  intro nu' j _ _
  refine ⟨fun _ => 1, fun _ => Subgroup.one_mem _, fun _ => map_one _, fun _ => map_one _, ?_⟩
  simpa only [mul_one, cfourDef_leftover_reduce_merged] using H nu' j

end Residual

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms cfourDef_jacobi_solve
#print axioms cfourDef_swap_inner
#print axioms cfourDef_commSq_correction
#print axioms cfourDef_shuffle
#print axioms cfourDef_common_dress
#print axioms cfourDef_strip
#print axioms cfourDef_triple_mem_zLayer
#print axioms cfourDef_defect_eq
#print axioms cfourDef_defect_mem_zLayer
#print axioms cfourDef_core_mem_zLayer
#print axioms cfourDef_z_push
#print axioms cfourDef_z_sq
#print axioms cfourDef_z_cancel
#print axioms cfourDef_assemble
#print axioms cfourDefCorr_zero
#print axioms cfourDefCorr_one
#print axioms cfourDefCorr_two
#print axioms cfourDefCorr_handleU
#print axioms cfourDefCorr_handleV
#print axioms cfourDefCorr_admissible
#print axioms cfourDef_relator_step
#print axioms cfourDef_leftover_reduce
#print axioms cfourDef_triple_mul_jacobi
#print axioms cfourDef_leftover_reduce_merged
#print axioms cfourDef_comm_inv_right
#print axioms cfourDef_comm_swap
#print axioms cfourDef_comm_zpow_mem
#print axioms cfourDef_comm_dress_mem
#print axioms cfourDef_comm_genU_mem
#print axioms cfourDef_comm_genV_mem
#print axioms cfourDef_comm_dress_frame_mem
#print axioms cfourDef_core_knob_pair
#print axioms cfourDef_supply_of_residual
#print axioms cfourDef_residual_of_vanish

end AxiomPins

end SqCore

end Dyadic

end GQ2
