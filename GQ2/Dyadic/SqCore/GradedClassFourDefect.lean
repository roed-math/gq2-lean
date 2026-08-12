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
residue `⁅⁅A, x₁⁆, A⁆` of that pairing, and the two defects.  This file commits the first two and
opens up the third.

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

/-! ## §5 Axiom pins -/

section AxiomPins

#print axioms cfourDef_jacobi_solve
#print axioms cfourDef_commSq_correction
#print axioms cfourDef_shuffle
#print axioms cfourDef_common_dress
#print axioms cfourDef_strip
#print axioms cfourDef_triple_mem_zLayer
#print axioms cfourDef_defect_eq
#print axioms cfourDef_defect_mem_zLayer
#print axioms cfourDef_core_mem_zLayer

end AxiomPins

end SqCore

end Dyadic

end GQ2
