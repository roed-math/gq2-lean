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

/-! ## §3 Axiom pins -/

section AxiomPins

#print axioms cfourDef_jacobi_solve
#print axioms cfourDef_commSq_correction

end AxiomPins

end SqCore

end Dyadic

end GQ2
