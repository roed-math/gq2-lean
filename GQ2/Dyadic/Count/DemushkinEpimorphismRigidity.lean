/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Demushkin
import GQ2.Dyadic.Count.Scalar
import GQ2.MaxProPCohomology

/-!
# Epimorphism rigidity for pro-two Demushkin groups

This file isolates the low-degree cohomological core of the standard rigidity argument for a
continuous epimorphism between finitely generated pro-`2` Demushkin groups of equal rank.

Degree-one inflation is injective for every surjection.  Equal Demushkin rank therefore makes
it bijective.  Cup-product naturality and nondegeneracy then imply that degree-two inflation is
nonzero, hence bijective because both degree-two groups have order two.

What remains is exactly the kernel term in the continuous Hochschild--Serre five-term sequence:
bijectivity in degree one and injectivity in degree two force the conjugation-invariant
mod-two characters of the kernel to vanish.  The final definitions expose this seam separately
from the pro-two group fact that a nontrivial closed normal subgroup has such a character.
-/

set_option autoImplicit false

namespace GQ2.Dyadic

open GQ2 ContCoh

noncomputable section

section Inflation

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

local instance scalarActionG : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
local instance scalarContinuousG : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G
local instance scalarActionH : DistribMulAction H (ZMod 2) := scalarActionZmodTwo H
local instance scalarContinuousH : ContinuousSMul H (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul H

/-- Mod-two degree-one inflation along a continuous homomorphism, with the canonical trivial
scalar actions at source and target. -/
def demushkinH1Inflation (f : ContinuousMonoidHom G H) :
    H1 H (ZMod 2) →+ H1 G (ZMod 2) :=
  inf1 f (fun _ _ ↦ rfl)

/-- Mod-two degree-two inflation along a continuous homomorphism, with the canonical trivial
scalar actions at source and target. -/
def demushkinH2Inflation (f : ContinuousMonoidHom G H) :
    H2 H (ZMod 2) →+ H2 G (ZMod 2) :=
  inf2 f (fun _ _ ↦ rfl)

/-- Degree-one inflation with trivial coefficients is injective along every surjection. -/
theorem demushkinH1Inflation_injective_of_surjective
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f) :
    Function.Injective (demushkinH1Inflation f) := by
  intro x y hxy
  obtain ⟨zx, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  obtain ⟨zy, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) y
  rw [demushkinH1Inflation, inf1_H1mk, inf1_H1mk] at hxy
  have hz := congrArg
    (H1equivZ1OfTrivial (G := G) (M := ZMod 2) (scalarActionZmodTwo_triv G)) hxy
  apply congrArg (H1mk H (ZMod 2))
  apply Subtype.ext
  funext h
  obtain ⟨g, rfl⟩ := hf h
  exact congrFun (congrArg Subtype.val hz) g

/-- Inflation commutes with the trivial-coefficient cup product. -/
theorem demushkinH2Inflation_trivialCupPairing
    (f : ContinuousMonoidHom G H) (x y : H1 H (ZMod 2)) :
    demushkinH2Inflation f
        (trivialCupPairing 2 H (scalarActionZmodTwo_triv H) x y) =
      trivialCupPairing 2 G (scalarActionZmodTwo_triv G)
        (demushkinH1Inflation f x) (demushkinH1Inflation f y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) y
  simp only [trivialCupPairing, demushkinH1Inflation, demushkinH2Inflation]
  rw [cup11_mk_mk, inf2_H2mk, inf1_H1mk, inf1_H1mk, cup11_mk_mk]
  rfl

/-- A surjection between Demushkin groups of equal rank induces an isomorphism on mod-two
degree-one cohomology. -/
theorem demushkinH1Inflation_bijective_of_surjective_of_rank_eq
    (f : ContinuousMonoidHom G H) (hf : Function.Surjective f)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : demushkinRank 2 G = demushkinRank 2 H) :
    Function.Bijective (demushkinH1Inflation f) := by
  letI : Finite (H1 G (ZMod 2)) := hDG.finiteH1
  letI : Finite (H1 H (ZMod 2)) := hDH.finiteH1
  apply (demushkinH1Inflation_injective_of_surjective f hf).bijective_of_nat_card_le
  rw [hDG.card_H1_eq_pow, hDH.card_H1_eq_pow, hrank]

/-- Surjectivity in degree one makes degree-two inflation nonzero between positive-rank
Demushkin groups.  Since both degree-two groups have order two, it is injective. -/
theorem demushkinH2Inflation_injective_of_demushkin_of_H1_surjective
    (f : ContinuousMonoidHom G H)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : 0 < demushkinRank 2 G)
    (hH1 : Function.Surjective (demushkinH1Inflation f)) :
    Function.Injective (demushkinH2Inflation f) := by
  letI : Finite (H1 G (ZMod 2)) := hDG.finiteH1
  letI : Fintype (H1 G (ZMod 2)) := Fintype.ofFinite _
  have hH1card : Fintype.card (H1 G (ZMod 2)) = 2 ^ demushkinRank 2 G := by
    rw [← Nat.card_eq_fintype_card]
    exact hDG.card_H1_eq_pow
  have hH1large : 1 < Fintype.card (H1 G (ZMod 2)) := by
    rw [hH1card]
    exact Nat.one_lt_pow hrank.ne' (by omega)
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hH1large
  let x := a - b
  have hx : x ≠ 0 := sub_ne_zero.mpr hab
  obtain ⟨y, hxy⟩ := hDG.nondegen_left' (scalarActionZmodTwo_triv G) x hx
  obtain ⟨xH, hxH⟩ := hH1 x
  obtain ⟨yH, hyH⟩ := hH1 y
  let cupH := trivialCupPairing 2 H (scalarActionZmodTwo_triv H) xH yH
  have hcupImage : demushkinH2Inflation f cupH =
      trivialCupPairing 2 G (scalarActionZmodTwo_triv G) x y := by
    dsimp only [cupH]
    rw [demushkinH2Inflation_trivialCupPairing, hxH, hyH]
  obtain ⟨w, hw, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (0 : H2 H (ZMod 2))).mp hDH.cardH2
  have hcupw : cupH = w := by
    apply hwuniq cupH
    intro hzero
    apply hxy
    rw [← hcupImage, hzero, map_zero]
  have hfw : demushkinH2Inflation f w ≠ 0 := by
    rw [← hcupw, hcupImage]
    exact hxy
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  by_contra hz0
  have hzw : z = w := hwuniq z hz0
  exact hfw (hzw ▸ hz)

/-- Under the same hypotheses, degree-two inflation is an isomorphism, not merely injective. -/
theorem demushkinH2Inflation_bijective_of_demushkin_of_H1_surjective
    (f : ContinuousMonoidHom G H)
    (hDG : IsDemushkin 2 G) (hDH : IsDemushkin 2 H)
    (hrank : 0 < demushkinRank 2 G)
    (hH1 : Function.Surjective (demushkinH1Inflation f)) :
    Function.Bijective (demushkinH2Inflation f) := by
  letI : Finite (H2 G (ZMod 2)) := Nat.finite_of_card_ne_zero (by
    rw [hDG.cardH2]
    decide)
  apply (demushkinH2Inflation_injective_of_demushkin_of_H1_surjective
    f hDG hDH hrank hH1).bijective_of_nat_card_le
  rw [hDG.cardH2, hDH.cardH2]

end Inflation

end

end GQ2.Dyadic
