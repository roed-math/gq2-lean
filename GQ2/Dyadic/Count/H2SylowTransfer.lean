/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SplitRightExact
import Mathlib.GroupTheory.Sylow

/-!
# Odd-index transfer reduction for degree-two right exactness

For an open subgroup `U ≤ G`, the classical restriction/corestriction argument reduces
surjectivity of a coefficient map on `H²(G,-)` to surjectivity on `H²(U,-)` whenever
`[G:U]` is odd and the coefficients have exponent two.  This file formalizes the diagram
chase independently of a construction of corestriction.

The current continuous-cohomology API has restriction in degree two, but its only explicit
degree-two corestriction is `Corestriction.cor2Fun`, for trivial `ZMod 2` coefficients.  The
structure `H2RestrictionTransferSquare` therefore records exactly the two missing
general-coefficient properties: naturality in coefficients and
`cor ∘ res = [G:U]`.  Once those are supplied, the reduction is unconditional.

The final section identifies the relevant subgroup as the preimage of a Sylow `2`-subgroup
of a finite surjective action image and proves that this preimage is open of odd index.
-/

namespace GQ2.ContCoh

noncomputable section

variable {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-! ## Elementary coefficient and restriction calculations -/

/-- Degree-two continuous cohomology inherits exponent two from its coefficients. -/
theorem H2.add_self_eq_zero_of_coeff (hB₂ : ∀ b : B, b + b = 0)
    (x : H2 G B) : x + x = 0 := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := B) x
  rw [← map_add]
  have hz : z + z = 0 := by
    apply Subtype.ext
    funext p
    exact hB₂ (z.1 p)
  rw [hz, map_zero]

/-- Restriction computes by restricting a represented cocycle. -/
theorem res2_H2mk (U : Subgroup G) (z : Z2 G A) :
    res2 G A U (H2mk G A z) =
      H2mk U A
        (Z2comap (subgroupIncl G U) (AddMonoidHom.id A) continuous_id
          (fun _ _ ↦ rfl) z) :=
  rfl

/-- Restriction in degree two commutes with a coefficient map. -/
theorem mapCoeff2_res2
    (U : Subgroup G) (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (x : H2 G A) :
    mapCoeff2 g hgC (fun (u : U) a ↦ hg u.1 a) (res2 G A U x) =
      res2 G B U (mapCoeff2 g hgC hg x) := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := A) x
  rw [res2_H2mk, mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff, res2_H2mk]
  apply congrArg (H2mk U B)
  apply Subtype.ext
  rfl

/-! ## The abstract restriction/corestriction square -/

/-- The part of degree-two transfer needed for a single coefficient quotient.

No transfer is postulated globally: the two additive maps and the two standard identities are
local data for `A → B`.  A future general-coefficient corestriction construction should produce
this structure canonically. -/
structure H2RestrictionTransferSquare
    (U : Subgroup G) (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a) where
  /-- Corestriction for the source coefficient. -/
  corSource : H2 U A →+ H2 G A
  /-- Corestriction for the target coefficient. -/
  corTarget : H2 U B →+ H2 G B
  /-- Corestriction is natural in the coefficient map. -/
  naturality : ∀ x : H2 U A,
    mapCoeff2 g hgC hg (corSource x) =
      corTarget (mapCoeff2 g hgC (fun (u : U) a ↦ hg u.1 a) x)
  /-- Corestriction after restriction is multiplication by the subgroup index. -/
  cor_res_target : ∀ y : H2 G B,
    corTarget (res2 G B U y) = U.index • y

/-- Restriction to an odd-index subgroup detects degree-two coefficient right exactness.

Given a lift after restriction, corestrict it.  Naturality moves the coefficient map past
corestriction, and `cor ∘ res = [G:U]` returns the original class because odd multiplication
is the identity on an exponent-two group. -/
theorem H2RightExactAt.of_oddIndex_restriction
    (U : Subgroup G) (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hB₂ : ∀ b : B, b + b = 0) (hodd : Odd U.index)
    (T : H2RestrictionTransferSquare U g hgC hg)
    (hU : H2RightExactAt (G := U) g hgC (fun u a ↦ hg u.1 a)) :
    H2RightExactAt g hgC hg := by
  intro y
  obtain ⟨x, hx⟩ := hU (res2 G B U y)
  refine ⟨T.corSource x, ?_⟩
  rw [T.naturality, hx, T.cor_res_target]
  exact GQ2.odd_nsmul_eq_self (H2.add_self_eq_zero_of_coeff hB₂) hodd y

/-! ## Preimage of a Sylow subgroup of the finite action image -/

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The subgroup of `G` lying over a chosen Sylow `2`-subgroup of a finite quotient. -/
def sylowTwoPreimage (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) : Subgroup G :=
  P.1.comap rho.toMonoidHom

/-- A Sylow preimage is open when the finite quotient is discrete. -/
theorem isOpen_sylowTwoPreimage (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) :
    IsOpen ((sylowTwoPreimage rho P : Subgroup G) : Set G) := by
  change IsOpen (rho ⁻¹' (P.1 : Set C))
  exact (isOpen_discrete (P.1 : Set C)).preimage rho.continuous_toFun

/-- Under a surjection, the index of the Sylow preimage is the Sylow index. -/
theorem sylowTwoPreimage_index (rho : ContinuousMonoidHom G C)
    (hrho : Function.Surjective rho) (P : Sylow 2 C) :
    (sylowTwoPreimage rho P).index = P.index :=
  Subgroup.index_comap_of_surjective P.1 hrho

/-- The preimage of a Sylow `2`-subgroup has odd index. -/
theorem odd_sylowTwoPreimage_index (rho : ContinuousMonoidHom G C)
    (hrho : Function.Surjective rho) (P : Sylow 2 C) :
    Odd (sylowTwoPreimage rho P).index := by
  rw [sylowTwoPreimage_index rho hrho P]
  exact Nat.not_even_iff_odd.mp (fun heven ↦ P.not_dvd_index heven.two_dvd)

/-- Sylow-transfer reduction for a finite surjective action image.

This is the formal endpoint of the reduction: it leaves only right exactness on the open
preimage of the Sylow `2`-subgroup and the standard general-coefficient transfer square. -/
theorem H2RightExactAt.of_sylowTwoPreimage
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho) (P : Sylow 2 C)
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hB₂ : ∀ b : B, b + b = 0)
    (T : H2RestrictionTransferSquare (sylowTwoPreimage rho P) g hgC hg)
    (hP : H2RightExactAt (G := sylowTwoPreimage rho P) g hgC
      (fun u a ↦ hg u.1 a)) :
    H2RightExactAt g hgC hg :=
  H2RightExactAt.of_oddIndex_restriction (sylowTwoPreimage rho P) g hgC hg hB₂
    (odd_sylowTwoPreimage_index rho hrho P) T hP

/-- A bundled witness for the two genuinely subgroup-local inputs in the Sylow reduction:
general-coefficient transfer and right exactness on the Sylow preimage. -/
structure SylowTwoH2RightExactWitness
    (rho : ContinuousMonoidHom G C) (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a) where
  /-- The selected Sylow subgroup of the finite image. -/
  sylow : Sylow 2 C
  /-- The restriction/corestriction square for its preimage. -/
  transfer : H2RestrictionTransferSquare (sylowTwoPreimage rho sylow) g hgC hg
  /-- Right exactness after restricting the acting group to that preimage. -/
  rightExact : H2RightExactAt (G := sylowTwoPreimage rho sylow) g hgC
    (fun u a ↦ hg u.1 a)

/-- A bundled Sylow witness proves right exactness for the original acting group. -/
theorem SylowTwoH2RightExactWitness.toH2RightExact
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho)
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hB₂ : ∀ b : B, b + b = 0)
    (W : SylowTwoH2RightExactWitness rho g hgC hg) :
    H2RightExactAt g hgC hg :=
  H2RightExactAt.of_sylowTwoPreimage rho hrho W.sylow g hgC hg hB₂
    W.transfer W.rightExact

end

end GQ2.ContCoh
