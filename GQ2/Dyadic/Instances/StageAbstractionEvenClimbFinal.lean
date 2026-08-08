/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRawToBracket

/-!
# W52-EV3FB §3: the even climb composed at the supplies

The composition of this wave's two files against the committed reduction
`evenKernel_residualSupply_of_supplies`, landing `EvenClimbResidualSupply` per field and per
branch with boundary one of `StageAbstractionEvenKernelAdapted.lean` §3 discharged.

## Why this lane stops at the supplies

The obvious next step would be to restate `evenAssembly_orientedEquiv{N,M}`
(`StageAbstractionEvenAssembly.lean` §3) with their residual hypothesis `Hres` removed.  That
step is deliberately **not** taken here.  The W52-RANGE lane proved the range identity and in
doing so machine-checked that the `Hrange` hypothesis of those endpoints, which quantifies
`MonoidHom.range chiCycKTwo = imChi{N,M} α` over *every* `K` at one fixed `α`, is inconsistent:
an odd-degree `K` has full range.  The endpoints are therefore vacuous as stated, and a
corollary of them would inherit the vacuity while looking like progress.

So this file ends at the level where its statements are honest, namely per `K`.
`evenClimbFinal_residualSupply{N,M}` mention no `Hrange` at all; they are exactly the inputs
the endpoint re-cut needs, and they survive that re-cut unchanged because they are per-`G`,
per-`chi` statements about a single field.

## What replaced `Hres`

`StageAbstractionEvenKernelAdapted.lean` §3 reduced `EvenClimbResidualSupply` to three inputs:
the derivation criterion, the relator kill, and the raw-to-bracket upgrade, the first and third
being this lane's ticket.  After `StageAbstractionEvenDerivKer.lean` the criterion is a
theorem, so it is gone, and what remains is

* `Hfam`, a coordinate derivation family at every stage whose functionals annihilate the
  current defect;
* `Hup`, the committed `EvenKernelRawToBracketSupply`.

**This is the same shape as the odd route's endpoint.**  The L template's
`nonempty_orientedEquiv_oddDegree_of_family_of_digitRepair` carries precisely two inputs of
this kind, `Hfam` and `Hrepair`, and constructs neither.

`StageAbstractionEvenRawToBracket.lean` §2 offers the route to `Hup`
(`evenRawTo_supply_of_neutral`), and its §4 prices that route: it forces the character
filtration not to drop between consecutive layers, one digit deeper than the committed even
bound `evenSharp_map_le_deep` provides.  That price is real and is not paid by anything in this
lane, which is why `Hup` is carried rather than discharged.

## Numbering

1. the residual supply from the discharged criterion;
2. the two branch specialisations at the field.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The residual supply from the discharged criterion

Boundary one is now supplied by `evenDeriv_derivKerCriterion`, so a family need only be
exhibited together with its relator kill.  Everything else is the committed reduction. -/

section Residual

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **The even residual supply, with boundary one discharged.**  The criterion of
`StageAbstractionEvenKernelAdapted.lean` §3 is no longer a hypothesis: it is
`evenDeriv_derivKerCriterion`, fed the two mod-`4` facts of that file's §1. -/
theorem evenClimbFinal_residualSupply
    (hfg : ∃ t : Finset G, (Subgroup.closure (t : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple W v G chi k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (hv1 : ∀ i : Fin (MarkedCore.coreRank h), i ≠ 1 →
      (2 : ℤ_[2]) ^ 2 ∣ ((v i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (hvd : (2 : ℤ_[2]) ^ 2 ∣ ((v 0 * v 1 : ℤ_[2]ˣ) : ℤ_[2]) + 1)
    (Hup : EvenKernelRawToBracketSupply s W v G chi) :
    EvenClimbResidualSupply s W v G chi := by
  refine evenKernel_residualSupply_of_supplies (evenKernel_rawDefectSupply_of_family ?_) Hup
  intro k hk T
  obtain ⟨F, Hrel⟩ := Hfam k hk T
  exact ⟨F, evenDeriv_derivKerCriterion hfg hpro hk F hv1 hvd, Hrel⟩

end Residual

/-! ## §2 The two branch specialisations at the field

At `G = G_K(2)` the two hypotheses `hfg` and `hpro` of §1 are the committed
`LSquare.maxProTwoGalK_isTopologicallyFinGen` and `isProP_maxProPQuotient`, and the two mod-`4`
facts are `StageAbstractionEvenKernelAdapted.lean` §1 on each branch.  Note that `hα : 2 ≤ α`
is consumed on both branches, on the `N` side for the diagonal partner `nUnit α ≡ −1 (mod 4)`
and on the `M` side for `mUnit α ≡ 1 (mod 4)` at index `3`. -/

section Branches

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
variable [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N` branch residual supply**, modulo a family and the raw-to-bracket upgrade. -/
theorem evenClimbFinal_residualSupplyN {α h : ℕ} (hα : 2 ≤ α)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hup : EvenKernelRawToBracketSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenClimbResidualSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenClimbFinal_residualSupply (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient Hfam evenKernel_vN_sub_one_dvd_four
    (evenKernel_vN_diagonal_add_one_dvd_four hα) Hup

/-- **The `M` branch residual supply**, the same composition against the `M` value table. -/
theorem evenClimbFinal_residualSupplyM {α h : ℕ} (hα : 2 ≤ α)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hup : EvenKernelRawToBracketSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenClimbResidualSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenClimbFinal_residualSupply (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient Hfam (evenKernel_vM_sub_one_dvd_four hα)
    evenKernel_vM_diagonal_add_one_dvd_four Hup

end Branches

end

end GQ2.Dyadic.StageGeneric

/-! ## §4 Axiom pins

Every public declaration of this file, printed, together with the two committed endpoints this
file restates, so that the comparison is on the page.  §1 is arithmetic-free and prints std-3;
§2 acquires exactly one census axiom, `absGalQ2_isTopologicallyFinitelyGenerated`, from
`maxProTwoGalK_isTopologicallyFinGen`, which is the same axiom the odd route acquires at the
same station and the only one this lane may acquire. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the residual supply
#print axioms evenClimbFinal_residualSupply

-- §2 the branch specialisations
#print axioms evenClimbFinal_residualSupplyN
#print axioms evenClimbFinal_residualSupplyM

end AxiomPins
