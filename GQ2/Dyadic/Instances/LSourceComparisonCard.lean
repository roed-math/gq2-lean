/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleEquiv
import GQ2.Dyadic.Instances.LSourceComparison

/-!
# Cardinality adapter for the L source-comparison package

This file replaces the three explicit degree-two equivalences in
`LSquare.SourceComparisonPackage` by cardinal equalities.  On the primal and dual module
sides, the equivalences are the concrete global relator-obstruction maps.  Consequently their
all-action-compatible-finite-quotient resolver families remain explicit inputs: the target-local
resolvers in `SourceComparisonAt` do not imply these stronger hypotheses.  On the scalar side,
two-torsion and cardinality two give a noncomputable additive orientation.

The Tate cup bijectivity and the three comparison-square assumptions are unchanged.  No
cardinality equality or resolver family is proved here.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

section Adapter

variable {Gamma C A : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A]
  [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Gamma (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [DistribMulAction Gamma (ZMod 2)]
  [ContinuousSMul Gamma (ZMod 2)]
  {iota rel : Type} [Fintype iota] [DecidableEq iota] [Fintype rel]
  {gen : iota → Gamma} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {J : Set iota}

/-- The concrete source-to-word `H²` equivalence used by the cardinal adapter. -/
noncomputable abbrev sourceModuleH2Equiv_of_card_eq
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolveAll : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hcard : Nat.card (H2 Gamma A) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w A)) :
    H2 Gamma A ≃+ WordH2 (fun i ↦ rho (gen i)) w A :=
  globalModuleH2WordEquiv_of_card_eq
    hpres rho hcompat hwildLevel hA₂ hresolveAll hcard

/-- A scalar `H²` orientation obtained only from its explicit two-element cardinality. -/
noncomputable abbrev sourceScalarH2Equiv_of_card_eq
    (hcard : Nat.card (H2 Gamma (ZMod 2)) = Nat.card (ZMod 2)) :
    H2 Gamma (ZMod 2) ≃+ ZMod 2 :=
  addEquivZModTwo_of_card_eq
    (H2_two_torsionG (by decide : ∀ z : ZMod 2, z + z = 0)) hcard

/--
Build the original L source-comparison package from three cardinal equalities.

The two module-valued equivalences use `hresolveAllA` and `hresolveAllDual`, which quantify
over every action-compatible finite quotient.  These are intentionally distinct from, and
strictly stronger than, the one-target resolvers used to construct `SourceComparisonAt`.
The cup and square arguments have exactly the same statements as the corresponding fields of
`SourceComparisonPackage`, after substituting the generated equivalences.
-/
noncomputable def sourceComparisonPackage_of_moduleH2_card_eq
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolveAllA : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hresolveAllDual : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) (ElemDual A) :=
        DistribMulAction.compHom (ElemDual A) rhoV
      ResolvesAt W w (WordLift (ElemDual A) (Gamma ⧸ V.toSubgroup)))
    (hcardA : Nat.card (H2 Gamma A) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w A))
    (hcardDual : Nat.card (H2 Gamma (ElemDual A)) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w (ElemDual A)))
    (hcardScalar : Nat.card (H2 Gamma (ZMod 2)) = Nat.card (ZMod 2))
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hend : IsStokesEndpoint w)
    (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam)
    (h0A : H0 Gamma A ≃+ ↥(heisD0 (A := A) (fun i ↦ rho (gen i))).ker)
    (h1A : H1 Gamma A ≃+ WordH1 (fun i ↦ rho (gen i)) w A)
    (h0Dual : H0 Gamma (ElemDual A) ≃+
      ↥(heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))).ker)
    (h1Dual : H1 Gamma (ElemDual A) ≃+
      WordH1 (fun i ↦ rho (gen i)) w (ElemDual A))
    (cup02_bijective : Function.Bijective (sourceCup02 hpair))
    (cup11_bijective : Function.Bijective (sourceCup11 hpair))
    (cup20_bijective : Function.Bijective (sourceCup20 hpair))
    (square02_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC0 (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))
          (stokesUC0_bijective
            (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))).trans
        (scalarDualTransport
          (sourceModuleH2Equiv_of_card_eq hpres rho hcompatDual hwildLevel
            (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresolveAllDual hcardDual)
          (sourceScalarH2Equiv_of_card_eq hcardScalar)))
          (stokesH0Map
            (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup02 hpair (h0A.symm x))
    (square11_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC1
            (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i)))
            (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))
          (wordH1_target_uc (A := A) (fun i ↦ rho (gen i)) w hr)).trans
        (scalarDualTransport h1Dual (sourceScalarH2Equiv_of_card_eq hcardScalar)))
          (stokesH1Map
            (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend)
            (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup11 hpair (h1A.symm x))
    (square20_commutes : ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC2 (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))))
          (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
            (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))))).trans
        (scalarDualTransport h0Dual (sourceScalarH2Equiv_of_card_eq hcardScalar)))
          (stokesH2Map
            (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup20 hpair
          ((sourceModuleH2Equiv_of_card_eq hpres rho hcompatA hwildLevel hA₂
            hresolveAllA hcardA).symm x)) :
    SourceComparisonPackage (fun i ↦ rho (gen i)) w hr hend hpair
      h0A h1A h0Dual h1Dual where
  h2A := sourceModuleH2Equiv_of_card_eq
    hpres rho hcompatA hwildLevel hA₂ hresolveAllA hcardA
  h2Dual := sourceModuleH2Equiv_of_card_eq
    hpres rho hcompatDual hwildLevel
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hresolveAllDual hcardDual
  h2Scalar := sourceScalarH2Equiv_of_card_eq hcardScalar
  cup02_bijective := cup02_bijective
  cup11_bijective := cup11_bijective
  cup20_bijective := cup20_bijective
  square02_commutes := square02_commutes
  square11_commutes := square11_commutes
  square20_commutes := square20_commutes

end Adapter

end

end GQ2.Dyadic.LSquare
