/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Frozen
import GQ2.Dyadic.Count.HTwoModuleFlexible
import GQ2.Dyadic.Instances.LSourceComparisonCard

/-!
# The flexible module-valued H² comparison for the L row

The frozen `L` presentation has an honest resolver at every finite target `Q`: use
`lSqFam h q (omega2Exp (Nat.card Q))`.  Lagrange's theorem supplies the only
arithmetic input.  In particular, at the action-compatible quotient `Γ/V` the local
target is `WordLift A (Γ/V)`, so its resolver exponent may depend on `V` and `A`.

`lFlexibleResolverSystem` compares those quotient-dependent words with one supplied
target-local resolver.  The comparison is semantic, through `PWord.eval` naturality;
there is no fixed-exponent all-level hypothesis and no exponent-invariance lemma.
The resulting L-specific map is injective.  An explicit equality of finite
cardinalities upgrades that same map to the additive equivalence used by the source
comparison package.  No cardinal equality or Tate-cup statement is proved here.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

/-! ## Quotient-local L resolvers -/

/-- Every finite group target has the canonical cardinality-level L resolver. -/
theorem resolvesAt_lSqFam_natCard {Q : Type} [Group Q] [TopologicalSpace Q]
    [DiscreteTopology Q] [Finite Q] (h q : ℕ) :
    ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q (omega2Exp (Nat.card Q))) Q :=
  resolvesAt_lSqFam Nat.card_pos.ne' (fun x ↦ orderOf_dvd_natCard x) h q

/-- Existential form of `resolvesAt_lSqFam_natCard`, convenient for the flexible API. -/
theorem exists_lSqFam_resolver {Q : Type} [Group Q] [TopologicalSpace Q]
    [DiscreteTopology Q] [Finite Q] (h q : ℕ) :
    ∃ word : Fin 2 → FreeGroup (Generator (2 * h + 1)),
      ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h)) word Q :=
  ⟨Certificates.LSqStokes.lSqFam h q (omega2Exp (Nat.card Q)),
    resolvesAt_lSqFam_natCard h q⟩

section LMap

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)

/-- The L flexible resolver system.  At level `V` it selects the cardinality-level
resolver for `WordLift A (GammaL ⧸ V)` and compares it with `hres` at the fixed target.
The target exponent `e` is never required to work at any other quotient. -/
noncomputable def lFlexibleResolverSystem
    (rho : ContinuousMonoidHom GammaL C)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C)) :
    ∀ (V : OpenNormalSubgroup GammaL)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A)
        (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup
          (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i)) := by
  apply flexibleResolverSystemOfResolvers rho (fun _ ↦ rfl) hres
  intro V hV
  let rhoV := quotientActionHom rho V hV
  letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  exact exists_lSqFam_resolver h q

/-- The L-specific arbitrary-coefficient map from continuous H² to the fixed target
word cokernel, built from only the target-local resolver `hres`. -/
noncomputable def lModuleH2WordFlexible
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C)) :
    H2 GammaL A →+
      WordH2
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e) A :=
  globalModuleH2WordFlexible
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) hA₂
      (lFlexibleResolverSystem rho hres)

/-- Representative regression: the L map reads the canonical global relator
obstruction and then passes to the target word cokernel. -/
@[simp] theorem lModuleH2WordFlexible_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C))
    (f : Z2 GammaL A) :
    lModuleH2WordFlexible rho hcompat hA₂ hres (H2mk GammaL A f) =
      QuotientAddGroup.mk'
        (heisD1 (A := A)
          (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
          (Certificates.LSqStokes.lSqFam h q e)).range
        (moduleObsFam (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
          (gammaGen (2 * h + 1) q (Words.LSq.lSqW h)) rho hcompat f) := rfl

/-- The flexible L module-valued H² word map is injective. -/
theorem lModuleH2WordFlexible_injective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C)) :
    Function.Injective (lModuleH2WordFlexible rho hcompat hA₂ hres) :=
  globalModuleH2WordFlexible_injective
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) hA₂
      (lFlexibleResolverSystem rho hres)

/-- Equal cardinality makes the concrete flexible L map bijective. -/
theorem lModuleH2WordFlexible_bijective_of_card_eq
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C))
    (hcard : Nat.card (H2 GammaL A) =
      Nat.card (WordH2
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e) A)) :
    Function.Bijective (lModuleH2WordFlexible rho hcompat hA₂ hres) := by
  let f := lModuleH2WordFlexible rho hcompat hA₂ hres
  have hinj : Function.Injective f :=
    lModuleH2WordFlexible_injective rho hcompat hA₂ hres
  letI : Finite (H2 GammaL A) := Finite.of_injective f hinj
  letI : Fintype (H2 GammaL A) := Fintype.ofFinite _
  letI : Fintype (WordH2
      (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
      (Certificates.LSqStokes.lSqFam h q e) A) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
  simpa only [Nat.card_eq_fintype_card] using hcard

/-- The additive H² equivalence used by the L source comparison, conditional only on
the explicit source/target cardinal equality and the supplied target-local resolver. -/
noncomputable def lModuleH2EquivFlexible_of_card_eq
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C))
    (hcard : Nat.card (H2 GammaL A) =
      Nat.card (WordH2
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e) A)) :
    H2 GammaL A ≃+
      WordH2
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e) A :=
  AddEquiv.ofBijective (lModuleH2WordFlexible rho hcompat hA₂ hres)
    (lModuleH2WordFlexible_bijective_of_card_eq rho hcompat hA₂ hres hcard)

/-- Representative regression for the cardinality-upgraded L equivalence. -/
@[simp] theorem lModuleH2EquivFlexible_of_card_eq_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) (WordLift A C))
    (hcard : Nat.card (H2 GammaL A) =
      Nat.card (WordH2
        (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (Certificates.LSqStokes.lSqFam h q e) A))
    (f : Z2 GammaL A) :
    lModuleH2EquivFlexible_of_card_eq rho hcompat hA₂ hres hcard (H2mk GammaL A f) =
      QuotientAddGroup.mk'
        (heisD1 (A := A)
          (fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
          (Certificates.LSqStokes.lSqFam h q e)).range
        (moduleObsFam (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
          (gammaGen (2 * h + 1) q (Words.LSq.lSqW h)) rho hcompat f) := rfl

end LMap

end

end GQ2.Dyadic.LSquare
