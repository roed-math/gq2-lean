/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SectionRefinementCoordinates

/-!
# The concrete finite bar--universal-Fox chain homotopy

The forward and reverse finite comparison maps already constructed through degree two can be
completed to an explicit chain homotopy in those degrees without any one-relator input.  This
file adds the third finite bar chain module, its boundary and canonical contraction.  It then
proves

`∂₃ H₂ + H₁ ∂₂ + forward₂ reverse₂ = id`

on every bar two-chain, where `reverse₂` lands in the full free relation kernel.  All maps are
specialized at the end to the actual improved-square quotient marking.

This is the maximal automatic part of the reverse comparison.  Passing from the full relation
kernel to the single improved relator, compatibly over all finite quotients, is isolated in
`SqFiniteInputCompletedSyzygyBoundaryAt`.  It is the minimal completed-syzygy projection of the
existing eventual package and contains neither a cocycle primitive nor any cohomological
vanishing assertion.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

variable {Q I : Type} [Group Q]

/-! ## Bar degree three and the canonical contraction -/

/-- Degree three of the finite mod-two inhomogeneous bar resolution. -/
abbrev FiniteModTwoBarChainThree (Q : Type) :=
  RegularModTwoRelationModule Q (Q × Q × Q)

/-- The bar boundary `B₃ → B₂` in characteristic two. -/
def finiteModTwoBarBoundaryThree :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × (Q × Q × Q) =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (p.1 * p.2.1, (p.2.2.1, p.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1 * p.2.2.1, p.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1, p.2.2.1 * p.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1, p.2.2.1)) 1)

@[simp] theorem finiteModTwoBarBoundaryThree_single
    (g q r s : Q) (a : ZMod 2) :
    finiteModTwoBarBoundaryThree
        (Finsupp.single (g, (q, r, s)) a) =
      Finsupp.single (g * q, (r, s)) a +
        Finsupp.single (g, (q * r, s)) a +
        Finsupp.single (g, (q, r * s)) a +
        Finsupp.single (g, (q, r)) a := by
  classical
  rw [finiteModTwoBarBoundaryThree, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_add, smul_eq_mul]

/-- The second bar chain identity `∂₂∂₃ = 0`. -/
theorem finiteModTwoBarBoundaryTwo_comp_boundaryThree :
    (finiteModTwoBarBoundaryTwo (Q := Q)).comp
        (finiteModTwoBarBoundaryThree (Q := Q)) = 0 := by
  classical
  apply LinearMap.ext
  intro c
  change finiteModTwoBarBoundaryTwo (finiteModTwoBarBoundaryThree c) = 0
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q, r, s⟩
      simp only [map_add, ih, add_zero,
        finiteModTwoBarBoundaryThree_single,
        finiteModTwoBarBoundaryTwo_single, mul_assoc]
      let A : FiniteModTwoBarChainOne Q := Finsupp.single (g * (q * r), s) a
      let B : FiniteModTwoBarChainOne Q := Finsupp.single (g * q, r * s) a
      let C : FiniteModTwoBarChainOne Q := Finsupp.single (g * q, r) a
      let D : FiniteModTwoBarChainOne Q := Finsupp.single (g, q * (r * s)) a
      let E : FiniteModTwoBarChainOne Q := Finsupp.single (g, q * r) a
      let F : FiniteModTwoBarChainOne Q := Finsupp.single (g, q) a
      change (A + B + C) + (A + D + E) + (B + D + F) + (C + E + F) = 0
      calc
        (A + B + C) + (A + D + E) + (B + D + F) + (C + E + F) =
            (A + A) + (B + B) + (C + C) +
              (D + D) + (E + E) + (F + F) := by abel
        _ = 0 := by
          have hA : A + A = 0 := regularModTwoRelationModule_add_self Q Q A
          have hB : B + B = 0 := regularModTwoRelationModule_add_self Q Q B
          have hC : C + C = 0 := regularModTwoRelationModule_add_self Q Q C
          have hD : D + D = 0 := regularModTwoRelationModule_add_self Q Q D
          have hE : E + E = 0 := regularModTwoRelationModule_add_self Q Q E
          have hF : F + F = 0 := regularModTwoRelationModule_add_self Q Q F
          rw [hA, hB, hC, hD, hE, hF]
          simp

/-- Insert a bar two-cell `g[q|r]` as the bar three-cell `[g|q|r]`. -/
def finiteModTwoBarContractTwo :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainThree Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × (Q × Q) =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (1, (p.1, p.2.1, p.2.2)) 1)

@[simp] theorem finiteModTwoBarContractTwo_single
    (g q r : Q) (a : ZMod 2) :
    finiteModTwoBarContractTwo (Finsupp.single (g, (q, r)) a) =
      Finsupp.single (1, (g, q, r)) a := by
  classical
  rw [finiteModTwoBarContractTwo, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The all-chain contraction identity `∂₃s₂ + s₁∂₂ = id` on bar degree two. -/
theorem finiteModTwoBar_contracting_identity_two
    (c : FiniteModTwoBarChainTwo Q) :
    finiteModTwoBarBoundaryThree (finiteModTwoBarContractTwo c) +
        finiteModTwoBarContractOne (finiteModTwoBarBoundaryTwo c) = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q, r⟩
      simp only [map_add, finiteModTwoBarContractTwo_single,
        finiteModTwoBarBoundaryThree_single,
        finiteModTwoBarBoundaryTwo_single,
        finiteModTwoBarContractOne_single, one_mul]
      let A : FiniteModTwoBarChainTwo Q := Finsupp.single (1, (g * q, r)) a
      let B : FiniteModTwoBarChainTwo Q := Finsupp.single (1, (g, q * r)) a
      let C : FiniteModTwoBarChainTwo Q := Finsupp.single (1, (g, q)) a
      let S : FiniteModTwoBarChainTwo Q := Finsupp.single (g, (q, r)) a
      let T : FiniteModTwoBarChainTwo Q :=
        finiteModTwoBarBoundaryThree (finiteModTwoBarContractTwo c)
      let U : FiniteModTwoBarChainTwo Q :=
        finiteModTwoBarContractOne (finiteModTwoBarBoundaryTwo c)
      change S + A + B + C + T + (A + B + C + U) = S + c
      calc
        S + A + B + C + T + (A + B + C + U) =
            S + (T + U) + (A + A) + (B + B) + (C + C) := by abel
        _ = S + (T + U) := by
          rw [regularModTwoRelationModule_add_self,
            regularModTwoRelationModule_add_self,
            regularModTwoRelationModule_add_self]
          simp
        _ = S + c := by rw [ih]

/-! ## The universal-Fox forward--reverse homotopy -/

/-- The degree-one error `forward₁ reverse₁ + id`. -/
def finiteBarForwardReverseDifferenceOne
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainOne Q :=
  (finiteMarkedToBarOne m).comp (finiteBarToMarkedOne m heval) + LinearMap.id

/-- The degree-one forward--reverse error is a bar cycle. -/
theorem finiteBarForwardReverseDifferenceOne_boundary
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarChainOne Q) :
    finiteModTwoBarBoundaryOne (finiteBarForwardReverseDifferenceOne m heval c) = 0 := by
  rw [finiteBarForwardReverseDifferenceOne, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, map_add,
    finiteMarkedToBarOne_boundary, finiteBarToMarkedOne_boundary]
  exact regularModTwoRelationModule_add_self Q Unit _

/-- Fill the degree-one forward--reverse error by the canonical contraction. -/
def finiteBarForwardReverseHomotopyOne
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
  (finiteModTwoBarContractOne (Q := Q)).comp
    (finiteBarForwardReverseDifferenceOne m heval)

/-- The boundary of the degree-one homotopy is exactly `forward₁ reverse₁ + id`. -/
theorem finiteBarForwardReverseHomotopyOne_boundary
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarChainOne Q) :
    finiteModTwoBarBoundaryTwo (finiteBarForwardReverseHomotopyOne m heval c) =
      finiteMarkedToBarOne m (finiteBarToMarkedOne m heval c) + c := by
  have hcontract := finiteModTwoBar_contracting_identity
    (Q := Q) (finiteBarForwardReverseDifferenceOne m heval c)
  rw [finiteBarForwardReverseDifferenceOne_boundary m heval c,
    map_zero, add_zero] at hcontract
  simpa [finiteBarForwardReverseHomotopyOne,
    finiteBarForwardReverseDifferenceOne] using hcontract

/-- The forward degree-two map for the presentation with one generator for every element of the
full free relation kernel. -/
def finiteUniversalRelationToBarTwo (m : I → Q) :
    RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo Q :=
  finiteFoxToBarTwo m (fun r : FreeRelationKernel m ↦ r.1)

/-- The universal relation-to-bar map has the expected boundary. -/
theorem finiteUniversalRelationToBarTwo_boundary
    (m : I → Q) (c : RegularModTwoRelationModule Q (FreeRelationKernel m)) :
    finiteModTwoBarBoundaryTwo (finiteUniversalRelationToBarTwo m c) =
      finiteMarkedToBarOne m ((finiteUniversalRelationFoxBoundary m).map c) := by
  exact finiteFoxToBarTwo_boundary m (fun r : FreeRelationKernel m ↦ r.1)
    (fun r ↦ r.2) c

/-- The degree-two error before applying the canonical contraction. -/
def finiteBarForwardReverseDifferenceTwo
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
  LinearMap.id +
    (finiteUniversalRelationToBarTwo m).comp
      (finiteBarToUniversalRelationTwo m heval) +
    (finiteBarForwardReverseHomotopyOne m heval).comp finiteModTwoBarBoundaryTwo

/-- The degree-two forward--reverse error is a bar cycle. -/
theorem finiteBarForwardReverseDifferenceTwo_boundary
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarChainTwo Q) :
    finiteModTwoBarBoundaryTwo (finiteBarForwardReverseDifferenceTwo m heval c) = 0 := by
  simp only [finiteBarForwardReverseDifferenceTwo, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, map_add]
  rw [finiteUniversalRelationToBarTwo_boundary,
    ← finiteBarToMarkedOne_boundaryTwo,
    finiteBarForwardReverseHomotopyOne_boundary]
  let A : FiniteModTwoBarChainOne Q := finiteModTwoBarBoundaryTwo c
  let B : FiniteModTwoBarChainOne Q :=
    finiteMarkedToBarOne m (finiteBarToMarkedOne m heval A)
  change A + B + (B + A) = 0
  calc
    A + B + (B + A) = (A + A) + (B + B) := by abel
    _ = 0 := by
      rw [regularModTwoRelationModule_add_self,
        regularModTwoRelationModule_add_self]
      simp

/-- Fill the degree-two error by the canonical bar contraction. -/
def finiteBarForwardReverseHomotopyTwo
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainThree Q :=
  (finiteModTwoBarContractTwo (Q := Q)).comp
    (finiteBarForwardReverseDifferenceTwo m heval)

/-- **Concrete low-degree chain-homotopy identity.** The universal-Fox forward--reverse
comparison is chain-homotopic to the identity on every bar two-chain. -/
theorem finiteBarForwardReverseHomotopyTwo_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarChainTwo Q) :
    finiteModTwoBarBoundaryThree (finiteBarForwardReverseHomotopyTwo m heval c) +
        finiteBarForwardReverseHomotopyOne m heval
          (finiteModTwoBarBoundaryTwo c) +
        finiteUniversalRelationToBarTwo m
          (finiteBarToUniversalRelationTwo m heval c) = c := by
  have hcontract := finiteModTwoBar_contracting_identity_two
    (Q := Q) (finiteBarForwardReverseDifferenceTwo m heval c)
  rw [finiteBarForwardReverseDifferenceTwo_boundary m heval c,
    map_zero, add_zero] at hcontract
  change finiteModTwoBarBoundaryThree
      (finiteModTwoBarContractTwo
        (finiteBarForwardReverseDifferenceTwo m heval c)) + _ + _ = c
  rw [hcontract]
  simp only [finiteBarForwardReverseDifferenceTwo, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  let A : FiniteModTwoBarChainTwo Q := c
  let B : FiniteModTwoBarChainTwo Q :=
    finiteUniversalRelationToBarTwo m
      (finiteBarToUniversalRelationTwo m heval c)
  let C : FiniteModTwoBarChainTwo Q :=
    finiteBarForwardReverseHomotopyOne m heval
      (finiteModTwoBarBoundaryTwo c)
  change A + B + C + C + B = A
  calc
    A + B + C + C + B = A + (B + B) + (C + C) := by abel
    _ = A := by
      rw [regularModTwoRelationModule_add_self,
        regularModTwoRelationModule_add_self]
      simp

/-- Explicit finite chain comparison data through bar degree two. -/
structure FiniteUniversalBarFoxChainHomotopy
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) where
  homotopyOne : FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q
  homotopyTwo : FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainThree Q
  homotopyOne_boundary : ∀ c,
    finiteModTwoBarBoundaryTwo (homotopyOne c) =
      finiteMarkedToBarOne m (finiteBarToMarkedOne m heval c) + c
  homotopyTwo_identity : ∀ c,
    finiteModTwoBarBoundaryThree (homotopyTwo c) +
        homotopyOne (finiteModTwoBarBoundaryTwo c) +
        finiteUniversalRelationToBarTwo m
          (finiteBarToUniversalRelationTwo m heval c) = c

/-- The previously constructed forward and reverse maps satisfy the explicit low-degree finite
chain-homotopy interface. -/
def finiteUniversalBarFoxChainHomotopy
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteUniversalBarFoxChainHomotopy m heval where
  homotopyOne := finiteBarForwardReverseHomotopyOne m heval
  homotopyTwo := finiteBarForwardReverseHomotopyTwo m heval
  homotopyOne_boundary := finiteBarForwardReverseHomotopyOne_boundary m heval
  homotopyTwo_identity := finiteBarForwardReverseHomotopyTwo_identity m heval

/-- The concrete universal-Fox chain homotopy at an actual improved-square quotient. -/
def sqOpenQuotientUniversalBarFoxChainHomotopy
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :
    FiniteUniversalBarFoxChainHomotopy
      (sqOpenQuotientMarking h V)
      (sqOpenQuotientFreeEvaluation_surjective h V) :=
  finiteUniversalBarFoxChainHomotopy
    (sqOpenQuotientMarking h V)
    (sqOpenQuotientFreeEvaluation_surjective h V)

/-- Regression form of the degree-two homotopy identity for the actual improved-square
quotient marking and the concrete maps already constructed in the forward/reverse files. -/
theorem sqOpenQuotientBarForwardReverseHomotopyTwo_identity
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (c : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ V.toSubgroup)) :
    finiteModTwoBarBoundaryThree
        (finiteBarForwardReverseHomotopyTwo
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V) c) +
      finiteBarForwardReverseHomotopyOne
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (finiteModTwoBarBoundaryTwo c) +
      finiteUniversalRelationToBarTwo (sqOpenQuotientMarking h V)
          (sqOpenQuotientBarToUniversalRelationTwo h V c) = c :=
  finiteBarForwardReverseHomotopyTwo_identity
    (sqOpenQuotientMarking h V)
    (sqOpenQuotientFreeEvaluation_surjective h V) c

/-! ## Exact separation of the remaining completed input -/

/-- The smallest completed relation-syzygy datum in the eventual comparison: a compatible
finite family and the statement that its actual completed Fox boundary factors through `d³`.
This is independent of the reconstruction choice and contains no primitive. -/
structure SqFiniteInputCompletedSyzygyBoundaryAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  relationSyzygy : SqCompatibleFiniteRelationSyzygyAt h V
  boundaryDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))
  boundary_relationSyzygy : ∀ c,
    (sqCompletedModTwoFoxBoundary h).map (relationSyzygy.toCompleted c) =
      boundaryDefect (finiteModTwoBarDThree _ c)

/-- Every finite coordinate of the residual completed identity is the literal improved-square
Fox row.  Thus the remaining syzygy field cannot be discharged by an unrelated finite
presentation. -/
theorem SqFiniteInputCompletedSyzygyBoundaryAt.finite_boundary_relationSyzygy
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (B : SqFiniteInputCompletedSyzygyBoundaryAt h V)
    (U : OpenNormalSubgroup (DSq h : Type))
    (c : FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)) :
    (sqFiniteLevelModTwoFoxBoundary h
        (fun i ↦ QuotientGroup.mk' U.toSubgroup (sqGen h i))).map
        (B.relationSyzygy.coordinate U c) =
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U
        (B.boundaryDefect (finiteModTwoBarDThree _ c)) := by
  have hboundary := congrArg
    (fun z : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)) ↦
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U z)
    (B.boundary_relationSyzygy c)
  rw [sqCompletedModTwoFoxBoundary_coordinate] at hboundary
  rw [B.relationSyzygy.coordinate_toCompleted] at hboundary
  exact hboundary

/-- Extract the completed syzygy/boundary part of an eventual comparison. -/
def SqFiniteInputEventualBarFoxCorrectionAt.syzygyBoundary
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputEventualBarFoxCorrectionAt h V) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V where
  relationSyzygy := C.relationSyzygy
  boundaryDefect := C.boundaryDefect
  boundary_relationSyzygy := C.boundary_relationSyzygy

end

end GQ2.Dyadic.Count
