/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
import GQ2.Dyadic.Instances.GammaRPWordNielsenElementary

namespace GQ2.Dyadic


/-!
# A mixed Nielsen repair of the head-handle pair source

The pure pair exchange has a uniform Stokes radical when the original `sigma` action is
trivial.  The smallest repair is a finite right Nielsen shear after the exchange.  On the
backward substitution it sends the promoted compact handle letter to `sigma * x₀`, while
retaining the remaining pair images.  Thus the displaced `x₂` coordinate acquires the free
dual `U_j` coordinate as a second-order partner.

This file is entirely rank-uniform.  It constructs the finite Nielsen pair and pins the five
letter images needed by the later Fox and Heisenberg calculations.
-/

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.GammaRPWordNielsen
open Instances.GammaRPWordNielsenElementary
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairSource

namespace Instances.EvenMHeadHandleMixed

def rightMulForward {n : ℕ} (a b : Generator n) :
    Generator n → PWord (Generator n) := fun g ↦
  if g = a then .mul (.gen a) (.inv (.gen b)) else .gen g

def rightMulBackward {n : ℕ} (a b : Generator n) :
    Generator n → PWord (Generator n) := fun g ↦
  if g = a then .mul (.gen a) (.gen b) else .gen g

def rightMulNielsen {n : ℕ} (a b : Generator n) (hab : a ≠ b) :
    PWordNielsenPair n where
  forward := rightMulForward a b
  backward := rightMulBackward a b
  backward_forward g := by
    classical
    by_cases hg : g = a
    · subst g
      simp [rightMulForward, rightMulBackward, hab.symm, mul_assoc]
    · simp [rightMulForward, rightMulBackward, hg]
  forward_backward g := by
    classical
    by_cases hg : g = a
    · subst g
      simp [rightMulForward, rightMulBackward, hab.symm, mul_assoc]
    · simp [rightMulForward, rightMulBackward, hg]

def headHandleMixedNielsen {h : ℕ} (j : Fin h) : PWordNielsenPair (2 + 2 * h) :=
  GammaRPWordNielsenElementary.PWordNielsenPair.trans
    (headHandlePairNielsen j)
    (rightMulNielsen (handleU j) (coreLetter h 0)
      (Certificates.MCompact.handleU_ne_coreLetter j 0))

def headHandleMixedW (alpha : ℕ) {h : ℕ} (j : Fin h) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.subst (headHandleMixedNielsen j).backward
    (Words.MCompact.mCompactW alpha h)

theorem headHandleMixedNielsen_backward_of_ne {h : ℕ} (j : Fin h)
    (g : Generator (2 + 2 * h)) (hg : g ≠ handleU j) :
    (headHandleMixedNielsen j).backward g =
      .gen (headHandlePairSwap j g) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) g) = _
  rw [rightMulBackward, if_neg hg, PWord.subst_gen]
  change PWord.gen ((headHandlePairSwap j).symm g) = _
  rw [headHandlePairSwap_symm]

@[simp] theorem headHandleMixedNielsen_backward_tau {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward .tau = .gen .tau := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) .tau) = _
  rw [rightMulBackward, if_neg (by simp [handleU]), PWord.subst_gen]
  exact headHandlePairNielsen_backward_tau j

@[simp] theorem headHandleMixedNielsen_backward_sigma {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward .sigma = .gen (handleU j) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) .sigma) = _
  rw [rightMulBackward, if_neg (by simp [handleU]), PWord.subst_gen]
  change PWord.gen ((headHandlePairSwap j).symm .sigma) = _
  rw [headHandlePairSwap_symm, headHandlePairSwap_sigma]

@[simp] theorem headHandleMixedNielsen_backward_handleU {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward (handleU j) =
      .mul (.gen .sigma) (.gen (coreLetter h 0)) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) (handleU j)) = _
  rw [rightMulBackward, if_pos rfl, PWord.subst_mul, PWord.subst_gen,
    PWord.subst_gen]
  change PWord.mul (PWord.gen ((headHandlePairSwap j).symm (handleU j)))
    (PWord.gen ((headHandlePairSwap j).symm (coreLetter h 0))) = _
  have hcoreZero : headHandlePairSwap j (coreLetter h 0) = coreLetter h 0 := by
    rw [headHandlePairSwap]
    change tailHandleSwap j (headHandleSwap j (coreLetter h 0)) = coreLetter h 0
    rw [headHandleSwap_coreLetter, tailHandleSwap_coreZero]
  rw [headHandlePairSwap_symm, headHandlePairSwap_handleU_self,
    hcoreZero]

@[simp] theorem headHandleMixedNielsen_backward_coreTwo {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward (coreLetter h 2) =
      .gen (handleV j) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) (coreLetter h 2)) = _
  rw [rightMulBackward, if_neg
    (Certificates.MCompact.handleU_ne_coreLetter j 2).symm, PWord.subst_gen]
  change PWord.gen ((headHandlePairSwap j).symm (coreLetter h 2)) = _
  rw [headHandlePairSwap_symm, headHandlePairSwap_coreTwo]

@[simp] theorem headHandleMixedNielsen_backward_coreZero {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward (coreLetter h 0) =
      .gen (coreLetter h 0) := by
  rw [headHandleMixedNielsen_backward_of_ne j (coreLetter h 0)
    (Certificates.MCompact.handleU_ne_coreLetter j 0).symm]
  congr 1
  rw [headHandlePairSwap]
  change tailHandleSwap j (headHandleSwap j (coreLetter h 0)) = coreLetter h 0
  rw [headHandleSwap_coreLetter, tailHandleSwap_coreZero]

@[simp] theorem headHandleMixedNielsen_backward_coreOne {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward (coreLetter h 1) =
      .gen (coreLetter h 1) := by
  rw [headHandleMixedNielsen_backward_of_ne j (coreLetter h 1)
    (Certificates.MCompact.handleU_ne_coreLetter j 1).symm]
  congr 1
  rw [headHandlePairSwap]
  change tailHandleSwap j (headHandleSwap j (coreLetter h 1)) = coreLetter h 1
  rw [headHandleSwap_coreLetter, tailHandleSwap_coreOne]

@[simp] theorem headHandleMixedNielsen_backward_handleV {h : ℕ} (j : Fin h) :
    (headHandleMixedNielsen j).backward (handleV j) =
      .gen (coreLetter h 2) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) (coreLetter h 0) (handleV j)) = _
  rw [rightMulBackward, if_neg (by simp [handleV, handleU]), PWord.subst_gen]
  change PWord.gen ((headHandlePairSwap j).symm (handleV j)) = _
  rw [headHandlePairSwap_symm, headHandlePairSwap_handleV_self]

end EvenMHeadHandleMixed
end Instances
end
end GQ2.Dyadic

section AxiomAudit

open GQ2.Dyadic.Instances.EvenMHeadHandleMixed

#print axioms rightMulNielsen
#print axioms headHandleMixedNielsen
#print axioms headHandleMixedNielsen_backward_of_ne
#print axioms headHandleMixedNielsen_backward_tau
#print axioms headHandleMixedNielsen_backward_sigma
#print axioms headHandleMixedNielsen_backward_handleU
#print axioms headHandleMixedNielsen_backward_coreZero
#print axioms headHandleMixedNielsen_backward_coreOne
#print axioms headHandleMixedNielsen_backward_coreTwo
#print axioms headHandleMixedNielsen_backward_handleV

end AxiomAudit
