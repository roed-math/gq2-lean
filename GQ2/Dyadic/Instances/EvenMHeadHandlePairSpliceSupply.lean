/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSplice
import GQ2.Dyadic.Instances.GammaRUniformStokesSupply

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
noncomputable section
open GQ2 GQ2.Dyadic Count MarkedCore
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSplice
open Instances.EvenMHeadHandleSource
open Instances.FieldFamilyFlexibleCertificate

/-- The corrected normalized M0 source, repaired by the compact-M tame splice. -/
def headHandlePairSpliceW
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  tameSplice (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
    (Words.MCompact.mCompactW alpha h)

/-- Complete finite Stokes supply, without a residual analytic assumption. -/
theorem uniformStokesSupply_headHandlePairSplice
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hq : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    UniformStokesSupply (2 + 2 * h) q
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP)
      (pinnedResolvedFamily (2 + 2 * h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP)) where
  level := pinnedLevelResolver_tameSplice_mCompact hq
    (fun _N hN hNtwo => headHandlePairPrime_pinned_endpoint halpha hq0 hq j nuP hN hNtwo)
  stokes := fun _ _ _ _ _ rho A _ _ _ hA₂ =>
    pushedStokesDuality_headHandlePairSplice halpha hα hq0 hq j nuP rho A hA₂

/-- The complete normalized pro-2 presentation survives the analytic splice. -/
def flexibleCore_headHandlePairSplice
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hU : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) (DM alpha h) nuP :=
  GQ2.Dyadic.FlexibleCoreLeavesRN.ofTameSplice
    (headHandlePairPrimeCorrectedFlexibleCore halpha hq0 hq j nuP hU)
    (Words.MCompact.mCompactW alpha h)

theorem headHandlePairSpliceW_specializes
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    TameSpec.TameSpecializes (2 + 2 * h) q
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) :=
  tameSpecializes_tameSplice
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hq j nuP)
    (Count.tameSpecializes_mCompact hq0 hq alpha h)

#print axioms headHandlePairSpliceW
#print axioms uniformStokesSupply_headHandlePairSplice
#print axioms flexibleCore_headHandlePairSplice
#print axioms headHandlePairSpliceW_specializes
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply

