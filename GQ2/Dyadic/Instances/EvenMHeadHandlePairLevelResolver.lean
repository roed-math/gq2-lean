/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FiniteLevelProfiniteResolver
import GQ2.Dyadic.Instances.EvenMHeadHandlePairStokes
import GQ2.Dyadic.Instances.NpcActionImageDevissage

/-!
# The normalized even-M word has a uniform level resolver

The prime-to-two corrected, all-rank normalized even-M word from
`EvenMHeadHandlePairStokes` is resolved here at a level depending only on the finite acting
group.  The resolver is therefore independent of the coefficient module and fits the generic
`LevelResolver` interface used by action-image devissage.

This closes the full syntactic side of the general argument.  The remaining row input is the
`SimpleActionImageStokes` statement: Stokes duality itself for the normalized word on simple
finite action images.  No class, rank, field, or frozen word is selected here.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.RowActionImage

/-- The corrected normalized relator family resolved at a coefficient-independent level. -/
noncomputable def headHandlePairPrimeLevelFamily
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (N : ℕ) : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree (levelStokesZhatResolver N) (levelStokesZtwoResolver N)
    (gammaFam (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP) l)

theorem headHandlePairPrimeLevelFamily_resolves
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {alpha h q N : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N) :
    ResolvesAt
      (gammaFam (2 + 2 * h) q
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP))
      (headHandlePairPrimeLevelFamily alpha h q halpha hq0 hqe j nuP N) Q := by
  exact resolvesAt_levelStokesResolvers hN hord _

theorem headHandlePairPrimeLevelFamily_endpoint
    {alpha h q N : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hN : N ≠ 0) :
    IsStokesEndpoint
      (headHandlePairPrimeLevelFamily alpha h q halpha hq0 hqe j nuP N) := by
  change IsStokesEndpoint (fun l : Fin 2 ↦
    heisToFree (levelStokesZhatResolver N) (levelStokesZtwoResolver N)
      (gammaFam (2 + 2 * h) q
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP) l))
  letI : NeZero N := ⟨hN⟩
  have H := isStokesEndpoint_primeToTwoCorrection (CycTest N) hq0 hqe
    (headHandlePairNormalizedW alpha h halpha j nuP)
    (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP)
    (headHandlePairNormalized_stokesResolver_isStokesEndpoint
      (Q := CycTest N) halpha hqe j nuP)
  simpa [levelStokesZhatResolver,
    levelStokesZtwoResolver, headHandlePairPrimeCorrectedW, hN] using H

/-- The generic `LevelResolver` instance for the corrected normalized even-M source. -/
noncomputable def headHandlePairPrimeLevelResolver
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    LevelResolver (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
      (headHandlePairPrimeLevelFamily alpha h q halpha hq0 hqe j nuP) where
  resolves := fun _ _ _ _ _ _N hN hord ↦
    headHandlePairPrimeLevelFamily_resolves halpha hq0 hqe j nuP hN hord
  endpoint := fun _N hN _ ↦
    headHandlePairPrimeLevelFamily_endpoint halpha hq0 hqe j nuP hN

#print axioms headHandlePairPrimeLevelFamily_resolves
#print axioms headHandlePairPrimeLevelFamily_endpoint
#print axioms headHandlePairPrimeLevelResolver

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
