/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameInertiaPrimeToTwo
import GQ2.Dyadic.Count.Frozen

/-!
# A resolver for every profinite exponent in a finite target

For a fixed finite group `Q` and profinite exponent `gamma`, continuity makes the locus of
profinite integers acting on every element of `Q` as `gamma` an open neighborhood of `gamma`.
Density of the ordinary integers supplies one integer in that locus.  Choosing independently
at every exponent gives a single resolver which computes every `PWord` in `Q`.

This is deliberately target-dependent and noncomputable.  It is the fully generic existence
counterpart to the explicit `omega2Exp`, `padicOmega2Exp`, and display resolvers used when
closed formulas matter.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.Count

section FiniteTarget

variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]

/-- Profinite exponents acting on every element of `Q` as `gamma` does. -/
def finiteZhatResolverSet (gamma : Zhat) : Set Zhat :=
  ⋂ x : Q, (x ^ᶻ ·) ⁻¹' {x ^ᶻ gamma}

theorem finiteZhatResolverSet_isOpen (gamma : Zhat) :
    IsOpen (finiteZhatResolverSet Q gamma) := by
  unfold finiteZhatResolverSet
  apply isOpen_iInter_of_finite
  intro x
  exact (continuous_zpowHat x).isOpen_preimage _ (isOpen_discrete _)

theorem finiteZhatResolverSet_mem (gamma : Zhat) :
    gamma ∈ finiteZhatResolverSet Q gamma := by
  simp [finiteZhatResolverSet]

/-- One ordinary exponent computes `gamma` simultaneously on every element of `Q`. -/
theorem exists_integer_resolver (gamma : Zhat) :
    ∃ n : ℤ, ∀ x : Q, x ^ n = x ^ᶻ gamma := by
  obtain ⟨n, hn⟩ := Zhat.denseRange_ofInt.exists_mem_open
    (finiteZhatResolverSet_isOpen Q gamma)
    ⟨gamma, finiteZhatResolverSet_mem Q gamma⟩
  refine ⟨n, ?_⟩
  have H : Zhat.ofInt n ∈ finiteZhatResolverSet Q gamma := hn
  intro x
  have hx := Set.mem_iInter.mp H x
  change x ^ᶻ Zhat.ofInt n = x ^ᶻ gamma at hx
  simpa using hx

/-- A target-dependent integer representative of every profinite exponent. -/
noncomputable def finiteZhatResolver (gamma : Zhat) : ℤ :=
  Classical.choose (exists_integer_resolver Q gamma)

theorem finiteZhatResolver_spec (gamma : Zhat) (x : Q) :
    x ^ finiteZhatResolver Q gamma = x ^ᶻ gamma :=
  Classical.choose_spec (exists_integer_resolver Q gamma) x

/-- The corresponding resolver for `Ztwo` exponents. -/
noncomputable def finiteZtwoResolver (z : ℤ_[2]) : ℤ :=
  finiteZhatResolver Q (padicOmega2 z)

/-- The generic finite resolvers compute every node of every reflected word. -/
theorem resolvedAt_finiteResolvers {X : Type} (mu : X → Q) (w : PWord X) :
    PWord.ResolvedAt mu (finiteZhatResolver Q) (finiteZtwoResolver Q) w := by
  induction w with
  | one => trivial
  | gen g => trivial
  | mul u v ihu ihv => exact ⟨ihu, ihv⟩
  | inv u ih => exact ih
  | conj u g ihu ihg => exact ⟨ihu, ihg⟩
  | comm u v ihu ihv => exact ⟨ihu, ihv⟩
  | zpow u k ih => exact ih
  | z2pow u z ih =>
      refine ⟨ih, ?_⟩
      exact (finiteZhatResolver_spec Q (padicOmega2 z) (PWord.eval mu u)).symm
  | profPow u gamma ih =>
      refine ⟨ih, ?_⟩
      exact (finiteZhatResolver_spec Q gamma (PWord.eval mu u)).symm

/-- Every reflected relator family has a target-dependent finite resolution. -/
theorem resolvesAt_finiteResolvers {X rho : Type} (W : rho → PWord X) :
    ResolvesAt W
      (fun k ↦ heisToFree (finiteZhatResolver Q) (finiteZtwoResolver Q) (W k)) Q :=
  resolvesAt_of_resolvedAt fun f k ↦ resolvedAt_finiteResolvers Q f (W k)

#print axioms exists_integer_resolver
#print axioms finiteZhatResolver_spec
#print axioms resolvedAt_finiteResolvers
#print axioms resolvesAt_finiteResolvers

end FiniteTarget

end


end GQ2.Dyadic
