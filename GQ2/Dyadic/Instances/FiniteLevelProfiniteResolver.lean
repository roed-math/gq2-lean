/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FiniteStokesResolver
import GQ2.Dyadic.Count.Resolve

/-!
# A coefficient-independent resolver at each finite level

At a nonzero level `N`, the cyclic test group `Z/N` detects the residue class of every
profinite exponent.  Mapping its generator to any element killed by `N` transports that one
test to every finite target.  Enlarging the cyclic test by the parity detector from
`FiniteStokesResolver` therefore gives integer resolvers which:

* depend only on `N`, not on the eventual coefficient module;
* resolve every profinite and `2`-adic node of every word in every target killed by `N`;
* retain the mod-two exponent information needed by the Stokes endpoint.

This is the generic level-indexed resolver required by action-image devissage.  It contains no
row-, rank-, field-, or finite-class specialization.
-/

namespace GQ2.Dyadic

open GQ2
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates

noncomputable section

/-- The homomorphism from the cyclic level test which sends its generator to `x`. -/
def cycTestHom {Q : Type} [Group Q] (N : ℕ) (x : Q) (hx : x ^ N = 1) :
    CycTest N →* Q := by
  let f : Additive (Multiplicative ℤ) →+ Additive Q := (zpowersHom Q x).toAdditive
  have hf : f (N : ℤ) = 0 := by
    change Additive.ofMul (x ^ (N : ℤ)) = 0
    rw [zpow_natCast, hx]
    rfl
  exact AddMonoidHom.toMultiplicative (ZMod.lift N ⟨f, hf⟩)

@[simp] theorem cycTestHom_gen {Q : Type} [Group Q] (N : ℕ) (x : Q)
    (hx : x ^ N = 1) : cycTestHom N x hx (CycTest.gen N) = x := by
  change Additive.toMul
      ((ZMod.lift N ⟨(zpowersHom Q x).toAdditive, _⟩) (1 : ZMod N)) = x
  rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by norm_num, ZMod.lift_coe]
  change x ^ (1 : ℤ) = x
  simp

/-- Equality of exponents on the cyclic level test transports to every element killed by the
level. -/
theorem zpow_eq_zpowHat_of_cycTest
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} [NeZero N] {e : ℤ} {gamma : Zhat}
    (H : CycTest.gen N ^ e = CycTest.gen N ^ᶻ gamma)
    (x : Q) (hx : orderOf x ∣ N) : x ^ e = x ^ᶻ gamma := by
  have hxN : x ^ N = 1 := orderOf_dvd_iff_pow_eq_one.mp hx
  let f : ContinuousMonoidHom (CycTest N) Q :=
    ⟨cycTestHom N x hxN, continuous_of_discreteTopology⟩
  have hfgen : f (CycTest.gen N) = x := by
    exact cycTestHom_gen N x hxN
  calc
    x ^ e = f (CycTest.gen N ^ e) := by rw [map_zpow, hfgen]
    _ = f (CycTest.gen N ^ᶻ gamma) := congrArg f H
    _ = x ^ᶻ gamma := by rw [map_zpowHat, hfgen]

/-- The level-only profinite resolver.  The zero branch makes the definition total; all
resolution statements use a nonzero level. -/
noncomputable def levelStokesZhatResolver (N : ℕ) : Zhat → ℤ :=
  if hN : N = 0 then stokesZhatResolver (CycTest 1)
  else by
    letI : NeZero N := ⟨hN⟩
    exact stokesZhatResolver (CycTest N)

/-- The corresponding level-only `2`-adic resolver. -/
noncomputable def levelStokesZtwoResolver (N : ℕ) : ℤ_[2] → ℤ :=
  if hN : N = 0 then stokesZtwoResolver (CycTest 1)
  else by
    letI : NeZero N := ⟨hN⟩
    exact stokesZtwoResolver (CycTest N)

theorem levelStokesZhatResolver_cyc_spec {N : ℕ} [NeZero N]
    (gamma : Zhat) :
    CycTest.gen N ^ levelStokesZhatResolver N gamma =
      CycTest.gen N ^ᶻ gamma := by
  have hN : N ≠ 0 := NeZero.ne N
  simpa [levelStokesZhatResolver, hN] using
    stokesZhatResolver_spec (CycTest N) gamma (CycTest.gen N)

/-- The level resolver computes every profinite exponent on every target killed by the level. -/
theorem levelStokesZhatResolver_spec
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (gamma : Zhat) (x : Q) :
    x ^ levelStokesZhatResolver N gamma = x ^ᶻ gamma :=
  let _ : NeZero N := ⟨hN⟩
  zpow_eq_zpowHat_of_cycTest
    (levelStokesZhatResolver_cyc_spec gamma) x (hord x)

/-- Every node of every word is resolved uniformly at its killing level. -/
theorem resolvedAt_levelStokesResolvers
    {X Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (mu : X → Q) (w : PWord X) :
    PWord.ResolvedAt mu (levelStokesZhatResolver N)
      (levelStokesZtwoResolver N) w := by
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
      have H := levelStokesZhatResolver_spec hN hord (padicOmega2 z) (PWord.eval mu u)
      have hrel : levelStokesZtwoResolver N z =
          levelStokesZhatResolver N (padicOmega2 z) := by
        simp [levelStokesZtwoResolver, levelStokesZhatResolver, hN,
          stokesZtwoResolver, stokesZhatResolver, finiteZtwoResolver]
      rw [hrel]
      exact H.symm
  | profPow u gamma ih =>
      exact ⟨ih, (levelStokesZhatResolver_spec hN hord gamma (PWord.eval mu u)).symm⟩

/-- Every reflected relator family has one coefficient-independent resolution per level. -/
theorem resolvesAt_levelStokesResolvers
    {X rho Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (W : rho → PWord X) :
    ResolvesAt W
      (fun k ↦ heisToFree (levelStokesZhatResolver N)
        (levelStokesZtwoResolver N) (W k)) Q :=
  resolvesAt_of_resolvedAt fun f k ↦
    resolvedAt_levelStokesResolvers hN hord f (W k)

#print axioms cycTestHom_gen
#print axioms zpow_eq_zpowHat_of_cycTest
#print axioms levelStokesZhatResolver_spec
#print axioms resolvedAt_levelStokesResolvers
#print axioms resolvesAt_levelStokesResolvers

end

end GQ2.Dyadic
