/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcHandlePhaseData

/-!
# Projected unramified procyclic-M data

This file supplies the two transport facts needed by the arbitrary-display unramified boundary.
Resolver correctness descends through a surjective central-extension projection, including the
genuine two-valued `npcResolver`.  Independently, the exact source-level resolved-family pivot
projects to `sigma` on an odd head for every display representing the selected field unit.  Thus
fixed-point-freeness is obtained without replacing the source exponent by the action-image
exponent.
-/

namespace GQ2.Dyadic.Instances.MpcUnramifiedProjectedData

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Certificates GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.MProcyclicUnram

/-- Resolver correctness descends along a surjective group homomorphism. -/
theorem resolverLifts_of_surjective
    {G H : Type*} [Group G] [Finite G] [Group H]
    (E : Zhat → ℤ) (f : G →* H) (hf : Function.Surjective f)
    (hres : ResolverLifts E G) : ResolverLifts E H := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_zpow, hres x, powOmega2_map]

/-- A surjective base map induces a surjective map of the pulled-back central extension. -/
theorem projExt_surjective
    {L L' : Type*} [Group L] [Group L']
    (c : WordCoh.TwoCocycle L) (phi : L' →* L)
    (hphi : Function.Surjective phi) :
    Function.Surjective (WordCoh.projExt c phi) := by
  intro p
  obtain ⟨x, hx⟩ := hphi p.base
  refine ⟨((x, p.fib) : WordCoh.CentExt (c.comap phi)), ?_⟩
  exact WordCoh.CentExt.ext hx rfl

/-- Resolver correctness on a pulled-back central extension descends to its target. -/
theorem resolverLifts_comap_target_of_surjective
    {L L' : Type*} [Group L] [Finite L'] [Group L']
    (c : WordCoh.TwoCocycle L) (phi : L' →* L)
    (hphi : Function.Surjective phi) (E : Zhat → ℤ)
    (hres : ResolverLifts E (WordCoh.CentExt (c.comap phi))) :
    ResolverLifts E (WordCoh.CentExt c) :=
  resolverLifts_of_surjective E (WordCoh.projExt c phi)
    (projExt_surjective c phi hphi) hres

/-- The resolver used by the displayed Mpc family at a finite level. -/
noncomputable def resolvedE (N : ℕ) : EtaDisplay → Zhat → ℤ
  | .one => fun _ ↦ (omega2Exp N : ℤ)
  | .lit _ => fun _ ↦ (omega2Exp N : ℤ)
  | .hat num den => npcResolver N ⟨num, den⟩

/-- The `Z2` resolver used by the displayed Mpc family at a finite level. -/
noncomputable def resolvedE2 (N : ℕ) : EtaDisplay → ℤ_[2] → ℤ
  | .one => fun _ ↦ (omega2Exp N : ℤ)
  | .lit _ => fun _ ↦ (omega2Exp N : ℤ)
  | .hat _ _ => fun _ ↦ 0

/-- On an odd projected head, every display representing the selected unit evaluates to the
projected `sigma`. -/
theorem projected_evalFin_etaDisplay_eq_sigma
    {n N : ℕ} {C H : Type} [Group C] [Finite C]
    [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    {eta : ℤ_[2]ˣ} (t : Marking n C) (pi : C →* H) (d : EtaDisplay)
    (hd : d.RepresentsUnit eta)
    (hN : N ≠ 0) (hord : orderOf (pi t.σ) ∣ N)
    (hodd : Odd (orderOf (pi t.σ))) :
    pi (PWord.evalFin ⇑t (resolvedE N d) (resolvedE2 N d)
      (d.toPWord (n := n))) = pi t.σ := by
  rw [PWord.map_evalFin]
  cases d with
  | one => rfl
  | lit k =>
      change (pi t.σ) ^ k = pi t.σ
      have hd' : Zhat.ofInt k = etaHatZ (eta : ℤ_[2]) := hd
      calc
        (pi t.σ) ^ k = GQ2.zpowHat (pi t.σ) (Zhat.ofInt k) :=
          (GQ2.zpowHat_ofInt (pi t.σ) k).symm
        _ = GQ2.zpowHat (pi t.σ) (etaHatZ (eta : ℤ_[2])) := by rw [hd']
        _ = pi t.σ := zpowHat_etaHatZ_of_odd hodd
  | hat num den =>
      change PWord.evalFin (fun g ↦ pi (t g))
        (resolvedE N (.hat num den)) (resolvedE2 N (.hat num den))
        (.profPow (.gen Generator.sigma) (EtaData.toZhat ⟨num, den⟩)) = pi t.σ
      rw [PWord.evalFin_profPow_of_ne (fun g ↦ pi (t g))
          (resolvedE N (.hat num den)) (resolvedE2 N (.hat num den))
          (PWord.gen Generator.sigma)
          (Words.Npc.toZhat_ne_omega2 ⟨num, den⟩),
        PWord.evalFin_gen, resolvedE, npcResolver_toZhat, zpow_natCast]
      change pi t.σ ^ (1 + padicOmega2Exp
        (EtaData.toPadic ⟨num, den⟩ - 1) N) = pi t.σ
      rw [← Count.zpowHat_etaHatZ_zpow hN hord (EtaData.toPadic ⟨num, den⟩),
        zpowHat_etaHatZ_of_odd hodd]

/-- The displayed resolved family is the Mpc family at its canonical display resolver. -/
theorem resolvedFamily_eq_mpcFamOf_resolvedE
    {alpha r pp h q N : ℕ} (d : EtaDisplay) :
    resolvedFamily alpha r pp h q d N =
      mpcFamOf alpha r pp h q d (resolvedE N d) (resolvedE2 N d) := by
  cases d with
  | one => exact (mpcFamOf_const alpha r pp h q (omega2Exp N) .one).symm
  | lit k => exact (mpcFamOf_const alpha r pp h q (omega2Exp N) (.lit k)).symm
  | hat num den => rfl

/-- The canonical display resolver is correct on the source word-lift group. -/
theorem resolverLifts_resolvedE_wordLift
    {N : ℕ} {d : EtaDisplay}
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V] (hN : N = 4 * Monoid.exponent C)
    (hV2 : ∀ v : V, v + v = 0) :
    ResolverLifts (resolvedE N d) (WordLift V C) := by
  subst N
  cases d with
  | one => exact resolverLifts_uniformWordLift_ramified hV2
  | lit k => exact resolverLifts_uniformWordLift_ramified hV2
  | hat num den =>
      exact GQ2.Dyadic.NProcyclic.resolverLifts_npcResolver_wordLift
        hV2 ⟨num, den⟩

/-- The exact source resolved-family row has a fixed-point-free pivot whenever the projected
head sigma is odd and fixed-point free. -/
theorem exists_resolvedFamily_unramified_smul_row_fpf_of_projected
    {alpha r pp h q : ℕ} {d : EtaDisplay} {eta : ℤ_[2]ˣ}
    {C H V : Type} [Group C] [Finite C] [Group H] [Finite H]
    [TopologicalSpace H] [DiscreteTopology H]
    [AddCommGroup V] [Finite V] [DistribMulAction C V]
    [DistribMulAction H V]
    (t : Marking (2 + 2 * h) C) (pi : C →* H)
    (hpi : ∀ (c : C) (v : V), c • v = pi c • v)
    (hd : d.RepresentsUnit eta) (hV2 : ∀ v : V, v + v = 0)
    (halpha : 1 ≤ alpha) (hq : Even q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (htau : ∀ v : V, t.τ • v = v)
    (hsigma2 : ∀ v : V, powOmega2 t.σ • v = v)
    (hsigmaOdd : Odd (orderOf (pi t.σ)))
    (hsigmaFpf : ∀ v : V, pi t.σ • v = v → v = 0) :
    ∃ u : C,
      (∀ x : Generator (2 + 2 * h) → V,
        heisD1 ⇑t
            (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) x =
          ![t.σ⁻¹ • x .tau,
            x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))]) ∧
      (∀ v : V, u • v = v → v = 0) := by
  let N := 4 * Monoid.exponent C
  let E := resolvedE N d
  let E2 := resolvedE2 N d
  let u := PWord.evalFin ⇑t E E2 (d.toPWord (n := 2 + 2 * h))
  have hlift : ResolverLifts E (WordLift V C) :=
    resolverLifts_resolvedE_wordLift (d := d) rfl hV2
  have hrow : ∀ x : Generator (2 + 2 * h) → V,
      heisD1 ⇑t
          (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) x =
        ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))] := by
    intro x
    rw [resolvedFamily_eq_mpcFamOf_resolvedE]
    exact heisD1_mpcFamOf_unramified_apply t E E2 hlift hV2 halpha hq
      hwild htau hsigma2 rfl x
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even C).1
  have hord : orderOf (pi t.σ) ∣ N :=
    (orderOf_map_dvd pi t.σ).trans
      ((Monoid.order_dvd_exponent t.σ).trans ⟨4, by simp [N, mul_comm]⟩)
  have huval : pi u = pi t.σ :=
    projected_evalFin_etaDisplay_eq_sigma t pi d hd hN hord hsigmaOdd
  refine ⟨u, hrow, ?_⟩
  intro v hv
  apply hsigmaFpf v
  rw [← huval, ← hpi]
  exact hv

#print axioms resolverLifts_of_surjective
#print axioms projExt_surjective
#print axioms resolverLifts_comap_target_of_surjective
#print axioms resolvedE
#print axioms resolvedE2
#print axioms projected_evalFin_etaDisplay_eq_sigma
#print axioms resolvedFamily_eq_mpcFamOf_resolvedE
#print axioms resolverLifts_resolvedE_wordLift
#print axioms exists_resolvedFamily_unramified_smul_row_fpf_of_projected

end
end GQ2.Dyadic.Instances.MpcUnramifiedProjectedData
