/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.M0RamifiedStokes
import GQ2.Dyadic.Instances.N0M0CompactBranches

/-!
# The compact-`M` ramified branch, reduced to one pairing statement

`M0ActionImageDevissage` leaves two word-specific residues for the compact-`M` row.  The
unramified one is discharged in `N0M0CompactBranches`.  This file reduces the ramified one to a
single named proposition, `RamifiedNormalPairingSeparates`: left nondegeneracy of the traced
Stokes pairing on the *ramified normal coordinates* `M × M × (Fin h × Fin 2 → M)` of the
canonical action image.

Everything else on that branch is proved (`M0RamifiedStokes`): the first Fox row is the
compact-`N` one, the differential is onto, and every degree-one cocycle has a unique normal
representative.  The residual statement is exactly the second-order computation
`heisZ_mCompact_ram` — see the module docstring of `M0RamifiedStokes` for why the compact-`N`
argument does not transfer.
-/

namespace GQ2.Dyadic.MCompact

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact

/-- **The residual compact-`M` ramified input.**  On every simple elementary coefficient with
`tau` fixed-point free, the traced pairing of the uniform compact-`M` family separates the
nonzero ramified normal coordinates. -/
def RamifiedNormalPairingSeparates (α h q : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo (gamma α h q : Type) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (mCompactW α h) .tau • m = m → m = 0) →
    ∀ p : M × M × (Fin h × Fin 2 → M), p ≠ 0 →
      ∃ r : ElemDual M × ElemDual M × (Fin h × Fin 2 → ElemDual M),
        heisEta1 (actionGenerators α h q M)
            (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (ActionImage α h q M))))
            (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h r.1 r.2.1 r.2.2) ≠ 0

set_option maxHeartbeats 1600000 in
/-- **The compact-`M` ramified branch, from the residual pairing statement.** -/
theorem ramifiedSimpleStokes_of_separation {α h q : ℕ} (hq : Even q)
    (hsep : RamifiedNormalPairingSeparates α h q) : RamifiedSimpleStokes α h q := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτfpf
  let t := actionImageMarking (2 + 2 * h) q (mCompactW α h) M
  have ht : t.TameRelAt q := actionImage_mCompact_tameRelAt
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := fun m hm ↦ hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  exact mCompactStokesDuality_ramified_of_separation t hM₂ hq ht hwild hτfpf' hTodd
    actionImage_mCompact_relator_death_resolved (hsep M hM₂ hsimple hτfpf)

set_option maxHeartbeats 2400000 in
/-- **The compact-`M` uniform pushed Stokes residue**, reduced to the residual pairing
statement alone. -/
theorem uniformPushedHsimp_of_separation {α h q : ℕ} (hα : 2 ≤ α) (hq : Even q)
    (hsep : RamifiedNormalPairingSeparates α h q) : UniformPushedHsimp α h q :=
  uniformPushedHsimp_of_ramified hα hq (ramifiedSimpleStokes_of_separation hq hsep)

set_option maxHeartbeats 2400000 in
/-- **Corrected exact lifting for the compact-`M` presentation**, reduced to the residual
pairing statement alone. -/
theorem exactLiftingRN_of_separation {α h q : ℕ} (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hsep : RamifiedNormalPairingSeparates α h q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_ramified hα hq0 hqe (ramifiedSimpleStokes_of_separation hqe hsep) nuP

end

end GQ2.Dyadic.MCompact
