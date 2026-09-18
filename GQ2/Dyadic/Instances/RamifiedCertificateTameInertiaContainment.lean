/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueProTwoKernel
import GQ2.ZhatTorsion

/-!
# Actual tame inertia acts trivially on the canonical residue field

The wild subgroup has pro-two residue image. Unit norm reciprocity and density identify the
kernel of its two-primary coordinate, so that image is trivial. The canonical residue coordinate
therefore descends to the presented tame quotient. Its tame inertia generator is torsion in the
abelian target, and hence is trivial in `Zhat`. No signed full Frobenius law is required.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Every continuous `Zhat` character of a genuine tame presentation kills tame inertia. -/
theorem inertiaPartQ_le_ker_zhat_character {q : ℕ} (hq : 2 ≤ q)
    (phi : ContinuousMonoidHom (Tq q) Zhat) : inertiaPartQ q ≤ phi.toMonoidHom.ker := by
  letI : CommGroup Zhat :=
    { (inferInstance : Group Zhat) with mul_comm := Words.Mpc.zhat_mul_comm }
  have hrel : phi (tqTau q) = phi (tqTau q) ^ q := by
    have h := tame_rel_map_q phi.toMonoidHom
    change (phi (tqSigma q))⁻¹ * phi (tqTau q) * phi (tqSigma q) =
      phi (tqTau q) ^ q at h
    simpa only [mul_comm (phi (tqSigma q))⁻¹, mul_assoc, inv_mul_cancel, mul_inv_cancel,
      mul_one] using
      h
  have hpow : phi (tqTau q) ^ (q - 1) = 1 := by
    apply mul_right_cancel (b := phi (tqTau q))
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), ← hrel, one_mul]
  have htau : phi (tqTau q) = 1 := Zhat.eq_one_of_pow_eq_one _ (by omega) hpow
  have hclosed : IsClosed (phi.toMonoidHom.ker : Set (Tq q)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage phi.continuous_toFun
  refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact htau

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The wild subgroup in the oriented tame quotient lies in canonical absolute inertia. -/
theorem orientedTame_wild_le_absoluteInertia (T : OrientedTameQuotientK B FF) :
    T.W ≤ absoluteInertiaK (K := K) := by
  apply proTwo_le_absoluteInertia_of_nu_eq_one B FF T.W T.isClosed T.isProP
  intro g
  rw [← T.tame_reciprocity_K g.val]
  have hg : T.tameFK g.val = 1 := by
    change g.val ∈ T.tameFK.toMonoidHom.ker
    rw [T.ker_tameFK]
    exact g.property
  rw [hg, map_one, map_one]

/-- The actual canonical residue coordinate descended through the oriented tame quotient. -/
def absoluteResidueTameCoordinate (T : OrientedTameQuotientK B FF) :
    ContinuousMonoidHom (Tq (qOf K FF)) Zhat :=
  haveI := T.normal
  (quotientLift T.W (absoluteResidueCoordinateK (K := K)) (by
    rw [absoluteResidueCoordinateK_ker]
    exact orientedTame_wild_le_absoluteInertia T)).comp
      (T.equiv.symm : ContinuousMonoidHom (Tq (qOf K FF)) (GalK K ⧸ T.W))

@[simp] theorem absoluteResidueTameCoordinate_tameFK
    (T : OrientedTameQuotientK B FF) (g : GalK K) :
    absoluteResidueTameCoordinate T (T.tameFK g) =
      absoluteResidueCoordinateK (K := K) g := by
  haveI := T.normal
  unfold absoluteResidueTameCoordinate
  change quotientLift T.W (absoluteResidueCoordinateK (K := K)) (by
    rw [absoluteResidueCoordinateK_ker]
    exact orientedTame_wild_le_absoluteInertia T)
    (T.equiv.symm (T.equiv (QuotientGroup.mk g))) = _
  rw [T.equiv.symm_apply_apply]
  rfl

/-- Full tame inertia acts trivially on the canonical absolute residue field, as a consequence
of the existing full finite-layer norm reciprocity and the oriented pro-two tame marking. -/
theorem orientedFullTameInertiaLiesInAbsoluteInertiaAt_of_norm_reciprocity
    (T : OrientedTameQuotientK B FF) :
    OrientedFullTameInertiaLiesInAbsoluteInertiaAt T := by
  intro g hg
  have h := inertiaPartQ_le_ker_zhat_character (two_le_qOf K FF)
    (absoluteResidueTameCoordinate T) hg
  change absoluteResidueTameCoordinate T (T.tameFK g) = 1 at h
  rw [absoluteResidueTameCoordinate_tameFK] at h
  have hm : g ∈ (absoluteResidueCoordinateK (K := K)).toMonoidHom.ker := h
  rw [absoluteResidueCoordinateK_ker] at hm
  exact hm

#print axioms inertiaPartQ_le_ker_zhat_character
#print axioms orientedTame_wild_le_absoluteInertia
#print axioms absoluteResidueTameCoordinate
#print axioms absoluteResidueTameCoordinate_tameFK
#print axioms orientedFullTameInertiaLiesInAbsoluteInertiaAt_of_norm_reciprocity

end
end GQ2.Dyadic
