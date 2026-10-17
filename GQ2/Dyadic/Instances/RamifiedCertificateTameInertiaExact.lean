/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusCompatibility
import GQ2.Dyadic.Instances.RamifiedCertificateTameInertiaContainment
import GQ2.ZhatTorsion

/-!
# Exact comparison of full tame inertia with actual residue inertia

Forward containment lets the actual residue character descend through the full tame unramified
coordinate to a continuous endomorphism of Zhat. Its image contains a nonzero integer: some
positive power of an absolute Frobenius lift fixes the finite base field. The proved Zhat
injectivity criterion therefore forces the reverse containment as well.

Combining this argument with the norm-reciprocity forward theorem gives exact inertia equality
for every oriented tame quotient. No signed full Frobenius normalization, relative norm
reciprocity, odd field degree, or Galois condition over the dyadic base is assumed.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

private instance compact_galK : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact

private instance t2_galK : T2Space (GalK K) := inferInstanceAs (T2Space ↥(K.fixingSubgroup))
private instance td_galK : TotallyDisconnectedSpace (GalK K) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(K.fixingSubgroup))

private theorem full_tame_coordinate_surjective
    (T : OrientedTameQuotientK B FF) :
    Function.Surjective ((tqToZhat (qOf K FF)).comp T.tameFK) := by
  intro z
  obtain ⟨x, hx⟩ := (qurQEquivZhat (qOf K FF)).surjective z
  obtain ⟨a, ha⟩ := quotientMk_surjective (inertiaPartQ (qOf K FF)) x
  change qMkQ (qOf K FF) a = x at ha
  obtain ⟨g, hg⟩ := T.tameFK_surjective a
  refine ⟨g, ?_⟩
  change tqToZhat (qOf K FF) (T.tameFK g) = z
  rw [hg, ← qurQToZhat_qMkQ, ha]
  exact hx

private theorem full_tame_coordinate_eq_one_iff
    (T : OrientedTameQuotientK B FF) (g : GalK K) :
    ((tqToZhat (qOf K FF)).comp T.tameFK) g = 1 ↔
      T.tameFK g ∈ inertiaPartQ (qOf K FF) := by
  change tqToZhat (qOf K FF) (T.tameFK g) = 1 ↔ _
  rw [← qurQToZhat_qMkQ]
  change qurQEquivZhat (qOf K FF) (qMkQ (qOf K FF) (T.tameFK g)) = 1 ↔ _
  rw [mem_inertiaPartQ_iff_qMkQ_eq_one]
  constructor
  · intro h
    apply (qurQEquivZhat (qOf K FF)).injective
    exact h.trans (map_one _).symm
  · intro h
    rw [h, map_one]

/-- The actual residue coordinate on a finite local Galois subgroup contains a nonzero
integer: a positive power of an absolute Frobenius lift fixes the finite base field. -/
theorem absoluteResidueCoordinateK_range_contains_integer :
    ∃ n : ℕ, n ≠ 0 ∧ Zhat.ofInt (n : ℤ) ∈
      (absoluteResidueCoordinateK (K := K)).toMonoidHom.range := by
  obtain ⟨g, hg⟩ := exists_squaresOddRootsOfUnity
  have hres : absoluteResidueAlgAction g = absoluteResidueFrobenius :=
    (squaresOddRootsOfUnity_iff_residueFrobenius g).mp hg
  letI : (K.fixingSubgroup : Subgroup (Kummer.GaloisGroup ℚ_[2])).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  obtain ⟨n, hn, _, hgn⟩ := K.fixingSubgroup.exists_pow_mem_of_index_ne_zero
    Subgroup.FiniteIndex.index_ne_zero g
  refine ⟨n, Nat.ne_of_gt hn, ⟨⟨g ^ n, hgn⟩, ?_⟩⟩
  change absoluteResidueGalEquivZhat (absoluteResidueAlgAction (g ^ n)) = _
  rw [map_pow, hres, map_pow, absoluteResidueGalEquivZhat_frobenius,
    ← zpow_natCast, Zhat.ofInt_one_zpow]

/-- Forward full-inertia containment is automatically exact for a finite local base.
No choice of arithmetic versus geometric Frobenius generator is required. -/
theorem fullTameInertia_comap_eq_absoluteInertiaK_of_forward
    (T : OrientedTameQuotientK B FF)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    (inertiaPartQ (qOf K FF)).comap T.tameFK.toMonoidHom =
      absoluteInertiaK (K := K) := by
  let t : ContinuousMonoidHom (GalK K) Zhat := (tqToZhat (qOf K FF)).comp T.tameFK
  let a : ContinuousMonoidHom (GalK K) Zhat := absoluteResidueCoordinateK (K := K)
  have hsurj : Function.Surjective t := full_tame_coordinate_surjective T
  have hker : t.toMonoidHom.ker ≤ a.toMonoidHom.ker := by
    intro g hg
    rw [absoluteResidueCoordinateK_ker]
    exact Hfull g ((full_tame_coordinate_eq_one_iff T g).mp hg)
  let fHom : Zhat →* Zhat := t.toMonoidHom.liftOfSurjective hsurj ⟨a.toMonoidHom, hker⟩
  have hf (g : GalK K) : fHom (t g) = a g := by
    exact t.toMonoidHom.liftOfRightInverse_comp_apply (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨a.toMonoidHom, hker⟩ g
  have hfcont : Continuous fHom := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hsurj t.continuous_toFun).continuous_iff.mpr
    have heq : (fun g : GalK K ↦ fHom (t g)) = a := funext hf
    change Continuous (fun g : GalK K ↦ fHom (t g))
    rw [heq]
    exact a.continuous_toFun
  let f : ContinuousMonoidHom Zhat Zhat := ⟨fHom, hfcont⟩
  obtain ⟨n, hn, g, hg⟩ := absoluteResidueCoordinateK_range_contains_integer (K := K)
  have hinj : Function.Injective f :=
    Zhat.endomorphism_injective_of_integer_mem_range f hn ⟨t g, (hf g).trans hg⟩
  ext g
  constructor
  · exact Hfull g
  · intro hg
    apply (full_tame_coordinate_eq_one_iff T g).mp
    apply hinj
    change fHom (t g) = fHom 1
    rw [hf, map_one]
    exact (show g ∈ a.toMonoidHom.ker from by
      rw [absoluteResidueCoordinateK_ker]
      exact hg)

/-- In particular actual inertia maps into full tame inertia, the direction needed by the
anchored unramified norm-field argument. -/
theorem actualInertia_mem_fullTameInertia_of_forward
    (T : OrientedTameQuotientK B FF)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T)
    (g : GalK K) (hg : subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup) :
    T.tameFK g ∈ inertiaPartQ (qOf K FF) := by
  have hm : g ∈ (inertiaPartQ (qOf K FF)).comap T.tameFK.toMonoidHom := by
    rw [fullTameInertia_comap_eq_absoluteInertiaK_of_forward T Hfull]
    exact hg
  exact hm

/-- The full abstract tame-inertia preimage is the actual residue inertia subgroup. -/
theorem fullTameInertia_comap_eq_absoluteInertiaK
    (T : OrientedTameQuotientK B FF) :
    (inertiaPartQ (qOf K FF)).comap T.tameFK.toMonoidHom =
      absoluteInertiaK (K := K) :=
  fullTameInertia_comap_eq_absoluteInertiaK_of_forward T
    (orientedFullTameInertiaLiesInAbsoluteInertiaAt_of_norm_reciprocity T)

/-- Actual inertia maps into full abstract tame inertia for every oriented tame quotient. -/
theorem actualInertia_mem_fullTameInertia
    (T : OrientedTameQuotientK B FF)
    (g : GalK K) (hg : subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup) :
    T.tameFK g ∈ inertiaPartQ (qOf K FF) :=
  actualInertia_mem_fullTameInertia_of_forward T
    (orientedFullTameInertiaLiesInAbsoluteInertiaAt_of_norm_reciprocity T) g hg

#print axioms absoluteResidueCoordinateK_range_contains_integer
#print axioms fullTameInertia_comap_eq_absoluteInertiaK_of_forward
#print axioms actualInertia_mem_fullTameInertia_of_forward
#print axioms fullTameInertia_comap_eq_absoluteInertiaK
#print axioms actualInertia_mem_fullTameInertia
end
end GQ2.Dyadic

