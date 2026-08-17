/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueInertia
import GQ2.Dyadic.OrientedTameBundle
import GQ2.TeichmullerLift

/-!
# The residue-action bridge left by oriented tame reciprocity

`RamifiedCertificateResidueInertia` reduces the general-`q` compatible residue lift to the
field statement that the kernel of `nuTq q ∘ tame` acts trivially on the absolute residue
field.  For an `OrientedTameQuotientK`, `tame_reciprocity_K` identifies this composite with
the marked unramified coordinate `B.nu_ur ∘ toAbK` after the injective map `ztwoIota`.

The current `LocalReciprocity` and `MarkedRecip` interfaces do not identify `ker B.nu_ur` with
the kernel of the absolute residue action.  In particular, their cyclotomic clauses only see
the `2`-power cyclotomic character and do not state how `ker B.nu_ur` acts on prime-to-`2`
roots of unity.  This module isolates that exact seam without adding an axiom.

The useful reduction is spectral.  The B13 Teichmüller approximation can be sharpened so that
the nearby root of unity has odd order (`2 ^ f - 1`).  Therefore an absolute Galois element
which fixes every odd-order root of unity is residue-trivial in the norm formulation
`IsResidueTrivial ⊥`; existing odd-root separation proves the converse.  It follows that the
single, equivalent compatibility premise
`NuUrFixesOddRootsOfUnityAt B` produces:

* `NuUrAbsoluteResidueKernelAt B`;
* `TameInertiaAbsoluteResidueTrivialAt` for the oriented tame quotient;
* the full `CompatibleResidueLiftAt` packet after reindexing by `params.qK = qOf K FF`.

Thus the remaining input is neither a finite-action constraint nor another tame-group
calculation: it is precisely local reciprocity's compatibility with the prime-to-`2`
cyclotomic, equivalently Teichmüller, residue action.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Odd-order Teichmüller approximation -/

/-- Every norm-one element of `ℚ̄₂` is within norm `< 1` of an odd-order root of unity.
This sharpens `ResidueLift.exists_rootOfUnity_near` by retaining that its B13 exponent is
`2 ^ f - 1`. -/
theorem exists_odd_rootOfUnity_near (y : ℚ̄₂) (hy : ‖y‖ = 1) :
    ∃ (m : ℕ) (ζ : ℚ̄₂), Odd m ∧ ζ ^ m = 1 ∧ ‖y - ζ‖ < 1 := by
  classical
  have hint : IsIntegral ℚ_[2] y := Algebra.IsIntegral.isIntegral y
  set k : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.adjoin ℚ_[2] {y} with hk
  haveI : FiniteDimensional ℚ_[2] k := IntermediateField.adjoin.finiteDimensional hint
  set D := dyadicUnitFiltration k with hD
  have hymem : y ∈ k := IntermediateField.mem_adjoin_simple_self ℚ_[2] y
  have hy0 : (⟨y, hymem⟩ : ↥k) ≠ 0 := by
    intro h0
    rw [Subtype.ext_iff] at h0
    rw [show y = (0 : ℚ̄₂) from h0, norm_zero] at hy
    exact one_ne_zero hy.symm
  set u : (↥k)ˣ := Units.mk0 ⟨y, hymem⟩ hy0 with hu
  have humem : u ∈ normUnits k := by
    show ‖((u : ↥k) : ℚ̄₂)‖ = 1
    exact hy
  set m : ℕ := 2 ^ D.f - 1 with hm_def
  have hm : 1 ≤ m := by
    have h2 : 2 ≤ 2 ^ D.f := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ D.f := Nat.pow_le_pow_right (by norm_num) D.hf_pos
    omega
  have hmodd : Odd m := by
    have heven : Even (2 ^ D.f) :=
      Nat.even_pow.mpr ⟨by decide, Nat.ne_of_gt D.hf_pos⟩
    obtain ⟨j, hj⟩ := heven
    rw [hm_def]
    use j - 1
    omega
  have hcardQ : Nat.card (↥(normUnits k) ⧸
      (depthUnits k D.π 1).subgroupOf (normUnits k)) = m := D.card_gr_zero
  have hq : (QuotientGroup.mk' ((depthUnits k D.π 1).subgroupOf (normUnits k))
      ((⟨u, humem⟩ : ↥(normUnits k)) ^ m)) = 1 := by
    rw [map_pow, ← hcardQ]
    exact pow_card_eq_one'
  have hmem2 : (⟨u, humem⟩ : ↥(normUnits k)) ^ m
      ∈ (depthUnits k D.π 1).subgroupOf (normUnits k) :=
    (QuotientGroup.eq_one_iff _).mp hq
  have hdepth : u ^ m ∈ depthUnits k D.π 1 := by
    simpa using (Subgroup.mem_subgroupOf).mp hmem2
  have hbound := ((mem_depthUnits k D.π 1 (u ^ m)).mp hdepth).2
  have hcoe : (((u ^ m : (↥k)ˣ) : ↥k) : ℚ̄₂) = y ^ m := by
    rw [Units.val_pow_eq_pow_val]
    push_cast
    rfl
  rw [hcoe, pow_one] at hbound
  have hlt : ‖y ^ m - 1‖ < 1 := lt_of_le_of_lt hbound D.hπ_lt
  obtain ⟨ζ, hζ, hnear⟩ := ResidueLift.exists_nthRoot_near y m hm hlt
  exact ⟨m, ζ, hmodd, hζ, hnear⟩

/-! ## Odd roots detect the absolute residue action -/

/-- An absolute Galois element fixes every odd-order root of unity. -/
def FixesOddRootsOfUnity (g : Kummer.GaloisGroup ℚ_[2]) : Prop :=
  ∀ (m : ℕ) (ζ : ℚ̄₂), Odd m → ζ ^ m = 1 → g • ζ = ζ

/-- Fixing all odd-order roots of unity implies triviality on the absolute residue field.
The fixedness argument of `IsResidueTrivial ⊥` is not needed. -/
theorem isResidueTrivial_bot_of_fixesOddRootsOfUnity (g : Kummer.GaloisGroup ℚ_[2])
    (hfix : FixesOddRootsOfUnity g) :
    IsResidueTrivial (⊥ : Subgroup AbsGalQ2) g := by
  intro x _ hx1
  rcases lt_or_eq_of_le hx1 with hlt | heq
  · have hnorm : ‖g • x‖ = ‖x‖ := norm_galois _ _
    have hbound : ‖g • x - x‖ ≤ ‖x‖ := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_eq ?_
      rw [norm_neg, hnorm, max_self]
    exact lt_of_le_of_lt hbound hlt
  · obtain ⟨m, ζ, hmodd, hζ, hnear⟩ := exists_odd_rootOfUnity_near x heq
    have hfixζ : g • ζ = ζ := hfix m ζ hmodd hζ
    have hsplit : g • x - x = (g • x - g • ζ) + (ζ - x) := by
      rw [hfixζ]
      ring
    have hA : ‖g • x - g • ζ‖ < 1 := by
      have hsmul : g • x - g • ζ = g • (x - ζ) := by
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_sub]
      rw [hsmul, norm_galois]
      exact hnear
    have hB : ‖ζ - x‖ < 1 := by
      rw [norm_sub_rev]
      exact hnear
    rw [hsplit]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hA hB)

/-- Absolute residue-triviality fixes every odd-order root of unity: two such roots in the
same residue class are equal by odd-root separation. -/
theorem fixesOddRootsOfUnity_of_isResidueTrivial_bot
    (g : Kummer.GaloisGroup ℚ_[2])
    (hg : IsResidueTrivial (⊥ : Subgroup AbsGalQ2) g) :
    FixesOddRootsOfUnity g := by
  intro m ζ hm hζ
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm.pos
  have hnormpow : ‖ζ‖ ^ m = 1 := by
    rw [← norm_pow, hζ, norm_one]
  have hnorm : ‖ζ‖ = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hnormpow (ne_of_lt (pow_lt_one₀ (norm_nonneg ζ) hlt hm0))
    · exact absurd hnormpow
        (ne_of_gt ((one_lt_pow_iff_of_nonneg (norm_nonneg ζ) hm0).mpr hgt))
  have hclose : ‖g • ζ - ζ‖ < 1 := hg ζ (by
    intro a ha
    rw [show a = 1 from ha]
    exact one_smul _ _) hnorm.le
  have hgζ : (g • ζ) ^ m = 1 := by
    rw [AlgEquiv.smul_def, ← map_pow, hζ, map_one]
  by_contra hne
  have hsep := TeichmullerLift.norm_sub_eq_one_of_pow_eq_one hm hgζ hζ hne
  rw [hsep] at hclose
  exact lt_irrefl 1 hclose

/-- Fixing odd-order roots of unity is exactly absolute residue-triviality. -/
theorem fixesOddRootsOfUnity_iff_isResidueTrivial_bot
    (g : Kummer.GaloisGroup ℚ_[2]) :
    FixesOddRootsOfUnity g ↔ IsResidueTrivial (⊥ : Subgroup AbsGalQ2) g :=
  ⟨isResidueTrivial_bot_of_fixesOddRootsOfUnity g,
    fixesOddRootsOfUnity_of_isResidueTrivial_bot g⟩

/-! ## The marked-reciprocity seam and oriented tame producer -/

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- Evaluation of `nuTq` is unchanged by reindexing a tame quotient along the parameter
modulus equality. -/
theorem nuTq_tameAtParams_apply (params : FieldParameters) {q : ℕ}
    (params_qK : params.qK = q)
    (tame : ContinuousMonoidHom (GalK K) (Tq q)) (g : GalK K) :
    nuTq params.qK ((tameAtParams params params_qK tame) g) = nuTq q (tame g) := by
  subst q
  rfl

/-- Surjectivity is unchanged by reindexing a tame quotient along the parameter modulus
equality. -/
theorem tameAtParams_surjective (params : FieldParameters) {q : ℕ}
    (params_qK : params.qK = q)
    (tame : ContinuousMonoidHom (GalK K) (Tq q)) (htame : Function.Surjective tame) :
    Function.Surjective (tameAtParams params params_qK tame) := by
  subst q
  exact htame

variable [FiniteDimensional ℚ_[2] K]

/-- The missing local-reciprocity compatibility, stated on the Teichmüller representatives
which suffice to detect the absolute residue action. -/
def NuUrFixesOddRootsOfUnityAt (B : MarkedRecip R K) : Prop :=
  ∀ g : GalK K, B.nu_ur (toAbK K g) = 1 →
    FixesOddRootsOfUnity (subtypeAnc (GalKsub K) g)

/-- The standard kernel-of-unramified-coordinate statement in the repository's absolute
spectral residue vocabulary. -/
def NuUrAbsoluteResidueKernelAt (B : MarkedRecip R K) : Prop :=
  ∀ g : GalK K, B.nu_ur (toAbK K g) = 1 →
    IsResidueTrivial (⊥ : Subgroup AbsGalQ2) (subtypeAnc (GalKsub K) g)

/-- Fixing odd-order roots turns the unramified-coordinate kernel into the absolute residue
kernel. -/
theorem nuUrAbsoluteResidueKernelAt_of_fixesOddRoots (B : MarkedRecip R K)
    (hfix : NuUrFixesOddRootsOfUnityAt B) :
    NuUrAbsoluteResidueKernelAt B := by
  intro g hg
  exact isResidueTrivial_bot_of_fixesOddRootsOfUnity
    (subtypeAnc (GalKsub K) g) (hfix g hg)

/-- The Teichmüller formulation of the missing reciprocity compatibility is equivalent to the
absolute-residue-kernel formulation consumed by W170. -/
theorem nuUrFixesOddRootsOfUnityAt_iff_nuUrAbsoluteResidueKernelAt
    (B : MarkedRecip R K) :
    NuUrFixesOddRootsOfUnityAt B ↔ NuUrAbsoluteResidueKernelAt B := by
  constructor
  · exact nuUrAbsoluteResidueKernelAt_of_fixesOddRoots B
  · intro hres g hg
    exact fixesOddRootsOfUnity_of_isResidueTrivial_bot
      (subtypeAnc (GalKsub K) g) (hres g hg)

/-- Oriented tame reciprocity transports absolute residue-triviality of `ker B.nu_ur` to
absolute residue-triviality of the kernel of `nuTq ∘ T.tameFK`. -/
theorem orientedTame_inertia_absoluteResidue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (hres : NuUrAbsoluteResidueKernelAt B) :
    ∀ g : GalK K, nuTq (qOf K FF) (T.tameFK g) = 1 →
      IsResidueTrivial (⊥ : Subgroup AbsGalQ2) (subtypeAnc (GalKsub K) g) := by
  intro g hg
  apply hres g
  rw [← T.tame_reciprocity_K g, hg, map_one]

/-- The direct W170 producer from the kernel-of-unramified-coordinate residue statement. -/
theorem tameInertiaAbsoluteResidueTrivialAt_of_nuUrKernel
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (params : FieldParameters) (params_qK : params.qK = qOf K FF)
    (hres : NuUrAbsoluteResidueKernelAt B) :
    TameInertiaAbsoluteResidueTrivialAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) := by
  intro g hg
  apply orientedTame_inertia_absoluteResidue B FF T hres g
  simpa only [nuTq_tameAtParams_apply] using hg

/-- The odd-root compatibility supplies W170's absolute tame-inertia statement. -/
theorem tameInertiaAbsoluteResidueTrivialAt_of_nuUrFixesOddRoots
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (params : FieldParameters) (params_qK : params.qK = qOf K FF)
    (hfix : NuUrFixesOddRootsOfUnityAt B) :
    TameInertiaAbsoluteResidueTrivialAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  tameInertiaAbsoluteResidueTrivialAt_of_nuUrKernel B FF T params params_qK
    (nuUrAbsoluteResidueKernelAt_of_fixesOddRoots B hfix)

/-- The kernel-of-unramified-coordinate residue statement produces the full compatible residue
lift for the oriented tame quotient. -/
theorem compatibleResidueLiftAt_of_nuUrKernel
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (params : FieldParameters) (params_qK : params.qK = qOf K FF)
    (hres : NuUrAbsoluteResidueKernelAt B) :
    CompatibleResidueLiftAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  compatibleResidueLiftAt_of_inertia params (GalKsub K)
    (tameAtParams params params_qK T.tameFK)
    (tameAtParams_surjective params params_qK T.tameFK T.tameFK_surjective)
    (tameInertiaAbsoluteResidueTrivialAt_of_nuUrKernel B FF T params params_qK hres)

/-- The strongest producer available from the current interfaces plus the exact missing
prime-to-`2` reciprocity/residue compatibility. -/
theorem compatibleResidueLiftAt_of_nuUrFixesOddRoots
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (params : FieldParameters) (params_qK : params.qK = qOf K FF)
    (hfix : NuUrFixesOddRootsOfUnityAt B) :
    CompatibleResidueLiftAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  compatibleResidueLiftAt_of_nuUrKernel B FF T params params_qK
    (nuUrAbsoluteResidueKernelAt_of_fixesOddRoots B hfix)

#print axioms exists_odd_rootOfUnity_near
#print axioms isResidueTrivial_bot_of_fixesOddRootsOfUnity
#print axioms fixesOddRootsOfUnity_of_isResidueTrivial_bot
#print axioms fixesOddRootsOfUnity_iff_isResidueTrivial_bot
#print axioms nuUrAbsoluteResidueKernelAt_of_fixesOddRoots
#print axioms nuUrFixesOddRootsOfUnityAt_iff_nuUrAbsoluteResidueKernelAt
#print axioms orientedTame_inertia_absoluteResidue
#print axioms tameInertiaAbsoluteResidueTrivialAt_of_nuUrKernel
#print axioms tameInertiaAbsoluteResidueTrivialAt_of_nuUrFixesOddRoots
#print axioms compatibleResidueLiftAt_of_nuUrKernel
#print axioms compatibleResidueLiftAt_of_nuUrFixesOddRoots

end
end GQ2.Dyadic
