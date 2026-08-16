/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN
import GQ2.Dyadic.LabuteInterface
import GQ2.Dyadic.MarkedCore.Certificate
import GQ2.Dyadic.MarkedCore.ClearWide
import GQ2.Dyadic.Instances.FieldUnimodularity

/-!
# The positive-level Npc marked-core certificate

The compact-N marked-matching theorem normalizes a primitive `(sigma, x2)` row.  It cannot
serve the positive-level Npc row `(2^r, 0)` when `r > 0`, since that row is not primitive.
This module records the correct level-`r` input and performs the normalization without assuming
the desired full marking equality.

`NpcMarkedData` is finite generator-row data.  The plane values are divisible by `2^r`, their
quotients form a primitive pair, `x1` has residue `eta` modulo `2^r`, and the handle values
vanish.  The proof uses the exact determinant-one plane action to make the sigma value exactly
`2^r`, N2 to clear x2, and the proved N5 family to correct x1.  Generator extensionality then
upgrades these calculations to equality of continuous homomorphisms.

The final theorem `npcMarkedCoreRealization_of_oriented` constructs the field-facing
`MarkedCoreRealization (DN alpha h) (npcNu alpha r h eta)`.  Its remaining hypotheses are the
oriented abstract core equivalence and the explicit finite row data above.  Thus it sharply
reduces the field-side problem without renaming the missing arithmetic as a realization premise.

No new axiom is introduced.  Every declaration has the standard axiom set
`[propext, Classical.choice, Quot.sound]`.
-/

namespace GQ2.Dyadic.Instances.NpcCert

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN

/-- Finite generator-row data for the positive-level Npc marking. -/
def NpcMarkedData (alpha r h : ℕ) (eta : ℤ_[2]ˣ)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  (∃ a b : ℤ_[2],
      toAdd (nu' (dnSigma alpha h)) = 2 ^ r * a ∧
      toAdd (nu' (dnX2 alpha h)) = 2 ^ r * b ∧
      (IsUnit a ∨ IsUnit b)) ∧
    (∃ w : ℤ_[2], toAdd (nu' (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w) ∧
    (∀ j : Fin h, toAdd (nu' (dnGen alpha h (handleIdxU j))) = 0) ∧
    ∀ j : Fin h, toAdd (nu' (dnGen alpha h (handleIdxV j))) = 0

/-- Exact `SL₂` normalization of a level-`r` primitive plane row. -/
theorem npcPlane_normalize
    {alpha r h : ℕ}
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    {a b : ℤ_[2]}
    (hsigma : toAdd (nu' (dnSigma alpha h)) = 2 ^ r * a)
    (hx2 : toAdd (nu' (dnX2 alpha h)) = 2 ^ r * b)
    (hpair : IsUnit a ∨ IsUnit b) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      toAdd (nu' (Psi (dnSigma alpha h))) = 2 ^ r ∧
      (∃ c : ℤ_[2], toAdd (nu' (Psi (dnX2 alpha h))) = 2 ^ r * c) ∧
      ∀ i : Fin (coreRank h), i ≠ 2 → i ≠ 3 →
        toAdd (nu' (Psi (dnGen alpha h i))) = toAdd (nu' (dnGen alpha h i)) := by
  rcases hpair with ha | hb
  · let T : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
      !![((ha.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), 0; 0, ((ha.unit : ℤ_[2]ˣ) : ℤ_[2])]
    have hdet : T.det = 1 := by
      simp only [T, Matrix.det_fin_two_of, mul_zero, sub_zero]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    obtain ⟨Psi, hPsi⟩ := nCorePlane_sl2_lift alpha h hdet
    refine ⟨Psi, hPsi.1, ?_, ⟨a * b, ?_⟩, ?_⟩
    · have hrow := congrFun (hPsi.2 nu') 2
      simp [nuFrame_apply, nCoreMat_two, T, smul_eq_mul] at hrow
      rw [show dnSigma alpha h = dnGen alpha h 2 from rfl, hrow,
        show dnGen alpha h 2 = dnSigma alpha h from rfl, hsigma]
      calc
        ((ha.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (2 ^ r * a) =
            2 ^ r * (((ha.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * a) := by ring
        _ = 2 ^ r := by rw [ha.val_inv_mul, mul_one]
    · have hrow := congrFun (hPsi.2 nu') 3
      simp [nuFrame_apply, nCoreMat_three, T, smul_eq_mul] at hrow
      rw [show dnX2 alpha h = dnGen alpha h 3 from rfl, hrow,
        show dnGen alpha h 3 = dnX2 alpha h from rfl, hx2]
      ring
    · intro i hi2 hi3
      have hrow := congrFun (hPsi.2 nu') i
      rw [nuFrame_apply, nCoreMat_of_ne _ _ hi2 hi3, nuFrame_apply] at hrow
      exact hrow
  · let T : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
      !![0, ((hb.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]);
        -((hb.unit : ℤ_[2]ˣ) : ℤ_[2]), 0]
    have hdet : T.det = 1 := by
      simp only [T, Matrix.det_fin_two_of, zero_mul, zero_sub, mul_neg, neg_neg]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    obtain ⟨Psi, hPsi⟩ := nCorePlane_sl2_lift alpha h hdet
    refine ⟨Psi, hPsi.1, ?_, ⟨-(b * a), ?_⟩, ?_⟩
    · have hrow := congrFun (hPsi.2 nu') 2
      simp [nuFrame_apply, nCoreMat_two, T, smul_eq_mul] at hrow
      rw [show dnSigma alpha h = dnGen alpha h 2 from rfl, hrow,
        show dnGen alpha h 3 = dnX2 alpha h from rfl, hx2]
      calc
        ((hb.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (2 ^ r * b) =
            2 ^ r * (((hb.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * b) := by ring
        _ = 2 ^ r := by rw [hb.val_inv_mul, mul_one]
    · have hrow := congrFun (hPsi.2 nu') 3
      simp [nuFrame_apply, nCoreMat_three, T, smul_eq_mul] at hrow
      rw [show dnX2 alpha h = dnGen alpha h 3 from rfl, hrow,
        show dnGen alpha h 2 = dnSigma alpha h from rfl, hsigma]
      ring
    · intro i hi2 hi3
      have hrow := congrFun (hPsi.2 nu') i
      rw [nuFrame_apply, nCoreMat_of_ne _ _ hi2 hi3, nuFrame_apply] at hrow
      exact hrow

/-- Existing N-core moves turn the finite positive-level row data into full Npc marking
compatibility. -/
theorem npcMarkedMatching
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    (hdata : NpcMarkedData alpha r h eta nu') :
    ∃ u : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (u x) = chiN alpha h x) ∧
      ∀ x, nu' (u x) = npcNuPadic alpha r h eta x := by
  rcases hdata with ⟨⟨a, b, hsigma, hx2, hpair⟩, ⟨w, hx1⟩, hU, hV⟩
  obtain ⟨Psi0, h0chi, hsigma0, ⟨c, hx20⟩, h0other⟩ :=
    npcPlane_normalize nu' hsigma hx2 hpair
  let nu2 : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Psi0)
  have hsigma2 : toAdd (nu2 (dnSigma alpha h)) = 2 ^ r := hsigma0
  have hx22 : toAdd (nu2 (dnX2 alpha h)) = 2 ^ r * c := hx20
  have hx12 : toAdd (nu2 (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w := by
    exact (h0other 1 nCoreOne_ne_two
      (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))).trans hx1
  have hU2 : ∀ j : Fin h, toAdd (nu2 (dnGen alpha h (handleIdxU j))) = 0 := by
    intro j
    exact (h0other _ (nHandleIdxU_ne_two j) (handleIdxU_ne_three j)).trans (hU j)
  have hV2 : ∀ j : Fin h, toAdd (nu2 (dnGen alpha h (handleIdxV j))) = 0 := by
    intro j
    exact (h0other _ (nHandleIdxV_ne_two j) (handleIdxV_ne_three j)).trans (hV j)
  let k : ℤ_[2] := -c
  let nu3 : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu2.comp (autHom (dnTauDEquiv alpha h k))
  have hgen3 : ∀ i : Fin (coreRank h),
      nu3 (dnGen alpha h i) =
        nu2 (tauDMark (isProP_DN alpha h) k (dnGen alpha h) i) := fun i => by
    show nu2 (dnTauDEquiv alpha h k (dnGen alpha h i)) = _
    rw [dnTauDEquiv_gen]
  have hsigma3 : toAdd (nu3 (dnSigma alpha h)) = 2 ^ r := by
    rw [show dnSigma alpha h = dnGen alpha h 2 from rfl, hgen3, tauDMark_two]
    exact hsigma2
  have hx23 : toAdd (nu3 (dnX2 alpha h)) = 0 := by
    rw [show dnX2 alpha h = dnGen alpha h 3 from rfl, hgen3, tauDMark_three,
      map_mul, toAdd_mul, toAdd_map_zpowZtwo (isProP_DN alpha h) nu2,
      show dnGen alpha h 2 = dnSigma alpha h from rfl, hsigma2,
      show dnGen alpha h 3 = dnX2 alpha h from rfl, hx22]
    dsimp only [k]
    ring
  have hx13 : toAdd (nu3 (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w := by
    rw [show dnX1 alpha h = dnGen alpha h 1 from rfl, hgen3,
      tauDMark_of_ne _ _ _
        (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))]
    exact hx12
  have hU3 : ∀ j : Fin h, toAdd (nu3 (dnGen alpha h (handleIdxU j))) = 0 := by
    intro j
    rw [hgen3, tauDMark_of_ne _ _ _ (handleIdxU_ne_three j)]
    exact hU2 j
  have hV3 : ∀ j : Fin h, toAdd (nu3 (dnGen alpha h (handleIdxV j))) = 0 := by
    intro j
    rw [hgen3, tauDMark_of_ne _ _ _ (handleIdxV_ne_three j)]
    exact hV2 j
  obtain ⟨Psi5, h5chi, h5frame⟩ := nMixHypothesis_coreMix alpha h (-w)
  refine ⟨Psi5.trans ((dnTauDEquiv alpha h k).trans Psi0), fun x => ?_, ?_⟩
  · show chiN alpha h (Psi0 (dnTauDEquiv alpha h k (Psi5 x))) = chiN alpha h x
    rw [h0chi, chiN_dnTauDEquiv, h5chi]
  · have hgen : ∀ i : Fin (coreRank h),
        nu3 (Psi5 (dnGen alpha h i)) = npcNuPadic alpha r h eta (dnGen alpha h i) := by
      intro i
      have hrow := congrFun (h5frame nu3) i
      rw [nuFrame_apply, nFrameMixX1] at hrow
      apply Multiplicative.toAdd.injective
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hrow, Function.update_of_ne nCoreZero_ne_one, nuFrame_apply,
          show dnGen alpha h 0 = dnX0 alpha h from rfl, nChar_dnX0, toAdd_one]
        change 0 = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 0))
        rw [npcNuPadic_gen_zero, toAdd_ofAdd]
      · rw [hrow, Function.update_self, nuFrame_apply, nuFrame_apply,
          show dnGen alpha h 1 = dnX1 alpha h from rfl,
          show dnGen alpha h 2 = dnSigma alpha h from rfl,
          hx13, hsigma3]
        change (eta : ℤ_[2]) + 2 ^ r * w + -w * 2 ^ r =
          toAdd (npcNuPadic alpha r h eta (dnGen alpha h 1))
        rw [npcNuPadic_gen_one, toAdd_ofAdd]
        ring
      · rw [hrow, Function.update_of_ne nCoreTwo_ne_one, nuFrame_apply,
          show dnGen alpha h 2 = dnSigma alpha h from rfl,
          hsigma3]
        change 2 ^ r = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 2))
        rw [npcNuPadic_gen_two, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne nCoreThree_ne_one, nuFrame_apply,
          show dnGen alpha h 3 = dnX2 alpha h from rfl,
          hx23]
        change 0 = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 3))
        rw [npcNuPadic_gen_three, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne (nHandleIdxU_ne_one j), nuFrame_apply,
          hU3 j, npcNuPadic_gen_handleU, toAdd_one]
      · rw [hrow, Function.update_of_ne (nHandleIdxV_ne_one j), nuFrame_apply,
          hV3 j, npcNuPadic_gen_handleV, toAdd_one]
    have heq : nu3.comp (autHom Psi5) = npcNuPadic alpha r h eta :=
      dn_hom_ext _ _ hgen
    intro x
    exact DFunLike.congr_fun heq x

/-! ## Certificate and field-facing realization -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Pull an abstract marking back to the N-core along a continuous equivalence. -/
def npcCert_transport {alpha h : ℕ} (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN alpha h : Type) G)
    (hcont : Continuous fun x : (DN alpha h : Type) => nuG (f x)) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuG (f x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := hcont

/-- A marked-core certificate whose normal form is the positive-level Npc marking. -/
structure MarkedCoreCertificateNpc (alpha r h : ℕ) (eta : ℤ_[2]ˣ)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  abstractEquiv : ContinuousMulEquiv (DN alpha h : Type) G
  orientation : ∀ x, chiG (abstractEquiv x) = chiN alpha h x
  correction : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)
  correction_chi : ∀ x, chiN alpha h (correction x) = chiN alpha h x
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) =
    npcNuPadic alpha r h eta x

omit [IsTopologicalGroup G] in
/-- Produce an Npc certificate from the finite positive-level generator-row data. -/
theorem npcCert_marked_matching_certificate
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN alpha h : Type) G)
    (horient : ∀ x, chiG (f x) = chiN alpha h x)
    (hcont : Continuous fun x : (DN alpha h : Type) => nuG (f x))
    (hdata : NpcMarkedData alpha r h eta (npcCert_transport nuG f hcont)) :
    Nonempty (MarkedCoreCertificateNpc alpha r h eta chiG nuG) := by
  obtain ⟨u, huchi, hunu⟩ := npcMarkedMatching (npcCert_transport nuG f hcont) hdata
  exact ⟨⟨f, horient, u, huchi, hunu⟩⟩

/-- The `Ztwo` Npc marking reads as `npcNuPadic` through the canonical seam. -/
theorem ztwoIota_npcNu (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (x : (DN alpha h : Type)) :
    ztwoIota (npcNu alpha r h eta x) = npcNuPadic alpha r h eta x := by
  change ztwoIota (ztwoIota.symm (npcNuPadic alpha r h eta x)) = _
  exact ztwoIota.apply_symm_apply _

section KTwo

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The Npc certificate at the canonical characters on the maximal pro-2 quotient. -/
abbrev MarkedCoreCertificateKTwoNpc (B : MarkedRecip Rec K)
    (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :=
  MarkedCoreCertificateNpc alpha r h eta (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Produce the field-side positive-level certificate at an oriented equivalence. -/
theorem npcCert_marked_matching_certificate_KTwo
    (B : MarkedRecip Rec K) {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))
    (hdata : NpcMarkedData alpha r h eta
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    Nonempty (MarkedCoreCertificateKTwoNpc B alpha r h eta) := by
  exact npcCert_marked_matching_certificate _ _ e.1 e.2 _ hdata

/-- Adapt an Npc certificate to the common field-side marked-core realization. -/
def npcCert_realization {B : MarkedRecip Rec K} {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (C : MarkedCoreCertificateKTwoNpc B alpha r h eta) :
    MarkedCoreRealization (K := K) (B := B) (DN alpha h) (npcNu alpha r h eta) where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => (ztwoIota_npcNu alpha r h eta x).trans (C.correction_nu x).symm

/-- Construct the exact field-side Npc realization directly from the finite marked row. -/
theorem npcMarkedCoreRealization_of_oriented
    (B : MarkedRecip Rec K) {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))
    (hdata : NpcMarkedData alpha r h eta
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DN alpha h) (npcNu alpha r h eta)) := by
  obtain ⟨C⟩ := npcCert_marked_matching_certificate_KTwo B e hdata
  exact ⟨npcCert_realization C⟩

end KTwo

/-! ## Axiom pins -/

#print axioms NpcMarkedData
#print axioms npcPlane_normalize
#print axioms npcMarkedMatching
#print axioms npcCert_transport
#print axioms MarkedCoreCertificateNpc
#print axioms npcCert_marked_matching_certificate
#print axioms ztwoIota_npcNu
#print axioms MarkedCoreCertificateKTwoNpc
#print axioms npcCert_marked_matching_certificate_KTwo
#print axioms npcCert_realization
#print axioms npcMarkedCoreRealization_of_oriented

end
end GQ2.Dyadic.Instances.NpcCert
