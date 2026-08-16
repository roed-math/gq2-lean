/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCertificate
import GQ2.Dyadic.CertificateSupplyFamilyRN

/-!
# Positive-level Npc normalization from field data

This module sharpens `NpcCertificate` at positive level. The field level makes every
cyclotomic-kernel coordinate divisible by `2^r`, but the existing handle clearer assumes a
unit pivot. The first section proves the needed divisible-pivot variant directly from the
committed Eichler frame moves and lifts it to `DN alpha h`.

The resulting normalization requires three named inputs:

* `NpcChiKerLevel`, derived from `MarkedRecip.nu_ker_chi_le`;
* `NpcX1Residue`, derived from the family selector's `IsEtaFor` equation;
* `NpcPlanePrimitiveAtLevel`, the primitive quotient condition on the chosen
  `(sigma, x2)` plane.

The first two are discharged by `FamilyFieldBranchSelection`. The last is deliberately
retained: `SemanticSelectedCoreLeavesRN.ofNpc` packages the canonical target presentation and
marking, not the transported coordinates of an arbitrary oriented field equivalence.

The headline `npcMarkedCoreRealization_of_familySelection` therefore exposes exactly the
remaining plane premise and constructs the required positive-level `MarkedCoreRealization`.
No new axiom is introduced; every declaration has the standard axiom set.
-/

namespace GQ2.Dyadic.Instances.NpcCertificateLevel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.NpcCert
open GQ2.Dyadic.SelectedCoreLeavesRN

/-! ## Divisible-pivot handle clearing -/

/-- Clear one handle when its two coordinates are explicit multiples of the pivot. -/
theorem exists_frameClear_one_of_mul
    {h : ℕ} (j : Fin h) (v : Fin (coreRank h) → ℤ_[2]) (d u z : ℤ_[2])
    (hpiv : v 2 = d)
    (hU : v (handleIdxU j) = d * u)
    (hV : v (handleIdxV j) = d * z) :
    ∃ phi ∈ Submonoid.closure (frameClearGens h),
      phi v (handleIdxU j) = 0 ∧ phi v (handleIdxV j) = 0 ∧ phi v 2 = v 2 ∧
      phi v 1 = v 1 ∧
      (∀ i : Fin h, i ≠ j → phi v (handleIdxU i) = v (handleIdxU i)) ∧
      ∀ i : Fin h, i ≠ j → phi v (handleIdxV i) = v (handleIdxV i) := by
  refine ⟨frameEnd (frameEichlerV j (-z)) * frameEnd (frameEichlerU j (-u)),
    mul_mem (frameEichlerV_mem_clearGens _ _) (frameEichlerU_mem_clearGens _ _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show frameEichlerV j (-z) (frameEichlerU j (-u) v) (handleIdxU j) = 0
    rw [frameEichlerV_handleU, frameEichlerU_handleU_self, smul_eq_mul, hpiv, hU]
    ring
  · show frameEichlerV j (-z) (frameEichlerU j (-u) v) (handleIdxV j) = 0
    rw [frameEichlerV_handleV_self, frameEichlerU_handleV, frameEichlerU_two,
      smul_eq_mul, hpiv, hV]
    ring
  · show frameEichlerV j (-z) (frameEichlerU j (-u) v) 2 = v 2
    rw [frameEichlerV_two, frameEichlerU_two]
  · show frameEichlerV j (-z) (frameEichlerU j (-u) v) 1 = v 1
    rw [frameEichlerV_of_ne _ _ _ (Ne.symm (nHandleIdxV_ne_one j))
      (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega)),
      frameEichlerU_of_ne _ _ _ (Ne.symm (nHandleIdxU_ne_one j))
        (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))]
  · intro i hij
    show frameEichlerV j (-z) (frameEichlerU j (-u) v) (handleIdxU i) =
      v (handleIdxU i)
    rw [frameEichlerV_handleU, frameEichlerU_handleU_of_ne _ _ _ hij]
  · intro i hij
    show frameEichlerV j (-z) (frameEichlerU j (-u) v) (handleIdxV i) =
      v (handleIdxV i)
    rw [frameEichlerV_of_ne _ _ _ (fun hc => hij (handleIdxV_injective hc))
      (handleIdxV_ne_three i), frameEichlerU_handleV]

/-- Clear the first `n` handles, retaining the untouched tail coordinates. -/
theorem exists_frameClear_lt_of_mul
    {h : ℕ} (v : Fin (coreRank h) → ℤ_[2]) (d : ℤ_[2])
    (hpiv : v 2 = d)
    (hU : ∀ j : Fin h, ∃ u : ℤ_[2], v (handleIdxU j) = d * u)
    (hV : ∀ j : Fin h, ∃ z : ℤ_[2], v (handleIdxV j) = d * z)
    (n : ℕ) :
    ∃ phi ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, (j : ℕ) < n →
        phi v (handleIdxU j) = 0 ∧ phi v (handleIdxV j) = 0) ∧
      phi v 2 = v 2 ∧
      phi v 1 = v 1 ∧
      (∀ j : Fin h, n ≤ (j : ℕ) → phi v (handleIdxU j) = v (handleIdxU j)) ∧
      ∀ j : Fin h, n ≤ (j : ℕ) → phi v (handleIdxV j) = v (handleIdxV j) := by
  induction n with
  | zero =>
      exact ⟨1, one_mem _, fun j hj => absurd hj (by omega), rfl, rfl,
        fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨phi, hphi, hclear, htwo, hone, hUtail, hVtail⟩ := ih
    by_cases hn : n < h
    · let jn : Fin h := ⟨n, hn⟩
      obtain ⟨u, hu⟩ := hU jn
      obtain ⟨z, hz⟩ := hV jn
      obtain ⟨psi, hpsi, hUc, hVc, htwo', hone', hUne, hVne⟩ :=
        exists_frameClear_one_of_mul jn (phi v) d u z
          (by rw [htwo, hpiv])
          (by rw [hUtail jn (by simp [jn]), hu])
          (by rw [hVtail jn (by simp [jn]), hz])
      refine ⟨psi * phi, mul_mem hpsi hphi, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        by_cases hjn : (j : ℕ) = n
        · have hje : j = jn := Fin.ext hjn
          subst hje
          exact ⟨hUc, hVc⟩
        · have hjne : j ≠ jn := fun hc => hjn (by rw [hc])
          obtain ⟨hcU, hcV⟩ := hclear j (by omega)
          exact ⟨(hUne j hjne).trans hcU, (hVne j hjne).trans hcV⟩
      · show psi (phi v) 2 = v 2
        rw [htwo', htwo]
      · show psi (phi v) 1 = v 1
        rw [hone', hone]
      · intro j hj
        have hjne : j ≠ jn := by
          intro hje
          have : (j : ℕ) = n := by rw [hje]
          omega
        exact (hUne j hjne).trans (hUtail j (by omega))
      · intro j hj
        have hjne : j ≠ jn := by
          intro hje
          have : (j : ℕ) = n := by rw [hje]
          omega
        exact (hVne j hjne).trans (hVtail j (by omega))
    · refine ⟨phi, hphi, fun j hj => hclear j ?_, htwo, hone, ?_, ?_⟩
      · have := j.isLt
        omega
      · intro j hj
        have : False := by omega
        exact this.elim
      · intro j hj
        have : False := by omega
        exact this.elim

/-- Clear every handle coordinate whose value is divisible by the pivot. -/
theorem exists_frameClear_of_mul
    {h : ℕ} (v : Fin (coreRank h) → ℤ_[2]) (d : ℤ_[2])
    (hpiv : v 2 = d)
    (hU : ∀ j : Fin h, ∃ u : ℤ_[2], v (handleIdxU j) = d * u)
    (hV : ∀ j : Fin h, ∃ z : ℤ_[2], v (handleIdxV j) = d * z) :
    ∃ phi ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, phi v (handleIdxU j) = 0) ∧
      (∀ j : Fin h, phi v (handleIdxV j) = 0) ∧ phi v 2 = v 2 ∧
      phi v 1 = v 1 := by
  obtain ⟨phi, hphi, hclear, htwo, hone, -, -⟩ :=
    exists_frameClear_lt_of_mul v d hpiv hU hV h
  exact ⟨phi, hphi, fun j => (hclear j j.isLt).1,
    fun j => (hclear j j.isLt).2, htwo, hone⟩

/-- Lift divisible-pivot handle clearing to the N-core. -/
theorem exists_dnClear_nu_of_mul
    {alpha r h : ℕ}
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    (hpiv : toAdd (nu' (dnSigma alpha h)) = 2 ^ r)
    (hU : ∀ j : Fin h, ∃ u : ℤ_[2],
      toAdd (nu' (dnGen alpha h (handleIdxU j))) = 2 ^ r * u)
    (hV : ∀ j : Fin h, ∃ z : ℤ_[2],
      toAdd (nu' (dnGen alpha h (handleIdxV j))) = 2 ^ r * z) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ j : Fin h, nu' (Psi (dnGen alpha h (handleIdxU j))) = 1) ∧
      (∀ j : Fin h, nu' (Psi (dnGen alpha h (handleIdxV j))) = 1) ∧
      nu' (Psi (dnX1 alpha h)) = nu' (dnX1 alpha h) ∧
      nu' (Psi (dnSigma alpha h)) = nu' (dnSigma alpha h) := by
  obtain ⟨F, hF, hFU, hFV, hFtwo, hFone⟩ :=
    exists_frameClear_of_mul (nuFrame nu' (dnGen alpha h)) (2 ^ r) hpiv hU hV
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dnRealizes alpha h hF
  refine ⟨Psi, fun x => chiN_of_mem_dnClearAuts alpha h hmem x, ?_, ?_, ?_, ?_⟩
  · intro j
    apply Multiplicative.toAdd.injective
    have hrow := congrFun (hbridge nu') (handleIdxU j)
    rw [hFU j] at hrow
    exact hrow.trans toAdd_one.symm
  · intro j
    apply Multiplicative.toAdd.injective
    have hrow := congrFun (hbridge nu') (handleIdxV j)
    rw [hFV j] at hrow
    exact hrow.trans toAdd_one.symm
  · apply Multiplicative.toAdd.injective
    have hrow := congrFun (hbridge nu') 1
    rw [hFone] at hrow
    exact hrow
  · apply Multiplicative.toAdd.injective
    have hrow := congrFun (hbridge nu') 2
    rw [hFtwo] at hrow
    exact hrow

/-! ## Level-form Npc normalization -/

/-- The field level, read on the N-core. -/
def NpcChiKerLevel (alpha r h : ℕ)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∀ x, chiN alpha h x = 1 → ∃ y : ℤ_[2], toAdd (nu' x) = 2 ^ r * y

/-- The only primitive-coordinate input left after the level and eta equations are used. -/
def NpcPlanePrimitiveAtLevel (alpha r h : ℕ)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ a b : ℤ_[2],
    toAdd (nu' (dnSigma alpha h)) = 2 ^ r * a ∧
    toAdd (nu' (dnX2 alpha h)) = 2 ^ r * b ∧
    (IsUnit a ∨ IsUnit b)

/-- The selected eta is the residue of the transported x1-coordinate modulo the level. -/
def NpcX1Residue (alpha r h : ℕ) (eta : ℤ_[2]ˣ)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ w : ℤ_[2], toAdd (nu' (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w

/-- The level and x1 residue, plus a primitive quotient plane, suffice for full Npc marking
compatibility.  Handle divisibility comes from the level and is cleared by
`exists_dnClear_nu_of_mul`. -/
theorem npcMarkedMatching_of_level
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : NpcChiKerLevel alpha r h nu')
    (hplane : NpcPlanePrimitiveAtLevel alpha r h nu')
    (hx1 : NpcX1Residue alpha r h eta nu') :
    ∃ u : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (u x) = chiN alpha h x) ∧
      ∀ x, nu' (u x) = npcNuPadic alpha r h eta x := by
  rcases hplane with ⟨a, b, hsigma, hx2, hpair⟩
  rcases hx1 with ⟨w, hx1⟩
  obtain ⟨Psi0, h0chi, hsigma0, -, h0other⟩ :=
    npcPlane_normalize nu' hsigma hx2 hpair
  let nu2 : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Psi0)
  have hlev2 : NpcChiKerLevel alpha r h nu2 := by
    intro x hx
    apply hlev (Psi0 x)
    exact (h0chi x).trans hx
  have hsigma2 : toAdd (nu2 (dnSigma alpha h)) = 2 ^ r := hsigma0
  have hx12 : toAdd (nu2 (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w := by
    exact (h0other 1 nCoreOne_ne_two
      (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))).trans hx1
  have hU2 : ∀ j : Fin h, ∃ y : ℤ_[2],
      toAdd (nu2 (dnGen alpha h (handleIdxU j))) = 2 ^ r * y := by
    intro j
    apply hlev2
    exact chiN_handleU alpha h j
  have hV2 : ∀ j : Fin h, ∃ y : ℤ_[2],
      toAdd (nu2 (dnGen alpha h (handleIdxV j))) = 2 ^ r * y := by
    intro j
    apply hlev2
    exact chiN_handleV alpha h j
  obtain ⟨Psih, hhchi, hUh, hVh, hx1h, hsigmah⟩ :=
    exists_dnClear_nu_of_mul nu2 hsigma2 hU2 hV2
  let nu3 : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu2.comp (autHom Psih)
  have hlev3 : NpcChiKerLevel alpha r h nu3 := by
    intro x hx
    apply hlev2 (Psih x)
    exact (hhchi x).trans hx
  have hsigma3 : toAdd (nu3 (dnSigma alpha h)) = 2 ^ r := by
    show toAdd (nu2 (Psih (dnSigma alpha h))) = 2 ^ r
    rw [hsigmah]
    exact hsigma2
  have hx13 : toAdd (nu3 (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w := by
    show toAdd (nu2 (Psih (dnX1 alpha h))) = _
    rw [hx1h]
    exact hx12
  have hU3 : ∀ j : Fin h, nu3 (dnGen alpha h (handleIdxU j)) = 1 := hUh
  have hV3 : ∀ j : Fin h, nu3 (dnGen alpha h (handleIdxV j)) = 1 := hVh
  obtain ⟨c, hx23⟩ := hlev3 (dnX2 alpha h) (chiN_dnX2 alpha h)
  let k : ℤ_[2] := -c
  let nu4 : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu3.comp (autHom (dnTauDEquiv alpha h k))
  have hgen4 : ∀ i : Fin (coreRank h),
      nu4 (dnGen alpha h i) =
        nu3 (tauDMark (isProP_DN alpha h) k (dnGen alpha h) i) := fun i => by
    show nu3 (dnTauDEquiv alpha h k (dnGen alpha h i)) = _
    rw [dnTauDEquiv_gen]
  have hsigma4 : toAdd (nu4 (dnSigma alpha h)) = 2 ^ r := by
    rw [show dnSigma alpha h = dnGen alpha h 2 from rfl, hgen4, tauDMark_two]
    exact hsigma3
  have hx24 : toAdd (nu4 (dnX2 alpha h)) = 0 := by
    rw [show dnX2 alpha h = dnGen alpha h 3 from rfl, hgen4, tauDMark_three,
      map_mul, toAdd_mul, toAdd_map_zpowZtwo (isProP_DN alpha h) nu3,
      show dnGen alpha h 2 = dnSigma alpha h from rfl, hsigma3,
      show dnGen alpha h 3 = dnX2 alpha h from rfl, hx23]
    dsimp only [k]
    ring
  have hx14 : toAdd (nu4 (dnX1 alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w := by
    rw [show dnX1 alpha h = dnGen alpha h 1 from rfl, hgen4,
      tauDMark_of_ne _ _ _
        (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))]
    exact hx13
  have hU4 : ∀ j : Fin h, nu4 (dnGen alpha h (handleIdxU j)) = 1 := by
    intro j
    rw [hgen4, tauDMark_of_ne _ _ _ (handleIdxU_ne_three j)]
    exact hU3 j
  have hV4 : ∀ j : Fin h, nu4 (dnGen alpha h (handleIdxV j)) = 1 := by
    intro j
    rw [hgen4, tauDMark_of_ne _ _ _ (handleIdxV_ne_three j)]
    exact hV3 j
  obtain ⟨Psi5, h5chi, h5frame⟩ := nMixHypothesis_coreMix alpha h (-w)
  refine ⟨Psi5.trans ((dnTauDEquiv alpha h k).trans (Psih.trans Psi0)),
    fun x => ?_, ?_⟩
  · show chiN alpha h (Psi0 (Psih (dnTauDEquiv alpha h k (Psi5 x)))) =
      chiN alpha h x
    rw [h0chi, hhchi, chiN_dnTauDEquiv, h5chi]
  · have hgen : ∀ i : Fin (coreRank h),
        nu4 (Psi5 (dnGen alpha h i)) = npcNuPadic alpha r h eta (dnGen alpha h i) := by
      intro i
      have hrow := congrFun (h5frame nu4) i
      rw [nuFrame_apply, nFrameMixX1] at hrow
      apply Multiplicative.toAdd.injective
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hrow, Function.update_of_ne nCoreZero_ne_one, nuFrame_apply,
          show dnGen alpha h 0 = dnX0 alpha h from rfl, nChar_dnX0, toAdd_one]
        change 0 = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 0))
        rw [npcNuPadic_gen_zero, toAdd_ofAdd]
      · rw [hrow, Function.update_self, nuFrame_apply, nuFrame_apply,
          show dnGen alpha h 1 = dnX1 alpha h from rfl,
          show dnGen alpha h 2 = dnSigma alpha h from rfl, hx14, hsigma4]
        change (eta : ℤ_[2]) + 2 ^ r * w + -w * 2 ^ r =
          toAdd (npcNuPadic alpha r h eta (dnGen alpha h 1))
        rw [npcNuPadic_gen_one, toAdd_ofAdd]
        ring
      · rw [hrow, Function.update_of_ne nCoreTwo_ne_one, nuFrame_apply,
          show dnGen alpha h 2 = dnSigma alpha h from rfl, hsigma4]
        change 2 ^ r = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 2))
        rw [npcNuPadic_gen_two, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne nCoreThree_ne_one, nuFrame_apply,
          show dnGen alpha h 3 = dnX2 alpha h from rfl, hx24]
        change 0 = toAdd (npcNuPadic alpha r h eta (dnGen alpha h 3))
        rw [npcNuPadic_gen_three, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne (nHandleIdxU_ne_one j), nuFrame_apply,
          hU4 j, npcNuPadic_gen_handleU, toAdd_one]
      · rw [hrow, Function.update_of_ne (nHandleIdxV_ne_one j), nuFrame_apply,
          hV4 j, npcNuPadic_gen_handleV, toAdd_one]
    have heq : nu4.comp (autHom Psi5) = npcNuPadic alpha r h eta :=
      dn_hom_ext _ _ hgen
    intro x
    exact DFunLike.congr_fun heq x

/-! ## Field and selector adapters -/

section Field

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The bundle level transported to an arbitrary oriented N-core equivalence. -/
theorem npcChiKerLevel_of_level
    (B : MarkedRecip Rec K) {alpha r h : ℕ} (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    NpcChiKerLevel alpha r h
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)) := by
  intro x hx
  obtain ⟨g, hg⟩ := maxProPMk_surjective (p := 2) (G := GalK K) (e.1 x)
  have hchi : chiCycKAb K (toAbK K g) = 1 := by
    rw [chiCycKAb_toAbK, ← chiCycKTwo_maxProPMk, hg]
    exact (e.2 x).trans hx
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le _ hchi
  refine ⟨y, ?_⟩
  change toAdd (nuUrKTwo B (e.1 x)) = 2 ^ r * y
  rw [← hg, nuUrKTwo_maxProPMk, ← hr]
  exact hy

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The selector's eta equation is exactly the transported x1 residue. -/
theorem npcX1Residue_of_isEtaFor
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ} (hr : B.r = r)
    (hmem : nUnit alpha ∈ (B.fieldMarkedPair FF).C)
    (heta : IsEtaFor (B.fieldMarkedPair FF).datum ⟨nUnit alpha, hmem⟩ eta)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    NpcX1Residue alpha r h eta
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)) := by
  let P := B.fieldMarkedPair FF
  obtain ⟨g, hg⟩ := maxProPMk_surjective (p := 2) (G := GalK K)
    (e.1 (dnX1 alpha h))
  have hchi : P.chi (toAbK K g) = nUnit alpha := by
    change chiCycKAb K (toAbK K g) = nUnit alpha
    rw [chiCycKAb_toAbK, ← chiCycKTwo_maxProPMk, hg]
    exact (e.2 (dnX1 alpha h)).trans (chiN_dnX1 alpha h)
  have heta' : P.lambdaAt (nUnit alpha) hmem =
      PadicInt.toZModPow P.r (eta : ℤ_[2]) :=
    (P.isEtaFor_datum_iff (nUnit alpha) hmem eta).mp heta
  have hnuMod : PadicInt.toZModPow P.r
      (P.nu (toAbK K g)).toAdd = PadicInt.toZModPow P.r (eta : ℤ_[2]) :=
    (P.lambdaAt_spec (nUnit alpha) hmem (toAbK K g) hchi).symm.trans heta'
  have hmod : PadicInt.toZModPow r
      (toAdd (nuUrKTwo B (e.1 (dnX1 alpha h))) - (eta : ℤ_[2])) = 0 := by
    rw [map_sub, ← hg, nuUrKTwo_maxProPMk]
    change PadicInt.toZModPow r
      ((P.nu (toAbK K g)).toAdd) - PadicInt.toZModPow r (eta : ℤ_[2]) = 0
    change PadicInt.toZModPow B.r
      ((P.nu (toAbK K g)).toAdd) = PadicInt.toZModPow B.r (eta : ℤ_[2]) at hnuMod
    rw [hr] at hnuMod
    exact sub_eq_zero.mpr hnuMod
  obtain ⟨w, hw⟩ := MarkedPair.exists_eq_two_pow_mul hmod
  exact ⟨w, by
    change toAdd (nuUrKTwo B (e.1 (dnX1 alpha h))) =
      (eta : ℤ_[2]) + 2 ^ r * w
    linear_combination hw⟩

/-- Build the field-side realization from the reduced three-clause input. -/
theorem npcMarkedCoreRealization_of_level
    (B : MarkedRecip Rec K) {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))
    (hlev : NpcChiKerLevel alpha r h
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)))
    (hplane : NpcPlanePrimitiveAtLevel alpha r h
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)))
    (hx1 : NpcX1Residue alpha r h eta
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DN alpha h) (npcNu alpha r h eta)) := by
  obtain ⟨u, -, hunu⟩ := npcMarkedMatching_of_level _ hlev hplane hx1
  exact ⟨{
    equiv := u.trans e.1
    nu_equiv := fun x => (ztwoIota_npcNu alpha r h eta x).trans (hunu x).symm }⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- On an Npc branch, the family selector exposes exactly the selected eta equation. -/
theorem familyNpc_isEtaFor
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)}
    {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) :
    ∃ hmem : nUnit alpha ∈ Q.C,
      IsEtaFor Q.datum ⟨nUnit alpha, hmem⟩ eta := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
    dsimp only at hbranch
    subst branch
    cases W with
    | L degree_odd level_zero =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | M beta hbeta heven marked =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | N beta hbeta heven marked =>
        simp only [FamilyFieldBranchWitness.Matches] at arithmetic_matches
        rcases arithmetic_matches with ⟨rfl, -, heta⟩
        exact ⟨marked.unit_mem, heta⟩

/-- The corrected family selector closes the level and eta clauses.  The only remaining
field-side input is the primitive quotient condition on the selected `(sigma,x2)` plane. -/
theorem npcMarkedCoreRealization_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K)))
    (hplane : NpcPlanePrimitiveAtLevel alpha r
      (handleCount FP (.Npc alpha r eta))
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DN alpha (handleCount FP (.Npc alpha r eta)))
      (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta)) := by
  have hr : B.r = r := by
    have h := S.level_eq
    rw [hbranch] at h
    exact h.symm
  obtain ⟨hmem, heta⟩ := familyNpc_isEtaFor S hbranch
  apply npcMarkedCoreRealization_of_level B e
  · exact npcChiKerLevel_of_level B hr e
  · exact hplane
  · exact npcX1Residue_of_isEtaFor B FF hr hmem heta e

end Field

#print axioms exists_frameClear_one_of_mul
#print axioms exists_frameClear_lt_of_mul
#print axioms exists_frameClear_of_mul
#print axioms exists_dnClear_nu_of_mul
#print axioms NpcChiKerLevel
#print axioms NpcPlanePrimitiveAtLevel
#print axioms NpcX1Residue
#print axioms npcMarkedMatching_of_level
#print axioms npcChiKerLevel_of_level
#print axioms npcX1Residue_of_isEtaFor
#print axioms npcMarkedCoreRealization_of_level
#print axioms familyNpc_isEtaFor
#print axioms npcMarkedCoreRealization_of_familySelection

end
end GQ2.Dyadic.Instances.NpcCertificateLevel
