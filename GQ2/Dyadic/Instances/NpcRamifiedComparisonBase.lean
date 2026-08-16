/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcRamifiedBranch
import GQ2.Dyadic.Instances.NpcWordPhaseModel
import GQ2.Dyadic.Instances.WordPhaseModel

/-!
# Ramified procyclic-N comparison base

The honest ramified Fox row has two entries.  Its normal cocycles therefore have

`x2 = u⁻¹ • (g • x0 - x0)`,

not `x2 = 0`.  This file rebrackets those twisted normal coordinates, optionally replacing
the raw `x0` by an invertible cross coordinate `Phi x0`, and assembles every first-order and
source-comparison step.  The only remaining input is the pointwise source-phase calculation
and quadraticity of its resulting head diagonal.

That input is genuinely second order.  `NpcJetGeneral.npcW_hessRelZTarget_handles` assumes
`x2 = 0`; on the normal cocycles below that would force `g • x0 = x0`.  Moreover the
`omega2` block at nonzero `x2` has the truncated central charge documented in
`NpcRamifiedBranch` and computed opaquely in `NpcRamifiedRow`; it is nonzero in general.
Consequently the phase hypothesis below cannot honestly be replaced by the old Hessian
theorem.  The generic constructor makes this exact boundary explicit without renaming it as
a new proposition.
-/

namespace GQ2.Dyadic.Instances.NpcRamifiedComparisonBase

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.NProcyclic
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.NpcWordPhaseModel

/-- Rebracket the raw twisted coordinates while replacing `c0` by `a = Phi c0`. -/
def wPnpcRamifiedCoordsEquiv (h : ℕ) (A : Type*) [AddCommGroup A] (Phi : A ≃+ A) :
    (A × A × (Fin h × Fin 2 → A)) ≃ ((A × A) × (Fin h → A × A)) where
  toFun r := ((Phi r.1, r.2.1), fun j ↦ finTwoProdAddEquiv (fun k ↦ r.2.2 (j, k)))
  invFun p := (Phi.symm p.1.1, p.1.2,
    fun jk ↦ (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2)
  left_inv r := by
    apply Prod.ext
    · exact Phi.symm_apply_apply r.1
    · apply Prod.ext
      · rfl
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k <;> rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · exact Phi.apply_symm_apply p.1.1
      · rfl
    · funext j
      apply Prod.ext <;> rfl

/-- The honest twisted ramified Npc normal cochain in endpoint bracketing. -/
def wPnpcTwistedPhaseNormal (h : ℕ) {A : Type*} [AddCommGroup A]
    {C : Type*} [Group C] [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) : Generator (2 + 2 * h) → A :=
  let r := (wPnpcRamifiedCoordsEquiv h A Phi).symm p
  evenTwistedNormal h g u r.1 r.2.1 r.2.2

@[simp] theorem wPnpcTwistedPhaseNormal_sigma (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) :
    wPnpcTwistedPhaseNormal h g u Phi p .sigma = 0 := by
  simp [wPnpcTwistedPhaseNormal]

@[simp] theorem wPnpcTwistedPhaseNormal_tau (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) :
    wPnpcTwistedPhaseNormal h g u Phi p .tau = 0 := by
  simp [wPnpcTwistedPhaseNormal]

@[simp] theorem wPnpcTwistedPhaseNormal_coreLetter (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (i : Fin 3) :
    wPnpcTwistedPhaseNormal h g u Phi p (coreLetter h i) =
      ![Phi.symm p.1.1, p.1.2,
        u⁻¹ • (g • Phi.symm p.1.1 - Phi.symm p.1.1)] i := by
  fin_cases i <;> rfl

@[simp] theorem wPnpcTwistedPhaseNormal_handleU {h : ℕ}
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (j : Fin h) :
    wPnpcTwistedPhaseNormal h g u Phi p (handleU j) = (p.2 j).1 := by
  show evenTwistedNormal h g u _ _ _ (handleU j) = _
  rw [evenTwistedNormal_handleU]
  rfl

@[simp] theorem wPnpcTwistedPhaseNormal_handleV {h : ℕ}
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) (j : Fin h) :
    wPnpcTwistedPhaseNormal h g u Phi p (handleV j) = (p.2 j).2 := by
  show evenTwistedNormal h g u _ _ _ (handleV j) = _
  rw [evenTwistedNormal_handleV]
  rfl

theorem wPnpcTwistedPhaseNormal_coordsEquiv (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (r : A × A × (Fin h × Fin 2 → A)) :
    wPnpcTwistedPhaseNormal h g u Phi (wPnpcRamifiedCoordsEquiv h A Phi r) =
      evenTwistedNormal h g u r.1 r.2.1 r.2.2 := by
  simp [wPnpcTwistedPhaseNormal]

@[simp] theorem wPnpcTwistedPhaseNormal_x2 (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A)) :
    wPnpcTwistedPhaseNormal h g u Phi p (.wild (Certificates.x2Idx h)) =
      u⁻¹ • (g • Phi.symm p.1.1 - Phi.symm p.1.1) := by
  change wPnpcTwistedPhaseNormal h g u Phi p (coreLetter h 2) = _
  exact wPnpcTwistedPhaseNormal_coreLetter h g u Phi p 2

/-- The old Hessian theorem's `x2 = 0` premise forces the raw `c0` to be fixed by `g`. -/
theorem fixed_of_wPnpcTwistedPhaseNormal_x2_eq_zero (h : ℕ)
    {A : Type*} [AddCommGroup A] {C : Type*} [Group C]
    [DistribMulAction C A] (g u : C) (Phi : A ≃+ A)
    (p : (A × A) × (Fin h → A × A))
    (hx2 : wPnpcTwistedPhaseNormal h g u Phi p
      (.wild (Certificates.x2Idx h)) = 0) :
    g • Phi.symm p.1.1 = Phi.symm p.1.1 := by
  rw [wPnpcTwistedPhaseNormal_x2] at hx2
  have hz := congrArg (fun x : A ↦ u • x) hx2
  have hdiff : g • Phi.symm p.1.1 - Phi.symm p.1.1 = 0 := by
    simpa using hz
  exact sub_eq_zero.mp hdiff

variable {h q : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [Finite A] [DistribMulAction C A]

omit [Finite A] in
theorem wPnpcTwistedPhaseNormal_closed
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (g u : C) (hrow : IsTwoEntryRamifiedRow t w q g u A)
    (Phi : A ≃+ A) (p : (A × A) × (Fin h → A × A)) :
    heisD1 (A := A) t w (wPnpcTwistedPhaseNormal h g u Phi p) = 0 := by
  unfold wPnpcTwistedPhaseNormal
  exact heisD1_evenTwistedNormal_eq_zero g u t w hrow _ _ _

theorem wPnpcTwistedPhaseNormal_form
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (g u : C) (hrow : IsTwoEntryRamifiedRow t w q g u A)
    (Phi : A ≃+ A)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (htauFpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) t w x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPnpcTwistedPhaseNormal h g u Phi p ∈ Set.range (heisD0 t) := by
  intro x hx
  obtain ⟨r, hrmem, huniq⟩ :=
    evenTwistedNormalForm_of_twoEntry_row g u t w hrow hwild htauFpf hr x hx
  refine ⟨wPnpcRamifiedCoordsEquiv h A Phi r, ?_, ?_⟩
  · change x - wPnpcTwistedPhaseNormal h g u Phi
      (wPnpcRamifiedCoordsEquiv h A Phi r) ∈ _
    rw [wPnpcTwistedPhaseNormal_coordsEquiv]
    exact hrmem
  · intro p hp
    have hpr : (wPnpcRamifiedCoordsEquiv h A Phi).symm p = r := by
      refine huniq _ ?_
      simpa [wPnpcTwistedPhaseNormal] using hp
    rw [← hpr, Equiv.apply_symm_apply]

/-- Assemble the honest ramified normal form into the Npc source/word comparison.

The only analytic hypothesis is `hphase`.  The separate `hd0` is exactly the additional fact
needed by `wPnpcPhaseModel`; the result is returned in that model's conjunction shape. -/
noncomputable def wPnpcPhaseComparison_of_twistedHeadPhase
    {alpha r h q N : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0))
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (g u : DD.C0) (Phi : DD.Vmod ≃+ DD.Vmod)
    (hrow : IsTwoEntryRamifiedRow
      (Marking.mk (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
      (resolvedFamily alpha r h q d N) q g u DD.Vmod)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) • v = v → v = 0)
    (hr : ∀ k, FreeGroup.lift
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
      (resolvedFamily alpha r h q d N k) = 1)
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (a : ZMod 2), gamma • a = a)
    (d0 : DD.Vmod → ZMod 2) (hd0 : IsQuadraticFp2 d0)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) =
          wPnpcTwistedPhaseNormal h g u Phi p →
      QZero DD rho c = wPnpcWallHandlePhase d0 DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    IsQuadraticFp2 d0 ∧ Nonempty (SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h)) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  refine ⟨hd0, ⟨?_⟩⟩
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPnpcTwistedPhaseNormal h g u Phi)
    (wPnpcTwistedPhaseNormal_closed _ _ g u hrow Phi)
    (wPnpcTwistedPhaseNormal_form _ _ g u hrow Phi hwild htauFpf hr)
    htriv (wPnpcWallHandlePhase d0 DD.qbar h) hphase

#print axioms wPnpcRamifiedCoordsEquiv
#print axioms wPnpcTwistedPhaseNormal
#print axioms wPnpcTwistedPhaseNormal_coreLetter
#print axioms fixed_of_wPnpcTwistedPhaseNormal_x2_eq_zero
#print axioms wPnpcTwistedPhaseNormal_closed
#print axioms wPnpcTwistedPhaseNormal_form
#print axioms wPnpcPhaseComparison_of_twistedHeadPhase

end
end GQ2.Dyadic.Instances.NpcRamifiedComparisonBase
