/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcWordPhaseSeam
import GQ2.Dyadic.Instances.MpcUnramifiedHessian
import GQ2.Dyadic.Instances.NpcJetGeneral

/-!
# The unramified Npc Hessian at full operator-twisted offsets

This file evaluates the corrected procyclic-N word without imposing the old boundary condition
`x₂ = 0`.  The delta and correction blocks vanish at an honest unramified resolver; the inverse
boundary conjugate contributes the missing `polar q x₂ x₁` term.  At the operator-twisted normal
coordinates `x₂ = Φ x₀`, the result is an opaque diagonal in `x₀`, the expected cross term
`polar q x₁ (Φ x₀)`, and the standard hyperbolic handle tail.

This closes the full-offset word/Hessian decomposition only.  Proving that
`npcUnramifiedDiagonal` is quadratic, identifying it with a standard Npc diagonal, and evaluating
its Gauss sum remain separate inputs.
-/

namespace GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MCompact

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

section Word

variable {h : ℕ} (s : C) (vv : Fin (2 + 2 * h + 1) → V)
  (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

private noncomputable abbrev mu :=
  WordCoh.lift (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat)

theorem evalZ_deltaZeroW_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (deltaZeroW h) = 1 := by
  rw [deltaZeroW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_inv, PWord.evalZ_gen, mul_one]
  rw [hessDeltaBlock_P1 dat hdat hV2 s vv E E₂ hE he 0]
  change hessSlice dat hdat (vv (Certificates.x0Idx h)) 0 *
      (hessSlice dat hdat (vv (Certificates.x0Idx h)) 0)⁻¹ = 1
  exact mul_inv_cancel _

theorem evalZ_dBlockW_one (hV2 : ∀ v : V, v + v = 0) {eω : ℕ}
    (hE : E omega2 = (eω : ℤ)) (he : eω % 4 = 1) (r : ℕ) (d : EtaData) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (dBlockW h r d) = 1 := by
  rw [dBlockW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_conj, PWord.evalZ_inv, mul_one]
  simp [evalZ_deltaZeroW_one dat hdat s vv E E₂ hV2 hE he, conjR]

theorem evalZ_eBlockW_one (hV2 : ∀ v : V, v + v = 0) {eω : ℕ}
    (hE : E omega2 = (eω : ℤ)) (he : eω % 4 = 1) (r : ℕ) (d : EtaData) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (eBlockW h r d) = 1 := by
  rw [eBlockW, PWord.evalZ_comm,
    evalZ_dBlockW_one dat hdat s vv E E₂ hV2 hE he r d]
  simp [commR]

theorem conjR_slice_mul_line
    (hV2 : ∀ v : V, v + v = 0) (c₁ c₂ : V) (B : C) :
    conjR (hessSlice dat hdat c₂ 0)
        (hessSlice dat hdat c₁ 0 * hessLine dat hdat B) =
      conjR (hessSlice dat hdat c₂ 0) (hessLine dat hdat B) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q c₂ c₁) := by
  let x := hessSlice dat hdat c₂ 0
  let y := hessSlice dat hdat c₁ 0
  let z := hessLine dat hdat B
  let cc := WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q c₂ c₁)
  have hc : commR x y = cc := hessSlice_commR dat hdat hV2 c₂ c₁ 0 0
  change x⁻¹ * y⁻¹ * x * y = cc at hc
  have hxy : y⁻¹ * x * y = x * cc := by
    calc
      y⁻¹ * x * y = x * (x⁻¹ * y⁻¹ * x * y) := by group
      _ = x * cc := by rw [hc]
  change conjR x (y * z) = conjR x z * cc
  rw [conjR, mul_inv_rev]
  calc
    z⁻¹ * y⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z := by group
    _ = z⁻¹ * (x * cc) * z := by rw [hxy]
    _ = z⁻¹ * x * (cc * z) := by group
    _ = z⁻¹ * x * (z * cc) := by rw [(Certificates.MpcJet.incl_commute _ _).eq]
    _ = z⁻¹ * x * z * cc := by group

theorem inv_conjR_slice_mul_line
    (hV2 : ∀ v : V, v + v = 0) (c₁ c₂ : V) (B : C) :
    (conjR (hessSlice dat hdat c₂ 0)
        (hessSlice dat hdat c₁ 0 * hessLine dat hdat B))⁻¹ =
      (conjR (hessSlice dat hdat c₂ 0) (hessLine dat hdat B))⁻¹ *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q c₂ c₁) := by
  rw [conjR_slice_mul_line dat hdat hV2, mul_inv_rev]
  let cc := WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q c₂ c₁)
  have hcinv : cc⁻¹ = cc := by
    calc
      cc⁻¹ = cc⁻¹ * 1 := by rw [mul_one]
      _ = cc⁻¹ * (cc * cc) := by rw [centExt_incl_mul_self]
      _ = cc := by group
  rw [hcinv, (Certificates.MpcJet.incl_commute _ _).eq]

theorem evalZ_bW_line (r : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (bW h r) =
      hessLine dat hdat (s ^ (2 ^ r : ℤ)) := by
  rw [bW, PWord.evalZ_zpow, PWord.evalZ_gen]
  change (hessLineHom dat hdat s) ^ (2 ^ r : ℤ) = hessLineHom dat hdat (s ^ (2 ^ r : ℤ))
  exact (map_zpow (hessLineHom dat hdat) s (2 ^ r : ℤ)).symm

theorem evalZ_aW_line (d : EtaData) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (aW h d) =
      hessLine dat hdat (s ^ E d.toZhat) := by
  rw [aW, PWord.evalZ_profPow, PWord.evalZ_gen]
  change (hessLineHom dat hdat s) ^ E d.toZhat = hessLineHom dat hdat (s ^ E d.toZhat)
  exact (map_zpow (hessLineHom dat hdat) s (E d.toZhat)).symm

theorem evalZ_boundaryInvConj
    (hV2 : ∀ v : V, v + v = 0) (r : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂
        (.inv (.conj (.gen (coreLetter h 2))
          (PWord.prodList [.gen (coreLetter h 1), bW h r]))) =
      (conjR (hessSlice dat hdat (vv (Certificates.x2Idx h)) 0)
          (hessLine dat hdat (s ^ (2 ^ r : ℤ))))⁻¹ *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) := by
  rw [PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen,
    PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_gen, mul_one]
  rw [evalZ_bW_line dat hdat s vv E E₂ r]
  change (conjR (hessSlice dat hdat (vv (Certificates.x2Idx h)) 0)
      (hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 *
        hessLine dat hdat (s ^ (2 ^ r : ℤ))))⁻¹ = _
  exact inv_conjR_slice_mul_line dat hdat hV2 _ _ _

/-- The part of the unramified Npc value that is independent of `x₁` and the handles. -/
noncomputable def npcUnramifiedCoreElt (α r : ℕ) (d : EtaData) (c₀ c₂ : V) :
    WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  hessSlice dat hdat c₀ 0 ^ ((2 : ℤ) + 2 ^ α) *
    (commR (hessSlice dat hdat c₀ 0) (hessLine dat hdat (s ^ E d.toZhat)) *
      ((conjR (hessSlice dat hdat c₂ 0)
        (hessLine dat hdat (s ^ (2 ^ r : ℤ))))⁻¹ * hessSlice dat hdat c₂ 0))

theorem evalZ_npcW_fullOffset
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hV2 : ∀ v : V, v + v = 0) {eω : ℕ}
    (hE : E omega2 = (eω : ℤ)) (he : eω % 4 = 1)
    (α r : ℕ) (d : EtaData) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (npcW α r h d) =
      npcUnramifiedCoreElt dat hdat s E α r d
          (vv (Certificates.x0Idx h)) (vv (Certificates.x2Idx h)) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) := by
  rw [npcW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_comm, mul_one]
  rw [evalZ_aW_line dat hdat s vv E E₂ d,
    evalZ_boundaryInvConj dat hdat s vv E E₂ hV2 r,
    hessDeltaBlock_P1 dat hdat hV2 s vv E E₂ hE he 2,
    evalZ_eBlockW_one dat hdat s vv E E₂ hV2 hE he r d,
    one_mul,
    Certificates.hess_handlesW_eval dat hdat hV2 s 1 vv E E₂]
  rw [show mu dat hdat s vv (coreLetter h 0) =
      hessSlice dat hdat (vv (Certificates.x0Idx h)) 0 from rfl]
  unfold npcUnramifiedCoreElt
  rw [show WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) =
        hessSlice dat hdat 0
          (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) from rfl]
  rw [show vv (xIdx h 2) = vv (Certificates.x2Idx h) from rfl]
  have hc := Certificates.MpcJet.incl_commute
    (c := kappa0Cocycle dat hdat)
    (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h)))
    (hessSlice dat hdat (vv (Certificates.x2Idx h)) 0)
  simp only [mul_assoc]
  rw [← mul_assoc
    (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))))
    (hessSlice dat hdat (vv (Certificates.x2Idx h)) 0)
    (hessSlice dat hdat 0
      (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))))]
  rw [hc.eq]
  group

/-- The diagonal left after removing the full-offset `x₁` cross term. -/
noncomputable def npcUnramifiedDiagonal (α r : ℕ) (d : EtaData) (Φ : V →+ V)
    (c₀ : V) : ZMod 2 :=
  (npcUnramifiedCoreElt dat hdat s E α r d c₀ (Φ c₀)).fib

/-- The wild-coordinate vector underlying an operator-twisted normal cochain. -/
def npcPhiOffsets (h : ℕ) (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) : Fin (2 + 2 * h + 1) → V :=
  fun i ↦ evenPhiNormal h Φ c₀ c₁ z (.wild i)

@[simp] theorem npcPhiOffsets_x0 (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) :
    npcPhiOffsets h Φ c₀ c₁ z (Certificates.x0Idx h) = c₀ := by
  change evenPhiNormal h Φ c₀ c₁ z (coreLetter h 0) = c₀
  simp

@[simp] theorem npcPhiOffsets_x1 (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) :
    npcPhiOffsets h Φ c₀ c₁ z (Certificates.x1Idx h) = c₁ := by
  change evenPhiNormal h Φ c₀ c₁ z (coreLetter h 1) = c₁
  simp

@[simp] theorem npcPhiOffsets_x2 (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) :
    npcPhiOffsets h Φ c₀ c₁ z (Certificates.x2Idx h) = Φ c₀ := by
  change evenPhiNormal h Φ c₀ c₁ z (coreLetter h 2) = Φ c₀
  simp

@[simp] theorem npcPhiOffsets_hIdxU (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) (j : Fin h) :
    npcPhiOffsets h Φ c₀ c₁ z (Certificates.hIdxU j) = z (j, 0) := by
  change evenPhiNormal h Φ c₀ c₁ z (handleU j) = z (j, 0)
  exact evenPhiNormal_handleU Φ c₀ c₁ z j

@[simp] theorem npcPhiOffsets_hIdxV (Φ : V →+ V) (c₀ c₁ : V)
    (z : Fin h × Fin 2 → V) (j : Fin h) :
    npcPhiOffsets h Φ c₀ c₁ z (Certificates.hIdxV j) = z (j, 1) := by
  change evenPhiNormal h Φ c₀ c₁ z (handleV j) = z (j, 1)
  exact evenPhiNormal_handleV Φ c₀ c₁ z j

theorem hessRelZ_npcW_evenPhiNormal
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    (hV2 : ∀ v : V, v + v = 0) {eω : ℕ}
    (hE : E omega2 = (eω : ℤ)) (he : eω % 4 = 1)
    (α r : ℕ) (d : EtaData) (Φ : V →+ V)
    (c₀ c₁ : V) (z : Fin h × Fin 2 → V) :
    hessRelZ
        (Certificates.hessMark s 1 (npcPhiOffsets h Φ c₀ c₁ z))
        (kappa0Cocycle dat hdat) E E₂ (npcW α r h d) =
      npcUnramifiedDiagonal dat hdat s E α r d Φ c₀ +
        polar q c₁ (Φ c₀) +
        ∑ j, polar q (z (j, 0)) (z (j, 1)) := by
  rw [hessRelZ, hessEvalZ,
    evalZ_npcW_fullOffset dat hdat s (npcPhiOffsets h Φ c₀ c₁ z) E E₂
      hV2 hE he α r d]
  simp only [WordCoh.CentExt.mul_fib, WordCoh.CentExt.mul_base,
    WordCoh.CentExt.incl_fib, WordCoh.CentExt.incl_base,
    (kappa0Cocycle dat hdat).κ_one_right, add_zero]
  simp only [npcPhiOffsets_x0, npcPhiOffsets_x1, npcPhiOffsets_x2,
    npcPhiOffsets_hIdxU, npcPhiOffsets_hIdxV]
  unfold npcUnramifiedDiagonal
  rw [polar_comm]

#print axioms evalZ_deltaZeroW_one
#print axioms evalZ_dBlockW_one
#print axioms evalZ_eBlockW_one
#print axioms conjR_slice_mul_line
#print axioms inv_conjR_slice_mul_line
#print axioms evalZ_bW_line
#print axioms evalZ_aW_line
#print axioms evalZ_boundaryInvConj
#print axioms npcUnramifiedCoreElt
#print axioms evalZ_npcW_fullOffset
#print axioms npcUnramifiedDiagonal
#print axioms npcPhiOffsets
#print axioms npcPhiOffsets_x0
#print axioms npcPhiOffsets_x1
#print axioms npcPhiOffsets_x2
#print axioms npcPhiOffsets_hIdxU
#print axioms npcPhiOffsets_hIdxV
#print axioms hessRelZ_npcW_evenPhiNormal

end Word

end
end GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
