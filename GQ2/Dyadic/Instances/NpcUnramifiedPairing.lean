/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcRamifiedPairing
import GQ2.Dyadic.Instances.NpcUnramifiedProcyclic

/-!
# The procyclic-`N` unramified pairing on `Φ`-normal coordinates

`NpcUnramifiedProcyclic` reduces the *generic* unramified sub-branch of the corrected
procyclic-`N` row to one statement: left nondegeneracy of the traced Stokes pairing on the
operator-twisted normal coordinates

`A × A × (Fin h × Fin 2 → A) → (Generator (2 + 2h) → A)`,  `x₂ = Φ x₀`,

with `Φ = (1 − B⁻¹)⁻¹(1 − A⁻¹)` the solution operator of the unramified cocycle equation.
This file evaluates that pairing and discharges the statement.

**The value.**  On `Φ`-normal coordinates the `σ`- and `τ`-offsets vanish on both sides, so the
whole `e`-sensitive part of `heisZ_npc_res_one` dies: the boundary block's `τ`-terms, the
`C(e,2)`-block and — decisively — the S3.2 correction block `L_c(y_τ)(x₁) + y₁(L_c x_τ)`, which
is *pure `τ`* at the honest resolver class.  What survives is

```
λ₀(A·d₀) + λ₁(Φ d₀) + (Φ_D λ₀)(d₁) + (Φ_D λ₀)((1 + B)·Φ d₀) + Σ_j handles.
```

The first entry is worth a remark.  The row hands out `λ₀(A⁻¹d₀)` in the diagonal slot and
`λ₀((A + 1)·bnd)` in the front-block slot, with `bnd = (1 + B⁻¹)Φd₀`; the cocycle equation turns
the boundary jet into `(1 + A⁻¹)d₀`, and over `𝔽₂` the two entries collapse to the *single*
invertible operator `A` — the `A⁻¹` cancels rather than the `A`.  So the `x₀`-diagonal is
`λ₀(A d₀)`, and it is a diagonal, hence useless for separation, exactly as on the ramified row.

**Separation** is therefore decided by the two off-diagonal entries `λ₁(Φ d₀)` and
`(Φ_D λ₀)(d₁)`, and both are invertible because `Φ` and `Φ_D` are bijective
(`unramPhi_bijective`).  That bijectivity is where the branch arithmetic is consumed: it needs
`A⁻¹` fixed-point free, and `A = σ` on this branch by
`RowActionImage.actionImage_unramified_sigma_etaPow`.  No Arf sign and no `f`-parity hypothesis
is used anywhere, so the `q = 4` refutation of `GammaLSourceArfGeneral` does not reach this row.
-/

namespace GQ2.Dyadic.NProcyclicUnram

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.Npc
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- The corrected cross operator kills the zero vector: `L_c` is additive in its argument. -/
theorem lcSmul_zero {C M : Type*} [Group C] [AddCommGroup M] [DistribMulAction C M]
    (S : C) (k : ℤ) (r : ℕ) : lcSmul S k r (0 : M) = 0 := by
  simp [lcSmul]

/-! ## The pairing on `Φ`-normal coordinates -/

section Pairing

variable {h α r q : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C)

set_option maxHeartbeats 3200000 in
/-- **The procyclic-`N` unramified pairing on `Φ`-normal coordinates.**  The `x₀`-diagonal is the
single invertible operator `A`; the two off-diagonal entries are `Φ` and its dual; the handles
are the `h` standard hyperbolic planes.  Every `e`-sensitive block and the whole S3.2 correction
block vanish, because `Φ`-normal cochains are `σ`- and `τ`-free on both sides. -/
theorem heisEta1_npc_phiNormal (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (hα : 2 ≤ α) (d : EtaData)
    (Φ : A →+ A) (ΦD : ElemDual A →+ ElemDual A)
    (hΦ : ∀ v : A, Φ v - ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ : C) • Φ v
      = v - ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ : C) • v)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenPhiNormal h Φ d₀ d₁ z) (evenPhiNormal h ΦD lam₀ lam₁ mu)
      = lam₀ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) • d₀)
        + lam₁ (Φ d₀) + (ΦD lam₀) d₁
        + ((ΦD lam₀) (Φ d₀) + (ΦD lam₀) ((t.σ ^ ((2 : ℤ) ^ r)) • Φ d₀))
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  set X : Generator (2 + 2 * h) → A := evenPhiNormal h Φ d₀ d₁ z with hX
  set Y : Generator (2 + 2 * h) → ElemDual A := evenPhiNormal h ΦD lam₀ lam₁ mu with hY
  have hXσ : X .sigma = 0 := by simp [hX]
  have hXτ : X .tau = 0 := by simp [hX]
  have hYσ : Y .sigma = 0 := by simp [hY]
  have hYτ : Y .tau = 0 := by simp [hY]
  have hX2 : X (coreLetter h 2) = Φ d₀ := by simp [hX]
  have htame : (heisEvalZ ⇑t X Y (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
      (Certificates.tameRelW (2 + 2 * h) q)).z = 0 :=
    heisZ_tameRelW_eq_zero_of_tame_offsets_zero t X Y _ _ hXσ hXτ hYσ hYτ
  have hbnd : npcBoundaryJet t X r 1
      = d₀ - ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ : C) • d₀ := by
    rw [npcBoundaryJet, hX2, hXτ, one_nsmul, add_zero, ← hΦ, sub_eq_add_neg]
    abel
  have hAbnd : (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)
        • (d₀ - ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ : C) • d₀)
      = (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) • d₀ - d₀ := by
    rw [smul_sub, smul_inv_smul]
  rw [NProcyclicRam.heisEta1_resolvedFamily_apply t X Y (4 * Monoid.exponent C) d, htame,
    zero_add,
    heisZ_npc_res_one t X Y (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ)) hA₂
      hwild hτ hXσ hYσ hα (npcResolver_omega2 (4 * Monoid.exponent C) d)
      (omega2Exp_fourMulExponent_mod_four C) d,
    hbnd, hAbnd, hXτ, hYτ, hX2]
  simp only [hX, hY, evenPhiNormal_coreLetter, evenPhiNormal_handleU, evenPhiNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, lcSmul_zero, ElemDual.zero_apply, map_zero, add_zero, map_sub]
  generalize lam₀ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • d₀) = c₁
  generalize lam₀ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) • d₀) = c₂
  generalize lam₀ d₀ = c₃
  generalize lam₁ (Φ d₀) = c₄
  generalize (ΦD lam₀) d₁ = c₅
  generalize (ΦD lam₀) (Φ d₀) = c₆
  generalize (ΦD lam₀) ((t.σ ^ ((2 : ℤ) ^ r)) • Φ d₀) = c₇
  generalize (∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0)))) = c₈
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈
  decide

/-! ## Left nondegeneracy -/

set_option maxHeartbeats 1600000 in
/-- **Left nondegeneracy of the procyclic-`N` unramified pairing on `Φ`-normal coordinates.**  A
surviving `d₀` is seen by `λ₁` through the injective `Φ`; a surviving `d₁` is seen by `λ₀`
through the surjective `Φ_D`; otherwise a handle coordinate does it.  The `x₀`-diagonal
`λ₀(A d₀)` is never consulted, and no Arf sign or residue-degree parity is used. -/
theorem npc_phiNormal_pairing_separates_left (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (hα : 2 ≤ α) (d : EtaData)
    (Φ : A →+ A) (ΦD : ElemDual A →+ ElemDual A)
    (hΦ : ∀ v : A, Φ v - ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ : C) • Φ v
      = v - ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ : C) • v)
    (hΦinj : Function.Injective Φ) (hΦDsurj : Function.Surjective ΦD)
    (p : A × A × (Fin h × Fin 2 → A)) (hp : p ≠ 0) :
    ∃ rr : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
          (evenPhiNormal h Φ p.1 p.2.1 p.2.2)
          (evenPhiNormal h ΦD rr.1 rr.2.1 rr.2.2) ≠ 0 := by
  classical
  have heval := heisEta1_npc_phiNormal (α := α) (r := r) (q := q) t hA₂ hwild hτ hα d Φ ΦD hΦ
  by_cases hd₀ : p.1 = 0
  · by_cases hd₁ : p.2.1 = 0
    · have hz : p.2.2 ≠ 0 := by
        intro hz
        exact hp (Prod.ext hd₀ (Prod.ext hd₁ (by simpa using hz)))
      obtain ⟨⟨j, kk⟩, hjk⟩ := Function.ne_iff.mp hz
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
      have hsplit : ∀ b : Fin h × Fin 2 → ElemDual A,
          heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
              (evenPhiNormal h Φ p.1 p.2.1 p.2.2) (evenPhiNormal h ΦD 0 0 b)
            = ∑ c, (b (c, 0) (p.2.2 (c, 1)) + b (c, 1) (p.2.2 (c, 0))) := by
        intro b
        rw [heval p.1 p.2.1 p.2.2 0 0 b]
        simp
      fin_cases kk
      · refine ⟨(0, 0, Pi.single (j, 1) lam), ?_⟩
        rw [hsplit]
        have hsum : ∑ b, ((Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
              (p.2.2 (b, 1))
            + (Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 1) (p.2.2 (b, 0)))
            = lam (p.2.2 (j, 0)) := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using hlam
      · refine ⟨(0, 0, Pi.single (j, 0) lam), ?_⟩
        rw [hsplit]
        have hsum : ∑ b, ((Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
              (p.2.2 (b, 1))
            + (Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 1) (p.2.2 (b, 0)))
            = lam (p.2.2 (j, 1)) := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using hlam
    · obtain ⟨nu, hnu⟩ := elemDual_separates hA₂ hd₁
      obtain ⟨lam₀, hlam₀⟩ := hΦDsurj nu
      refine ⟨(lam₀, 0, 0), ?_⟩
      rw [heval p.1 p.2.1 p.2.2 lam₀ 0 0, hd₀, hlam₀]
      simpa using hnu
  · have hne : Φ p.1 ≠ 0 := by
      intro hh
      exact hd₀ (hΦinj (by rw [hh, map_zero]))
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
    refine ⟨(0, lam, 0), ?_⟩
    rw [heval p.1 p.2.1 p.2.2 0 lam 0]
    simpa using hlam

end Pairing

end

end GQ2.Dyadic.NProcyclicUnram

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicUnram.lcSmul_zero
#print axioms GQ2.Dyadic.NProcyclicUnram.heisEta1_npc_phiNormal
#print axioms GQ2.Dyadic.NProcyclicUnram.npc_phiNormal_pairing_separates_left

end AxiomAudit
