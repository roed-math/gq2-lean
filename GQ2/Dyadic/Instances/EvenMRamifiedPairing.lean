/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenMRamifiedRow
import GQ2.Dyadic.Instances.M0RamifiedBranch

/-!
# The compact-`M` ramified normal pairing, and the unconditional branch

`EvenMRamifiedRow` computes the compact-`M` second-order row on ramified normal offsets.  This
file turns it into the traced Stokes pairing on the normal coordinates, proves the residual
input `MCompact.RamifiedNormalPairingSeparates` of `M0RamifiedBranch`, and records the three
consequences unconditionally.

The core Gram matrix on `(x₀, x₁)` is `((0,1),(1,1))`: `lam₁(d₁) + (lam₀(d₁) + lam₁(d₀))`.  It is
unimodular over `𝔽₂` — the determinant is `0·1 − 1·1 = 1` — so left nondegeneracy is a two-case
split, exactly as for the compact-`N` matrix `((1,1),(1,0))`, but with the roles of the two core
coordinates exchanged: here it is `lam₀` that detects `d₁` and `lam₁` that detects `d₀` once `d₁`
is gone.  No Arf or determinant sign is consumed, so the `q = 4` refutation of
`GammaLSourceArfGeneral` is not in play and no residue-degree parity hypothesis appears.
-/

namespace GQ2.Dyadic.MCompactRam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Certificates.MProcyclic

/-! ## The uniform resolver at the base level -/

/-- The coefficient-independent Heisenberg level resolves `ω₂` in the acting group itself.  This
is the base-level twin of `resolverLifts_uniformWordLift_ramified`, and it is what lets the
`evalFin`-level `trivAct` facts of `M0Fox` be read off the `evalZ`-level bases. -/
theorem resolverLifts_uniform_base (C : Type*) [Group C] [Finite C] :
    ResolverLifts (fun _ ↦ ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ)) C := by
  intro p
  rw [zpow_natCast]
  exact powOmega2_pow_eq p ((Monoid.order_dvd_exponent p).trans ⟨4, by ring⟩)
    (fourMulExponent_ne_zero_and_even C).1

/-! ## The pairing on ramified normal coordinates -/

set_option maxHeartbeats 1600000 in
/-- **The compact-`M` middle Stokes map on ramified normal coordinates**: the constant unimodular
core matrix `((0,1),(1,1))` plus `h` standard hyperbolic planes.  The tame relator contributes
nothing, because a normal cochain vanishes on `sigma` and `tau`. -/
theorem heisEta1_mCompactFam_normal
    {h α q : ℕ} {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
      = lam₁ d₁ + (lam₀ d₁ + lam₁ d₀)
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have htame : (heisEvalZ ⇑t (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
      (fun _ ↦ ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ))
      (fun _ ↦ ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ))
      (tameRelW (2 + 2 * h) q)).z = 0 := by
    apply heisZ_tameRelW_eq_zero_of_tame_offsets_zero <;> simp
  rw [Certificates.MCompact.heisEta1_mCompactFam_apply t _ _, htame, zero_add,
    heisZ_mCompact_ram (α := α) t _ _ _ _ hA₂ hwild hτfpf hTodd (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (resolverLifts_uniformWordLift_ramified hA₂)
      (resolverLifts_uniformWordLift_ramified hA₂D) (resolverLifts_uniform_base C)]
  simp only [evenNormal_coreLetter, evenNormal_handleU, evenNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Left nondegeneracy of the compact-`M` ramified normal pairing.**  If `d₁` survives, `lam₀`
detects it; if only `d₀` survives, `lam₁` detects it through the diagonal; otherwise a handle
coordinate does.  This is the whole content of the unimodularity of `((0,1),(1,1))`. -/
theorem mCompactFam_normal_pairing_separates_left
    {h α q : ℕ} {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (p : A × A × (Fin h × Fin 2 → A)) (hp : p ≠ 0) :
    ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t (mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
          (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h r.1 r.2.1 r.2.2) ≠ 0 := by
  classical
  by_cases hd₁ : p.2.1 = 0
  · by_cases hd₀ : p.1 = 0
    · have hz : p.2.2 ≠ 0 := by
        intro hz
        exact hp (Prod.ext hd₀ (Prod.ext hd₁ (by simpa using hz)))
      obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hz
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
      fin_cases k
      · refine ⟨(0, 0, Pi.single (j, 1) lam), ?_⟩
        rw [heisEta1_mCompactFam_normal (α := α) t hA₂ hwild hτfpf hTodd, hd₀, hd₁]
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
        rw [heisEta1_mCompactFam_normal (α := α) t hA₂ hwild hτfpf hTodd, hd₀, hd₁]
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
    · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₀
      refine ⟨(0, lam, 0), ?_⟩
      rw [heisEta1_mCompactFam_normal (α := α) t hA₂ hwild hτfpf hTodd, hd₁]
      simpa using hlam
  · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₁
    refine ⟨(lam, 0, 0), ?_⟩
    rw [heisEta1_mCompactFam_normal (α := α) t hA₂ hwild hτfpf hTodd]
    simpa using hlam

end

end GQ2.Dyadic.MCompactRam

namespace GQ2.Dyadic.MCompact

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact

set_option maxHeartbeats 1600000 in
/-- **The residual compact-`M` ramified input, proved.** -/
theorem ramifiedNormalPairingSeparates {α h q : ℕ} :
    RamifiedNormalPairingSeparates α h q := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτfpf p hp
  let t := actionImageMarking (2 + 2 * h) q (mCompactW α h) M
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := fun m hm ↦ hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  exact MCompactRam.mCompactFam_normal_pairing_separates_left (α := α) (q := q) t hM₂ hwild
    hτfpf' hTodd p hp

set_option maxHeartbeats 1600000 in
/-- **The compact-`M` ramified branch, unconditionally.** -/
theorem ramifiedSimpleStokes {α h q : ℕ} (hq : Even q) : RamifiedSimpleStokes α h q :=
  ramifiedSimpleStokes_of_separation hq ramifiedNormalPairingSeparates

set_option maxHeartbeats 2400000 in
/-- **The compact-`M` uniform pushed Stokes residue, unconditionally.** -/
theorem uniformPushedHsimp {α h q : ℕ} (hα : 2 ≤ α) (hq : Even q) : UniformPushedHsimp α h q :=
  uniformPushedHsimp_of_separation hα hq ramifiedNormalPairingSeparates

set_option maxHeartbeats 2400000 in
/-- **Corrected exact lifting for the compact-`M` presentation, unconditionally.** -/
theorem exactLiftingRN_unconditional {α h q : ℕ} (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_separation hα hq0 hqe ramifiedNormalPairingSeparates nuP

end

end GQ2.Dyadic.MCompact

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.MCompactRam.resolverLifts_uniform_base
#print axioms GQ2.Dyadic.MCompactRam.heisEta1_mCompactFam_normal
#print axioms GQ2.Dyadic.MCompactRam.mCompactFam_normal_pairing_separates_left
#print axioms GQ2.Dyadic.MCompact.ramifiedNormalPairingSeparates
#print axioms GQ2.Dyadic.MCompact.ramifiedSimpleStokes
#print axioms GQ2.Dyadic.MCompact.uniformPushedHsimp
#print axioms GQ2.Dyadic.MCompact.exactLiftingRN_unconditional

end AxiomAudit
