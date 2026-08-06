/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcRamifiedRow

/-!
# The procyclic-`N` ramified pairing on twisted normal coordinates

`NpcRamifiedRow` computes the ramified second-order row of `npcW` with the `ω₂`-charge left
opaque.  This file evaluates the traced Stokes pairing on the *twisted* normal coordinates of
`NpcTwoEntryRamifiedRow` and settles the branch statement
`NProcyclic.RamifiedTwistedPairingSeparates`.

**The verdict on the recorded obstruction.**  The charge

`Z_e = Σ_{0 ≤ j < k < e} (T^j y₂)(T^k x₂)`

is genuinely there and genuinely nonzero in general — nothing here evaluates it away.  But it
sits *entirely* in the `(x₀, y₀)` diagonal block of the core Gram matrix, because on twisted
normal coordinates both `x₂` and `y₂` are determined by `x₀` resp. `y₀`.  The core matrix is

```
            λ₀            λ₁
   d₀   A⁻¹ + Ψ         A⁻¹
   d₁      A             0
```

with `Ψ` the (unevaluated) charge operator.  Left nondegeneracy never touches the diagonal: a
surviving `d₀` is detected by `λ₁` through the invertible entry `A⁻¹`, and a surviving `d₁` by
`λ₀` through the invertible entry `A`.  So the charge does **not** break separation, the branch
statement is true as formalized, and no corrected normal form and no extra hypothesis are
needed.

Two further facts make the proof cheap.  In each of the three separating configurations the
dual parameter is a *single* coordinate, so either `y₂ = 0` or `x₂ = 0`, and the charge vanishes
by the one-sided purity lemmas of `NpcRamifiedRow` — the truncated geometric sum is never
evaluated, at any residue degree.  In particular **no Arf sign and no `f`-parity hypothesis is
consumed**, so the `q = 4` refutation recorded in `GammaLSourceArfGeneral` does not reach this
row.
-/

namespace GQ2.Dyadic.NProcyclicRam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.Npc
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## Two algebraic identities of the twisted coordinate -/

section Algebra

variable {C M : Type*} [Group C] [AddCommGroup M] [DistribMulAction C M]

/-- **The twisted `x₂`-coordinate absorbs the correction operator.**  On a `2`-torsion module

`B·(A⁻¹ − 1)v + L_c v = A⁻¹v`,   `L_c = A⁻¹ + B + B·A⁻¹`,

which is the whole reason the `x₁`-column of the ramified pairing is the *invertible* `A⁻¹`
rather than the corrected operator. -/
theorem twistedX2_add_lcSmul (hM₂ : ∀ w : M, w + w = 0) (S : C) (k : ℤ) (r : ℕ) (v : M) :
    ((S ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • ((S ^ k)⁻¹ • v - v) + lcSmul S k r v = (S ^ k)⁻¹ • v := by
  have hneg : ∀ w : M, -w = w := fun w => neg_eq_of_add_eq_zero_left (hM₂ w)
  rw [inv_inv, lcSmul, smul_sub, mul_smul, sub_eq_add_neg, hneg]
  generalize (S ^ ((2 : ℤ) ^ r)) • ((S ^ k)⁻¹ • v) = a
  generalize (S ^ ((2 : ℤ) ^ r)) • v = b
  generalize (S ^ k)⁻¹ • v = c
  rw [show a + b + (c + b + a) = a + a + (b + b + c) from by abel, hM₂, hM₂, zero_add, zero_add]

/-- **The `x₀`-diagonal of the twisted pairing cancels against the front-block cross term.**
Both sides of the `x₂`-twist carry the same `B`, so the `x₂`-diagonal is `B`-free, and the two
copies of the front block's operator kill it over `𝔽₂`. -/
theorem twistedDiagonal_cancel (gA uB : C) (v : M) (lam : ElemDual M) :
    (uB⁻¹ • (gA • lam - lam)) (uB⁻¹ • (gA • v - v))
        + lam (uB • (uB⁻¹ • (gA • v - v)))
        + (gA • lam) (uB • (uB⁻¹ • (gA • v - v))) = 0 := by
  rw [smul_inv_smul, ElemDual.smul_apply, inv_inv, smul_inv_smul, ElemDual.sub_apply]
  generalize (gA • lam) (gA • v - v) = c₁
  generalize lam (gA • v - v) = c₂
  revert c₁ c₂
  decide

end Algebra

/-! ## The resolved family's traced pairing -/

section Family

variable {h α r q : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C)

/-- The uniform level resolves `ω₂` in the acting group itself — the base-group twin of
`NProcyclic.resolverLifts_npcResolver_wordLift`. -/
theorem resolverLifts_npcResolver_base (C : Type*) [Group C] [Finite C] (d : EtaData) :
    ResolverLifts (npcResolver (4 * Monoid.exponent C) d) C := by
  intro p
  rw [npcResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq p ((Monoid.order_dvd_exponent p).trans ⟨4, by ring⟩)
    (fourMulExponent_ne_zero_and_even C).1

omit [Finite C] [Finite A] in
/-- The traced pairing of the resolved procyclic-`N` family is the sum of the tame and the wild
second-order values. -/
theorem heisEta1_resolvedFamily_apply (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) (N : ℕ) (d : EtaData) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d N) x y
      = (heisEvalZ ⇑t x y (npcResolver N d) (fun _ ↦ (0 : ℤ))
          (Certificates.tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y (npcResolver N d) (fun _ ↦ (0 : ℤ))
            (Words.Npc.npcW α r h d)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, NProcyclic.resolvedFamily, npcFamOf_zero,
    npcFamOf_one, ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end Family

/-! ## The pairing on twisted normal coordinates -/

section Twisted

variable {h α r q : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C)

set_option maxHeartbeats 3200000 in
/-- **The procyclic-`N` ramified pairing on twisted normal coordinates.**

The core matrix is `((A⁻¹ + Ψ, A⁻¹), (A, 0))` with `Ψ` the `ω₂`-charge, plus the `h` standard
hyperbolic planes.  The charge sits only on the diagonal: everywhere else the twist and the
correction operator combine, by `twistedX2_add_lcSmul`, into the invertible `A⁻¹`. -/
theorem heisEta1_npc_twisted (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hα : 2 ≤ α) (d : EtaData)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) d₀ d₁ z)
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) lam₀ lam₁ mu)
      = lam₀ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • d₀)
        + lam₁ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • d₀)
        + ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • lam₀) d₁
        + (heisEvalZ ⇑t
            (evenTwistedNormal h
              ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
              ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) d₀ d₁ z)
            (evenTwistedNormal h
              ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
              ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) lam₀ lam₁ mu)
            (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
            (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))).z
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  set k : ℤ := npcResolver (4 * Monoid.exponent C) d d.toZhat with hk
  set gA : C := (t.σ ^ k)⁻¹ with hgA
  set uB : C := (t.σ ^ ((2 : ℤ) ^ r))⁻¹ with huB
  set X : Generator (2 + 2 * h) → A := evenTwistedNormal h gA uB d₀ d₁ z with hX
  set Y : Generator (2 + 2 * h) → ElemDual A := evenTwistedNormal h gA uB lam₀ lam₁ mu with hY
  have htame : (heisEvalZ ⇑t X Y (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
      (Certificates.tameRelW (2 + 2 * h) q)).z = 0 := by
    apply heisZ_tameRelW_eq_zero_of_tame_offsets_zero <;> simp [hX, hY]
  rw [heisEta1_resolvedFamily_apply t X Y (4 * Monoid.exponent C) d, htame, zero_add,
    heisZ_npc_ram (α := α) (r := r) t X Y _ _ hA₂ hwild hτfpf hTodd (by simp [hX])
      (by simp [hY]) hα (NProcyclic.resolverLifts_npcResolver_wordLift hA₂ d)
      (NProcyclic.resolverLifts_npcResolver_wordLift hA₂D d) (resolverLifts_npcResolver_base C d) d]
  have hX0 : X (coreLetter h 0) = d₀ := by simp [hX]
  have hX1 : X (coreLetter h 1) = d₁ := by simp [hX]
  have hX2 : X (coreLetter h 2) = uB⁻¹ • (gA • d₀ - d₀) := by simp [hX]
  have hY0 : Y (coreLetter h 0) = lam₀ := by simp [hY]
  have hY1 : Y (coreLetter h 1) = lam₁ := by simp [hY]
  have hY2 : Y (coreLetter h 2) = uB⁻¹ • (gA • lam₀ - lam₀) := by simp [hY]
  have hhU : ∀ j : Fin h, X (handleU j) = z (j, 0) := by intro j; simp [hX]
  have hhV : ∀ j : Fin h, X (handleV j) = z (j, 1) := by intro j; simp [hX]
  have hhUD : ∀ j : Fin h, Y (handleU j) = mu (j, 0) := by intro j; simp [hY]
  have hhVD : ∀ j : Fin h, Y (handleV j) = mu (j, 1) := by intro j; simp [hY]
  have e₁ : lam₁ (uB⁻¹ • (gA • d₀ - d₀)) + lam₁ (lcSmul t.σ k r d₀) = lam₁ (gA • d₀) := by
    rw [← map_add, huB, hgA, twistedX2_add_lcSmul hA₂ t.σ k r d₀]
  have e₂ : (uB⁻¹ • (gA • lam₀ - lam₀)) d₁ + lcSmul t.σ k r lam₀ d₁ = (gA • lam₀) d₁ := by
    rw [← ElemDual.add_apply, huB, hgA, twistedX2_add_lcSmul hA₂D t.σ k r lam₀]
  have e₃ := twistedDiagonal_cancel gA uB d₀ lam₀
  simp only [hX0, hX1, hX2, hY0, hY1, hY2, hhU, hhV, hhUD, hhVD]
  rw [show (t.σ ^ ((2 : ℤ) ^ r))⁻¹ = uB from rfl]
  generalize (heisEvalZ ⇑t X Y (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
    (PWord.omega2Pow (PWord.prodList
      [(.gen (coreLetter h 2) : PWord (Generator (2 + 2 * h))), .gen .tau]))).z = Zc
  rw [Finset.sum_congr rfl (fun j _ ↦ rfl)]
  rw [show lam₀ (gA • d₀) + lam₁ (gA • d₀) + (gA • lam₀) d₁ + Zc
      + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0)))
    = (lam₁ (uB⁻¹ • (gA • d₀ - d₀)) + lam₁ (lcSmul t.σ k r d₀))
      + ((uB⁻¹ • (gA • lam₀ - lam₀)) d₁ + lcSmul t.σ k r lam₀ d₁)
      + ((uB⁻¹ • (gA • lam₀ - lam₀)) (uB⁻¹ • (gA • d₀ - d₀))
          + lam₀ (uB • (uB⁻¹ • (gA • d₀ - d₀)))
          + (gA • lam₀) (uB • (uB⁻¹ • (gA • d₀ - d₀))))
      + lam₀ (gA • d₀) + Zc + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0)))
    from by rw [e₁, e₂, e₃]; abel]
  generalize lam₁ (uB⁻¹ • (gA • d₀ - d₀)) = c₁
  generalize lam₁ (lcSmul t.σ k r d₀) = c₂
  generalize (uB⁻¹ • (gA • lam₀ - lam₀)) d₁ = c₃
  generalize lcSmul t.σ k r lam₀ d₁ = c₄
  generalize (uB⁻¹ • (gA • lam₀ - lam₀)) (uB⁻¹ • (gA • d₀ - d₀)) = c₅
  generalize lam₀ (uB • (uB⁻¹ • (gA • d₀ - d₀))) = c₆
  generalize (gA • lam₀) (uB • (uB⁻¹ • (gA • d₀ - d₀))) = c₇
  generalize lam₀ (gA • d₀) = c₈
  generalize (∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0)))) = c₉
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ Zc
  decide

set_option maxHeartbeats 1600000 in
/-- **The `λ₁`-column of the twisted pairing**: with the dual `x₀`-parameter switched off, both
`y₂` and `y_τ` vanish, so the `ω₂`-charge is dual-pure and dies.  What is left is the invertible
entry `A⁻¹` against `d₀`, plus the handle planes. -/
theorem heisEta1_npc_twisted_lamZero (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hα : 2 ≤ α) (d : EtaData)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) d₀ d₁ z)
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) 0 lam₁ mu)
      = lam₁ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • d₀)
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  have hcharge := heisZ_omega2Block_of_dual_zero (E₂ := fun _ ↦ (0 : ℤ)) t
    (evenTwistedNormal h
      ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) d₀ d₁ z)
    (evenTwistedNormal h
      ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) 0 lam₁ mu)
    (npcResolver (4 * Monoid.exponent C) d) 2 hwild (by simp) (by simp)
  rw [heisEta1_npc_twisted (α := α) (r := r) (q := q) t hA₂ hwild hτfpf hTodd hα d, hcharge]
  simp

set_option maxHeartbeats 1600000 in
/-- **The `λ₀`-column of the twisted pairing at a vanishing primal `x₀`-parameter**: now `x₂`
and `x_τ` vanish, so the `ω₂`-charge is primal-pure and dies, and the invertible entry `A`
against `d₁` survives. -/
theorem heisEta1_npc_twisted_dZero (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hα : 2 ≤ α) (d : EtaData)
    (d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) 0 d₁ z)
        (evenTwistedNormal h
          ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
          ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) lam₀ lam₁ mu)
      = lam₀ ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) • d₁)
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  have hcharge := heisZ_omega2Block_of_prim_zero (E₂ := fun _ ↦ (0 : ℤ)) t
    (evenTwistedNormal h
      ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) 0 d₁ z)
    (evenTwistedNormal h
      ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) lam₀ lam₁ mu)
    (npcResolver (4 * Monoid.exponent C) d) 2 hwild (by simp) (by simp)
  rw [heisEta1_npc_twisted (α := α) (r := r) (q := q) t hA₂ hwild hτfpf hTodd hα d, hcharge,
    ElemDual.smul_apply, inv_inv]
  simp

/-! ## Left nondegeneracy -/

set_option maxHeartbeats 1600000 in
/-- **Left nondegeneracy of the procyclic-`N` twisted pairing.**  If `d₀` survives it is seen by
`λ₁` through `A⁻¹`; if only `d₁` survives it is seen by `λ₀` through `A`; otherwise a handle
coordinate does it.  The `ω₂`-charge is confined to the `(d₀, λ₀)` diagonal and is therefore
never consulted — and no Arf sign or residue-degree parity is used anywhere. -/
theorem npc_twisted_pairing_separates_left (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hα : 2 ≤ α) (d : EtaData)
    (p : A × A × (Fin h × Fin 2 → A)) (hp : p ≠ 0) :
    ∃ rr : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
          (evenTwistedNormal h
            ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
            ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) p.1 p.2.1 p.2.2)
          (evenTwistedNormal h
            ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
            ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) rr.1 rr.2.1 rr.2.2) ≠ 0 := by
  classical
  by_cases hd₀ : p.1 = 0
  · by_cases hd₁ : p.2.1 = 0
    · have hz : p.2.2 ≠ 0 := by
        intro hz
        exact hp (Prod.ext hd₀ (Prod.ext hd₁ (by simpa using hz)))
      obtain ⟨⟨j, kk⟩, hjk⟩ := Function.ne_iff.mp hz
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
      have hsplit : ∀ b : Fin h × Fin 2 → ElemDual A,
          heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
              (evenTwistedNormal h
                ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
                ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) p.1 p.2.1 p.2.2)
              (evenTwistedNormal h
                ((t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹)
                ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) 0 0 b)
            = ∑ c, (b (c, 0) (p.2.2 (c, 1)) + b (c, 1) (p.2.2 (c, 0))) := by
        intro b
        rw [heisEta1_npc_twisted_lamZero (α := α) (r := r) (q := q) t hA₂ hwild hτfpf hTodd hα d]
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
    · have hne : (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) • p.2.1 ≠ 0 := by
        intro hh
        refine hd₁ ?_
        rw [← inv_smul_smul (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) p.2.1, hh,
          smul_zero]
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
      refine ⟨(lam, 0, 0), ?_⟩
      rw [hd₀, heisEta1_npc_twisted_dZero (α := α) (r := r) (q := q) t hA₂ hwild hτfpf hTodd hα d]
      simpa using hlam
  · have hne : (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat)⁻¹ • p.1 ≠ 0 := by
      intro hh
      refine hd₀ ?_
      rw [← smul_inv_smul (t.σ ^ npcResolver (4 * Monoid.exponent C) d d.toZhat) p.1, hh,
        smul_zero]
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
    refine ⟨(0, lam, 0), ?_⟩
    rw [heisEta1_npc_twisted_lamZero (α := α) (r := r) (q := q) t hA₂ hwild hτfpf hTodd hα d]
    simpa using hlam

end Twisted

/-! ## The branch statement, and the ramified branch -/

section Branch

open GQ2.Dyadic.NProcyclic

set_option maxHeartbeats 1600000 in
/-- **The residual procyclic-`N` ramified input, proved.**  The `ω₂`-charge recorded in
`NpcRamifiedBranch` is real but harmless: it lives only on the `(x₀, y₀)` diagonal, and left
nondegeneracy is decided by the two off-diagonal entries `A⁻¹` and `A`, both invertible. -/
theorem ramifiedTwistedPairingSeparates {alpha r h q : ℕ} {d : EtaData} (hα : 2 ≤ alpha) :
    RamifiedTwistedPairingSeparates alpha r h q d := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτfpf p hp
  let t := actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  have hwild : ∀ (j : Fin (2 + 2 * h + 1)) (m : M), t.x j • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := fun m hm ↦ hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  exact npc_twisted_pairing_separates_left (α := alpha) (r := r) (q := q) t hM₂ hwild hτfpf'
    hTodd hα d p hp

set_option maxHeartbeats 3200000 in
/-- **The procyclic-`N` ramified branch, unconditionally.** -/
theorem ramifiedActionImageStokes {alpha r h q : ℕ} {d : EtaData} (hα : 2 ≤ alpha)
    (hqe : Even q) :
    RamifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (NProcyclic.resolvedFamily alpha r h q d) :=
  NProcyclic.ramifiedActionImageStokes_of_separation (by omega) hqe
    (ramifiedTwistedPairingSeparates hα)

end Branch

end

end GQ2.Dyadic.NProcyclicRam

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicRam.twistedX2_add_lcSmul
#print axioms GQ2.Dyadic.NProcyclicRam.twistedDiagonal_cancel
#print axioms GQ2.Dyadic.NProcyclicRam.resolverLifts_npcResolver_base
#print axioms GQ2.Dyadic.NProcyclicRam.heisEta1_resolvedFamily_apply
#print axioms GQ2.Dyadic.NProcyclicRam.heisEta1_npc_twisted
#print axioms GQ2.Dyadic.NProcyclicRam.heisEta1_npc_twisted_lamZero
#print axioms GQ2.Dyadic.NProcyclicRam.heisEta1_npc_twisted_dZero
#print axioms GQ2.Dyadic.NProcyclicRam.npc_twisted_pairing_separates_left
#print axioms GQ2.Dyadic.NProcyclicRam.ramifiedTwistedPairingSeparates
#print axioms GQ2.Dyadic.NProcyclicRam.ramifiedActionImageStokes

end AxiomAudit
