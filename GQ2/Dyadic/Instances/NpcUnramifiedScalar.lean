/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenScalarSeparation
import GQ2.Dyadic.Instances.NpcScalarRow

/-!
# The scalar sub-branch of the procyclic-`N` unramified obligation

On the `tau`-unramified branch the action image is procyclic, so either `sigma` acts without
nonzero fixed vectors — settled in `NpcUnramifiedBranch` — or `sigma` acts trivially and then the
*whole* action image does.  This file settles the second case.

With a completely trivial action the bottom differential vanishes, so `sigma` is a free normal
coordinate; the scalar normal cochains are `N0M0ScalarStokes`'s, and the row is
`heisZ_npc_scalar_free`.  The resulting Gram matrix is **not** the compact rows':

```
        ν₀        ν₁        ν₂            b_σ
 a_σ    n_η        0        2^r            0
 d₀      1         0         0            n_η
 d₁      0         0         1             0
 d₂      0         1         0            2^r
```

(plus the `h` hyperbolic handle planes).  Both `sigma`-planes carry a conjugator exponent read
modulo `2`, and `2^r` is even at every noncompact `r ≥ 1`.  So the `sigma`-coordinate is seen
**only** through `n_η = E(η̂)`, and:

* if `n_η` is odd the matrix is nondegenerate on the left and the branch closes
  (`npc_scalarNormal_pairing_separates_left`);
* if `n_η` is even the vector `(a_σ, 0, 2^r·a_σ, 0, 0)` lies in the left kernel for every `a_σ`
  (`heisEta1_npc_scalarNormal_kernel`), so the traced pairing is genuinely degenerate and the
  branch is **false**.

`n_η = 1 + padicOmega2Exp(η − 1, N)` is odd exactly when `η` is a `2`-adic **unit**
(`odd_npcResolver_toZhat_of_oneUnit`), which is what every `NpcDisplayFor` supplies and what a
bare `EtaData` does not.  This is the one hypothesis the procyclic-`N` row's scalar sub-branch
needs and the other three branches do not; **no Arf sign and no residue-degree parity is used**,
so the `q = 4` refutation of `GammaLSourceArfGeneral` does not reach this row either.
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

/-! ## The parity of the `η̂`-resolver -/

/-- The `2`-adic representative of an even element is even, at every truncation level. -/
theorem even_val_two_mul {k : ℕ} (u : ZMod (2 ^ k)) : Even ((2 * u).val) := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨0, ?_⟩
    have hlt : (2 * u).val < 2 ^ 0 := ZMod.val_lt _
    simp only [pow_zero] at hlt
    omega
  · have hdvd : (2 : ℕ) ∣ (2 * u).val := by
      rw [ZMod.val_mul, Nat.dvd_mod_iff (dvd_pow_self 2 hk.ne')]
      refine Dvd.dvd.mul_right ?_ _
      have h2 : ((2 : ZMod (2 ^ k))).val = 2 % 2 ^ k := by
        rw [show (2 : ZMod (2 ^ k)) = ((2 : ℕ) : ZMod (2 ^ k)) by norm_cast, ZMod.val_natCast]
      rw [h2, Nat.dvd_mod_iff (dvd_pow_self 2 hk.ne')]
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by omega⟩

/-- **The `η̂`-exponent of a `2`-adic unit is even at every level.**  `padicOmega2Exp` scales the
truncation of `η − 1` by the odd `ω₂`-exponent, and `η − 1` is even exactly when `η` is a
unit. -/
theorem even_padicOmega2Exp_of_oneUnit {η : ℤ_[2]} (z : ℤ_[2]) (hη : η = 1 + 2 * z) (N : ℕ) :
    Even (padicOmega2Exp (η - 1) N) := by
  have h2 : (η - 1 : ℤ_[2]) = 2 * z := by rw [hη]; ring
  have hmap : ∀ k : ℕ, Even ((PadicInt.toZModPow k (2 * z) : ZMod (2 ^ k)).val) := by
    intro k
    rw [map_mul, map_ofNat]
    exact even_val_two_mul _
  rw [padicOmega2Exp, h2]
  exact (hmap _).mul_right _

/-- **The `η̂`-resolver value is odd** as soon as `η` is a `2`-adic unit.  This is the one
arithmetic fact the scalar sub-branch consumes, and the one a bare `EtaData` does not supply. -/
theorem odd_npcResolver_toZhat_of_oneUnit {d : EtaData} (z : ℤ_[2])
    (hd : d.toPadic = 1 + 2 * z) (N : ℕ) :
    Odd (1 + padicOmega2Exp (d.toPadic - 1) N) := by
  obtain ⟨c, hc⟩ := even_padicOmega2Exp_of_oneUnit z hd N
  exact ⟨c, by omega⟩

/-! ## The scalar pairing of the procyclic-`N` family -/

section Pairing

variable {h α r q : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C)

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`N` traced pairing on scalar normal coordinates.**  The tame relator is
`tau`-pure and dies; what is left is `heisZ_npc_scalar_free` read at `x_τ = y_τ = 0`. -/
theorem heisEta1_npc_scalarNormal (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) (hα : 2 ≤ α) (hq : Even q)
    (d : EtaData) (p : ScalarParam h A) (rr : ScalarParam h (ElemDual A)) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenScalarNormalP h p) (evenScalarNormalP h rr)
      = rr.2.1 p.2.1
        + ((1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C)) • rr.2.1 p.1
          + (1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C)) • rr.1 p.2.1)
        + (rr.2.2.1 p.2.2.2.1 + rr.2.2.2.1 p.2.2.1)
        + ((2 ^ r : ℕ) • rr.1 p.2.2.2.1 + (2 ^ r : ℕ) • rr.2.2.2.1 p.1)
        + ∑ j, (rr.2.2.2.2 (j, 0) (p.2.2.2.2 (j, 1))
            + rr.2.2.2.2 (j, 1) (p.2.2.2.2 (j, 0))) := by
  have hτ : ∀ v : A, t.τ • v = v := fun v => htriv _ v
  have htame : (heisEvalZ ⇑t (evenScalarNormalP h p) (evenScalarNormalP h rr)
      (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
      (Certificates.tameRelW (2 + 2 * h) q)).z = 0 := by
    rw [Certificates.heisZ_tameRelW_unram t _ _ _ _ hA₂ hτ hq]
    simp [evenScalarNormalP]
  rw [NProcyclicRam.heisEta1_resolvedFamily_apply t _ _ (4 * Monoid.exponent C) d, htame,
    zero_add,
    heisZ_npc_scalar_free (r := r) t _ _ _ _ hA₂ htriv
      (NProcyclicRam.resolverLifts_npcResolver_base C d) (by simp [evenScalarNormalP])
      (by simp [evenScalarNormalP]) hα (npcResolver_omega2 (4 * Monoid.exponent C) d)
      (omega2Exp_fourMulExponent_mod_four C) d
      (npcResolver_toZhat (4 * Monoid.exponent C) d)]
  simp only [evenScalarNormalP, evenScalarNormal_coreLetter, evenScalarNormal_sigma,
    evenScalarNormal_handleU, evenScalarNormal_handleV, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

set_option maxHeartbeats 1600000 in
/-- **The scalar Gram matrix at an odd `η̂`-resolver**, grouped by dual coordinate: `ν₀` sees
`d₀ + a_σ`, `b_σ` sees `d₀ + 2^r·d₂`, `ν₁` sees `d₂` and `ν₂` sees `d₁ + 2^r·a_σ`. -/
theorem heisEta1_npc_scalarNormal_odd (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) (hα : 2 ≤ α) (hq : Even q)
    (d : EtaData)
    (hnn : Odd (1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C)))
    (p : ScalarParam h A) (rr : ScalarParam h (ElemDual A)) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenScalarNormalP h p) (evenScalarNormalP h rr)
      = rr.2.1 (p.2.1 + p.1) + rr.1 (p.2.1 + (2 ^ r : ℕ) • p.2.2.2.1)
        + rr.2.2.1 p.2.2.2.1 + rr.2.2.2.1 (p.2.2.1 + (2 ^ r : ℕ) • p.1)
        + ∑ j, (rr.2.2.2.2 (j, 0) (p.2.2.2.2 (j, 1))
            + rr.2.2.2.2 (j, 1) (p.2.2.2.2 (j, 0))) := by
  rw [heisEta1_npc_scalarNormal (α := α) (r := r) (q := q) t hA₂ htriv hα hq d p rr,
    nsmul_zmod2_odd hnn, nsmul_zmod2_odd hnn]
  simp only [map_add, map_nsmul]
  generalize rr.2.1 p.2.1 = c₁
  generalize rr.2.1 p.1 = c₂
  generalize rr.1 p.2.1 = c₃
  generalize rr.2.2.1 p.2.2.2.1 = c₄
  generalize rr.2.2.2.1 p.2.2.1 = c₅
  generalize (2 ^ r : ℕ) • rr.1 p.2.2.2.1 = c₆
  generalize (2 ^ r : ℕ) • rr.2.2.2.1 p.1 = c₇
  generalize (∑ j, (rr.2.2.2.2 (j, 0) (p.2.2.2.2 (j, 1))
    + rr.2.2.2.2 (j, 1) (p.2.2.2.2 (j, 0)))) = c₈
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈
  decide

set_option maxHeartbeats 1600000 in
/-- **The left kernel at an even `η̂`-resolver.**  With `n_η` even the `sigma`-row of the Gram
matrix is `2^r` alone, and `(a_σ, 0, 2^r·a_σ, 0, 0)` pairs to zero against *every* dual scalar
normal cochain.  At `a_σ ≠ 0` that parameter is nonzero, so the traced pairing on scalar normal
coordinates is degenerate and the sub-branch is false without the unit hypothesis. -/
theorem heisEta1_npc_scalarNormal_kernel (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) (hα : 2 ≤ α) (hq : Even q)
    (d : EtaData)
    (hnn : Even (1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C)))
    (aσ : A) (rr : ScalarParam h (ElemDual A)) :
    heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenScalarNormalP h
          ((aσ, 0, (2 ^ r : ℕ) • aσ, 0, 0) : ScalarParam h A))
        (evenScalarNormalP h rr) = 0 := by
  rw [heisEta1_npc_scalarNormal (α := α) (r := r) (q := q) t hA₂ htriv hα hq d _ rr,
    nsmul_zmod2_even hnn, nsmul_zmod2_even hnn]
  dsimp only
  simp only [map_zero, map_nsmul, Pi.zero_apply, smul_zero, add_zero, zero_add,
    Finset.sum_const_zero]
  exact CharTwo.add_self_eq_zero _

end Pairing

/-! ## Left nondegeneracy of the scalar pairing -/

section Separation

variable {h α r q : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C)

set_option maxHeartbeats 1600000 in
/-- **Left nondegeneracy of the procyclic-`N` scalar pairing at an odd `η̂`-resolver.**  The four
core rows are consulted in turn — `ν₁` for `d₂`, `ν₀` for `d₀ + a_σ`, `ν₂` for `d₁ + 2^r·a_σ`,
`b_σ` for `d₀` — and a handle coordinate closes the remaining case.  Note that the `sigma`
coordinate is never separated on its own: it is only ever seen *through* `d₀` or `d₁`, which is
exactly why an even `n_η` breaks the argument. -/
theorem npc_scalarNormal_pairing_separates_left (hA₂ : ∀ v : A, v + v = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) (hα : 2 ≤ α) (hq : Even q)
    (d : EtaData)
    (hnn : Odd (1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C)))
    (p : ScalarParam h A) (hp : p ≠ 0) :
    ∃ rr : ScalarParam h (ElemDual A),
      heisEta1 ⇑t (NProcyclic.resolvedFamily α r h q d (4 * Monoid.exponent C))
        (evenScalarNormalP h p) (evenScalarNormalP h rr) ≠ 0 := by
  classical
  have heval := heisEta1_npc_scalarNormal_odd (α := α) (r := r) (q := q) t hA₂ htriv hα hq d hnn p
  by_cases hd₂ : p.2.2.2.1 = 0
  · by_cases hs₀ : p.2.1 + p.1 = 0
    · by_cases hs₁ : p.2.2.1 + (2 ^ r : ℕ) • p.1 = 0
      · by_cases hd₀ : p.2.1 = 0
        · have haσ : p.1 = 0 := by
            have := hs₀
            rw [hd₀, zero_add] at this
            exact this
          have hd₁ : p.2.2.1 = 0 := by
            have := hs₁
            rw [haσ, smul_zero, add_zero] at this
            exact this
          have hz : p.2.2.2.2 ≠ 0 := by
            intro hz
            exact hp (Prod.ext haσ (Prod.ext hd₀ (Prod.ext hd₁ (Prod.ext hd₂
              (by simpa using hz)))))
          obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hz
          obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
          fin_cases k
          · refine ⟨(0, 0, 0, 0, Pi.single (j, 1) lam), ?_⟩
            rw [heval, hs₀, hs₁, hd₂]
            have hsum : ∑ b, ((Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
                  (p.2.2.2.2 (b, 1))
                + (Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 1)
                  (p.2.2.2.2 (b, 0))) = lam (p.2.2.2.2 (j, 0)) := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hbj
                simp [hbj]
              · simp
            rw [hsum]
            simpa using hlam
          · refine ⟨(0, 0, 0, 0, Pi.single (j, 0) lam), ?_⟩
            rw [heval, hs₀, hs₁, hd₂]
            have hsum : ∑ b, ((Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
                  (p.2.2.2.2 (b, 1))
                + (Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 1)
                  (p.2.2.2.2 (b, 0))) = lam (p.2.2.2.2 (j, 1)) := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hbj
                simp [hbj]
              · simp
            rw [hsum]
            simpa using hlam
        · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₀
          refine ⟨(lam, 0, 0, 0, 0), ?_⟩
          rw [heval, hs₀, hs₁, hd₂, smul_zero, add_zero]
          simpa using hlam
      · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hs₁
        refine ⟨(0, 0, 0, lam, 0), ?_⟩
        rw [heval, hs₀]
        simpa using hlam
    · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hs₀
      refine ⟨(0, lam, 0, 0, 0), ?_⟩
      rw [heval]
      simpa using hlam
  · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₂
    refine ⟨(0, 0, lam, 0, 0), ?_⟩
    rw [heval]
    simpa using hlam

end Separation

/-! ## The scalar branch, and the unramified obligation -/

section Branch

open GQ2.Dyadic.NProcyclic

/-- **The `tau`-row of the corrected procyclic-`N` family at a completely trivial action.**  Both
rows of the resolved family degenerate to the single `tau` entry: the tame row through the
`σ⁻¹`-pivot, the wild row because `A` and `B` are `σ`-powers (`foxD_npc_split`). -/
theorem heisD1_npcFam_tauRow_of_split {alpha r h q : ℕ} {d : EtaData}
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a) (hq : Even q)
    (hα : 1 ≤ alpha) (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (NProcyclic.resolvedFamily alpha r h q d (4 * Monoid.exponent C)) x
      = ![x .tau, x .tau] := by
  have hτ : ∀ a : A, t.τ • a = a := fun a => htriv _ a
  have hσ : ∀ a : A, t.σ • a = a := fun a => htriv _ a
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a := fun i a => htriv _ a
  have hσinv : ∀ a : A, t.σ⁻¹ • a = a := fun a =>
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr hσ)) a
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
          (Certificates.tameRelW (2 + 2 * h) q))).a = x .tau
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (NProcyclic.resolverLifts_npcResolver_wordLift hA₂ d),
      Certificates.foxD_tameRelW_unram t _ _ hA₂ hτ hq]
    exact hσinv _
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
          (Words.Npc.npcW alpha r h d))).a = x .tau
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (NProcyclic.resolverLifts_npcResolver_wordLift hA₂ d),
      Certificates.Npc.foxD_npc_split t _ _ hA₂ hwild hτ hσ hα d]

set_option maxHeartbeats 3200000 in
/-- **The scalar sub-branch of the procyclic-`N` unramified obligation.**  The complex is the
scalar one — `d⁰ = 0`, `d¹` the `tau`-pivot of rank one, five blocks of normal coordinates — and
the traced pairing separates them because the `η̂`-resolver value is odd.

⚠ The hypothesis `d.toPadic = 1 + 2z` (that `η` is a `2`-adic unit) is **necessary**: at an even
resolver value `heisEta1_npc_scalarNormal_kernel` exhibits a nonzero left kernel. -/
theorem scalarActionImageStokes {alpha r h q : ℕ} {d : EtaData} (hα : 2 ≤ alpha) (hqe : Even q)
    (z : ℤ_[2]) (hd : d.toPadic = 1 + 2 * z) :
    ScalarActionImageStokes alpha r h q d := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ hσ
  let C₀ := ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let t := actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let w₀ := NProcyclic.resolvedFamily alpha r h q d (4 * Monoid.exponent C₀)
  have hlv := NProcyclic.levelResolver (alpha := alpha) (r := r) (h := h) (q := q) d
    (by omega) hqe
  have hres₀ : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d)) w₀
      (HeisLift M C₀) := hlv.heis hM₂
  have hend : IsStokesEndpoint w₀ :=
    hlv.endpoint _ (fourMulExponent_ne_zero_and_even C₀).1
      (fourMulExponent_ne_zero_and_even C₀).2
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d)) w₀
      (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hres₀.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift ⇑t (w₀ k) = 1 := fun k ↦
    lower_rel (A := M) (actionImageHom (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)
      (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      hresWord k
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := fun m ↦ hτ m
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have htriv : ∀ (g : Generator (2 + 2 * h)) (m : M), t g • m = m :=
    marking_smul_trivial_of_split t hwild hτ' hσ
  have htrivD : ∀ (g : Generator (2 + 2 * h)) (lam : ElemDual M), t g • lam = lam :=
    fun g lam ↦ elemDual_smul_eq_self (htriv g) lam
  have hnn : Odd (1 + padicOmega2Exp (d.toPadic - 1) (4 * Monoid.exponent C₀)) :=
    odd_npcResolver_toZhat_of_oneUnit z hd _
  exact evenScalarStokesDuality_of_separation t w₀ hM₂ hr hend
    (heisD0_eq_zero_of_split t htriv) (heisD0_eq_zero_of_split t htrivD)
    (heisD1_npcFam_tauRow_of_split (alpha := alpha) (r := r) (d := d) t hM₂ htriv hqe (by omega))
    (heisD1_npcFam_tauRow_of_split (A := ElemDual M) (alpha := alpha) (r := r) (d := d) t hM₂D
      htrivD hqe (by omega))
    (npc_scalarNormal_pairing_separates_left (α := alpha) (r := r) (q := q) t hM₂ htriv hα hqe
      d hnn)

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`N` unramified branch, unconditionally in the coefficient** (and conditional
only on `η` being a `2`-adic unit). -/
theorem unramifiedActionImageStokes {alpha r h q : ℕ} {d : EtaData} (hα : 2 ≤ alpha)
    (hqe : Even q) (z : ℤ_[2]) (hd : d.toPadic = 1 + 2 * z) :
    UnramifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d) :=
  unramifiedActionImageStokes_of_scalar hα hqe (scalarActionImageStokes hα hqe z hd)

set_option maxHeartbeats 2400000 in
/-- **The corrected procyclic-`N` uniform pushed Stokes residue**, with both branches discharged:
the ramified one by `NProcyclicRam.ramifiedActionImageStokes` and the unramified one here. -/
theorem uniformPushedHsimp {alpha r h q : ℕ} {d : EtaData} (hα : 2 ≤ alpha) (hqe : Even q)
    (z : ℤ_[2]) (hd : d.toPadic = 1 + 2 * z) :
    UniformPushedHsimp alpha r h q d :=
  uniformPushedHsimp_of_branches (by omega) hqe
    (unramifiedActionImageStokes hα hqe z hd)
    (NProcyclicRam.ramifiedActionImageStokes hα hqe)

end Branch

end

end GQ2.Dyadic.NProcyclicUnram

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicUnram.even_val_two_mul
#print axioms GQ2.Dyadic.NProcyclicUnram.even_padicOmega2Exp_of_oneUnit
#print axioms GQ2.Dyadic.NProcyclicUnram.odd_npcResolver_toZhat_of_oneUnit
#print axioms GQ2.Dyadic.NProcyclicUnram.heisEta1_npc_scalarNormal
#print axioms GQ2.Dyadic.NProcyclicUnram.heisEta1_npc_scalarNormal_odd
#print axioms GQ2.Dyadic.NProcyclicUnram.heisEta1_npc_scalarNormal_kernel
#print axioms GQ2.Dyadic.NProcyclicUnram.npc_scalarNormal_pairing_separates_left
#print axioms GQ2.Dyadic.NProcyclicUnram.heisD1_npcFam_tauRow_of_split
#print axioms GQ2.Dyadic.NProcyclicUnram.scalarActionImageStokes
#print axioms GQ2.Dyadic.NProcyclicUnram.unramifiedActionImageStokes
#print axioms GQ2.Dyadic.NProcyclicUnram.uniformPushedHsimp

end AxiomAudit
