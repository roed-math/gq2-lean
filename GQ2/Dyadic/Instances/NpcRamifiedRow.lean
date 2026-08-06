/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Instances.NpcRamifiedBranch

/-!
# The procyclic-`N` second-order row in the ramified class

`NpcRamifiedBranch` reduces the procyclic-`N` ramified branch to one input, and records the
obstruction: the wild row is **two**-entry, so a cocycle has `x₂ = B(A⁻¹ − 1)x₀ ≠ 0` and the
`ω₂`-block `(x₂τ)^{ω₂}` is no longer second-order pure.  Its central charge

`Z_e = Σ_{0 ≤ j < k < e} (T^j y₂)(T^k x₂)`,  `T = x̄₂τ̄`,  `e = E(ω₂)`

is *not* killed by fixed-point-freeness (the geometric sum truncates), and no existing
`heisZ_npc_*` covers it — all three assume `τ` acts trivially.

This file computes the whole row **without** evaluating that charge.  Two observations do it.

* Every other block's jets are first-order data, and the first-order data is already banked:
  `heisEvalZ_a_eq_foxD`/`_l_eq_foxD` turn `foxD_omega2Block_ram`, `foxD_dBlockW` and
  `foxD_eBlockW` into second-order jet statements.  In particular the `ω₂`-block is
  **jet-zero** in the ramified class (its Fox row vanishes on both halves), so it contributes
  no cross term to the assembly and enters only through its own opaque charge.
* The charge itself is a `ℤ`-power of a lift with a one-sided-pure jet, so it vanishes as soon
  as *either* the primal or the dual offsets at `x₂` and `τ` vanish
  (`heisZ_omega2Block_of_prim_zero`, `heisZ_omega2Block_of_dual_zero`).  Both one-sided
  conditions are subgroup memberships, which is why no truncated geometric sum is ever needed.

The assembled row is `heisZ_npc_ram`, with the charge displayed as an opaque summand.  The
`x₂`-column is *not* free on a cocycle, so the row is stated for arbitrary offsets and
specialised in `NpcRamifiedPairing`.
-/

namespace GQ2.Dyadic.NProcyclicRam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.Npc
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count

/-! ## One-sided pure lifts

A lift with vanishing primal jet *and* vanishing centre generates a subgroup, and so does its
dual twin.  Membership in either is what makes a `ℤ`-power's charge vanish, with no power law
and no geometric sum. -/

section Pure

variable (A C : Type*) [AddCommGroup A] [Group C] [DistribMulAction C A]

/-- The lifts with vanishing primal jet and vanishing centre. -/
def heisPrimPure : Subgroup (HeisLift A C) where
  carrier := {p | p.a = 0 ∧ p.z = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {p q} hp hq =>
    ⟨by rw [HeisLift.mul_a, hp.1, hq.1, smul_zero, add_zero],
     by rw [HeisLift.mul_z, hp.2, hq.2, hq.1, smul_zero, map_zero, add_zero, add_zero]⟩
  inv_mem' := fun {p} hp =>
    ⟨by rw [HeisLift.inv_a, hp.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_z, hp.1, hp.2, map_zero, add_zero]⟩

/-- The lifts with vanishing dual jet and vanishing centre. -/
def heisDualPure : Subgroup (HeisLift A C) where
  carrier := {p | p.l = 0 ∧ p.z = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {p q} hp hq =>
    ⟨by rw [HeisLift.mul_l, hp.1, hq.1, smul_zero, add_zero],
     by rw [HeisLift.mul_z, hp.2, hq.2, hp.1, ElemDual.zero_apply, add_zero, add_zero]⟩
  inv_mem' := fun {p} hp =>
    ⟨by rw [HeisLift.inv_l, hp.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_z, hp.1, hp.2, ElemDual.zero_apply, add_zero]⟩

variable {A C}

@[simp] theorem mem_heisPrimPure {p : HeisLift A C} :
    p ∈ heisPrimPure A C ↔ p.a = 0 ∧ p.z = 0 := Iff.rfl

@[simp] theorem mem_heisDualPure {p : HeisLift A C} :
    p ∈ heisDualPure A C ↔ p.l = 0 ∧ p.z = 0 := Iff.rfl

/-- A `ℤ`-power of a primal-pure lift has vanishing charge. -/
theorem zpow_z_of_primPure {p : HeisLift A C} (ha : p.a = 0) (hz : p.z = 0) (k : ℤ) :
    (p ^ k).z = 0 := by
  have hmem : p ∈ heisPrimPure A C := ⟨ha, hz⟩
  exact (zpow_mem hmem k).2

/-- A `ℤ`-power of a dual-pure lift has vanishing charge. -/
theorem zpow_z_of_dualPure {p : HeisLift A C} (hl : p.l = 0) (hz : p.z = 0) (k : ℤ) :
    (p ^ k).z = 0 := by
  have hmem : p ∈ heisDualPure A C := ⟨hl, hz⟩
  exact (zpow_mem hmem k).2

end Pure

/-! ## The blocks of the procyclic-`N` word in the ramified class -/

section Blocks

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite A] in
/-- **The `ω₂`-block's charge vanishes on primal-free offsets.**  No geometric sum: the inner
word is primal-pure, and primal purity is a subgroup condition. -/
theorem heisZ_omega2Block_of_prim_zero (i : Fin 3)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hxi : x (coreLetter h i) = 0) (hxτ : x .tau = 0) :
    (heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))).z = 0 := by
  rw [PWord.omega2Pow, heisEvalZ_profPow]
  refine zpow_z_of_primPure ?_ ?_ (E omega2)
  · rw [heisF_deltaInner t x y E E₂ i hwild]
    show x (coreLetter h i) + x .tau = 0
    rw [hxi, hxτ, add_zero]
  · rw [heisF_deltaInner t x y E E₂ i hwild]
    show y (coreLetter h i) (x .tau) = 0
    rw [hxτ, map_zero]

omit [Finite C] [Finite A] in
/-- **The `ω₂`-block's charge vanishes on dual-free offsets.** -/
theorem heisZ_omega2Block_of_dual_zero (i : Fin 3)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hyi : y (coreLetter h i) = 0) (hyτ : y .tau = 0) :
    (heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))).z = 0 := by
  rw [PWord.omega2Pow, heisEvalZ_profPow]
  refine zpow_z_of_dualPure ?_ ?_ (E omega2)
  · rw [heisF_deltaInner t x y E E₂ i hwild]
    show y (coreLetter h i) + y .tau = 0
    rw [hyi, hyτ, add_zero]
  · rw [heisF_deltaInner t x y E E₂ i hwild]
    show y (coreLetter h i) (x .tau) = 0
    rw [hyi, ElemDual.zero_apply]

/-- **The `ω₂`-block is jet-zero in the ramified class**, on both halves: its Fox row vanishes
(`foxD_omega2Block_ram`) and the two Heisenberg jets *are* Fox rows. -/
theorem heisJet_omega2Block_ram (i : Fin 3)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C)) :
    heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      ∈ heisJetZero A C := by
  have hwildD : ∀ (j : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x j • lam = lam :=
    fun j lam => elemDual_smul_eq_self (hwild j) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam => elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam => elemDual_smul_eq_self hTodd lam
  constructor
  · rw [heisEvalZ_a_eq_foxD hresA ⇑t x y _,
      foxD_omega2Block_ram t E E₂ i hwild hτfpf hTodd]
  · rw [heisEvalZ_l_eq_foxD hresD ⇑t x y _,
      foxD_omega2Block_ram (V := ElemDual A) t E E₂ i hwildD hτfpfD hToddD]

/-- **The `δ₀`-letter's first-order row in the ramified class** is the plain `x₀`-offset: the
`ω₂`-block dies and the trailing `x₀⁻¹` survives. -/
theorem foxD_deltaZeroW_ram
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → A) :
    foxD ⇑t a E E₂ (deltaZeroW h) = -a (coreLetter h 0) := by
  have hmem : ∀ w ∈ [(PWord.omega2Pow (PWord.prodList
        [(.gen (coreLetter h 0) : PWord (Generator (2 + 2 * h))), .gen .tau])),
      .inv (.gen (coreLetter h 0))],
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C A := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact trivAct_evalFin_omega2Block t E E₂ 0 hwild hTodd
    · rw [PWord.evalFin_inv, PWord.evalFin_gen]
      exact inv_mem (Certificates.Npc.trivAct_coreLetter t hwild 0)
  rw [deltaZeroW, foxD_prodList_of_trivial _ _ _ _ _ hmem]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [foxD_omega2Block_ram t E E₂ 0 hwild hτfpf hTodd, foxD_inv, PWord.evalFin_gen, foxD_gen,
    mem_trivAct.mp (inv_mem (Certificates.Npc.trivAct_coreLetter t hwild 0)), zero_add]

/-- **The `δ₀`-letter at second order in the ramified class**: both jets are the plain
`x₀`-offsets, and the base acts trivially. -/
theorem heisJet_deltaZeroW_ram (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C)) (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a = x (coreLetter h 0)
      ∧ (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l = y (coreLetter h 0)
      ∧ ∀ v : A, (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).g • v = v := by
  have hwildD : ∀ (j : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x j • lam = lam :=
    fun j lam => elemDual_smul_eq_self (hwild j) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam => elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam => elemDual_smul_eq_self hTodd lam
  have hnegA : ∀ v : A, -v = v := fun v => neg_eq_of_add_eq_zero_left (hA₂ v)
  have hnegD : ∀ lam : ElemDual A, -lam = lam := fun lam =>
    neg_eq_of_add_eq_zero_left (ElemDual.add_self_eq_zero lam)
  refine ⟨?_, ?_, ?_⟩
  · rw [heisEvalZ_a_eq_foxD hresA ⇑t x y _,
      foxD_deltaZeroW_ram t E E₂ hwild hτfpf hTodd, hnegA]
  · rw [heisEvalZ_l_eq_foxD hresD ⇑t x y _,
      foxD_deltaZeroW_ram (A := ElemDual A) t E E₂ hwildD hτfpfD hToddD, hnegD]
  · intro v
    rw [heisEvalZ_g, evalZ_eq_evalFin_of_resolverLifts hres ⇑t (deltaZeroW h)]
    exact mem_trivAct.mp (trivAct_evalFin_deltaZeroW t E E₂ hwild hTodd) v

/-- **The `D`-block's second-order jets in the ramified class**: the corrected cross operator
`L_c = A⁻¹ + B + B·A⁻¹` applied to the plain `x₀`-offsets. -/
theorem heisJet_dBlockW_ram (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C)) (hres : ResolverLifts E C)
    (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).a
        = lcSmul t.σ (E d.toZhat) r (x (coreLetter h 0))
      ∧ (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).l
        = lcSmul t.σ (E d.toZhat) r (y (coreLetter h 0))
      ∧ ∀ v : A, (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).g • v = v := by
  have hwildD : ∀ (j : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x j • lam = lam :=
    fun j lam => elemDual_smul_eq_self (hwild j) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam => elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam => elemDual_smul_eq_self hTodd lam
  have hnegA : ∀ v : A, -v = v := fun v => neg_eq_of_add_eq_zero_left (hA₂ v)
  have hnegD : ∀ lam : ElemDual A, -lam = lam := fun lam =>
    neg_eq_of_add_eq_zero_left (ElemDual.add_self_eq_zero lam)
  refine ⟨?_, ?_, ?_⟩
  · rw [heisEvalZ_a_eq_foxD hresA ⇑t x y _, foxD_dBlockW t E E₂ hwild hTodd d,
      foxD_deltaZeroW_ram t E E₂ hwild hτfpf hTodd, hnegA, lcSmul, mul_smul]
    abel
  · rw [heisEvalZ_l_eq_foxD hresD ⇑t x y _,
      foxD_dBlockW (V := ElemDual A) t E E₂ hwildD hToddD d,
      foxD_deltaZeroW_ram (A := ElemDual A) t E E₂ hwildD hτfpfD hToddD, hnegD, lcSmul,
      mul_smul]
    abel
  · intro v
    rw [heisEvalZ_g, evalZ_eq_evalFin_of_resolverLifts hres ⇑t (dBlockW h r d)]
    exact mem_trivAct.mp (trivAct_evalFin_dBlockW t E E₂ hwild hTodd d) v

/-- **The correction block in the ramified class**: jet-zero central with value the
`L_c`-twisted pairing of the `x₀`- and `x₁`-offsets — the same shape as the unramified row's,
but read off the ramified `δ₀`-jet. -/
theorem heisF_eBlockW_ram (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C)) (hres : ResolverLifts E C)
    (d : EtaData) :
    heisEvalZ ⇑t x y E E₂ (eBlockW h r d)
      = ⟨0, 0,
          lcSmul t.σ (E d.toZhat) r (y (coreLetter h 0)) (x (coreLetter h 1))
            + y (coreLetter h 1) (lcSmul t.σ (E d.toZhat) r (x (coreLetter h 0))),
          commR (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).g (t (coreLetter h 1))⟩ := by
  obtain ⟨ha, hl, hg⟩ :=
    heisJet_dBlockW_ram (r := r) t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres d
  rw [eBlockW, heisEvalZ_comm, heisEvalZ_gen,
    heisCommR_of_trivial _ _ hg
      (mem_trivAct.mp (Certificates.Npc.trivAct_coreLetter t hwild 1)), ha, hl]

end Blocks

/-! ## The six-factor assembly -/

section Assembly

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The procyclic-`N` product law.**  Factors `1`, `4`, `5`, `6` are jet-zero and factor `2`'s
base acts trivially, so of the fifteen possible cross terms exactly one survives: `λ₂(a₃)`, the
front block's operator against the boundary jet. -/
theorem heisMul_six_z (P1 P2 P3 P4 P5 P6 : HeisLift A C)
    (h1 : P1 ∈ heisJetZero A C) (h4 : P4 ∈ heisJetZero A C) (h5 : P5 ∈ heisJetZero A C)
    (h6 : P6 ∈ heisJetZero A C) (h2g : ∀ v : A, P2.g • v = v) :
    (P1 * (P2 * (P3 * (P4 * (P5 * P6))))).z
      = P1.z + P2.z + P3.z + P4.z + P5.z + P6.z + P2.l P3.a := by
  have h56a : (P5 * P6).a = 0 := by rw [HeisLift.mul_a, h5.1, h6.1, smul_zero, add_zero]
  have h56z : (P5 * P6).z = P5.z + P6.z := heisJetZero_mul_z h5
  have h456a : (P4 * (P5 * P6)).a = 0 := by
    rw [HeisLift.mul_a, h56a, smul_zero, add_zero, h4.1]
  have h456z : (P4 * (P5 * P6)).z = P4.z + (P5.z + P6.z) := by
    rw [heisJetZero_mul_z h4, h56z]
  have h3456a : (P3 * (P4 * (P5 * P6))).a = P3.a := by
    rw [HeisLift.mul_a, h456a, smul_zero, add_zero]
  have h3456z : (P3 * (P4 * (P5 * P6))).z = P3.z + (P4.z + (P5.z + P6.z)) := by
    rw [heisMul_z_of_a_eq_zero _ _ h456a, h456z]
  rw [heisJetZero_mul_z h1, HeisLift.mul_z, h3456z, h3456a, h2g]
  abel

end Assembly

/-! ## The assembled ramified row -/

section Row

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

set_option maxHeartbeats 1600000 in
/-- **The corrected procyclic-`N` second-order row in the ramified class**, exact in the
resolver and with the `ω₂`-charge left opaque.

Block reading, in the order the factors occur:

* the **twisted `x₀`-diagonal** `y₀(A⁻¹x₀)` — the leading power's diagonal cancels against the
  front commutator's, exactly as in the unramified row;
* the **boundary block** on `(x₁, x₂)`, with the `x₂`-diagonal;
* the **`ω₂`-charge**, the genuinely new ramified atom, displayed and *not* evaluated;
* the **correction block** `L_c(y₀)(x₁) + y₁(L_c x₀)`, the whole S3.2 correction;
* the **front-block cross term** `(A⁻¹y₀ + y₀)(B⁻¹x₂)`, the second-order shadow of the new
  `x₀`-column `A⁻¹ + 1` paired against the boundary jet — here the *whole* boundary jet is
  `B⁻¹x₂`, because the `ω₂`-block is jet-zero on a ramified module;
* the `h` identity-operator hyperbolic planes.

No hypothesis on the `τ`-offsets is used: the ramified `ω₂`-block is jet-zero whatever they
are. -/
theorem heisZ_npc_ram (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (j : Fin (2 + 2 * h + 1)) (v : A), t.x j • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hα : 2 ≤ α)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C)) (hres : ResolverLifts E C)
    (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (npcW α r h d)).z
      = y (coreLetter h 0) ((t.σ ^ E d.toZhat)⁻¹ • x (coreLetter h 0))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1))
            + y (coreLetter h 2) (x (coreLetter h 2)))
        + (heisEvalZ ⇑t x y E E₂
            (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))).z
        + (lcSmul t.σ (E d.toZhat) r (y (coreLetter h 0)) (x (coreLetter h 1))
            + y (coreLetter h 1) (lcSmul t.σ (E d.toZhat) r (x (coreLetter h 0))))
        + (y (coreLetter h 0) ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2))
            + ((t.σ ^ E d.toZhat)⁻¹ • y (coreLetter h 0))
                ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have e1 := Certificates.Npc.heisF_leadingPow t x y E E₂ hA₂ hwild hα (α := α)
  have e2 := heisF_commX0A t x y E E₂ hwild hxσ hyσ d
  have e3 := heisF_invConjX2G t x y E E₂ hwild hxσ hyσ (r := r)
  have e4 := heisJet_omega2Block_ram t x y E E₂ 2 hwild hτfpf hTodd hresA hresD
  have e5 := heisF_eBlockW_ram (r := r) t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres d
  have h6mem := Certificates.Npc.heisF_handlesW_mem t x y E E₂ hwild
  have h6z := Certificates.Npc.heisF_handlesW_z t x y E E₂ hwild
  have h1jz : heisEvalZ ⇑t x y E E₂
      (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α)) ∈ heisJetZero A C := by
    rw [e1]; exact ⟨rfl, rfl⟩
  have h5jz : heisEvalZ ⇑t x y E E₂ (eBlockW h r d) ∈ heisJetZero A C := by
    rw [e5]; exact ⟨rfl, rfl⟩
  have h2g : ∀ v : A,
      (heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (aW h d))).g • v = v := by
    rw [e2]
    exact fun v => mem_trivAct.mp
      (Certificates.Npc.trivAct_commR_left
        (Certificates.Npc.trivAct_coreLetter t hwild 0) (t.σ ^ E d.toZhat)) v
  rw [npcW, heisEvalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [heisMul_six_z _ _ _ _ _ _ h1jz e4 h5jz h6mem h2g, e1, e2, e3, e5, h6z]
  dsimp only
  simp only [ElemDual.sub_apply, map_neg]
  generalize y (coreLetter h 0) (x (coreLetter h 0)) = c₁
  generalize y (coreLetter h 0) ((t.σ ^ E d.toZhat)⁻¹ • x (coreLetter h 0)) = c₂
  generalize y (coreLetter h 1) (x (coreLetter h 2)) = c₃
  generalize y (coreLetter h 2) (x (coreLetter h 1)) = c₄
  generalize y (coreLetter h 2) (x (coreLetter h 2)) = c₅
  generalize (heisEvalZ ⇑t x y E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))).z = c₆
  generalize lcSmul t.σ (E d.toZhat) r (y (coreLetter h 0)) (x (coreLetter h 1)) = c₇
  generalize y (coreLetter h 1) (lcSmul t.σ (E d.toZhat) r (x (coreLetter h 0))) = c₈
  generalize y (coreLetter h 0) ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)) = c₉
  generalize ((t.σ ^ E d.toZhat)⁻¹ • y (coreLetter h 0))
    ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)) = c₁₀
  generalize (∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j)))) = c₁₁
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁
  decide

end Row

end

end GQ2.Dyadic.NProcyclicRam

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicRam.zpow_z_of_primPure
#print axioms GQ2.Dyadic.NProcyclicRam.zpow_z_of_dualPure
#print axioms GQ2.Dyadic.NProcyclicRam.heisZ_omega2Block_of_prim_zero
#print axioms GQ2.Dyadic.NProcyclicRam.heisZ_omega2Block_of_dual_zero
#print axioms GQ2.Dyadic.NProcyclicRam.heisJet_omega2Block_ram
#print axioms GQ2.Dyadic.NProcyclicRam.foxD_deltaZeroW_ram
#print axioms GQ2.Dyadic.NProcyclicRam.heisJet_deltaZeroW_ram
#print axioms GQ2.Dyadic.NProcyclicRam.heisJet_dBlockW_ram
#print axioms GQ2.Dyadic.NProcyclicRam.heisF_eBlockW_ram
#print axioms GQ2.Dyadic.NProcyclicRam.heisMul_six_z
#print axioms GQ2.Dyadic.NProcyclicRam.heisZ_npc_ram

end AxiomAudit
