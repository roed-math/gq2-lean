/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNielsenStokes
import GQ2.Dyadic.Certificates.M0Fox

/-!
# First-order transport for the general head-handle pair source

The pair exchange transports the compact word by an alphabet equivalence, so its full Fox
derivative is the compact derivative at the transported marking and offset.  The transported
handle block is the only place where a formerly tame action enters a wild coordinate.  When
the original wild alphabet acts trivially, every handle except the selected one cancels and
the entire block is the universal row

`a(x₂) - sigma⁻¹ • a(x₂)`.

These statements are uniform in the rank, handle count, word parameters, coefficient, and
resolver.  They isolate the exact first-order correction needed for the strict-handle Stokes
normal form.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.EvenMHeadHandleSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairCore

/-- The pair-swapped Fox derivative is the compact derivative in transported coordinates. -/
theorem foxD_headHandlePairCompactW_eq
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h) :
    foxD ⇑t a E E₂ (headHandlePairCompactW alpha j) =
      foxD (fun g ↦ t (headHandlePairSwap j g))
        (fun g ↦ a (headHandlePairSwap j g)) E E₂ (mCompactW alpha h) := by
  rw [headHandlePairCompactW_eq_nielsenBackward]
  rw [foxD_def, foxD_def, Certificates.MProcyclic.foxEval_subst]
  unfold foxEval
  have hmaps :
      (fun g ↦ PWord.evalFin (foxLift ⇑t a) E E₂
        ((headHandlePairNielsen j).backward g)) =
      foxLift (fun g ↦ t (headHandlePairSwap j g))
        (fun g ↦ a (headHandlePairSwap j g)) := by
    funext g
    change foxEval ⇑t a E E₂ (.gen ((headHandlePairSwap j).symm g)) = _
    rw [headHandlePairSwap_symm]
    rfl
  exact congrArg WordLift.u
    (congrArg (fun mu => PWord.evalFin mu E E₂ (mCompactW alpha h)) hmaps)

/-- If every right-hand handle letter acts trivially, the handle derivative is the sum of the
individual right-hand commutator rows. -/
theorem foxD_handlesW_of_right_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hV : ∀ (k : Fin h) (v : A), t (handleV k) • v = v) :
    foxD ⇑t a E E₂ (handlesW h) =
      ((List.finRange h).map fun k =>
        a (handleV k) - (t (handleU k))⁻¹ • a (handleV k)).sum := by
  have hmem : ∀ w ∈ (List.finRange h).map fun k =>
      (PWord.comm (.gen (handleU k)) (.gen (handleV k)) :
        PWord (Generator (2 + 2 * h))),
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C A := by
    intro w hw
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact Certificates.MCompact.trivAct_commR_right
      (mem_trivAct.mpr (hV k))
  rw [handlesW, foxD_prodList_of_trivial _ _ _ _ _ hmem]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  exact Certificates.MCompact.foxD_comm_of_trivial_right
    t a E E₂ (mem_trivAct.mpr (hV k))

/-- After the full pair exchange, the entire handle block is the displaced-head row. -/
theorem foxD_handlesW_headHandlePair
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    foxD (fun g ↦ t (headHandlePairSwap j g))
        (fun g ↦ a (headHandlePairSwap j g)) E E₂ (handlesW h) =
      a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2) := by
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦ t (headHandlePairSwap j g)⟩
  let b : Generator (2 + 2 * h) → A := fun g ↦ a (headHandlePairSwap j g)
  change foxD ⇑s b E E₂ (handlesW h) = _
  rw [foxD_handlesW_of_right_trivial s b E E₂]
  · rw [← Fin.sum_univ_def, Finset.sum_eq_single j]
    · simp [s, b]
    · intro k _ hkj
      have hU : headHandlePairSwap j (handleU k) = handleU k := by
        rw [headHandlePairSwap]
        simp [headHandleSwap_handleU, hkj]
      have hV : headHandlePairSwap j (handleV k) = handleV k := by
        rw [headHandlePairSwap]
        simp [tailHandleSwap_handleV, hkj]
      change a (headHandlePairSwap j (handleV k)) -
        (t (headHandlePairSwap j (handleU k)))⁻¹ •
          a (headHandlePairSwap j (handleV k)) = 0
      rw [hU, hV]
      exact sub_eq_zero.mpr
        (mem_trivAct.mp (inv_mem (Certificates.trivAct_handleU t hwild k)) _).symm
    · simp
  · intro k v
    by_cases hkj : k = j
    · subst k
      change t (headHandlePairSwap j (handleV j)) • v = v
      rw [headHandlePairSwap_handleV_self]
      exact hwild _ v
    · have hV : headHandlePairSwap j (handleV k) = handleV k := by
        rw [headHandlePairSwap]
        simp [tailHandleSwap_handleV, hkj]
      change t (headHandlePairSwap j (handleV k)) • v = v
      rw [hV]
      exact hwild _ v

/-- The leading `a₀` word has the usual scalar action when only the three compact-core
letters, rather than the entire wild alphabet, act trivially. -/
theorem evalFin_a0W_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha : ℕ) (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (v : A) :
    PWord.evalFin ⇑t E E₂ (a0W alpha h) • v =
      ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • v := by
  rw [Certificates.MCompact.evalFin_a0W, mul_smul,
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hcore 0)))]

/-- The Fox derivative of `a₀` only uses triviality of the compact-core letters. -/
theorem foxD_a0W_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v) :
    foxD ⇑t a E E₂ (a0W alpha h) =
      -a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf alpha)⁻¹ •
        Certificates.MCompact.sigmaGeom t E E₂ a (mOf alpha) := by
  rw [a0W, Certificates.MCompact.foxD_prodList_pair,
    foxD_inv, PWord.evalFin_gen, foxD_gen,
    Certificates.MCompact.foxD_sigma2Pow_neg,
    PWord.evalFin_inv, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hcore 0))),
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hcore 0))), sub_eq_add_neg]

/-- The squared leading block retains its standard derivative under compact-core
triviality. -/
theorem foxD_leadingSquare_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v) :
    foxD ⇑t a E E₂ (.zpow (a0W alpha h) 2) =
      (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf alpha)⁻¹ •
        Certificates.MCompact.sigmaGeom t E E₂ a (mOf alpha)) +
      ((powOmega2 t.σ) ^ mOf alpha)⁻¹ •
        (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf alpha)⁻¹ •
          Certificates.MCompact.sigmaGeom t E E₂ a (mOf alpha)) := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
    foxD_zpow_natCast, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, one_smul, pow_one]
  rw [foxD_a0W_of_core_trivial t a E E₂ alpha hcore,
    evalFin_a0W_smul_of_core_trivial t E E₂ alpha hcore]

/-- The squared leading block has the standard scalar action under compact-core
triviality. -/
theorem evalFin_leadingSquare_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha : ℕ) (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (v : A) :
    PWord.evalFin ⇑t E E₂ (.zpow (a0W alpha h) 2) • v =
      ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • v := by
  have hmm : mOf alpha + mOf alpha = 2 * mOf alpha := by omega
  rw [PWord.evalFin_zpow, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
    zpow_natCast, pow_two, mul_smul,
    evalFin_a0W_smul_of_core_trivial t E E₂ alpha hcore,
    evalFin_a0W_smul_of_core_trivial t E E₂ alpha hcore,
    ← mul_smul, ← mul_inv_rev, ← pow_add, hmm]

/-- The leading commutator has the standard derivative under compact-core triviality. -/
theorem foxD_leadingComm_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v) :
    foxD ⇑t a E E₂ (.comm (a0W alpha h) (.gen (coreLetter h 1))) =
      a (coreLetter h 1) - (powOmega2 t.σ) ^ mOf alpha • a (coreLetter h 1) := by
  rw [Certificates.MCompact.foxD_comm_of_trivial_right _ _ _ _
      (by rw [PWord.evalFin_gen]; exact mem_trivAct.mpr (hcore 1)),
    foxD_gen, Certificates.MCompact.evalFin_a0W, mul_inv_rev, inv_inv,
    inv_inv, mul_smul, mem_trivAct.mp (mem_trivAct.mpr (hcore 0))]

/-- The leading commutator acts trivially under compact-core triviality. -/
theorem evalFin_leadingComm_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha : ℕ) (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (v : A) :
    PWord.evalFin ⇑t E E₂ (.comm (a0W alpha h) (.gen (coreLetter h 1))) • v = v := by
  rw [PWord.evalFin_comm, PWord.evalFin_gen]
  exact mem_trivAct.mp
    (Certificates.MCompact.trivAct_commR_right (mem_trivAct.mpr (hcore 1))) v

/-- The compact core Fox formula with a possibly nonzero handle-tail row.  Only the three
compact-core letters need act trivially; the correction block must fix the supplied tail row
honestly. -/
theorem foxD_mWordWith_core_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hj2 : ∀ v : A, PWord.evalFin ⇑t E E₂ (j2W h) • v = v)
    (B : PWord (Generator (2 + 2 * h))) (H : A)
    (htail : foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = H)
    (hB : PWord.evalFin ⇑t E E₂ B • H = H) :
    foxD ⇑t a E E₂ (mWordWith alpha h B) =
      (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0)) +
      (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) -
        ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1)) +
      (foxD ⇑t a E E₂ (j2W h) + foxD ⇑t a E E₂ B) + H := by
  have hsplit : (powOmega2 t.σ) ^ (2 * mOf alpha) =
      (powOmega2 t.σ) ^ mOf alpha * (powOmega2 t.σ) ^ mOf alpha := by
    rw [← pow_add]
    congr 1
    omega
  rw [mWordWith]
  simp only [List.cons_append, List.nil_append, PWord.prodList_cons]
  rw [foxD_mul, foxD_mul, foxD_mul, foxD_mul, foxD_mul, htail,
    hj2, Certificates.MCompact.evalFin_sigma2Block_smul,
    evalFin_leadingComm_smul_of_core_trivial t E E₂ alpha hcore,
    evalFin_leadingSquare_smul_of_core_trivial t E E₂ alpha hcore,
    foxD_leadingSquare_of_core_trivial t a E E₂ alpha hcore,
    foxD_leadingComm_of_core_trivial t a E E₂ alpha hcore,
    Certificates.MCompact.foxD_sigma2Block,
    Certificates.MCompact.sigmaGeom_two_mul]
  rw [hB]
  simp only [smul_add, smul_sub, smul_neg, hsplit, mul_inv_rev,
    mul_smul, inv_smul_smul]
  abel

private theorem foxD_invConjX2_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v) :
    foxD ⇑t a E E₂ (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma))) =
      -(t.σ⁻¹ • a (coreLetter h 2)) := by
  have hx2 := hcore 2
  have hconj : PWord.evalFin ⇑t E E₂
      (.conj (.gen (coreLetter h 2)) (.gen .sigma)) ∈ trivAct C A := by
    rw [PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_conjR (mem_trivAct.mpr hx2) _
  rw [foxD_inv, mem_trivAct.mp (inv_mem hconj), foxD_conj,
    PWord.evalFin_gen, PWord.evalFin_gen, foxD_gen, foxD_gen, hx2]
  simp

private theorem foxD_deltaInner_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v) :
    foxD ⇑t a E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau]) =
      a (coreLetter h i) + a .tau := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil,
    foxD_mul, foxD_mul, PWord.evalFin_gen, PWord.evalFin_gen,
    foxD_gen, foxD_gen, foxD_one, smul_zero, add_zero, hcore]

private theorem evalFin_deltaInner_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (i : Fin 3)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (v : A) :
    PWord.evalFin ⇑t E E₂
      (PWord.prodList [.gen (coreLetter h i), .gen .tau]) • v = t.τ • v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil,
    PWord.evalFin_mul, PWord.evalFin_mul, PWord.evalFin_gen,
    PWord.evalFin_gen, PWord.evalFin_one, mul_one, mul_smul, hcore]
  rfl

private theorem foxD_deltaBlock_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (i : Fin 3) :
    foxD ⇑t a E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) =
      a (coreLetter h i) + a .tau := by
  rw [foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hA₂ _
      (fun v => by rw [foxEval_g]; exact
        (evalFin_deltaInner_smul_of_core_trivial t E E₂ i hcore v).trans (hτ v))]
  exact foxD_deltaInner_of_core_trivial t a E E₂ i hcore

private theorem foxD_deltaBlock_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) (i : Fin 3) :
    foxD ⇑t a E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) = 0 := by
  have hbase : PWord.evalFin ⇑t E E₂
      (PWord.prodList [.gen (coreLetter h i), .gen .tau]) =
      t (coreLetter h i) * t.τ := by
    rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil,
      PWord.evalFin_mul, PWord.evalFin_mul, PWord.evalFin_gen,
      PWord.evalFin_gen, PWord.evalFin_one, mul_one]
    rfl
  rw [foxD_def, foxEval_omega2Pow]
  refine WordLift.powOmega2_u_of_oddFixedPointFree _
    (fun v hv => hτfpf v ?_) (fun v => ?_)
  · rw [foxEval_g] at hv
    exact (evalFin_deltaInner_smul_of_core_trivial t E E₂ i hcore v).symm.trans hv
  · rw [foxEval_g, hbase]
    exact WordLift.powOmega2_smul_of_trivial_mul _ _ (hcore i) hTodd v

private theorem trivAct_deltaBlock_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈
      trivAct C A := by
  rw [PWord.evalFin_omega2Pow]
  refine trivAct_powOmega2 (mem_trivAct.mpr fun v => ?_)
  rw [evalFin_deltaInner_smul_of_core_trivial t E E₂ i hcore v, hτ]

private theorem trivAct_deltaBlock_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈
      trivAct C A := by
  rw [PWord.evalFin_omega2Pow, Certificates.MCompact.evalFin_prodList_pair,
    PWord.evalFin_gen, PWord.evalFin_gen, Marking.apply_tau]
  exact mem_trivAct.mpr fun v =>
    WordLift.powOmega2_smul_of_trivial_mul _ _ (hcore i) hTodd v

private theorem foxD_j2W_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) :
    foxD ⇑t a E E₂ (j2W h) =
      -(t.σ⁻¹ • a (coreLetter h 2)) + (a (coreLetter h 2) + a .tau) := by
  rw [j2W, Certificates.MCompact.foxD_prodList_pair]
  rw [foxD_invConjX2_of_core_trivial t a E E₂ hcore,
    foxD_deltaBlock_unram_of_core_trivial t a E E₂ hA₂ hcore hτ 2,
    PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen,
    PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_conjR (mem_trivAct.mpr (hcore 2)) _))]

private theorem foxD_j2W_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    foxD ⇑t a E E₂ (j2W h) = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  rw [j2W, Certificates.MCompact.foxD_prodList_pair,
    foxD_invConjX2_of_core_trivial t a E E₂ hcore,
    foxD_deltaBlock_ram_of_core_trivial t a E E₂ hcore hτfpf hTodd 2,
    smul_zero, add_zero]

private theorem evalFin_j2W_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) ∈
      trivAct C A) (v : A) :
    PWord.evalFin ⇑t E E₂ (j2W h) • v = v := by
  rw [j2W, Certificates.MCompact.evalFin_prodList_pair, mul_smul,
    mem_trivAct.mp hδ, PWord.evalFin_inv, PWord.evalFin_conj,
    PWord.evalFin_gen, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_conjR (mem_trivAct.mpr (hcore 2)) _))]

private theorem trivAct_deltaC_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (i : Fin 3)
    (hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈
      trivAct C A) :
    PWord.evalFin ⇑t E E₂ (Words.MCompact.deltaC h i) ∈ trivAct C A := by
  rw [Words.MCompact.deltaC, Certificates.MCompact.evalFin_prodList_pair,
    PWord.evalFin_inv, PWord.evalFin_gen]
  exact mul_mem hδ (inv_mem (mem_trivAct.mpr (hcore i)))

private theorem foxD_deltaC_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (i : Fin 3) :
    foxD ⇑t a E E₂ (Words.MCompact.deltaC h i) = a .tau := by
  have hbase : ∀ v : A, PWord.evalFin ⇑t E E₂
      (PWord.prodList [(.gen (coreLetter h i) :
        PWord (Generator (2 + 2 * h))), .gen .tau]) • v = v := by
    intro v
    rw [Certificates.MCompact.evalFin_prodList_pair, PWord.evalFin_gen,
      PWord.evalFin_gen, mul_smul, Marking.apply_tau, hτ, hcore]
  rw [Words.MCompact.deltaC, Certificates.MCompact.foxD_prodList_pair,
    foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hA₂ _
      (fun v => by rw [foxEval_g]; exact hbase v),
    ← foxD_def, Certificates.MCompact.foxD_prodList_pair,
    PWord.evalFin_gen, foxD_gen, foxD_gen, hcore,
    PWord.evalFin_omega2Pow,
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hbase)),
    foxD_inv, PWord.evalFin_gen, foxD_gen,
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hcore i)))]
  abel

private theorem foxD_deltaC_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) (i : Fin 3) :
    foxD ⇑t a E E₂ (Words.MCompact.deltaC h i) = -a (coreLetter h i) := by
  have hδtriv := trivAct_deltaBlock_ram_of_core_trivial t E E₂ hcore hTodd i
  rw [Words.MCompact.deltaC, Certificates.MCompact.foxD_prodList_pair,
    foxD_deltaBlock_ram_of_core_trivial t a E E₂ hcore hτfpf hTodd i,
    mem_trivAct.mp hδtriv, foxD_inv, PWord.evalFin_gen,
    foxD_gen, mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hcore i))), zero_add]

private theorem foxD_eRevW_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) :
    foxD ⇑t a E E₂ (eRevW alpha h) =
      ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau + a .tau := by
  have hδ := trivAct_deltaBlock_unram_of_core_trivial t E E₂ hcore hτ
  rw [Certificates.MCompact.foxD_eRevW t E E₂
      (trivAct_deltaC_of_core_trivial t E E₂ hcore 0 (hδ 0))
      (trivAct_deltaC_of_core_trivial t E E₂ hcore 1 (hδ 1)),
    foxD_deltaC_unram_of_core_trivial t a E E₂ hA₂ hcore hτ,
    foxD_deltaC_unram_of_core_trivial t a E E₂ hA₂ hcore hτ,
    show ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau
        + ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a .tau
        + (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a .tau + a .tau) =
      (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau + a .tau) +
        (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a .tau +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a .tau) from by abel,
    hA₂, add_zero]

private theorem foxD_eRevW_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    foxD ⇑t a E E₂ (eRevW alpha h) =
      -(((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) +
        ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1) +
        (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0) +
          a (coreLetter h 0))) := by
  have hδ := trivAct_deltaBlock_ram_of_core_trivial t E E₂ hcore hTodd
  rw [Certificates.MCompact.foxD_eRevW t E E₂
      (trivAct_deltaC_of_core_trivial t E E₂ hcore 0 (hδ 0))
      (trivAct_deltaC_of_core_trivial t E E₂ hcore 1 (hδ 1)),
    foxD_deltaC_ram_of_core_trivial t a E E₂ hcore hτfpf hTodd,
    foxD_deltaC_ram_of_core_trivial t a E E₂ hcore hτfpf hTodd]
  simp only [smul_neg]
  abel

private theorem evalFin_eRevW_smul_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha : ℕ)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hδ : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈
      trivAct C A) (v : A) :
    PWord.evalFin ⇑t E E₂ (eRevW alpha h) • v = v := by
  have hd : ∀ i : Fin 3,
      PWord.evalFin ⇑t E E₂ (Words.MCompact.deltaC h i) ∈ trivAct C A :=
    fun i => trivAct_deltaC_of_core_trivial t E E₂ hcore i (hδ i)
  rw [eRevW]
  refine mem_trivAct.mp (trivAct_evalFin_prodList fun w hw => ?_) v
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · rw [PWord.evalFin_conj]
    exact trivAct_conjR (hd 1) _
  · rw [PWord.evalFin_conj]
    exact trivAct_conjR (hd 1) _
  · rw [PWord.evalFin_conj]
    exact trivAct_conjR (hd 0) _
  · exact hd 0

private theorem foxD_mCompact_unram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (H : A)
    (htail : foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = H) :
    foxD ⇑t a E E₂ (mCompactW alpha h) =
      ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau +
      (a (coreLetter h 0) +
        ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0)) +
      (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1) +
        ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1)) +
      (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) + H := by
  have hneg : ∀ v : A, -v = v := Certificates.neg_eq_self hA₂
  have hδ := trivAct_deltaBlock_unram_of_core_trivial t E E₂ hcore hτ
  rw [← mWordWith_eRevW,
    foxD_mWordWith_core_of_core_trivial t a E E₂ alpha hcore
      (evalFin_j2W_smul_of_core_trivial t E E₂ hcore (hδ 2))
      (eRevW alpha h) H htail
      (evalFin_eRevW_smul_of_core_trivial t E E₂ alpha hcore hδ H),
    foxD_j2W_unram_of_core_trivial t a E E₂ hA₂ hcore hτ,
    foxD_eRevW_unram_of_core_trivial t a E E₂ alpha hA₂ hcore hτ]
  simp only [sub_eq_add_neg, hneg]
  have hrearrange :
      a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0) +
        (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1)) +
        (t.σ⁻¹ • a (coreLetter h 2) + (a (coreLetter h 2) + a .tau) +
          (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau + a .tau)) + H =
      (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a .tau +
        (a (coreLetter h 0) +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0)) +
        (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1) +
          ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1)) +
        (a (coreLetter h 2) + t.σ⁻¹ • a (coreLetter h 2)) + H) +
        (a .tau + a .tau) := by abel
  rw [hrearrange, hA₂, add_zero]

private theorem foxD_mCompact_ram_of_core_trivial
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hA₂ : ∀ v : A, v + v = 0)
    (hcore : ∀ (i : Fin 3) (v : A), t (coreLetter h i) • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) (H : A)
    (htail : foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = H) :
    foxD ⇑t a E E₂ (mCompactW alpha h) =
      -(t.σ⁻¹ • a (coreLetter h 2)) + H := by
  have hneg : ∀ v : A, -v = v := Certificates.neg_eq_self hA₂
  have hδ := trivAct_deltaBlock_ram_of_core_trivial t E E₂ hcore hTodd
  rw [← mWordWith_eRevW,
    foxD_mWordWith_core_of_core_trivial t a E E₂ alpha hcore
      (evalFin_j2W_smul_of_core_trivial t E E₂ hcore (hδ 2))
      (eRevW alpha h) H htail
      (evalFin_eRevW_smul_of_core_trivial t E E₂ alpha hcore hδ H),
    foxD_j2W_ram_of_core_trivial t a E E₂ hcore hτfpf hTodd,
    foxD_eRevW_ram_of_core_trivial t a E E₂ alpha hcore hτfpf hTodd]
  simp only [sub_eq_add_neg, hneg]
  have hrearrange :
      a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0) +
        (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1)) +
        (t.σ⁻¹ • a (coreLetter h 2) +
          (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) +
            ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1) +
            (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0) +
              a (coreLetter h 0)))) + H =
      t.σ⁻¹ • a (coreLetter h 2) + H +
        (a (coreLetter h 0) + a (coreLetter h 0)) +
        (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0) +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 0)) +
        (((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1) +
          ((powOmega2 t.σ) ^ (2 * mOf alpha))⁻¹ • a (coreLetter h 1)) +
        (((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1) +
          ((powOmega2 t.σ) ^ mOf alpha)⁻¹ • a (coreLetter h 1)) := by abel
  rw [hrearrange, hA₂, hA₂, hA₂, hA₂,
    add_zero, add_zero, add_zero, add_zero]

private theorem headHandlePair_core_trivial
    {h : ℕ} {C A : Type*} [Group C]
    [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    ∀ (i : Fin 3) (v : A),
      t (headHandlePairSwap j (coreLetter h i)) • v = v := by
  intro i v
  obtain ⟨l, hl⟩ : ∃ l : Fin (2 + 2 * h + 1),
      headHandlePairSwap j (coreLetter h i) = .wild l := by
    rcases i with ⟨i, hi⟩
    interval_cases i
    · refine ⟨⟨0, by omega⟩, ?_⟩
      change headHandlePairSwap j (coreLetter h 0) = coreLetter h 0
      rw [headHandlePairSwap]
      change tailHandleSwap j (headHandleSwap j (coreLetter h 0)) = coreLetter h 0
      rw [headHandleSwap_coreLetter, tailHandleSwap_coreZero]
    · refine ⟨⟨1, by omega⟩, ?_⟩
      change headHandlePairSwap j (coreLetter h 1) = coreLetter h 1
      rw [headHandlePairSwap]
      change tailHandleSwap j (headHandleSwap j (coreLetter h 1)) = coreLetter h 1
      rw [headHandleSwap_coreLetter, tailHandleSwap_coreOne]
    · refine ⟨⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩, ?_⟩
      have hi2 : (⟨2, hi⟩ : Fin 3) = 2 := by apply Fin.ext; rfl
      rw [hi2]
      rw [headHandlePairSwap_coreTwo]
      apply congrArg Generator.wild
      apply Fin.ext
      rfl
  rw [hl]
  exact hwild l v

private theorem foxD_handleTailW_headHandlePair
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    foxD (fun g ↦ t (headHandlePairSwap j g))
      (fun g ↦ a (headHandlePairSwap j g)) E E₂
      (PWord.prodList (handleTailW h)) =
        a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2) := by
  cases h with
  | zero => exact Fin.elim0 j
  | succ k =>
      rw [handleTailW, PWord.prodList_cons, PWord.prodList_nil,
        foxD_mul, foxD_one, smul_zero, add_zero]
      exact foxD_handlesW_headHandlePair t a E E₂ j hwild

/-- On every unramified exponent-two module, the all-rank pair source has exactly the displaced
head row.  In particular, all promoted-handle terms cancel without fixing a rank or class. -/
theorem foxD_headHandlePairCompactW_unram
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h)
    (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) :
    foxD ⇑t a E E₂ (headHandlePairCompactW alpha j) =
      a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦ t (headHandlePairSwap j g)⟩
  let b : Generator (2 + 2 * h) → A := fun g ↦ a (headHandlePairSwap j g)
  have hcore : ∀ (i : Fin 3) (v : A), s (coreLetter h i) • v = v :=
    headHandlePair_core_trivial t j hwild
  have hsigma : ∀ v : A, s.σ • v = v := by
    intro v
    change t (headHandlePairSwap j .sigma) • v = v
    rw [headHandlePairSwap_sigma]
    exact hwild _ v
  have hs (k : ℕ) (v : A) : ((powOmega2 s.σ) ^ k)⁻¹ • v = v :=
    mem_trivAct.mp (inv_mem (pow_mem
      (trivAct_powOmega2 (mem_trivAct.mpr hsigma)) k)) v
  rw [foxD_headHandlePairCompactW_eq]
  change foxD ⇑s b E E₂ (mCompactW alpha h) = _
  rw [foxD_mCompact_unram_of_core_trivial s b E E₂ alpha hA₂ hcore
      (by intro v; change t (headHandlePairSwap j .tau) • v = v;
          rw [headHandlePairSwap_tau]; exact hτ v)
      (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2))
      (foxD_handleTailW_headHandlePair t a E E₂ j hwild)]
  simp only [hs, hA₂, add_zero, s, b, headHandlePairSwap_tau]
  rw [headHandlePairSwap_coreTwo]
  have hSinv : s.σ⁻¹ • a (handleV j) = a (handleV j) :=
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr hsigma)) _
  rw [hSinv, sub_self, add_zero]

/-- On every ramified exponent-two module, the all-rank pair source has a unit coefficient on
the selected `V`-handle, together with the same displaced-head row. -/
theorem foxD_headHandlePairCompactW_ram
    {h : ℕ} {C A : Type*} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (a : Generator (2 + 2 * h) → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h)
    (hA₂ : ∀ v : A, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτfpf : ∀ v : A, t.τ • v = v → v = 0)
    (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    foxD ⇑t a E E₂ (headHandlePairCompactW alpha j) =
      -a (handleV j) +
        (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦ t (headHandlePairSwap j g)⟩
  let b : Generator (2 + 2 * h) → A := fun g ↦ a (headHandlePairSwap j g)
  have hcore : ∀ (i : Fin 3) (v : A), s (coreLetter h i) • v = v :=
    headHandlePair_core_trivial t j hwild
  rw [foxD_headHandlePairCompactW_eq]
  change foxD ⇑s b E E₂ (mCompactW alpha h) = _
  rw [foxD_mCompact_ram_of_core_trivial s b E E₂ alpha hA₂ hcore
      (by intro v hv; apply hτfpf v;
          change t (headHandlePairSwap j .tau) • v = v at hv;
          simpa using hv)
      (by intro v; change powOmega2 (t (headHandlePairSwap j .tau)) • v = v;
          rw [headHandlePairSwap_tau]; exact hTodd v)
      (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2))
      (foxD_handleTailW_headHandlePair t a E E₂ j hwild)]
  change -((t (headHandlePairSwap j .sigma))⁻¹ •
      a (headHandlePairSwap j (coreLetter h 2))) +
      (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) = _
  rw [headHandlePairSwap_sigma, headHandlePairSwap_coreTwo]
  have hUinv : (t (handleU j))⁻¹ • a (handleV j) = a (handleV j) :=
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr (hwild _))) _
  rw [hUinv]


#print axioms foxD_headHandlePairCompactW_eq
#print axioms foxD_handlesW_of_right_trivial
#print axioms foxD_handlesW_headHandlePair
#print axioms evalFin_a0W_smul_of_core_trivial
#print axioms foxD_a0W_of_core_trivial
#print axioms foxD_leadingSquare_of_core_trivial
#print axioms evalFin_leadingSquare_smul_of_core_trivial
#print axioms foxD_leadingComm_of_core_trivial
#print axioms evalFin_leadingComm_smul_of_core_trivial
#print axioms foxD_mWordWith_core_of_core_trivial
#print axioms foxD_headHandlePairCompactW_unram
#print axioms foxD_headHandlePairCompactW_ram

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
