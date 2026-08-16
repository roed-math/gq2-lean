/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Certificates.MpcJet
import GQ2.Dyadic.Certificates.L

/-!
# Honest ramified compact-M Hessian

This file evaluates the compact-M word on the graph-type κ⁰-extension when the tame
`τ`-letter has odd order and acts fixed-point-freely.  It avoids the false `hP0` projector
and `hS₂` triviality assumptions of the older generic assembler by retaining the charged
δ-slices until the complete word is multiplied.  Their opaque power charges and moving-line
`m`-charges then cancel in pairs.
-/

namespace GQ2.Dyadic.Certificates.MCompactRamified

noncomputable section

open GQ2 GQ2.FoxH GQ2.QuadraticFp2
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert
open GQ2.Dyadic.Certificates.MpcJet

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

private abbrev KExt := WordCoh.CentExt (kappa0Cocycle dat hdat)

theorem sliceList_charges (l : List (V × ZMod 2)) :
    (l.map (fun p ↦ hessSlice dat hdat p.1 p.2)).prod
      = (l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [hessSlice_eq_zero_mul_incl dat hdat, ih]
      calc
        (hessSlice dat hdat p.1 0 * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) p.2) *
            ((l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod *
              WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (l.map Prod.snd).sum)
          = hessSlice dat hdat p.1 0 *
              (WordCoh.CentExt.incl (kappa0Cocycle dat hdat) p.2 *
                (l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod) *
              WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (l.map Prod.snd).sum := by group
        _ = hessSlice dat hdat p.1 0 *
              ((l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod *
                WordCoh.CentExt.incl (kappa0Cocycle dat hdat) p.2) *
              WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (l.map Prod.snd).sum := by
              rw [(incl_commute (c := kappa0Cocycle dat hdat) p.2
                (l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod).eq]
        _ = (hessSlice dat hdat p.1 0 *
              (l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod) *
              (WordCoh.CentExt.incl (kappa0Cocycle dat hdat) p.2 *
                WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (l.map Prod.snd).sum) := by
              group
        _ = _ := by rw [centExt_incl_mul]

theorem sliceOctagon_zero (hV2 : ∀ v : V, v + v = 0)
    (hqinv : ∀ (g : C) (v : V), q (g • v) = q v)
    (K : C) (a b : V) :
    ([(a, 0), (K⁻¹ • b, 0), (K⁻¹ • a, 0), ((K ^ 2)⁻¹ • b, 0),
        ((K ^ 2)⁻¹ • b, 0), (K⁻¹ • b, 0), (K⁻¹ • a, 0), (a, 0)].map
      (fun p ↦ hessSlice dat hdat p.1 p.2)).prod
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q a b) := by
  let A : KExt dat hdat := hessSlice dat hdat a 0
  let B : KExt dat hdat := hessSlice dat hdat (K⁻¹ • b) 0
  let D : KExt dat hdat := hessSlice dat hdat (K⁻¹ • a) 0
  let F : KExt dat hdat := hessSlice dat hdat ((K ^ 2)⁻¹ • b) 0
  have hA : A ^ 2 = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q a) := by
    change hessSlice dat hdat a 0 ^ 2 = _
    rw [NpcBridge.hessSlice_sq_of_npc dat hdat hV2,
      NpcBridge.hessSlice_zero_eq_incl]
  have hF : F ^ 2 = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b) := by
    rw [show F ^ 2 = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (q ((K ^ 2)⁻¹ • b)) by
        change hessSlice dat hdat ((K ^ 2)⁻¹ • b) 0 ^ 2 = _
        rw [NpcBridge.hessSlice_sq_of_npc dat hdat hV2,
          NpcBridge.hessSlice_zero_eq_incl]]
    rw [hqinv]
  have hBD : (B * D) ^ 2 = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q (a + b)) := by
    have hbase : B * D = hessSlice dat hdat (K⁻¹ • (b + a))
        (dat.f (K⁻¹ • b) (K⁻¹ • a)) := by
      simp only [B, D, hessSlice_mul]
      rw [smul_add]
      simp only [zero_add]
    rw [hbase, NpcBridge.hessSlice_sq_of_npc dat hdat hV2,
      NpcBridge.hessSlice_zero_eq_incl, hqinv, add_comm b a]
  change A * (B * (D * (F * (F * (B * (D * (A * 1))))))) = _
  rw [mul_one]
  calc
    A * (B * (D * (F * (F * (B * (D * A))))))
        = A * ((B * D) * (F * F) * (B * D) * A) := by group
    _ = A * ((B * D) * (F ^ 2) * (B * D) * A) := by rw [pow_two]
    _ = A * ((B * D) * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b)
          * (B * D) * A) := by rw [hF]
    _ = A * ((B * D) * (B * D) * A
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b)) := by
          rw [mul_incl_mul dat hdat (B * D) (B * D),
            mul_incl_mul dat hdat ((B * D) * (B * D)) A]
    _ = A * ((B * D) ^ 2 * A
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b)) := by rw [pow_two]
    _ = A * (WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q (a + b)) * A
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b)) := by rw [hBD]
    _ = A * A * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q (a + b))
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b) := by
          rw [(incl_commute (c := kappa0Cocycle dat hdat) (q (a + b)) A).eq]
          group
    _ = A ^ 2 * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q (a + b))
          * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b) := by rw [pow_two]
    _ = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q a + q (a + b) + q b) := by rw [hA, centExt_incl_mul, centExt_incl_mul]
    _ = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q a b) := by
          congr 1
          simp only [polar]
          abel

theorem leadingSlices (hV2 : ∀ v : V, v + v = 0)
    (hqinv : ∀ (g : C) (v : V), q (g • v) = q v) (K : C) (a b : V) :
    let X := hessSlice dat hdat a 0
    let Y := hessSlice dat hdat b 0
    let L := hessLine dat hdat K
    (X⁻¹ * L⁻¹) ^ 2 * commR (X⁻¹ * L⁻¹) Y * L ^ 2
      = ([(a, q a),
          (K⁻¹ • b, dat.m K⁻¹ b + q b),
          (K⁻¹ • a, q a + dat.m K⁻¹ a),
          ((K ^ 2)⁻¹ • b, dat.m (K ^ 2)⁻¹ b)].map
          (fun p ↦ hessSlice dat hdat p.1 p.2)).prod := by
  dsimp only
  rw [hessSlice_inv dat hdat hV2, zero_add]
  have hL2 : hessLine dat hdat K ^ 2 = hessLine dat hdat (K ^ 2) := by
    rw [pow_two, hessLine_mul, pow_two]
  calc
    (hessSlice dat hdat a (q a) * (hessLine dat hdat K)⁻¹) ^ 2 *
          commR (hessSlice dat hdat a (q a) * (hessLine dat hdat K)⁻¹)
            (hessSlice dat hdat b 0) * hessLine dat hdat K ^ 2
        = hessSlice dat hdat a (q a) *
            (conjR (hessSlice dat hdat b 0) (hessLine dat hdat K))⁻¹ *
            conjR (hessSlice dat hdat a (q a)) (hessLine dat hdat K) *
            conjR (hessSlice dat hdat b 0) (hessLine dat hdat K ^ 2) := by
              simp only [commR, conjR, pow_two]
              group
    _ = hessSlice dat hdat a (q a) *
          (hessSlice dat hdat (K⁻¹ • b) (dat.m K⁻¹ b))⁻¹ *
          hessSlice dat hdat (K⁻¹ • a) (q a + dat.m K⁻¹ a) *
          hessSlice dat hdat ((K ^ 2)⁻¹ • b) (dat.m (K ^ 2)⁻¹ b) := by
            rw [NpcBridge.hessSlice_conj_hessLine,
              NpcBridge.hessSlice_conj_hessLine, zero_add, hL2,
              NpcBridge.hessSlice_conj_hessLine, zero_add]
    _ = _ := by
      rw [hessSlice_inv dat hdat hV2]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hqinv K⁻¹ b]
      group

theorem correctionSlices (K : C) (a b : V) (z₀ z₁ : ZMod 2) :
    conjR (hessSlice dat hdat b z₁) (hessLine dat hdat (K ^ 2)) *
        conjR (hessSlice dat hdat b z₁) (hessLine dat hdat K) *
        conjR (hessSlice dat hdat a z₀) (hessLine dat hdat K) *
        hessSlice dat hdat a z₀
      = ([
          ((K ^ 2)⁻¹ • b, z₁ + dat.m (K ^ 2)⁻¹ b),
          (K⁻¹ • b, z₁ + dat.m K⁻¹ b),
          (K⁻¹ • a, z₀ + dat.m K⁻¹ a),
          (a, z₀)].map (fun p ↦ hessSlice dat hdat p.1 p.2)).prod := by
  rw [NpcBridge.hessSlice_conj_hessLine, NpcBridge.hessSlice_conj_hessLine,
    NpcBridge.hessSlice_conj_hessLine]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  group

theorem coreCancellation (hV2 : ∀ v : V, v + v = 0)
    (hqinv : ∀ (g : C) (v : V), q (g • v) = q v)
    (K : C) (a b : V) (p₀ p₁ : ZMod 2) :
    let X := hessSlice dat hdat a 0
    let Y := hessSlice dat hdat b 0
    let L := hessLine dat hdat K
    let z₀ := p₀ + q a
    let z₁ := p₁ + q b
    ((X⁻¹ * L⁻¹) ^ 2 * commR (X⁻¹ * L⁻¹) Y * L ^ 2) *
      (conjR (hessSlice dat hdat b z₁) (hessLine dat hdat (K ^ 2)) *
        conjR (hessSlice dat hdat b z₁) L *
        conjR (hessSlice dat hdat a z₀) L *
        hessSlice dat hdat a z₀)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q b + polar q a b) := by
  dsimp only
  rw [leadingSlices dat hdat hV2 hqinv K a b,
    correctionSlices dat hdat K a b (p₀ + q a) (p₁ + q b)]
  let l : List (V × ZMod 2) :=
    [(a, q a),
      (K⁻¹ • b, dat.m K⁻¹ b + q b),
      (K⁻¹ • a, q a + dat.m K⁻¹ a),
      ((K ^ 2)⁻¹ • b, dat.m (K ^ 2)⁻¹ b),
      ((K ^ 2)⁻¹ • b, (p₁ + q b) + dat.m (K ^ 2)⁻¹ b),
      (K⁻¹ • b, (p₁ + q b) + dat.m K⁻¹ b),
      (K⁻¹ • a, (p₀ + q a) + dat.m K⁻¹ a),
      (a, p₀ + q a)]
  rw [← List.prod_append, ← List.map_append]
  change (l.map (fun p ↦ hessSlice dat hdat p.1 p.2)).prod = _
  rw [sliceList_charges dat hdat l]
  have hzero :
      (l.map (fun p ↦ hessSlice dat hdat p.1 0)).prod
        = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q a b) := by
    exact sliceOctagon_zero dat hdat hV2 hqinv K a b
  rw [hzero, centExt_incl_mul]
  congr 1
  dsimp only [l]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  linear_combination
    2 * CharTwo.add_self_eq_zero (q a) +
    CharTwo.add_self_eq_zero (dat.m K⁻¹ b) +
    CharTwo.add_self_eq_zero (q b) +
    CharTwo.add_self_eq_zero (dat.m K⁻¹ a) +
    CharTwo.add_self_eq_zero (dat.m (K ^ 2)⁻¹ b) +
    CharTwo.add_self_eq_zero p₁ +
    CharTwo.add_self_eq_zero p₀

section Word

variable [Finite C] [Finite V]

omit [Finite V] in
theorem evalFin_sigma2W_hess {h : ℕ} (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ sigma2W
      = hessLine dat hdat (powOmega2 s) := by
  rw [sigma2W, PWord.evalFin_omega2Pow, PWord.evalFin_gen, hessLift_sigma]
  change powOmega2 (hessLineHom dat hdat s) = hessLineHom dat hdat (powOmega2 s)
  rw [← powOmega2_map]

omit [Finite V] in
theorem evalFin_sigma2Pow_hess {h : ℕ} (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : ℕ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
        (.zpow sigma2W (k : ℤ))
      = hessLine dat hdat ((powOmega2 s) ^ k) := by
  rw [PWord.evalFin_zpow, evalFin_sigma2W_hess dat hdat, zpow_natCast]
  change hessLineHom dat hdat (powOmega2 s) ^ k
    = hessLineHom dat hdat (powOmega2 s ^ k)
  rw [map_pow]

theorem evalFin_j2W_one {h : ℕ} (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (coreIdx h 2) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (j2W h) = 1 := by
  have hx2 : hessLift dat hdat (h := h) s u vv (coreLetter h 2) = 1 := by
    rw [hessLift_coreLetter, hv2]
    rfl
  rw [j2W, MCompact.evalFin_prodList_pair, PWord.evalFin_inv, PWord.evalFin_conj,
    PWord.evalFin_gen, hx2, one_conjR, inv_one, one_mul,
    show PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
        = Words.Mpc.uW h 2
      from rfl,
    evalFin_uW dat hdat s u hu hVu vv E E₂ 2,
    show vv (coreIdx h 2) = 0 from hv2,
    powCharge_zero_vec dat hdat, WordCoh.CentExt.incl_zero]

omit [Finite V] in
theorem evalFin_a0W_hess {h : ℕ} (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (α : ℕ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (a0W α h)
      = (hessSlice dat hdat (vv (coreIdx h 0)) 0)⁻¹ *
          (hessLine dat hdat ((powOmega2 s) ^ (mOf α)))⁻¹ := by
  rw [a0W, MCompact.evalFin_prodList_pair, PWord.evalFin_inv, PWord.evalFin_gen,
    hessLift_coreLetter, PWord.evalFin_zpow, evalFin_sigma2W_hess dat hdat,
    zpow_neg, zpow_natCast]
  have hp : hessLine dat hdat (powOmega2 s) ^ mOf α
      = hessLine dat hdat (powOmega2 s ^ mOf α) := by
    change hessLineHom dat hdat (powOmega2 s) ^ mOf α
      = hessLineHom dat hdat (powOmega2 s ^ mOf α)
    rw [map_pow]
  rw [hp]

theorem evalFin_eRevW_hess {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (α : ℕ) :
    let K := (powOmega2 s) ^ (mOf α)
    let z₀ := NpcJet.powCharge dat u (vv (coreIdx h 0)) (orderOf u)
      + q (vv (coreIdx h 0))
    let z₁ := NpcJet.powCharge dat u (vv (coreIdx h 1)) (orderOf u)
      + q (vv (coreIdx h 1))
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (eRevW α h)
      = conjR (hessSlice dat hdat (vv (coreIdx h 1)) z₁)
            (hessLine dat hdat (K ^ 2)) *
          conjR (hessSlice dat hdat (vv (coreIdx h 1)) z₁)
            (hessLine dat hdat K) *
          conjR (hessSlice dat hdat (vv (coreIdx h 0)) z₀)
            (hessLine dat hdat K) *
          hessSlice dat hdat (vv (coreIdx h 0)) z₀ := by
  dsimp only
  have hK2 : (powOmega2 s) ^ (2 * mOf α)
      = ((powOmega2 s) ^ (mOf α)) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [eRevW, evalFin_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [PWord.evalFin_conj, PWord.evalFin_conj, PWord.evalFin_conj,
    ← Certificates.MProcyclic.dW_eq_deltaCert,
    ← Certificates.MProcyclic.dW_eq_deltaCert,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 1,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 0,
    show 2 * (mOf α : ℤ) = ((2 * mOf α : ℕ) : ℤ) by norm_num,
    evalFin_sigma2Pow_hess dat hdat s u vv E E₂,
    evalFin_sigma2Pow_hess dat hdat s u vv E E₂,
    hK2]
  group

theorem evalFin_mCompact_ramified_zero (hV2 : ∀ v : V, v + v = 0)
    (α : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := 0) s u ![c₀, c₁, 0]) E E₂
        (mCompactW α 0)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q c₁ + polar q c₀ c₁) := by
  let vv : Fin 3 → V := ![c₀, c₁, 0]
  let K : C := (powOmega2 s) ^ (mOf α)
  let p₀ : ZMod 2 := NpcJet.powCharge dat u c₀ (orderOf u)
  let p₁ : ZMod 2 := NpcJet.powCharge dat u c₁ (orderOf u)
  have hv0 : vv (coreIdx 0 0) = c₀ := rfl
  have hv1 : vv (coreIdx 0 1) = c₁ := rfl
  have hv2 : vv (coreIdx 0 2) = 0 := rfl
  have hqinv : ∀ (g : C) (v : V), q (g • v) = q v :=
    Certificates.LSqStokes.factorSet_q_invariant dat hdat hV2
  change PWord.evalFin (hessLift dat hdat (h := 0) s u vv) E E₂
      (mCompactW α 0) = _
  rw [mCompactW, evalFin_prodList, List.map_append, List.prod_append]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    handleTailW, mul_one]
  rw [PWord.evalFin_zpow, PWord.evalFin_comm,
    evalFin_a0W_hess (h := 0) dat hdat s u vv E E₂ α,
    PWord.evalFin_gen, hessLift_coreLetter, hv1,
    show 2 * (mOf α : ℤ) = ((2 * mOf α : ℕ) : ℤ) by norm_num,
    evalFin_sigma2Pow_hess (h := 0) dat hdat s u vv E E₂ (2 * mOf α),
    evalFin_j2W_one (h := 0) dat hdat s u hu hVu vv hv2 E E₂,
    evalFin_eRevW_hess (h := 0) dat hdat hV2 s u hu hVu vv E E₂ α,
    hv0, hv1]
  have hK2 : (powOmega2 s) ^ (2 * mOf α) = K ^ 2 := by
    dsimp only [K]
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [hK2]
  have hc := coreCancellation dat hdat hV2 hqinv K c₀ c₁ p₀ p₁
  rw [← hc]
  have hline2 : hessLine dat hdat (K ^ 2) = hessLine dat hdat K ^ 2 := by
    simpa only [pow_two] using (hessLine_mul dat hdat K K).symm
  rw [hline2]
  dsimp only [K, p₀, p₁]
  simp only [one_mul]
  group

theorem hessRelZ_mCompact_ramified_zero (hV2 : ∀ v : V, v + v = 0)
    (α : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : Certificates.MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW α 0)
      = q c₁ + polar q c₀ c₁ := by
  rw [hessRelZ, hessEvalZ,
    Certificates.MProcyclic.evalZ_eq_evalFin_of_resolverLifts hres]
  change WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
    (PWord.evalFin (hessLift dat hdat (h := 0) s u ![c₀, c₁, 0]) E E₂
      (mCompactW α 0)) = _
  rw [evalFin_mCompact_ramified_zero dat hdat hV2 α s u hu hVu c₀ c₁ E E₂,
    WordCoh.CentExt.incl_fib]

/-! ## Axiom pins -/

#print axioms sliceList_charges
#print axioms sliceOctagon_zero
#print axioms leadingSlices
#print axioms correctionSlices
#print axioms coreCancellation
#print axioms evalFin_sigma2W_hess
#print axioms evalFin_sigma2Pow_hess
#print axioms evalFin_j2W_one
#print axioms evalFin_a0W_hess
#print axioms evalFin_eRevW_hess
#print axioms evalFin_mCompact_ramified_zero
#print axioms hessRelZ_mCompact_ramified_zero

end Word

end

end GQ2.Dyadic.Certificates.MCompactRamified
