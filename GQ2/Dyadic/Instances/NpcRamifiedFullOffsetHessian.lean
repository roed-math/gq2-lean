/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcRamifiedRow
import GQ2.Dyadic.Instances.MpcJetGeneral

/-!
# The ramified Npc Hessian at full operator-twisted offsets

This file evaluates the corrected procyclic-`N` word on the two-entry ramified normal cochains.
The `omega2` block is computed rather than hidden: for the mixed element over `(c2, tau)`, its
central value is exactly `NpcJet.powCharge dat tau c2 (orderOf tau)`.  The delta, correction,
boundary, and handle blocks then assemble to

```
npcRamifiedDiagonal c0 + polar q c1 (A⁻¹ • c0) + handles,
```

where `c2 = B • (A⁻¹ • c0 - c0)`.  The key cancellation is
`c2 + lcSmul c0 = A⁻¹ • c0`: the boundary pairing and the corrected `L_c` pairing therefore
combine into the single displayed cross term.

The honest finite evaluation needs only odd order and fixed-point-freeness of `tau`; passage to
the integer-resolver `hessRelZ` register adds exactly `ResolverLifts E (CentExt kappa0)`.

This is the full Hessian decomposition.  Proving that `npcRamifiedDiagonal` is quadratic and
identifying its Gauss model are deliberately left to a separate analytic wave.
-/

namespace GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian

noncomputable section

open GQ2 GQ2.SectionSix GQ2.FoxH GQ2.QuadraticFp2
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Certificates.MCompact

/-! The honest truncated central charge of a zero-fibre lift. -/

def centExtTruncatedCharge {L : Type*} [Group L] (c : WordCoh.TwoCocycle L)
    (b : L) (e : ℕ) : ZMod 2 :=
  ∑ k ∈ Finset.range e, c.κ (b ^ k) b

theorem centExt_pow_fib_of_fib_zero {L : Type*} [Group L] (c : WordCoh.TwoCocycle L)
    (p : WordCoh.CentExt c) (hp : p.fib = 0) (e : ℕ) :
    (p ^ e).fib = centExtTruncatedCharge c p.base e := by
  induction e with
  | zero => simp [centExtTruncatedCharge]
  | succ e ih =>
      rw [pow_succ, WordCoh.CentExt.mul_fib, ih, hp]
      rw [show (p ^ e).base = p.base ^ e by
        change WordCoh.CentExt.proj c (p ^ e) = _
        exact map_pow (WordCoh.CentExt.proj c) p e]
      simp [centExtTruncatedCharge, Finset.sum_range_succ]

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

def npcRamifiedOmegaCharge (u : C) (c₂ : V) (e : ℕ) : ZMod 2 :=
  centExtTruncatedCharge (kappa0Cocycle dat hdat) ((c₂, u) : SemiProd C V) e

theorem evalZ_deltaInner_eq_zeroFib (h : ℕ) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (i : Fin 3) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = ((((vv (xIdx h i), u) : SemiProd C V), 0) :
          WordCoh.CentExt (kappa0Cocycle dat hdat)) := by
  rw [PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_gen, mul_one]
  change hessSlice dat hdat (vv (xIdx h i)) 0 * hessLine dat hdat u = _
  exact NpcBridge.hessSlice_mul_hessLine dat hdat _ _ _

theorem evalZ_omega2Block_fib_eq_charge (h : ℕ) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (i : Fin 3) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    (PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))).fib
      = npcRamifiedOmegaCharge dat hdat u (vv (xIdx h i)) e := by
  rw [PWord.omega2Pow, PWord.evalZ_profPow,
    evalZ_deltaInner_eq_zeroFib dat hdat h s u vv E E₂ i, hE]
  exact (congrArg WordCoh.CentExt.fib (zpow_natCast _ e)).trans
    (centExt_pow_fib_of_fib_zero _ _ rfl e)

theorem evalZ_omega2Block_eq_powData (h : ℕ) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (i : Fin 3) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = NpcBridge.hessElt dat hdat
          (NpcJet.normSum u e (vv (xIdx h i))) (u ^ e)
          (NpcJet.powCharge dat u (vv (xIdx h i)) e) := by
  rw [PWord.omega2Pow, PWord.evalZ_profPow,
    evalZ_deltaInner_eq_zeroFib dat hdat h s u vv E E₂ i, hE]
  exact (zpow_natCast _ e).trans (NpcBridge.hessElt_pow dat hdat _ _ _)

theorem evalFin_omega2Block_eq_charge [Finite C] [Finite V]
    (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (i : Fin 3) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (NpcJet.powCharge dat u (vv (xIdx h i)) (orderOf u)) := by
  exact Certificates.MpcJet.evalFin_uW dat hdat s u hu hVu vv E E₂ i

theorem evalFin_deltaZero_eq_slice [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.deltaZeroW h)
      = hessSlice dat hdat (vv (Certificates.x0Idx h))
          (NpcJet.powCharge dat u (vv (Certificates.x0Idx h)) (orderOf u)
            + q (vv (Certificates.x0Idx h))) := by
  change PWord.evalFin
      (Certificates.MpcJet.hessLift dat hdat (h := h) s u vv) E E₂
        (Words.Mpc.dW h 0) = _
  exact Certificates.MpcJet.evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 0

theorem evalFin_aW_line (h : ℕ) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (d : EtaData) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.aW h d) = hessLine dat hdat (s ^ E d.toZhat) := by
  rw [Words.Npc.aW, PWord.evalFin_profPow_of_ne _ _ _ _ (Words.Npc.toZhat_ne_omega2 d),
    PWord.evalFin_gen]
  change (hessLineHom dat hdat s) ^ E d.toZhat = hessLineHom dat hdat (s ^ E d.toZhat)
  exact (map_zpow (hessLineHom dat hdat) s (E d.toZhat)).symm

theorem evalFin_bW_line (h r : ℕ) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.bW h r) = hessLine dat hdat (s ^ ((2 : ℤ) ^ r)) := by
  rw [Words.Npc.bW, PWord.evalFin_zpow, PWord.evalFin_gen]
  change (hessLineHom dat hdat s) ^ ((2 : ℤ) ^ r) =
    hessLineHom dat hdat (s ^ ((2 : ℤ) ^ r))
  exact (map_zpow (hessLineHom dat hdat) s ((2 : ℤ) ^ r)).symm

theorem evalFin_dBlock_exists [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (r : ℕ) (d : EtaData) :
    ∃ zD : ZMod 2,
      PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
          (Words.Npc.dBlockW h r d)
        = hessSlice dat hdat
            (Certificates.Npc.lcSmul s (E d.toZhat) r
              (vv (Certificates.x0Idx h))) zD := by
  let c₀ := vv (Certificates.x0Idx h)
  let z₀ := NpcJet.powCharge dat u c₀ (orderOf u) + q c₀
  have hδ : PWord.evalFin
      (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.deltaZeroW h) = hessSlice dat hdat c₀ z₀ :=
    evalFin_deltaZero_eq_slice dat hdat hV2 h s u hu hVu vv E E₂
  have hA := evalFin_aW_line dat hdat h s u vv E E₂ d
  have hB := evalFin_bW_line dat hdat h r s u vv E E₂
  simp only [Words.Npc.dBlockW, PWord.prodList_cons, PWord.prodList_nil,
    PWord.evalFin_mul, PWord.evalFin_one, PWord.evalFin_conj, PWord.evalFin_inv, mul_one]
  rw [hδ, hA, hB, NpcBridge.hessSlice_conj_hessLine,
    hessSlice_mul dat hdat, NpcBridge.hessLine_inv,
    NpcBridge.hessSlice_conj_hessLine,
    hessSlice_mul dat hdat]
  have hv :
      (s ^ E d.toZhat)⁻¹ • c₀ + (s ^ ((2 : ℤ) ^ r))⁻¹⁻¹ •
          (c₀ + (s ^ E d.toZhat)⁻¹ • c₀) =
        Certificates.Npc.lcSmul s (E d.toZhat) r c₀ := by
    simp only [Certificates.Npc.lcSmul, inv_inv, smul_add]
    rw [← mul_smul]
    abel
  rw [hv]
  exact ⟨_, rfl⟩

theorem evalFin_eBlock_eq_incl [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (r : ℕ) (d : EtaData) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.eBlockW h r d)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (polar q
            (Certificates.Npc.lcSmul s (E d.toZhat) r (vv (Certificates.x0Idx h)))
            (vv (Certificates.x1Idx h))) := by
  obtain ⟨zD, hD⟩ := evalFin_dBlock_exists dat hdat hV2 h s u hu hVu vv E E₂ r d
  rw [Words.Npc.eBlockW, PWord.evalFin_comm, hD]
  change commR
      (hessSlice dat hdat
        (Certificates.Npc.lcSmul s (E d.toZhat) r (vv (Certificates.x0Idx h))) zD)
      (hessSlice dat hdat (vv (Certificates.x1Idx h)) 0) = _
  exact hessSlice_commR dat hdat hV2 _ _ _ _

/-- The ramified Npc part independent of `x1` and the handle coordinates. -/
noncomputable def npcRamifiedCoreElt (s u : C) (E : Zhat → ℤ)
    (alpha r : ℕ) (d : EtaData) (c0 c2 : V) :
    WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  hessSlice dat hdat c0 0 ^ ((2 : ℤ) + 2 ^ alpha) *
    (commR (hessSlice dat hdat c0 0) (hessLine dat hdat (s ^ E d.toZhat)) *
      ((conjR (hessSlice dat hdat c2 0)
          (hessLine dat hdat (s ^ ((2 : ℤ) ^ r))))⁻¹ *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (NpcJet.powCharge dat u c2 (orderOf u))))

theorem evalFin_npcW_fullOffset [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha r : ℕ) (d : EtaData) :
    PWord.evalFin (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (Words.Npc.npcW alpha r h d)
      = npcRamifiedCoreElt dat hdat s u E alpha r d
          (vv (Certificates.x0Idx h)) (vv (Certificates.x2Idx h)) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (polar q
            (Certificates.Npc.lcSmul s (E d.toZhat) r (vv (Certificates.x0Idx h)))
            (vv (Certificates.x1Idx h))) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) := by
  have homega := evalFin_omega2Block_eq_charge dat hdat h s u hu hVu vv E E₂ 2
  have hhandles := Certificates.MpcJet.evalFin_handlesW dat hdat hV2 s u vv E E₂
  change PWord.evalFin
      (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (handlesW h) = _ at hhandles
  simp only [PWord.prodList_cons, PWord.prodList_nil] at homega
  simp only [Words.Npc.npcW, PWord.prodList_cons, PWord.prodList_nil,
    PWord.evalFin_mul, PWord.evalFin_one, PWord.evalFin_zpow, PWord.evalFin_gen,
    PWord.evalFin_comm, PWord.evalFin_inv, PWord.evalFin_conj, mul_one]
  rw [evalFin_aW_line dat hdat h s u vv E E₂ d,
    evalFin_bW_line dat hdat h r s u vv E E₂,
    homega,
    evalFin_eBlock_eq_incl dat hdat hV2 h s u hu hVu vv E E₂ r d,
    hhandles]
  change hessSlice dat hdat (vv (Certificates.x0Idx h)) 0 ^ ((2 : ℤ) + 2 ^ alpha) *
      (commR (hessSlice dat hdat (vv (Certificates.x0Idx h)) 0)
        (hessLine dat hdat (s ^ E d.toZhat)) *
      ((conjR (hessSlice dat hdat (vv (Certificates.x2Idx h)) 0)
        (hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 *
          hessLine dat hdat (s ^ ((2 : ℤ) ^ r))))⁻¹ *
      (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u)) *
      (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (polar q (Certificates.Npc.lcSmul s (E d.toZhat) r
          (vv (Certificates.x0Idx h))) (vv (Certificates.x1Idx h))) *
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))))))) = _
  rw [Instances.NpcUnramifiedFullOffsetHessian.inv_conjR_slice_mul_line dat hdat hV2]
  unfold npcRamifiedCoreElt
  have hc := Certificates.MpcJet.incl_commute
    (c := kappa0Cocycle dat hdat)
    (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h)))
    (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u)))
  have hswap (x y : WordCoh.CentExt (kappa0Cocycle dat hdat)) :
      x * WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) *
          (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u)) * y) =
        x * WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u)) *
          (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) * y) := by
    calc
      _ = x * (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h))) *
            WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u))) * y := by group
      _ = x * (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (NpcJet.powCharge dat u (vv (Certificates.x2Idx h)) (orderOf u)) *
            WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
              (polar q (vv (Certificates.x2Idx h)) (vv (Certificates.x1Idx h)))) * y := by
          rw [hc.eq]
      _ = _ := by group
  rw [hswap]
  group

theorem twistedBoundary_add_lc (hV2 : ∀ v : V, v + v = 0)
    (s : C) (k : ℤ) (r : ℕ) (c0 : V) :
    ((s ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • ((s ^ k)⁻¹ • c0 - c0) +
        Certificates.Npc.lcSmul s k r c0 = (s ^ k)⁻¹ • c0 := by
  have hneg : ∀ v : V, -v = v := fun v => neg_eq_of_add_eq_zero_left (hV2 v)
  simp only [Certificates.Npc.lcSmul, inv_inv, sub_eq_add_neg, hneg]
  rw [smul_add, ← mul_smul]
  have hB : s ^ ((2 : ℤ) ^ r) • c0 + s ^ ((2 : ℤ) ^ r) • c0 = 0 := hV2 _
  have hBA : (s ^ ((2 : ℤ) ^ r) * (s ^ k)⁻¹) • c0 +
      (s ^ ((2 : ℤ) ^ r) * (s ^ k)⁻¹) • c0 = 0 := hV2 _
  calc
    _ = ((s ^ ((2 : ℤ) ^ r) * (s ^ k)⁻¹) • c0 +
          (s ^ ((2 : ℤ) ^ r) * (s ^ k)⁻¹) • c0) +
        (s ^ ((2 : ℤ) ^ r) • c0 + s ^ ((2 : ℤ) ^ r) • c0) +
        (s ^ k)⁻¹ • c0 := by abel
    _ = (s ^ k)⁻¹ • c0 := by simp only [hBA, hB, zero_add]

def npcTwistedOffsets (h : ℕ) (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) : Fin (2 + 2 * h + 1) → V :=
  fun i => evenTwistedNormal h g bInv c0 c1 z (.wild i)

@[simp] theorem npcTwistedOffsets_x0 (h : ℕ) (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) :
    npcTwistedOffsets h g bInv c0 c1 z (Certificates.x0Idx h) = c0 := by
  change evenTwistedNormal h g bInv c0 c1 z (coreLetter h 0) = c0
  simp

@[simp] theorem npcTwistedOffsets_x1 (h : ℕ) (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) :
    npcTwistedOffsets h g bInv c0 c1 z (Certificates.x1Idx h) = c1 := by
  change evenTwistedNormal h g bInv c0 c1 z (coreLetter h 1) = c1
  simp

@[simp] theorem npcTwistedOffsets_x2 (h : ℕ) (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) :
    npcTwistedOffsets h g bInv c0 c1 z (Certificates.x2Idx h) =
      bInv⁻¹ • (g • c0 - c0) := by
  change evenTwistedNormal h g bInv c0 c1 z (coreLetter h 2) = _
  simp

@[simp] theorem npcTwistedOffsets_hIdxU {h : ℕ} (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) (j : Fin h) :
    npcTwistedOffsets h g bInv c0 c1 z (Certificates.hIdxU j) = z (j, 0) := by
  change evenTwistedNormal h g bInv c0 c1 z (handleU j) = z (j, 0)
  exact evenTwistedNormal_handleU g bInv c0 c1 z j

@[simp] theorem npcTwistedOffsets_hIdxV {h : ℕ} (g bInv : C) (c0 c1 : V)
    (z : Fin h × Fin 2 → V) (j : Fin h) :
    npcTwistedOffsets h g bInv c0 c1 z (Certificates.hIdxV j) = z (j, 1) := by
  change evenTwistedNormal h g bInv c0 c1 z (handleV j) = z (j, 1)
  exact evenTwistedNormal_handleV g bInv c0 c1 z j

noncomputable def npcRamifiedDiagonal (s u : C) (E : Zhat → ℤ)
    (alpha r : ℕ) (d : EtaData) (c0 : V) : ZMod 2 :=
  (npcRamifiedCoreElt dat hdat s u E alpha r d c0
    (((s ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • ((s ^ E d.toZhat)⁻¹ • c0 - c0))).fib

theorem evalFin_npcW_evenTwistedNormal [Finite C] [Finite V]
    (hq : IsQuadraticFp2 q) (hV2 : ∀ v : V, v + v = 0)
    (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha r : ℕ) (d : EtaData)
    (c0 c1 : V) (z : Fin h × Fin 2 → V) :
    (PWord.evalFin
      (WordCoh.lift
        (Certificates.hessMark s u
          (npcTwistedOffsets h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹ c0 c1 z))
        (kappa0Cocycle dat hdat)) E E₂ (Words.Npc.npcW alpha r h d)).fib =
      npcRamifiedDiagonal dat hdat s u E alpha r d c0 +
        polar q c1 ((s ^ E d.toZhat)⁻¹ • c0) +
        ∑ j, polar q (z (j, 0)) (z (j, 1)) := by
  rw [evalFin_npcW_fullOffset dat hdat hV2 h s u hu hVu
    (npcTwistedOffsets h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹ c0 c1 z)
    E E₂ alpha r d]
  simp only [WordCoh.CentExt.mul_fib, WordCoh.CentExt.incl_fib,
    WordCoh.CentExt.incl_base, (kappa0Cocycle dat hdat).κ_one_right, add_zero,
    npcTwistedOffsets_x0, npcTwistedOffsets_x1, npcTwistedOffsets_x2,
    npcTwistedOffsets_hIdxU, npcTwistedOffsets_hIdxV]
  unfold npcRamifiedDiagonal
  have hcross :
      polar q
          (((s ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • ((s ^ E d.toZhat)⁻¹ • c0 - c0)) c1 +
        polar q (Certificates.Npc.lcSmul s (E d.toZhat) r c0) c1 =
      polar q c1 ((s ^ E d.toZhat)⁻¹ • c0) := by
    rw [← hq.polar_add_left,
      twistedBoundary_add_lc hV2 s (E d.toZhat) r c0, polar_comm]
  linear_combination hcross

theorem hessRelZ_npcW_evenTwistedNormal [Finite C] [Finite V]
    (hq : IsQuadraticFp2 q) (hV2 : ∀ v : V, v + v = 0)
    (h : ℕ) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha r : ℕ) (d : EtaData)
    (c0 c1 : V) (z : Fin h × Fin 2 → V)
    (hres : Certificates.MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ
        (Certificates.hessMark s u
          (npcTwistedOffsets h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹ c0 c1 z))
        (kappa0Cocycle dat hdat) E E₂ (Words.Npc.npcW alpha r h d) =
      npcRamifiedDiagonal dat hdat s u E alpha r d c0 +
        polar q c1 ((s ^ E d.toZhat)⁻¹ • c0) +
        ∑ j, polar q (z (j, 0)) (z (j, 1)) := by
  rw [hessRelZ, hessEvalZ,
    Certificates.MProcyclic.evalZ_eq_evalFin_of_resolverLifts hres]
  exact evalFin_npcW_evenTwistedNormal dat hdat hq hV2 h s u hu hVu E E₂
    alpha r d c0 c1 z

end

/-! ## Axiom audit -/

#print axioms centExtTruncatedCharge
#print axioms centExt_pow_fib_of_fib_zero
#print axioms npcRamifiedOmegaCharge
#print axioms evalZ_deltaInner_eq_zeroFib
#print axioms evalZ_omega2Block_fib_eq_charge
#print axioms evalZ_omega2Block_eq_powData
#print axioms evalFin_omega2Block_eq_charge
#print axioms evalFin_deltaZero_eq_slice
#print axioms evalFin_aW_line
#print axioms evalFin_bW_line
#print axioms evalFin_dBlock_exists
#print axioms evalFin_eBlock_eq_incl
#print axioms npcRamifiedCoreElt
#print axioms evalFin_npcW_fullOffset
#print axioms twistedBoundary_add_lc
#print axioms npcTwistedOffsets
#print axioms npcTwistedOffsets_x0
#print axioms npcTwistedOffsets_x1
#print axioms npcTwistedOffsets_x2
#print axioms npcTwistedOffsets_hIdxU
#print axioms npcTwistedOffsets_hIdxV
#print axioms npcRamifiedDiagonal
#print axioms evalFin_npcW_evenTwistedNormal
#print axioms hessRelZ_npcW_evenTwistedNormal

end GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian
