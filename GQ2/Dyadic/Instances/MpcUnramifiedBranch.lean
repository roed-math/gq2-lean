/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcActionImageDevissage
import GQ2.Dyadic.Instances.N0M0CompactBranches

/-!
# The unramified Fox row of the corrected procyclic-`M` word

`MpcStokes` §6 computes the **ramified** row of the linear copy and `MpcFox` §5 kills the hat
copy's; both are stated inside a section that carries `hτfpf` (`tau` fixed-point free), which is
*false* on the unramified branch.  This file redoes the row at the unramified reading, and the
answer is not the procyclic-`N` shape:

```
D(R_{M,pc})(a) = a(τ) + (1 − G⁻¹)·a(x₂),        G = the value of the display `D = σ^{η̂}`.
```

**Exactly two entries, and they are the compact rows' two entries.**  Contrast
`Certificates.Npc.foxD_npc_unram`, whose `x₀`-column carries the extra block `A⁻¹ − 1` and which
therefore needs the `Φ`-normal route of `EvenPhiNormalStokes`; and contrast
`MCompact.foxD_mCompact_unram_simple`, which is literally this row with `G = σ`.  So the
procyclic-`M` unramified branch follows `N0M0UnramifiedStokes` (with the pivot generalized from
`σ⁻¹` to `G⁻¹`), not `NpcUnramifiedProcyclic`.

Two hypotheses do all the collapsing, and both are what a *simple* unramified coefficient
supplies (`RowActionImage.actionImage_wild_smul`,
`actionImage_sigma_powOmega2_smul_trivial`):

* `hwild` — the wild letters act trivially, hence so does every `δ`-letter, and
  `D(δ_i) = a(τ)` uniformly in `i` (`MCompact.foxD_deltaC_unram`);
* `hS₂` — `S₂ = σ^{ω₂}` acts trivially.  Every prefix weight on both copies is an `S₂`-power, so
  the thirteen-factor product rule becomes a plain sum, and every geometric operator `𝒢_c^k`
  becomes multiplication by `k`.  This is exactly the collapse that turns the compact-`M` row
  into the compact-`N` row, one row over.

The `σ`-column is *not* computed here: it is killed by WMP-b's coincidence lemma
(`Certificates.MProcyclic.foxColumn_sigma_mul_eq_zero`), whose `δ`-side hypotheses are supplied
below at the unramified reading.  That lemma is class-independent — it only ever needs the
`δ`-letters to act trivially and to be blind to `σ`-column offsets — so it is reused verbatim
rather than re-proved, and it is the reason the two copies' `σ`-entries never have to be
evaluated.
-/

namespace GQ2.Dyadic.MProcyclicUnram

noncomputable section

open GQ2 GQ2.SectionEight GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

/-! ## The `δ`-letters at the unramified reading -/

section Delta

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The unramified `δ`-row**: `D(δ_i) = a(τ)`, the *same* entry for every `i` — the
`τ`-contribution of the `ω₂`-block, with the two `x_i`-contributions cancelling over `𝔽₂`.
Cited from WM0-b through `dW_eq_deltaCert`, exactly as its ramified twin `foxD_dW_ram` is. -/
theorem foxD_dW_unram (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (i : Fin 3) : foxD ⇑t a E E₂ (dW h i) = a .tau :=
  MCompact.foxD_deltaC_unram t E E₂ hV₂ hwild hτ i a

omit [Finite C] [Finite V] in
/-- The `δ`-letters act trivially at the unramified reading too. -/
theorem trivAct_dW_unram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτ : ∀ w : V, t.τ • w = w) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V :=
  MCompact.trivAct_deltaC t E E₂ hwild i (MCompact.trivAct_deltaBlock_unram t E E₂ hwild hτ i)

/-- `σ`-column offsets are invisible to the unramified `δ`-row as well: `δ_i` carries no `σ`, so
its whole row is the `τ`-offset, which the `σ`-column vector zeroes. -/
theorem foxD_dW_sigma_single_unram (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (v : V) (i : Fin 3) :
    foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) = 0 := by
  rw [foxD_dW_unram t E E₂ _ hV₂ hwild hτ i,
    Pi.single_eq_of_ne (by simp : (Generator.tau : Generator (2 + 2 * h)) ≠ Generator.sigma)]

end Delta

/-! ## The `S₂`-collapse

On a simple unramified coefficient `S₂ = σ^{ω₂}` acts trivially, and *every* operator on either
copy of this row is an `S₂`-power.  These two lemmas turn `ActsAsPow (powOmega2 t.σ)` data into
plain triviality, which is what makes the whole assembly a sum with no weights. -/

section Collapse

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- Every `S₂`-power acts trivially once `S₂` does. -/
theorem smul_zpow_powOmega2 {u : C} (hS₂ : ∀ w : V, powOmega2 u • w = w) (k : ℤ) (w : V) :
    ((powOmega2 u) ^ k) • w = w :=
  mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hS₂) k) w

/-- Anything acting as an `S₂`-power acts trivially once `S₂` does. -/
theorem trivAct_of_actsAsPow {u : C} (hS₂ : ∀ w : V, powOmega2 u • w = w) {k : ℤ} {g : C}
    (hg : ActsAsPow (powOmega2 u) k g V) : g ∈ trivAct C V :=
  mem_trivAct.mpr fun w ↦ (hg w).trans (smul_zpow_powOmega2 hS₂ k w)

end Collapse

/-! ## The two copies at `σ`-free offsets

Both copies are `prodList`s all of whose factors act trivially (by the `S₂`-collapse), so both
rows are plain sums of the factor rows.  The hat copy's sum is **zero** — every one of its five
factors is either a doubled `a(τ)` or `σ`-only — and the linear copy's is the two-entry row. -/

section Rows

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

section Factors

variable (hσ : a Generator.sigma = 0) (hV₂ : ∀ w : V, w + w = 0)
  (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
  (hS₂ : ∀ w : V, powOmega2 t.σ • w = w)

include hσ hV₂ hwild hτ hS₂

omit hS₂ in
/-- `D(Â) = a(τ)`: the `Ĉ₀⁻ᵐ` tail is `σ`-only and the `δ₀`-head contributes the uniform
unramified `δ`-row. -/
theorem foxD_aHatW_unram (s' mm : ℕ) : foxD ⇑t a E E₂ (aHatW h s' mm) = a .tau := by
  have hz : foxD ⇑t a E E₂ (.zpow (c0HatW h s') (-(mm : ℤ))) = 0 := by
    rw [foxD_zpow_neg', foxD_zpow_natCast,
      Finset.sum_eq_zero fun i _ ↦ by
        rw [foxD_c0HatW_of_sigma_free t E E₂ a hσ s', smul_zero], smul_zero, neg_zero]
  rw [aHatW, MCompact.foxD_prodList_pair, hz, smul_zero, add_zero, foxD_inv,
    mem_trivAct.mp (inv_mem (trivAct_dW_unram t E E₂ hwild hτ 0)),
    foxD_dW_unram t E E₂ a hV₂ hwild hτ 0, Certificates.neg_eq_self hV₂]

omit hS₂ in
/-- `D(B̂) = a(τ)`: the `σ₂^p` tail is `σ`-only, in both emitted displays. -/
theorem foxD_bHatW_unram : ∀ pp : ℕ, foxD ⇑t a E E₂ (bHatW h pp) = a .tau
  | 0 => foxD_dW_unram t E E₂ a hV₂ hwild hτ 1
  | q + 1 => by
      have hs : foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 := by
        match q with
        | 0 => exact foxD_sigma2W_of_sigma_free t E E₂ a hσ
        | j + 1 =>
            rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
            exact foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
      rw [show bHatW h (q + 1) = PWord.prodList [dW h 1, sig2PowW h (q + 1)] from rfl,
        MCompact.foxD_prodList_pair, hs, smul_zero, add_zero,
        foxD_dW_unram t E E₂ a hV₂ hwild hτ 1]

/-- **`D(E₀₁^pc) = 0` at the unramified reading.**  All four `δ`-occurrences contribute the same
`a(τ)`, their `σ₂`-conjugators are invisible once `S₂` acts trivially, and four copies of one
vector cancel over `𝔽₂`.

⚠ Contrast the ramified `foxD_e01W_ram`, which is genuinely nonzero: there the four occurrences
carry the two *different* entries `a(x₀)` and `a(x₁)`. -/
theorem foxD_e01W_unram (aa bb : ℕ) : foxD ⇑t a E E₂ (e01W h aa bb) = 0 := by
  have hd0 := foxD_dW_unram t E E₂ a hV₂ hwild hτ 0
  have hd1 := foxD_dW_unram t E E₂ a hV₂ hwild hτ 1
  have ht0 := trivAct_dW_unram t E E₂ hwild hτ 0
  have ht1 := trivAct_dW_unram t E E₂ hwild hτ 1
  have hpow : ∀ k : ℕ, foxD ⇑t a E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (k : ℤ)) = 0 := fun k ↦
    foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
  have hconj : foxD ⇑t a E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ))) = a .tau := by
    rw [foxD_conj, hd1, hpow, smul_zero, add_zero, sub_zero, PWord.evalFin_zpow,
      MCompact.evalFin_sigma2W, ← zpow_neg, smul_zpow_powOmega2 hS₂]
  have htconj : PWord.evalFin ⇑t E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ)))
      ∈ trivAct C V := by
    rw [PWord.evalFin_conj]
    exact trivAct_conjR ht1 _
  have hinner : foxD ⇑t a E E₂
      (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (bb : ℤ)), dW h 1, dW h 0]) = a .tau := by
    rw [PWord.prodList_cons, foxD_mul, MCompact.foxD_prodList_pair, hconj, hd0, hd1,
      mem_trivAct.mp ht1, mem_trivAct.mp htconj,
      show a .tau + (a .tau + a .tau) = a .tau from by rw [hV₂, add_zero]]
  have htinner : PWord.evalFin ⇑t E E₂
      (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (bb : ℤ)), dW h 1, dW h 0])
      ∈ trivAct C V := by
    refine trivAct_evalFin_prodList fun w hw ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact htconj
    · exact ht1
    · exact ht0
  rw [e01W, MCompact.foxD_prodList_pair, foxD_conj, hinner, hpow, smul_zero, add_zero, sub_zero,
    PWord.evalFin_zpow, MCompact.evalFin_sigma2W, ← zpow_neg, smul_zpow_powOmega2 hS₂, hd0,
    PWord.evalFin_conj, mem_trivAct.mp (trivAct_conjR htinner _), hV₂]

/-- **`D(E₂^pc) = a(τ)` at the unramified reading.**  The orbit-norm base `z = δ₂δ₂^{σ₂^p}` is
first-order silent (two copies of `a(τ)`), so the whole norm block is; what survives is the head
conjugate `δ₂^{σ₂^s}`.

⚠ This is the one factor of either copy whose row is *not* zero apart from the `η̂`-commutator,
and it is the entry that becomes the row's `a(τ)`.  It is also where `ε` would live at the
ramified reading — and it does not, here: `p` is invisible once `S₂` acts trivially. -/
theorem foxD_e2W_unram (s' mm pp : ℕ) : foxD ⇑t a E E₂ (e2W h s' mm pp) = a .tau := by
  have hd2 := foxD_dW_unram t E E₂ a hV₂ hwild hτ 2
  have ht2 := trivAct_dW_unram t E E₂ hwild hτ 2
  have hsig : ∀ k : ℤ,
      foxD ⇑t a E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) k) = 0 := fun k ↦
    foxD_sigma2Pow_of_sigma_free t E E₂ a hσ k
  have hhead : foxD ⇑t a E E₂ (.conj (dW h 2) (.zpow sigma2W (s' : ℤ))) = a .tau := by
    rw [foxD_conj, hd2, hsig, smul_zero, add_zero, sub_zero, PWord.evalFin_zpow,
      MCompact.evalFin_sigma2W, ← zpow_neg, smul_zpow_powOmega2 hS₂]
  have hz : foxD ⇑t a E E₂ (zW h pp) = 0 := by
    match pp with
    | 0 =>
        rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl, foxD_zpow_natCast,
          Finset.sum_congr rfl fun i (_ : i ∈ Finset.range 2) ↦ by
            rw [hd2, mem_trivAct.mp (pow_mem ht2 i)],
          Finset.sum_const, Finset.card_range, two_nsmul, hV₂]
    | q + 1 =>
        rw [show zW h (q + 1)
              = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (q + 1))] from rfl,
          MCompact.foxD_prodList_pair, hd2, mem_trivAct.mp ht2, foxD_conj, hd2,
          show foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 from by
            match q with
            | 0 => exact foxD_sigma2W_of_sigma_free t E E₂ a hσ
            | j + 1 =>
                rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
                exact foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _,
          smul_zero, add_zero, sub_zero,
          (actsAsPow_sig2PowW t E E₂ (q + 1)).inv (a .tau), smul_zpow_powOmega2 hS₂, hV₂]
  have hnorm : foxD ⇑t a E E₂
      (PWord.prodList (Export.orbitNormFactors (zW h pp) (.zpow sigma2W (s' : ℤ)) mm)) = 0 := by
    rw [foxD_prodList_of_trivial _ _ _ _ _ (fun w hw ↦ by
      rw [orbitNormFactors_map, List.mem_map] at hw
      obtain ⟨j, -, rfl⟩ := hw
      rw [PWord.evalFin_conj]
      exact trivAct_conjR (trivAct_zW t E E₂ hwild
        (fun w ↦ mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hτ)) w) pp) _)]
    refine List.sum_eq_zero fun y hy ↦ ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    rw [orbitNormFactors_map, List.mem_map] at hw
    obtain ⟨j, -, rfl⟩ := hw
    rw [foxD_conj, hz, foxD_zpow_eq_zero t E E₂ a (hsig (s' : ℤ)) ((j : ℤ) + 1)]
    simp
  rw [e2W, MCompact.foxD_prodList_pair, hhead, foxD_conj, hnorm, hsig ((s' * mm : ℕ) : ℤ)]
  simp

/-! ### The two assembled copies -/

/-- **The hat copy's unramified Fox row vanishes at `σ`-free offsets** — at every
`(α, r, p, η, h)`.

Both mechanisms of `foxD_mpcHatW_ram` are still here, but they act on *one* entry rather than
two: `Â` and `B̂` both differentiate to `a(τ)`, so `Â²` doubles it away and `[Â,B̂]`'s four
`foxD_comm_general` terms cancel in pairs; `Ĉ₀^{2^α}` and `[Ĉ₀,D]` are `σ`-only; and `Ê₀₁` is
`foxD_e01W_unram`.  Unlike the ramified proof this needs no balance at all — `α ≥ 1` is not used
— because every prefix weight is *trivial*, not merely a power of `S₂`. -/
theorem foxD_mpcHatW_unram (α r pp : ℕ) (η : EtaDisplay) :
    foxD ⇑t a E E₂ (mpcHatW α r pp η h) = 0 := by
  have hTodd : ∀ w : V, powOmega2 t.τ • w = w := fun w ↦
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hτ)) w
  have hAtriv : PWord.evalFin ⇑t E E₂ (aHatW h (s r) (m α)) ∈ trivAct C V :=
    mem_trivAct.mpr fun w ↦
      (evalFin_aHatW_act t E E₂ hwild hTodd _ _ w).trans (smul_zpow_powOmega2 hS₂ _ w)
  have hBtriv : PWord.evalFin ⇑t E E₂ (bHatW h pp) ∈ trivAct C V :=
    mem_trivAct.mpr fun w ↦
      (evalFin_bHatW_act t E E₂ hwild hTodd pp w).trans (smul_zpow_powOmega2 hS₂ _ w)
  have hC0triv : PWord.evalFin ⇑t E E₂ (c0HatW h (s r)) ∈ trivAct C V := by
    refine mem_trivAct.mpr fun w ↦ ?_
    rw [evalFin_c0HatW_eq, smul_zpow_powOmega2 hS₂]
  have hf1 : foxD ⇑t a E E₂ (.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, one_smul, zero_add, mem_trivAct.mp hAtriv,
      foxD_aHatW_unram t E E₂ a hσ hV₂ hwild hτ, hV₂]
  have hf2 : foxD ⇑t a E E₂ (.comm (aHatW h (s r) (m α)) (bHatW h pp)) = 0 :=
    foxD_comm_of_trivial _ _ _ _ hAtriv hBtriv
  have hf3 : foxD ⇑t a E E₂ (.zpow (c0HatW h (s r)) ((2 ^ α : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [foxD_c0HatW_of_sigma_free t E E₂ a hσ, smul_zero]
  have hf4 : foxD ⇑t a E E₂ (.comm (c0HatW h (s r)) (η.toPWord (n := 2 + 2 * h))) = 0 := by
    rw [foxD_comm_general, foxD_c0HatW_of_sigma_free t E E₂ a hσ,
      foxD_etaDisplay_of_sigma_free t E E₂ a hσ]
    simp
  rw [mpcHatW, hatFactors, foxD_prodList_of_trivial _ _ _ _ _ (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · rw [PWord.evalFin_zpow]; exact zpow_mem hAtriv _
    · rw [PWord.evalFin_comm]; exact trivAct_commR hAtriv hBtriv
    · rw [PWord.evalFin_zpow]; exact zpow_mem hC0triv _
    · rw [PWord.evalFin_comm]; exact Certificates.Npc.trivAct_commR_left hC0triv _
    · exact trivAct_e01W t E E₂ hwild hTodd _ _)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hf1, hf2, hf3, hf4,
    foxD_e01W_unram t E E₂ a hσ hV₂ hwild hτ hS₂, add_zero]

/-- **The linear copy's unramified Fox row at `σ`-free offsets**:

```
D(R_lin^pc) = a(τ) + (1 − G⁻¹)·a(x₂),        G = the value of `D = σ^{η̂}`.
```

`A²`, `[A,B]`, `C₀^{2^α}` and `E₀₁^pc` are all silent — the first and third because `α ≥ 1`
makes their exponents even, the second because both entries act trivially, the fourth by
`foxD_e01W_unram` — so only the `η̂`-commutator and the orbit-norm head survive, and they supply
the two entries.

⚠ `E₂^pc` is again first-order **essential** (it *is* the `a(τ)`-entry) and `E₀₁^pc` again
first-order redundant, exactly as freeze row 5 records for the ramified reading. -/
theorem foxD_mpcLinW_unram {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    foxD ⇑t a E E₂ (mpcLinW α r pp η h)
      = a .tau + (a (coreLetter h 2)
          - (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)))⁻¹ • a (coreLetter h 2)) := by
  have hTodd : ∀ w : V, powOmega2 t.τ • w = w := fun w ↦
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hτ)) w
  have hAtriv : PWord.evalFin ⇑t E E₂ (aW h (s r) (m α)) ∈ trivAct C V :=
    trivAct_of_actsAsPow hS₂ (actsAsPow_aW t E E₂ hwild _ _)
  have hBtriv : PWord.evalFin ⇑t E E₂ (bW h pp) ∈ trivAct C V :=
    trivAct_of_actsAsPow hS₂ (actsAsPow_bW t E E₂ hwild pp)
  have hC0triv : PWord.evalFin ⇑t E E₂ (c0W h (s r)) ∈ trivAct C V :=
    trivAct_of_actsAsPow hS₂ (actsAsPow_c0W t E E₂ hwild (s r))
  have hC0 : foxD ⇑t a E E₂ (c0W h (s r)) = a (coreLetter h 2) := by
    rw [c0W, MCompact.foxD_prodList_pair,
      show foxD ⇑t a E E₂ (PWord.gen (coreLetter h 2)) = a (coreLetter h 2) from rfl,
      foxD_sigma2Pow_of_sigma_free t E E₂ a hσ, smul_zero, add_zero]
  -- factor 1: `A²` doubles away
  have hf1 : foxD ⇑t a E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, one_smul, zero_add, mem_trivAct.mp hAtriv, hV₂]
  -- factor 2: both entries act trivially
  have hf2 : foxD ⇑t a E E₂ (.comm (aW h (s r) (m α)) (bW h pp)) = 0 :=
    foxD_comm_of_trivial _ _ _ _ hAtriv hBtriv
  -- factor 3: `2^α` is even
  have hf3 : foxD ⇑t a E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.range (2 ^ α)) ↦ by
        rw [hC0, mem_trivAct.mp (pow_mem hC0triv i)],
      Finset.sum_const, Finset.card_range, two_pow_eq_two_mul_m hα, mul_comm, mul_nsmul,
      two_nsmul, hV₂]
  -- factor 4: the `η̂` commutator, the only entry with an operator in front
  have hf4 : foxD ⇑t a E E₂ (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))
      = -(a (coreLetter h 2)
          - (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)))⁻¹ • a (coreLetter h 2)) := by
    rw [foxD_comm_general, hC0, foxD_etaDisplay_of_sigma_free t E E₂ a hσ, smul_zero, smul_zero,
      mem_trivAct.mp (inv_mem hC0triv), mul_smul, mem_trivAct.mp (inv_mem hC0triv)]
    abel
  rw [mpcLinW, linFactors, foxD_prodList_of_trivial _ _ _ _ _ (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [PWord.evalFin_zpow]; exact zpow_mem hAtriv _
    · rw [PWord.evalFin_comm]; exact trivAct_commR hAtriv hBtriv
    · rw [PWord.evalFin_zpow]; exact zpow_mem hC0triv _
    · rw [PWord.evalFin_comm]; exact Certificates.Npc.trivAct_commR_left hC0triv _
    · exact trivAct_e01W t E E₂ hwild hTodd _ _
    · exact trivAct_e2W t E E₂ hwild hTodd _ _ _)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hf1, hf2, hf3, hf4,
    foxD_e01W_unram t E E₂ a hσ hV₂ hwild hτ hS₂,
    foxD_e2W_unram t E E₂ a hσ hV₂ hwild hτ hS₂, zero_add, add_zero]
  rw [Certificates.neg_eq_self hV₂]
  abel

end Factors

end Rows

end

end GQ2.Dyadic.MProcyclicUnram
