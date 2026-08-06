/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcActionImageDevissage
import GQ2.Dyadic.Instances.N0M0CompactBranches
import GQ2.Dyadic.Instances.NpcUnramifiedProcyclic

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

## What else is in this file

The row makes the whole first-order half of the branch available, so the rest of the file spends
it:

* the even unramified Stokes route generalized from the compact pivot `σ⁻¹` to an arbitrary
  fixed-point-free `u` (`evenUnramifiedStokesDuality_of_smul_row` and its three helpers), the
  unramified twin of `MpcActionImageDevissage`'s `SmulPivot` section;
* the family's complete differential, in both `sigma` classes
  (`heisD1_mpcFamOf_unramified_apply`, `heisD1_mpcFamOf_tauRow_of_split`);
* the branch itself, `unramifiedActionImageStokes_of_scalar`, over three named residues — one
  arithmetic and two second-order — and the four-residue `uniformPushedHsimp_of_residues`.

The arithmetic residue `DisplayFixedPointFree` is **discharged** for every display that
represents a field unit, i.e. for everything `SelectedEta.MpcDisplayFor` can produce
(`displayFixedPointFree_of_representsUnit`).  The two second-order residues,
`UnramifiedNormalPairingIsCompact` (generic sub-branch) and `ScalarActionImageStokes` (scalar
sub-branch), are the honest remainder; the scalar one's *first*-order half is discharged here
too, so what it still needs is exactly the scalar second-order row of `mpcW`, the analogue of
`NpcScalarRow`.
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

`A²`, `[A,B]`, `C₀^{2^α}` and `E₀₁^pc` are all silent — the first because its exponent is `2`,
the third because `α ≥ 1` makes `2^α` even, the second because both entries act trivially, the
fourth by `foxD_e01W_unram` — so only the `η̂`-commutator and the orbit-norm head survive, and
they supply the two entries.  `α ≥ 1` is used **here and nowhere else** on either copy.

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

/-! ### The headline row -/

set_option maxHeartbeats 800000 in
/-- **The corrected procyclic-`M` word's unramified Fox row**, at every `(α ≥ 1, r, p, η, h)` and
at **every** offset vector:

```
D(R_{M,pc})(a) = a(τ) + (1 − G⁻¹)·a(x₂),        G = the value of the display `D = σ^{η̂}`.
```

Two entries, in the `τ`- and `x₂`-columns: the **compact** shape
(`MCompact.foxD_mCompact_unram_simple` is the case `G = σ`), and *not* the three-entry
procyclic-`N` shape `(A⁻¹ − 1)a(x₀) + a(τ) + (1 − B⁻¹)a(x₂)` of
`Certificates.Npc.foxD_npc_unram`.  Every trace of `α`, `r` and `p` is gone: the balance
`s·2^α = 2·sm` is not even consulted, because on an `S₂`-trivial coefficient each of the two
blocks it balances is *separately* silent.

Three mechanisms, kept visible:

* the three trailing blocks are dead for the same reason as in the ramified row
  (`foxD_mpcW_eq_mpcProductW`, which carries no `τ`-class hypothesis at all);
* the hat copy's `σ`-free row is `0` (`foxD_mpcHatW_unram`), so it contributes nothing;
* the `σ`-column dies by WMP-b's coincidence lemma, reused verbatim at the unramified
  `δ`-supply.  As in the ramified branch, no `σ`-freeness of the offsets is *assumed*. -/
theorem foxD_mpcW_unram {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (hS₂ : ∀ w : V, powOmega2 t.σ • w = w) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = a .tau + (a (coreLetter h 2)
          - (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)))⁻¹ • a (coreLetter h 2)) := by
  have hTodd : ∀ w : V, powOmega2 t.τ • w = w := fun w ↦
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hτ)) w
  have hcol := congrArg (fun f : V →+ V ↦ f (a Generator.sigma))
    (foxColumn_sigma_mul_eq_zero t E E₂ α r pp η hV₂
      (trivAct_mpcLinW t E E₂ hα r pp η hwild hTodd) hwild
      (fun i ↦ trivAct_dW_unram t E E₂ hwild hτ i)
      (fun v i ↦ foxD_dW_sigma_single_unram t E E₂ hV₂ hwild hτ v i))
  simp only [foxColumn_apply, AddMonoidHom.zero_apply] at hcol
  rw [MProcyclicExact.foxD_mpcW_eq_mpcProductW t E E₂ a α r pp η hwild hTodd hV₂]
  conv_lhs => rw [← pi_single_add_sigmaKill a]
  rw [foxD_add, hcol, zero_add, foxD_mul,
    foxD_mpcHatW_unram t E E₂ (sigmaKill a) (sigmaKill_sigma a) hV₂ hwild hτ hS₂ α r pp η,
    smul_zero, add_zero,
    foxD_mpcLinW_unram t E E₂ (sigmaKill a) (sigmaKill_sigma a) hV₂ hwild hτ hS₂ hα r pp η,
    sigmaKill_of_ne a (by simp : (Generator.tau : Generator (2 + 2 * h)) ≠ Generator.sigma),
    sigmaKill_of_ne a (coreLetter_ne_sigma h 2)]

/-- The headline row in the shape a `heisD1` computation consumes: the `η̂`-display's value named
as a single group element `u`. -/
theorem foxD_mpcW_unram_of_eq {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {u : C}
    (hu : PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)) = u)
    (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (hS₂ : ∀ w : V, powOmega2 t.σ • w = w) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = a .tau + (a (coreLetter h 2) - u⁻¹ • a (coreLetter h 2)) := by
  rw [foxD_mpcW_unram t E E₂ a hα r pp η hV₂ hwild hτ hS₂, hu]

end Rows

/-! ## The even unramified route at a `u`-scaled boundary pivot

`N0M0UnramifiedStokes` runs the whole first-order half of the unramified even route — surjectivity
of the differential, the unique normal representative, and Stokes duality from the core pairing
formula — but it states its lemmas at the *compact* boundary operator `σ⁻¹` literally.  The
procyclic-`M` row's operator is `G⁻¹`, the inverse of whatever the `η̂`-display evaluates to: the
same shape with a different unit, so the arguments go through verbatim once the pivot is written
`1 − u⁻¹` for an arbitrary fixed-point-free group element `u`.

⚠ These four are **generalizations of `GQ2.Dyadic.{heisD1_surjective_of_unramified_row,
heisD1_evenNormal_eq_zero_of_unramified_row, evenNormalForm_of_unramified_row,
evenUnramifiedStokesDuality_of_row}`**, not new mathematics, and they are here rather than there
only because `N0M0UnramifiedStokes.lean` is not this ticket's file.  The compact case is `u = σ`,
so a hoist would let that file delete its four copies and keep them as specializations — exactly
as `MpcActionImageDevissage`'s `SmulPivot` section stands to `M0RamifiedStokes`.
-/

section UnramSmulPivot

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

omit [Finite A] in
/-- If `u` has no nonzero fixed vector then neither does `u⁻¹`. -/
theorem inv_fixedPointFree {u : C} (hufpf : ∀ a : A, u • a = a → a = 0) :
    ∀ a : A, u⁻¹ • a = a → a = 0 := fun a ha ↦
  hufpf a (by conv_lhs => rw [← ha]
              rw [smul_inv_smul])

/-- The `x₂`-column `1 − u⁻¹` is a pivot as soon as `u` is fixed-point free. -/
theorem oneSubInv_surjective_of_fixedPointFree {u : C}
    (hufpf : ∀ a : A, u • a = a → a = 0) : Function.Surjective (fun v : A ↦ v - u⁻¹ • v) := by
  have hs : Function.Surjective (fun v : A ↦ u⁻¹ • v - v) :=
    surjective_smul_sub_of_fixedPointFree (inv_fixedPointFree hufpf)
  intro b
  obtain ⟨v, hv⟩ := hs (-b)
  refine ⟨v, ?_⟩
  change v - u⁻¹ • v = b
  change u⁻¹ • v - v = -b at hv
  rw [← neg_sub, hv, neg_neg]

/-- Surjectivity of a differential with a `u`-scaled unramified boundary pivot. -/
theorem heisD1_surjective_of_unram_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (hufpf : ∀ a : A, u • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro r
  obtain ⟨v, hv⟩ := oneSubInv_surjective_of_fixedPointFree hufpf (r 1 - t.σ • r 0)
  let x : Generator (2 + 2 * h) → A := fun g ↦
    if g = .tau then t.σ • r 0 else if g = coreLetter h 2 then v else 0
  have hτx2 : (.tau : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.tau_ne_coreLetter_two h
  have hxτ : x .tau = t.σ • r 0 := by simp [x]
  have hxx2 : x (coreLetter h 2) = v := by simp [x, hτx2.symm]
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  fin_cases k
  · change t.σ⁻¹ • x .tau = r 0
    rw [hxτ, inv_smul_smul]
  · change x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2)) = r 1
    rw [hxτ, hxx2]
    change v - u⁻¹ • v = r 1 - t.σ • r 0 at hv
    rw [hv]
    abel

omit [Finite A] in
/-- Every normal cochain is a cocycle for a `u`-scaled unramified row. -/
theorem heisD1_evenNormal_eq_zero_of_unram_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (evenNormal h d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k <;> simp

set_option maxHeartbeats 1600000 in
/-- The unramified normal form at a `u`-scaled boundary pivot: the tame row kills `tau`, the
`u`-pivot kills `x₂` because `u` is fixed-point free, and a coboundary kills `sigma`. -/
theorem evenNormalForm_of_unram_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hufpf : ∀ a : A, u • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hSsurj : Function.Surjective (fun v : A ↦ t.σ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hσfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
  rw [hrow x] at hx
  have hxτ : x .tau = 0 := by
    have hz : t.σ⁻¹ • x .tau = 0 := by simpa using congrFun hx 0
    rw [← smul_inv_smul t.σ (x .tau), hz, smul_zero]
  have hxcore2 : x (coreLetter h 2) = 0 := by
    have hz : x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2)) = 0 := by
      simpa using congrFun hx 1
    rw [hxτ, zero_add, sub_eq_zero] at hz
    exact inv_fixedPointFree hufpf _ hz.symm
  obtain ⟨v, hv⟩ := hSsurj (x .sigma)
  let x' := x - heisD0 (⇑t) v
  have hx'σ : x' .sigma = 0 := by simp [x', heisD0_apply, hv]
  have hx'τ : x' .tau = 0 := by simp [x', heisD0_apply, hτ, hxτ]
  have hx'core2 : x' (coreLetter h 2) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore2]
  let z := (EvenCore.coreHandleAddEquiv h A x).2
  let p₀ : A × A × (Fin h × Fin 2 → A) := (x (coreLetter h 0), x (coreLetter h 1), z)
  have hnormal : evenNormal h p₀.1 p₀.2.1 p₀.2.2 = x' := by
    apply (EvenCore.coreHandleAddEquiv h A).injective
    apply Prod.ext
    · funext g
      cases g with
      | sigma => simpa [p₀] using hx'σ.symm
      | tau => simpa [p₀] using hx'τ.symm
      | wild i =>
          fin_cases i
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · simpa [p₀] using hx'core2.symm
    · funext jk
      rcases jk with ⟨j, k⟩
      fin_cases k
      · simp [p₀, z, x', heisD0_apply, hhandleUTriv]
      · simp [p₀, z, x', heisD0_apply, hhandleVTriv]
  refine ⟨p₀, ?_, ?_⟩
  · refine ⟨v, ?_⟩
    rw [hnormal]
    simp [x']
  · intro p hp
    obtain ⟨_, hu⟩ := hp
    apply Prod.ext
    · have hc := congrFun hu (coreLetter h 0)
      rw [heisD0_apply, hcoreTriv, sub_self] at hc
      simp only [Pi.sub_apply, evenNormal_coreLetter, Matrix.cons_val_zero] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · apply Prod.ext
      · have hc := congrFun hu (coreLetter h 1)
        rw [heisD0_apply, hcoreTriv, sub_self] at hc
        simp only [Pi.sub_apply, evenNormal_coreLetter, Matrix.cons_val_one,
          Matrix.cons_val_zero] at hc
        exact (sub_eq_zero.mp hc.symm).symm
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k
        · have hc := congrFun hu (handleU j)
          rw [heisD0_apply, hhandleUTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenNormal_handleU] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj
        · have hc := congrFun hu (handleV j)
          rw [heisD0_apply, hhandleVTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenNormal_handleV] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj

set_option maxHeartbeats 3200000 in
/-- **Stokes duality for an even unramified complex with a `u`-scaled boundary pivot.**  The word
enters only through its first Fox row and the core pairing formula. -/
theorem evenUnramifiedStokesDuality_of_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (hrowD : ∀ y : Generator (2 + 2 * h) → ElemDual A, heisD1 ⇑t w y
      = ![t.σ⁻¹ • y .tau,
          y .tau + (y (coreLetter h 2) - u⁻¹ • y (coreLetter h 2))])
    (hpairA : ∀ (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (lam₀ lam₁ : ElemDual A)
      (mu : Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t w (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
        = lam₀ (d₀ + d₁) + lam₁ d₀ + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hufpf : ∀ a : A, u • a = a → a = 0) :
    StokesDuality ⇑t w A := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτD : ∀ lam : ElemDual A, t.τ • lam = lam := fun lam ↦ elemDual_smul_eq_self hτ lam
  have hσfpfD : ∀ lam : ElemDual A, t.σ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hσfpf lam hlam
  have hufpfD : ∀ lam : ElemDual A, u • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hufpf lam hlam
  exact evenNormalStokesDuality t w hA₂ hr hend
    (heisD0_injective_of_sigma_fixedPointFree t hσfpf)
    (heisD0_injective_of_sigma_fixedPointFree (A := ElemDual A) t hσfpfD)
    (heisD1_surjective_of_unram_smul_row t w u hrowA hufpf)
    (heisD1_surjective_of_unram_smul_row (A := ElemDual A) t w u hrowD hufpfD)
    (fun p ↦ heisD1_evenNormal_eq_zero_of_unram_smul_row t w u hrowA p.1 p.2.1 p.2.2)
    (fun r ↦ heisD1_evenNormal_eq_zero_of_unram_smul_row (A := ElemDual A) t w u hrowD
      r.1 r.2.1 r.2.2)
    (evenNormalForm_of_unram_smul_row t w u hrowA hwild hτ hσfpf hufpf)
    (evenNormalForm_of_unram_smul_row (A := ElemDual A) t w u hrowD hwildD hτD hσfpfD hufpfD)
    (evenNormal_pairing_separates_left_of_formula t w hA₂ hpairA)

end UnramSmulPivot

/-! ## The complete unramified differential of the procyclic-`M` family -/

section Differential

set_option maxHeartbeats 800000 in
/-- **The complete first differential of the procyclic-`M` family on an unramified simple
module**: the `σ⁻¹`-pivot on `τ`, and the two-entry wild row `a(τ) + (1 − G⁻¹)a(x₂)`.  Exactly
the compact rows' differential with `σ⁻¹` replaced by `G⁻¹`
(`heisD1_mCompactFam_unramified_apply` is the case `u = σ`). -/
theorem heisD1_mpcFamOf_unramified_apply {alpha r pp h q : ℕ} {η : EtaDisplay}
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {u : C}
    (hlift : ResolverLifts E (WordLift A C)) (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha)
    (hq : Even q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hu : PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)) = u)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (mpcFamOf alpha r pp h q η E E₂) x
      = ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))] := by
  funext k
  fin_cases k
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (Certificates.tameRelW (2 + 2 * h) q))).a = t.σ⁻¹ • x .tau
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hlift,
      Certificates.foxD_tameRelW_unram t _ _ hA₂ hτ hq]
  · change (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ (mpcW alpha r pp η h))).a
      = x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hlift,
      foxD_mpcW_unram_of_eq t E E₂ x hα r pp hu hA₂ hwild hτ hS₂]

set_option maxHeartbeats 800000 in
/-- **The `tau`-row of the procyclic-`M` family at a completely trivial action.**  Both rows
degenerate to the single `tau` entry: the tame row through the `σ⁻¹`-pivot, the wild row because
the boundary operator `G` is a `σ`-power and `1 − G⁻¹ = 0`.  This is the procyclic-`M` twin of
`NProcyclicUnram.heisD1_npcFam_tauRow_of_split`. -/
theorem heisD1_mpcFamOf_tauRow_of_split {alpha r pp h q : ℕ} {η : EtaDisplay}
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hlift : ResolverLifts E (WordLift A C)) (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha)
    (hq : Even q)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (mpcFamOf alpha r pp h q η E E₂) x = ![x .tau, x .tau] := by
  have hτ : ∀ a : A, t.τ • a = a := fun a ↦ htriv _ a
  have hσ : ∀ a : A, t.σ • a = a := fun a ↦ htriv _ a
  have hσinv : ∀ a : A, t.σ⁻¹ • a = a := fun a ↦
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr hσ)) a
  have hS₂ : ∀ a : A, powOmega2 t.σ • a = a := fun a ↦
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hσ)) a
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a := fun i a ↦ htriv _ a
  obtain ⟨n, hn⟩ := exists_zpow_evalFin_etaDisplay t E E₂ η
  have hutriv : ∀ a : A, (t.σ ^ n)⁻¹ • a = a := fun a ↦
    mem_trivAct.mp (inv_mem (zpow_mem (mem_trivAct.mpr hσ) n)) a
  rw [heisD1_mpcFamOf_unramified_apply (alpha := alpha) (r := r) (pp := pp) t E E₂ hlift hA₂ hα
    hq hwild hτ hS₂ hn x]
  funext k
  fin_cases k
  · exact hσinv _
  · change x .tau + (x (coreLetter h 2) - (t.σ ^ n)⁻¹ • x (coreLetter h 2)) = x .tau
    rw [hutriv, sub_self, add_zero]

end Differential

end

end GQ2.Dyadic.MProcyclicUnram

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.MProcyclicUnram

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The two residual inputs of the procyclic-`M` unramified branch

The first-order half of the branch is complete: the row is two-entry, the differential is the
`u`-pivot one, the ends are acyclic on the `sigma`-ramified sub-branch and the normal
coordinates are the compact rows' `A × A × (Fin h × Fin 2 → A)`.  What is left is exactly two
statements, and they are of two different kinds.
-/

/-- **The arithmetic residue.**  On an unramified simple coefficient with `sigma` fixed-point
free, the `η̂`-display's value is fixed-point free too.

This is *not* a formality, and it is where the procyclic-`M` row differs from its procyclic-`N`
twin.  The `N` row's conjugator is `σ^{η̂}` for a genuine `EtaData`, and
`RowActionImage.actionImage_unramified_sigma_etaPow` proves it **equals** `σ` on an unramified
target (odd order kills the whole `η̂`-datum).  The `M` row carries an `EtaDisplay` instead, whose
third constructor is a *literal* power `σ^k`, and `σ^k` need not be fixed-point free even for odd
`k`: at `orderOf σ = 3` and `k = 3` the display evaluates to `1` and the row's `x₂`-column
vanishes identically.  So the condition is a real hypothesis on the display, discharged below for
the bare-`σ` display (`displayFixedPointFree_one`) — which is the `η = 1` row carrying
`ℚ₂(√−10)`, `ℚ₂(√10)` and the one-handle instance. -/
def DisplayFixedPointFree (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .tau • m = m) →
    (∀ m : M, (actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M).σ • m = m → m = 0) →
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
      resolvedFamily alpha r pp h q d
          (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M))
          = mpcFamOf alpha r pp h q d E E₂
        ∧ ResolverLifts E
            (WordLift M (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M))
        ∧ ResolverLifts E
            (WordLift (ElemDual M) (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M))
        ∧ ∀ m : M,
            PWord.evalFin (actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M) E E₂
              (d.toPWord (n := 2 + 2 * h)) • m = m → m = 0

/-- **The second-order residue of the generic unramified sub-branch.**  The traced pairing of the
procyclic-`M` family at the uniform level is the compact core Gram `((1,1),(1,0))` plus the `h`
standard hyperbolic handle planes, on the even normal coordinates.

This is the exact analogue of `heisEta1_mCompactFam_normal`, and — because the row is the compact
row — the *same* Gram matrix, not the `Φ`-twisted one the procyclic-`N` branch needs. -/
def UnramifiedNormalPairingIsCompact (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .tau • m = m) →
    ∀ (d₀ d₁ : M) (z : Fin h × Fin 2 → M) (lam₀ lam₁ : ElemDual M)
      (mu : Fin h × Fin 2 → ElemDual M),
      heisEta1 (actionImageGenerators (2 + 2 * h) q (mpcW alpha r pp d h) M)
          (resolvedFamily alpha r pp h q d
            (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M)))
          (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
        = lam₀ (d₀ + d₁) + lam₁ d₀ + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0)))

/-- **The residual scalar sub-branch.**  `sigma` acts trivially, hence — the unramified action
image being procyclic — every generator does, the ends of the complex carry cohomology and the
`sigma`-coordinate of a normal cochain is free.  The exact analogue of
`NProcyclic.ScalarActionImageStokes`. -/
def ScalarActionImageStokes (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .tau • m = m) →
    (∀ m : M, (actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M).σ • m = m) →
      StokesDuality (actionImageGenerators (2 + 2 * h) q (mpcW alpha r pp d h) M)
        (resolvedFamily alpha r pp h q d
          (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M))) M

/-- **The bare-`σ` display is fixed-point free wherever `sigma` is**: its value is `σ` on the
nose, at every marking and every resolver.  This is the `η = 1` row, i.e. `ℚ₂(√−10)`, `ℚ₂(√10)`
and the one-handle instance. -/
theorem displayFixedPointFree_one {alpha r pp h q : ℕ} :
    DisplayFixedPointFree alpha r pp h q .one := by
  intro M _ _ _ _ _ _ hM₂ _ _ hσfpf
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
    resolverLifts_uniformWordLift_ramified hM₂, resolverLifts_uniformWordLift_ramified hM₂D,
    fun m hm ↦ hσfpf m hm⟩

set_option maxHeartbeats 800000 in
/-- **The genuine `η̂` display is fixed-point free wherever `sigma` is** — and for the same reason
the procyclic-`N` row's conjugator is: at its own resolver the display's value is `σ` itself,
because `η̂` has odd components and the unramified action image has odd order
(`RowActionImage.actionImage_unramified_sigma_etaPow`).  This is the `η = −1/3` instance.

⚠ The third constructor `.lit k` is **not** free at an arbitrary `k`: its value is the literal
`σ^k`, and `σ^k = 1` as soon as `orderOf σ ∣ k` — which the branch's own hypotheses do not
forbid, since the tame relation is vacuous at `tau = 1` and leaves `orderOf σ` unconstrained
beyond being odd.  At such a marking the row's `x₂`-column would be identically zero while
`sigma` acts nontrivially, so the complex would be neither the generic one nor the scalar one.
What rescues it is not the branch but the *seam*: a literal exponent is only a representative,
and `RepresentsUnit` pins it — see `displayFixedPointFree_lit`. -/
theorem displayFixedPointFree_hat {alpha r pp h q : ℕ} (num den : ℤ) :
    DisplayFixedPointFree alpha r pp h q (.hat num den) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ hσfpf
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  set C₀ := ActionImage (2 + 2 * h) q (mpcW alpha r pp (.hat num den) h) M with hC₀
  set t := actionImageMarking (2 + 2 * h) q (mpcW alpha r pp (.hat num den) h) M with htdef
  refine ⟨_, _, rfl, NProcyclic.resolverLifts_npcResolver_wordLift hM₂ ⟨num, den⟩,
    NProcyclic.resolverLifts_npcResolver_wordLift hM₂D ⟨num, den⟩, fun m hm ↦ hσfpf m ?_⟩
  rwa [show (EtaDisplay.hat num den).toPWord (n := 2 + 2 * h)
        = .profPow (.gen Generator.sigma) ((⟨num, den⟩ : EtaData).toZhat) from rfl,
    PWord.evalFin_profPow_of_ne _ _ _ _ (Words.Npc.toZhat_ne_omega2 ⟨num, den⟩),
    PWord.evalFin_gen, Marking.apply_sigma,
    RowActionImage.actionImage_unramified_sigma_etaPow hM₂ hsimple hτ ⟨num, den⟩
      (fourMulExponent_ne_zero_and_even C₀).1
      ((Monoid.order_dvd_exponent t.σ).trans ⟨4, by ring⟩)] at hm

set_option maxHeartbeats 800000 in
/-- **A literal display that represents a `2`-adic unit is fixed-point free** — and, it turns
out, its value is `σ` itself.  `RepresentsUnit` says `Zhat.ofInt k = etaHatZ η`, the unramified
action image has odd order (`actionImage_unramified_orderOf_sigma_odd`), and `η̂` fixes every
element of odd order (`zpowHat_etaHatZ_of_odd`), so `σ^k = σ ^ᶻ Zhat.ofInt k = σ ^ᶻ η̂ = σ`.

This is what closes the `.lit` gap flagged on `displayFixedPointFree_hat`: the literal exponent
is only ever a *representative*, and the seam's `RepresentsUnit` obligation is exactly the
statement that it represents the branch's field unit. -/
theorem displayFixedPointFree_lit {alpha r pp h q : ℕ} {k : ℤ} {eta : ℤ_[2]ˣ}
    (hd : (EtaDisplay.lit k).RepresentsUnit eta) :
    DisplayFixedPointFree alpha r pp h q (.lit k) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ hσfpf
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hodd : Odd (orderOf (actionImageMarking (2 + 2 * h) q (mpcW alpha r pp (.lit k) h) M).σ) :=
    RowActionImage.actionImage_unramified_orderOf_sigma_odd hM₂ hsimple hτ
  refine ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
    resolverLifts_uniformWordLift_ramified hM₂, resolverLifts_uniformWordLift_ramified hM₂D,
    fun m hm ↦ hσfpf m ?_⟩
  rwa [show (EtaDisplay.lit k).toPWord (n := 2 + 2 * h) = .zpow (.gen Generator.sigma) k from rfl,
    PWord.evalFin_zpow, PWord.evalFin_gen, Marking.apply_sigma, ← zpowHat_ofInt,
    show Zhat.ofInt k = etaHatZ (eta : ℤ_[2]) from hd, zpowHat_etaHatZ_of_odd hodd] at hm

/-- **The arithmetic residue is discharged for every display that represents a field unit** — so
for every display the campaign's selection seam can produce (`MpcDisplayFor` carries exactly a
`RepresentsUnit` obligation, and its two constructors `one` and `ofNpc` produce `.one` and
`.hat`).

The three constructors close by three different routes, and only the middle one is free:

* `.one` — the value is `σ` syntactically, at every marking and resolver;
* `.lit k` — the value is `σ^k`, and `RepresentsUnit` plus odd order collapses it to `σ`;
* `.hat num den` — the value is the resolver's reading of `σ^{η̂}`, and
  `actionImage_unramified_sigma_etaPow` collapses it to `σ`.

So on the selected row the procyclic-`M` unramified branch needs **no** condition on `η` beyond
the one the seam already carries.  Compare the procyclic-`N` row, whose *scalar* sub-branch needs
the genuinely stronger `d.toPadic = 1 + 2z`
(`NpcDisplayFor.exists_toPadic_eq_one_add_two_mul`) because its scalar Gram matrix sees `η` only
through the parity of `1 + padicOmega2Exp(η − 1, N)`. -/
theorem displayFixedPointFree_of_representsUnit {alpha r pp h q : ℕ} {d : EtaDisplay}
    {eta : ℤ_[2]ˣ} (hd : d.RepresentsUnit eta) : DisplayFixedPointFree alpha r pp h q d := by
  cases d with
  | one => exact displayFixedPointFree_one
  | lit k => exact displayFixedPointFree_lit hd
  | hat num den => exact displayFixedPointFree_hat num den

set_option maxHeartbeats 3200000 in
/-- **The generic unramified sub-branch of the corrected procyclic-`M` row.**  On a simple
`tau`-unramified coefficient with `sigma` fixed-point free, the row is the compact two-entry row
with the boundary operator `G⁻¹`, so the ends are acyclic, the middle is freely parametrised by
the untwisted even normal coordinates, and the pairing separates them by
`UnramifiedNormalPairingIsCompact`.

Contrast `NProcyclicUnram.stokesDuality_actionImage_generic`, which has to route through the
solution operator `Φ = (1 − B⁻¹)⁻¹(1 − A⁻¹)` and the `Φ`-normal coordinates: the procyclic-`M`
row has no `x₀`-entry, so there is nothing to solve for. -/
theorem stokesDuality_actionImage_generic {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hfpf : DisplayFixedPointFree alpha r pp h q d)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q d)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M)
    (hτ : ∀ m : M, gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .tau • m = m)
    (hσfpf : ∀ m : M,
      (actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M).σ • m = m → m = 0) :
    StokesDuality (actionImageGenerators (2 + 2 * h) q (mpcW alpha r pp d h) M)
      (resolvedFamily alpha r pp h q d
        (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M))) M := by
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  obtain ⟨E, E₂, hfam, hliftM, hliftD, hufpf⟩ := hfpf M hM₂ hsimple hτ hσfpf
  have hpair' := hpair M hM₂ hsimple hτ
  set C₀ := ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M with hC₀
  set t := actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M with htdef
  have hlv := levelResolver (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) d hα hqe
  have hres₀ : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C₀)) (HeisLift M C₀) := hlv.heis hM₂
  have hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C₀)) :=
    hlv.endpoint _ (fourMulExponent_ne_zero_and_even C₀).1
      (fourMulExponent_ne_zero_and_even C₀).2
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C₀)) (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hres₀.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C₀) k) = 1 := fun k ↦
    lower_rel (A := M) (actionImageHom (2 + 2 * h) q (mpcW alpha r pp d h) M) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hresWord k
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := fun m ↦ hτ m
  have hS₂ : ∀ m : M, powOmega2 t.σ • m = m :=
    actionImage_sigma_powOmega2_smul_trivial hM₂ hsimple hτ
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual M), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτD : ∀ lam : ElemDual M, t.τ • lam = lam := fun lam ↦ elemDual_smul_eq_self hτ' lam
  have hS₂D : ∀ lam : ElemDual M, powOmega2 t.σ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hS₂ lam
  rw [hfam] at hend hr hpair'
  rw [hfam]
  exact evenUnramifiedStokesDuality_of_smul_row t _
    (PWord.evalFin ⇑t E E₂ (d.toPWord (n := 2 + 2 * h))) hM₂ hr hend
    (heisD1_mpcFamOf_unramified_apply (alpha := alpha) (r := r) (pp := pp) t E E₂ hliftM hM₂ hα
      hqe hwild hτ' hS₂ rfl)
    (heisD1_mpcFamOf_unramified_apply (A := ElemDual M) (alpha := alpha) (r := r) (pp := pp) t E
      E₂ hliftD hM₂D hα hqe hwildD hτD hS₂D rfl)
    hpair' hwild hτ' hσfpf hufpf

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`M` unramified branch, reduced to its scalar sub-branch.**  The `sigma`
dichotomy of `actionImage_sigma_split_or_fixedPointFree` splits the `tau`-unramified obligation
in two; the generic half is `stokesDuality_actionImage_generic`.

⚠ This is the procyclic-`M` twin `NProcyclic.unramifiedActionImageStokes_of_scalar` is not: that
one is `npcW`-specific, both in the word it names and in the `Φ`-normal route it takes. -/
theorem unramifiedActionImageStokes_of_scalar {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hfpf : DisplayFixedPointFree alpha r pp h q d)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q d)
    (hsc : ScalarActionImageStokes alpha r pp h q d) :
    UnramifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ
  rcases actionImage_sigma_split_or_fixedPointFree
    (n := 2 + 2 * h) (q := q) (R := mpcW alpha r pp d h) hM₂ hsimple hτ with hσ | hσfpf
  · exact hsc M hM₂ hsimple hτ hσ
  · exact stokesDuality_actionImage_generic hα hqe hfpf hpair M hM₂ hsimple hτ hσfpf

/-- **The procyclic-`M` uniform pushed residue, reduced to its four named inputs** — three
unramified, one ramified. -/
theorem uniformPushedHsimp_of_residues {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hfpf : DisplayFixedPointFree alpha r pp h q d)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q d)
    (hsc : ScalarActionImageStokes alpha r pp h q d)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_ramified_separation hα hqe
    (unramifiedActionImageStokes_of_scalar hα hqe hfpf hpair hsc) hsep

/-- **The `η = 1` row's uniform pushed residue, on three named inputs** — the arithmetic one is
discharged.  This is the display of `ℚ₂(√−10)`, `ℚ₂(√10)` and the one-handle instance, so it is
the row merge gate 9 sits on. -/
theorem uniformPushedHsimp_of_residues_one {alpha r pp h q : ℕ} (hα : 1 ≤ alpha) (hqe : Even q)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q .one)
    (hsc : ScalarActionImageStokes alpha r pp h q .one)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q .one) :
    UniformPushedHsimp alpha r pp h q .one :=
  uniformPushedHsimp_of_residues hα hqe displayFixedPointFree_one hpair hsc hsep

/-- The same for the genuine `η̂`-display row. -/
theorem uniformPushedHsimp_of_residues_hat {alpha r pp h q : ℕ} (num den : ℤ) (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q (.hat num den))
    (hsc : ScalarActionImageStokes alpha r pp h q (.hat num den))
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q (.hat num den)) :
    UniformPushedHsimp alpha r pp h q (.hat num den) :=
  uniformPushedHsimp_of_residues hα hqe (displayFixedPointFree_hat num den) hpair hsc hsep

/-- **The procyclic-`M` uniform pushed residue on the selected row, on three second-order inputs
only.**  Every display the seam can produce carries a `RepresentsUnit` obligation
(`MpcDisplayFor.represents`), and that is exactly what the arithmetic residue needs — so on the
selected row the only remaining inputs are the two unramified pairing statements and the ramified
one, all three of them second-order. -/
theorem uniformPushedHsimp_of_pairings {alpha r pp h q : ℕ} {d : EtaDisplay} {eta : ℤ_[2]ˣ}
    (hα : 1 ≤ alpha) (hqe : Even q) (hd : d.RepresentsUnit eta)
    (hpair : UnramifiedNormalPairingIsCompact alpha r pp h q d)
    (hsc : ScalarActionImageStokes alpha r pp h q d)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_residues hα hqe (displayFixedPointFree_of_representsUnit hd) hpair hsc hsep

end

end GQ2.Dyadic.MProcyclicExact

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_dW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.trivAct_dW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_dW_sigma_single_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.smul_zpow_powOmega2
#print axioms GQ2.Dyadic.MProcyclicUnram.trivAct_of_actsAsPow
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_aHatW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_bHatW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_e01W_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_e2W_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_mpcHatW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_mpcLinW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_mpcW_unram
#print axioms GQ2.Dyadic.MProcyclicUnram.foxD_mpcW_unram_of_eq
#print axioms GQ2.Dyadic.MProcyclicUnram.inv_fixedPointFree
#print axioms GQ2.Dyadic.MProcyclicUnram.oneSubInv_surjective_of_fixedPointFree
#print axioms GQ2.Dyadic.MProcyclicUnram.heisD1_surjective_of_unram_smul_row
#print axioms GQ2.Dyadic.MProcyclicUnram.heisD1_evenNormal_eq_zero_of_unram_smul_row
#print axioms GQ2.Dyadic.MProcyclicUnram.evenNormalForm_of_unram_smul_row
#print axioms GQ2.Dyadic.MProcyclicUnram.evenUnramifiedStokesDuality_of_smul_row
#print axioms GQ2.Dyadic.MProcyclicUnram.heisD1_mpcFamOf_unramified_apply
#print axioms GQ2.Dyadic.MProcyclicUnram.heisD1_mpcFamOf_tauRow_of_split
#print axioms GQ2.Dyadic.MProcyclicExact.displayFixedPointFree_one
#print axioms GQ2.Dyadic.MProcyclicExact.displayFixedPointFree_hat
#print axioms GQ2.Dyadic.MProcyclicExact.displayFixedPointFree_lit
#print axioms GQ2.Dyadic.MProcyclicExact.displayFixedPointFree_of_representsUnit
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_actionImage_generic
#print axioms GQ2.Dyadic.MProcyclicExact.unramifiedActionImageStokes_of_scalar
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_residues
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_residues_one
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_residues_hat
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_pairings

end AxiomAudit
