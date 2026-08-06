/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcActionImageDevissage
import GQ2.Dyadic.Instances.MpcExact
import GQ2.Dyadic.Instances.M0RamifiedStokes
import GQ2.Dyadic.Instances.NpcRamifiedBranch
import GQ2.Dyadic.Word.FoxProd

/-!
# Action-image devissage for the corrected procyclic-`M` row

The row-independent half of the argument is `RowActionImage`, built in
`NpcActionImageDevissage`.  This file supplies the procyclic-`M` inputs and the pushed residue
layer, exactly as its procyclic-`N` twin does.

The one structural difference is the resolver.  The `M` row's family is *display-dependent*: the
`ω₂`-only displays `.one` and `.lit k` use the constant resolver `omega2Exp N`, while a genuine
`.hat num den` display uses the two-valued `npcResolver N ⟨num, den⟩` shared with the `N` row.
`MProcyclicExact.resolvedFamily` already records that case split, and `levelResolver` below
discharges the `LevelResolver` interface one display at a time.  Nothing in the devissage sees
the split: the action-map transport theorem compares two Stokes complexes with *different* words,
so a per-display resolver is no obstacle at all.

What is left over is the same as for the `N` row, and is the honest state of both procyclic rows:
`SimpleActionImageStokes` — Stokes duality at the canonical action-image marking of a *simple*
elementary coefficient — is still an interface, not a theorem, and it splits along the
`tau`-dichotomy into an unramified obligation on a procyclic target
(`finiteActionImage_unramified_closure_sigma`) and a ramified obligation.
-/

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.SectionEight GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The whole word's ramified Fox row

`MpcStokes` §6 computes the **linear copy's** row (`foxD_mpcLinW_x2`, one entry in the
`x₂`-column) and `MpcFox` §5 shows the **hat copy's** row vanishes (`foxD_mpcHatW_ram`).  Neither
reaches `mpcW` itself, because

```
mpcW α r p η h = prodList (linFactors ++ hatFactors ++ [δ₀², [δ₀,δ₁]] ++ handleTailW h)
```

is a `prodList` over a four-block **append**, and `prodList` does not split syntactically over
`++` — the reason `Words/Mpc.lean` states its own factorization `eval_mpcW_factored` at the
*value* level only.  `Word/FoxProd.lean`'s `foxD_prodList_append` is the Fox-level law, and here
it costs nothing at all: the three trailing blocks each have **zero** row, so every prefix weight
the product rule produces is applied to `0` and no `S₂`-power is ever consulted.

The two new block rows are the easy ones.  The plus block `δ₀²[δ₀,δ₁]` is a square of a
trivially-acting value (hence `2·(−a(x₀)) = 0` in characteristic two) times a commutator of two
such (hence `0` by `foxD_comm_of_trivial`); the handle tail is empty at `h = 0` and the single
handle block otherwise, whose row is WN0-a's `foxD_handlesW`.
-/

section FullRow

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The handle tail's Fox row vanishes**, at every handle count: the `Mpc` row is on the
no-node-at-`h = 0` handle shape, so the tail is the empty list at `h = 0` and the single block
`H_h` otherwise. -/
theorem foxD_prodList_handleTailW
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) :
    foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = 0 := by
  cases h with
  | zero => rfl
  | succ n =>
      rw [show handleTailW (n + 1) = [handlesW (n + 1)] from rfl, PWord.prodList_cons,
        PWord.prodList_nil, foxD_mul, foxD_one, smul_zero, add_zero]
      exact foxD_handlesW t E E₂ hwild a

/-- **The plus block has zero Fox row** in characteristic two at the ramified reading.  Both
δ-letters evaluate into `trivAct` (`trivAct_dW_ram`), so the square contributes the doubled row
`2·D(δ₀)` and the commutator contributes nothing. -/
theorem foxD_plusW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (plusW h) = 0 := by
  have ht0 : PWord.evalFin ⇑t E E₂ (dW h 0) ∈ trivAct C V := trivAct_dW_ram t E E₂ hwild hTodd 0
  have ht1 : PWord.evalFin ⇑t E E₂ (dW h 1) ∈ trivAct C V := trivAct_dW_ram t E E₂ hwild hTodd 1
  have hsq : foxD ⇑t a E E₂ (PWord.zpow (dW h 0) ((2 : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast, WordLift.sum_pow_smul_of_trivial (mem_trivAct.mp ht0), two_nsmul,
      hV₂]
  have hcm : foxD ⇑t a E E₂ (PWord.comm (dW h 0) (dW h 1)) = 0 :=
    foxD_comm_of_trivial _ _ _ _ ht0 ht1
  rw [plusW, MCompact.foxD_prodList_pair, hsq, hcm, smul_zero, add_zero]

/-- **The whole word's Fox row is the two-copy pair's**, at *every* offset vector and with no
`τ`-class hypothesis beyond what the two dead blocks need.  This is the step `prodList` cannot
take on its own: the append law turns the four-block list into the pair `R_lin^pc·R̂^pc` followed
by two blocks whose rows vanish, and the prefix weights therefore multiply `0`. -/
theorem foxD_mpcW_eq_mpcProductW (α r pp : ℕ) (η : EtaDisplay)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = foxD ⇑t a E E₂ (PWord.mul (mpcLinW α r pp η h) (mpcHatW α r pp η h)) := by
  have hplus : foxD ⇑t a E E₂
      (PWord.prodList [PWord.zpow (dW h 0) ((2 : ℕ) : ℤ), PWord.comm (dW h 0) (dW h 1)]) = 0 :=
    foxD_plusW t E E₂ a hwild hTodd hV₂
  have htail : foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = 0 :=
    foxD_prodList_handleTailW t E E₂ a hwild
  rw [mpcW, foxD_prodList_append, foxD_prodList_append, foxD_prodList_append, hplus, htail,
    smul_zero, smul_zero, add_zero, add_zero, foxD_mul, mpcLinW, mpcHatW]

/-- **The whole word's Fox row is the linear copy's, read at σ-killed offsets** — at *every*
offset vector, on a ramified elementary coefficient.

Two mechanisms, kept visible: the σ-column dies by WMP-b's **coincidence** (the two copies'
σ-entries are the same operator, and `Φ + Φ = 0`), while the hat copy's remaining columns die by
Rem. 5.4.  Both are `Certificates.MProcyclic.foxD_mpcProductW_eq_lin`; what is new here is that
the *word* — not merely the pair — has that row. -/
theorem foxD_mpcW_eq_lin {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = foxD ⇑t (sigmaKill a) E E₂ (mpcLinW α r pp η h) :=
  (foxD_mpcW_eq_mpcProductW t E E₂ a α r pp η hwild hTodd hV₂).trans
    (foxD_mpcProductW_eq_lin t E E₂ hα r pp η hV₂ hwild hτfpf hTodd a)

/-- **The procyclic-`M` word's ramified Fox row is a single entry**, at every `(α ≥ 1, r, p, η,
h)` and at **every** offset vector:

```
D(R_{M,pc})(a) = S₂^{−s}·σ^{−n}·a(x₂).
```

This is the **compact shape** — supported on the `x₂`-column alone, with an invertible operator
in front, exactly as `MCompact.mCompactWildRow` read at the ramified interpretation `P ↦ 0` is
`(0,0,0,0,S⁻¹)`.  It is **not** the two-entry procyclic-`N` shape of `NpcRamifiedBranch`, and
that is the whole reason the procyclic-`M` ramified branch can follow `M0RamifiedStokes` rather
than `NpcRamifiedRow`: no `x₀`-entry means no `x₂ = B(A⁻¹−1)x₀` on a cocycle, hence no opaque
`ω₂`-charge to carry.

There is no σ-freeness hypothesis: the σ-column is not assumed away, it is proved to vanish. -/
theorem foxD_mpcW_x2 {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hη : ActsAsPow t.σ nη (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = ((powOmega2 t.σ) ^ (-(s r : ℤ))) • ((t.σ ^ (-nη)) • a (coreLetter h 2)) := by
  rw [foxD_mpcW_eq_lin t E E₂ a hα r pp η hwild hτfpf hTodd hV₂,
    foxD_mpcLinW_x2 t E E₂ (sigmaKill a) (sigmaKill_sigma a) hwild hτfpf hTodd hα r pp hη hV₂,
    sigmaKill_of_ne a (coreLetter_ne_sigma h 2)]

/-- The single-entry row in the `u • x(x₂)` shape the ramified normal-form route consumes: one
group element, applied to the `x₂`-coordinate. -/
theorem foxD_mpcW_smul {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hη : ActsAsPow t.σ nη (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = ((powOmega2 t.σ) ^ (-(s r : ℤ)) * t.σ ^ (-nη)) • a (coreLetter h 2) := by
  rw [foxD_mpcW_x2 t E E₂ a hα r pp hwild hτfpf hTodd hη hV₂, mul_smul]

end FullRow

/-! ## The ramified normal-form route at a `u`-scaled wild pivot

`M0RamifiedStokes` runs the whole first-order half of the ramified even route — surjectivity of
the differential, the unique normal representative, and Stokes duality from a left-separating
traced pairing — but it states its three lemmas at the *compact* row `−S⁻¹·x(x₂)` literally.
The procyclic-`M` row is `S₂^{−s}σ^{−n}·x(x₂)`: the same shape with a different unit, so the
arguments go through verbatim once the pivot is written `u • x(x₂)` for an arbitrary group
element `u` (the only property used is that `u` acts invertibly, which for a group element is
free).

⚠ These four are **generalizations of `GQ2.Dyadic.{heisD1_surjective_of_ramified_row,
heisD1_evenNormal_eq_zero_of_ramified_row, evenNormalForm_of_ramified_row,
evenRamifiedStokesDuality_of_row}`**, not new mathematics, and they are here rather than there
only because `M0RamifiedStokes.lean` is not this ticket's file.  The compact row is the case
`u = −S⁻¹` — which is `u = S⁻¹` on a characteristic-two coefficient — so a hoist would let
`M0RamifiedStokes` delete its four copies and keep them as specializations.
-/

section SmulPivot

variable {h q : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- Surjectivity of a differential whose wild row is a group element applied to the
`x₂`-coordinate. -/
theorem heisD1_surjective_of_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter h 2)])
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 + 2 * h) → A := fun g ↦
    if g = .sigma then v else if g = coreLetter h 2 then u⁻¹ • r 1 else 0
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  have hσx2 : (.sigma : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.sigma_ne_coreLetter_two h
  have hτσ : (.tau : Generator (2 + 2 * h)) ≠ .sigma := by simp
  have hτx2 : (.tau : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.tau_ne_coreLetter_two h
  fin_cases k
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau = r 0
    simp only [x, if_pos, if_neg hτσ, if_neg hτx2, zero_add, smul_zero, Finset.sum_const_zero,
      sub_zero]
    exact hv
  · change u • x (coreLetter h 2) = r 1
    have hx2 : x (coreLetter h 2) = u⁻¹ • r 1 := by simp [x, hσx2.symm]
    rw [hx2, smul_inv_smul]

omit [Finite A] in
/-- Every ramified normal cochain is a cocycle for a `u`-scaled wild pivot. -/
theorem heisD1_evenNormal_eq_zero_of_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter h 2)])
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (evenNormal h d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k <;> simp

set_option maxHeartbeats 1600000 in
/-- The ramified normal form at a `u`-scaled wild pivot: `u` kills `x₂` because it is
invertible, a coboundary kills `tau`, and the `q`-independent tame pivot kills `sigma`. -/
theorem evenNormalForm_of_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter h 2)])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
  have hxcore2 : x (coreLetter h 2) = 0 := by
    have hz := congrFun hx 1
    rw [hrow x] at hz
    have hz' : u • x (coreLetter h 2) = 0 := by simpa using hz
    rwa [smul_eq_zero_iff_eq] at hz'
  obtain ⟨v, hv⟩ := hTsurj (x .tau)
  let x' := x - heisD0 (⇑t) v
  have hx' : heisD1 (⇑t) w x' = 0 := by
    change heisD1 (⇑t) w (x - heisD0 (⇑t) v) = 0
    rw [map_sub, hx, heisD1_comp_heisD0 (⇑t) w hr v, sub_zero]
  have hx'τ : x' .tau = 0 := by simp [x', heisD0_apply, hv]
  have hx'core2 : x' (coreLetter h 2) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore2]
  have hx'σ : x' .sigma = 0 := by
    have hz := congrFun hx' 0
    rw [hrow x'] at hz
    have hz' : t.σ⁻¹ • (t.τ • x' .sigma - x' .sigma) = 0 := by simpa [hx'τ] using hz
    have hdiff : t.τ • x' .sigma - x' .sigma = 0 := by
      have hs := congrArg (t.σ • ·) hz'
      simpa using hs
    exact hτfpf _ (sub_eq_zero.mp hdiff)
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
/-- **Stokes duality for an even complex with a `u`-scaled wild pivot.**  The word enters only
through its first Fox row and through left nondegeneracy of the traced pairing on the normal
coordinates. -/
theorem evenRamifiedStokesDuality_of_smul_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter h 2)])
    (hrowD : ∀ y : Generator (2 + 2 * h) → ElemDual A, heisD1 ⇑t w y
      = ![t.σ⁻¹ • (y .tau + t.τ • y .sigma - y .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • y .tau,
          u • y (coreLetter h 2)])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (evenNormal h p.1 p.2.1 p.2.2)
          (evenNormal h r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t w A := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  exact evenNormalStokesDuality t w hA₂ hr hend
    (heisD0_injective_of_tau_fixedPointFree t hτfpf)
    (heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD)
    (heisD1_surjective_of_smul_row t w u hrowA hτfpf)
    (heisD1_surjective_of_smul_row (A := ElemDual A) t w u hrowD hτfpfD)
    (fun p ↦ heisD1_evenNormal_eq_zero_of_smul_row t w u hrowA p.1 p.2.1 p.2.2)
    (fun r ↦ heisD1_evenNormal_eq_zero_of_smul_row (A := ElemDual A) t w u hrowD
      r.1 r.2.1 r.2.2)
    (evenNormalForm_of_smul_row t w u hrowA hwild hτfpf hr)
    (evenNormalForm_of_smul_row (A := ElemDual A) t w u hrowD hwildD hτfpfD hr)
    hsep

end SmulPivot

/-! ## The row's level-indexed resolver -/

/-- The corrected procyclic-`M` row supplies a level-indexed resolver, one display at a time:
`resolvesAt_mpcFam` for the two `ω₂`-only displays and `resolvesAt_mpcFamOf_hat` for a genuine
`η̂`-display, with `resolvedFamily_isStokesEndpoint` as the common endpoint half. -/
theorem levelResolver {alpha r pp h q : ℕ} (d : EtaDisplay) (hα : 1 ≤ alpha) (hqe : Even q) :
    LevelResolver (2 + 2 * h) q (mpcW alpha r pp d h) (resolvedFamily alpha r pp h q d) where
  resolves := fun _ _ _ _ _ _ hN hord ↦ by
    cases d with
    | one => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | lit k => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | hat num den => exact resolvesAt_mpcFamOf_hat hN hord alpha r pp h q num den (fun _ ↦ 0)
  endpoint := fun _ hN hv ↦ resolvedFamily_isStokesEndpoint hN hv hα hqe d

/-! ## The pushed residues -/

/-- The source-facing residue for the corrected procyclic-`M` row: markings pushed forward from
the candidate group only, and the three induced word-cohomology bijections in place of the six
`StokesDuality` clauses. -/
def PushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
        (resolvedFamily alpha r pp h q d N k) = 1)
      (hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
          (resolvedFamily alpha r pp h q d N) V hr hend

/-- The coefficient-independent residue at the uniform level `4 * Monoid.exponent C`, in the
shape produced by action-image devissage.

The statement itself is written once, upstream, as `MProcyclicExact.UniformHsimp` in
`GQ2/Dyadic/Instances/MpcExact.lean`: that is the file which restates the whole clause stack over
the uniform residue, and it cannot name a definition living here because this file imports it.
This declaration is the row-uniform *name* for that one statement, matching the other rows
(`LSquare.UniformPushedHsimp`, `MCompact.UniformPushedHsimp`, `NProcyclic.UniformPushedHsimp`).
The two names denote the same proposition, so a term of either type is accepted where the other
is expected and every existing consumer of this name is unaffected. -/
def UniformPushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  UniformHsimp alpha r pp h q d

/-- Collapse regression: the row-uniform name and the upstream statement are the same
proposition, definitionally in both directions. -/
example : @UniformPushedHsimp = @UniformHsimp := rfl

/-- The historical all-markings residue implies the pushed cohomological one. -/
theorem pushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) : PushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho N hN hv hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g)⟩ with ht
  exact (stokesDuality_iff_cohomologyBijections ⇑t (resolvedFamily alpha r pp h q d N) V hr
    hend).mp (hsimp C t N hN hv hr V hV₂ hsimple)

/-! ## The pushed replacements for the two chain entry points -/

/-- The devissage step of the pushed residue, once relator death at the pushed marking is in
hand. -/
private theorem stokesDuality_of_pushed_of_relators {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hr : ∀ k, FreeGroup.lift
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N k) = 1)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A := by
  have hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N) :=
    resolvedFamily_isStokesEndpoint hN hv hα hqe d
  exact stokesDuality_of_simple _ (resolvedFamily alpha r pp h q d N) hr hend
    (fun V _ _ _ hV₂ hsimple ↦
      (stokesDuality_iff_cohomologyBijections _ (resolvedFamily alpha r pp h q d N) V hr
        hend).mpr (hsimp C rho N hN hv hr hend V hV₂ hsimple)) A hA₂

/-- `MProcyclicExact.stokesDuality` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed_of_relators hsimp hα hqe rho hN hv
    (fun k ↦ lower_rel (A := ZMod 2) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- `MProcyclicExact.stokesDuality_T` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_T_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  exact stokesDuality_of_pushed hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## The uniform residue, and the action-image route to it -/

/-- The pushed residue supplies the uniform one. -/
theorem uniformPushedHsimp_of_pushedHsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) (WordLift A C) := by
    refine (levelResolver d hα hqe).resolves (WordLift A C) (4 * Monoid.exponent C)
      (fourMulExponent_ne_zero_and_even C).1 ?_
    intro x
    refine (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) x).trans ?_
    exact mul_dvd_mul_right (by norm_num) (Monoid.exponent C)
  exact stokesDuality_of_pushed_of_relators hsimp hα hqe rho
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
    (fun k ↦ lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- Both weakenings composed. -/
theorem uniformPushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp) hα hqe

/-- **The action-image route for the corrected procyclic-`M` row, at every admissible level.**
The only remaining input is the simple-module branch at the canonical action image. -/
theorem stokesDuality_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : HeisLift A C, orderOf x ∣ N) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  pushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂ hN hord

/-- The uniform residue from the action image. -/
theorem uniformPushedHsimp_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  exact uniformPushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂

/-- The residue split along the `tau`-dichotomy, at the corrected procyclic-`M` word. -/
theorem uniformPushedHsimp_of_branches {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    (hram : RamifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_actionImage hα hqe (simpleActionImageStokes_of_branches hunram hram)

/-! ## The ramified branch of the procyclic-`M` residue

Everything first-order is now in hand, so the branch reduces to one second-order statement, in
exactly the shape `M0RamifiedBranch` reduces the compact-`M` one: left nondegeneracy of the
traced pairing on the **untwisted** even normal coordinates.  Untwisted is the point of the
shape correction: a one-entry row leaves the `x₂`-column free on a cocycle, so there is no
`A⁻¹−1` twist and no opaque `ω₂`-charge, which is what `NpcRamifiedBranch` has to carry.
-/

section RamifiedBranch

/-- Every display's resolved family is `mpcFamOf` at a resolver correct at the lift level, for
two coefficient modules at once — the primal and its dual, which have to share the resolver
because the normal-form route compares them. -/
theorem exists_resolver_resolvedFamily {alpha r pp h q : ℕ} (d : EtaDisplay)
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
    {B : Type*} [AddCommGroup B] [DistribMulAction C B]
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0) :
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
      resolvedFamily alpha r pp h q d (4 * Monoid.exponent C) = mpcFamOf alpha r pp h q d E E₂
        ∧ ResolverLifts E (WordLift A C) ∧ ResolverLifts E (WordLift B C) := by
  cases d with
  | one =>
      exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
        resolverLifts_uniformWordLift_ramified hA₂, resolverLifts_uniformWordLift_ramified hB₂⟩
  | lit k =>
      exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
        resolverLifts_uniformWordLift_ramified hA₂, resolverLifts_uniformWordLift_ramified hB₂⟩
  | hat num den =>
      exact ⟨_, _, rfl, NProcyclic.resolverLifts_npcResolver_wordLift hA₂ ⟨num, den⟩,
        NProcyclic.resolverLifts_npcResolver_wordLift hB₂ ⟨num, den⟩⟩

set_option maxHeartbeats 1600000 in
/-- **The complete first differential of the procyclic-`M` family on a ramified elementary
module**: the arbitrary-`q` tame row, and a single wild pivot `S₂^{−s}σ^{−n}` on the
`x₂`-coordinate. -/
theorem heisD1_mpcFamOf_ramified_apply {alpha r pp h q : ℕ} {η : EtaDisplay} {nη : ℤ}
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hlift : ResolverLifts E (WordLift A C)) (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0) (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hnη : PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h)) = t.σ ^ nη)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (mpcFamOf alpha r pp h q η E E₂) x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          ((powOmega2 t.σ) ^ (-(s r : ℤ)) * t.σ ^ (-nη)) • x (coreLetter h 2)] := by
  funext k
  fin_cases k
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (Certificates.tameRelW (2 + 2 * h) q))).a
      = t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hlift,
      Certificates.foxD_tameRelW_of_tameRel t _ _ ht]
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (mpcW alpha r pp η h))).a
      = ((powOmega2 t.σ) ^ (-(s r : ℤ)) * t.σ ^ (-nη)) • x (coreLetter h 2)
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hlift,
      foxD_mpcW_smul t E E₂ x hα r pp hwild hτfpf hTodd (fun v ↦ by rw [hnη]) hA₂]

/-- **The residual procyclic-`M` ramified input.**  On every simple elementary coefficient with
`tau` fixed-point free, the traced pairing of the corrected procyclic-`M` family at the uniform
level separates the nonzero even normal coordinates.

This is the exact analogue of `MCompact.RamifiedNormalPairingSeparates`, on the same
**untwisted** coordinates, and *not* of `NProcyclic.RamifiedTwistedPairingSeparates`. -/
def RamifiedNormalPairingSeparates (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (mpcW alpha r pp d h) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) .tau • m = m → m = 0) →
    ∀ p : M × M × (Fin h × Fin 2 → M), p ≠ 0 →
      ∃ rr : ElemDual M × ElemDual M × (Fin h × Fin 2 → ElemDual M),
        heisEta1 (actionImageGenerators (2 + 2 * h) q (mpcW alpha r pp d h) M)
            (resolvedFamily alpha r pp h q d
              (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M)))
            (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h rr.1 rr.2.1 rr.2.2) ≠ 0

set_option maxHeartbeats 3200000 in
/-- **The procyclic-`M` ramified branch, from the residual pairing statement.**  Every
first-order ingredient is discharged — the one-entry row, the surjective differential, the unique
normal representative — and `hsep` is exactly the second-order residue. -/
theorem ramifiedActionImageStokes_of_separation {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d) :
    RamifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτfpf
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  obtain ⟨E, E₂, hfam, hliftM, hliftD⟩ :=
    exists_resolver_resolvedFamily (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      (C := ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M) (A := M) (B := ElemDual M)
      d hM₂ hM₂D
  have hsep' := hsep M hM₂ hsimple hτfpf
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
  have ht : t.TameRelAt q := actionImage_tameRelAt
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := fun m hm ↦ hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual M), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual M, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf' lam hlam
  have hToddD : ∀ lam : ElemDual M, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  obtain ⟨nη, hnη⟩ := exists_zpow_evalFin_etaDisplay t E E₂ d
  rw [hfam] at hend hr hsep'
  rw [hfam]
  exact evenRamifiedStokesDuality_of_smul_row t _
    ((powOmega2 t.σ) ^ (-(s r : ℤ)) * t.σ ^ (-nη)) hM₂ hr hend
    (heisD1_mpcFamOf_ramified_apply (alpha := alpha) (r := r) (pp := pp) t E E₂ hliftM hM₂ hα ht
      hwild hτfpf' hTodd hnη)
    (heisD1_mpcFamOf_ramified_apply (A := ElemDual M) (alpha := alpha) (r := r) (pp := pp) t E E₂
      hliftD hM₂D hα ht hwildD hτfpfD hToddD hnη)
    hwild hτfpf' hsep'

/-- **The procyclic-`M` uniform pushed residue, reduced to its two branch inputs.** -/
theorem uniformPushedHsimp_of_ramified_separation {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_branches hα hqe hunram
    (ramifiedActionImageStokes_of_separation hα hqe hsep)

end RamifiedBranch

/-! ## Regression: the historical entry points factor through the pushed ones -/

/-- `MProcyclicExact.stokesDuality`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho hN hv hres A hA₂

/-- `MProcyclicExact.stokesDuality_T`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_T_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) :=
  stokesDuality_T_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho

end

/-! ## Axiom footprint -/

#print axioms GQ2.Dyadic.MProcyclicExact.foxD_prodList_handleTailW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_plusW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_eq_mpcProductW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_eq_lin
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_x2
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_smul
#print axioms GQ2.Dyadic.MProcyclicExact.heisD1_surjective_of_smul_row
#print axioms GQ2.Dyadic.MProcyclicExact.heisD1_evenNormal_eq_zero_of_smul_row
#print axioms GQ2.Dyadic.MProcyclicExact.evenNormalForm_of_smul_row
#print axioms GQ2.Dyadic.MProcyclicExact.evenRamifiedStokesDuality_of_smul_row
#print axioms GQ2.Dyadic.MProcyclicExact.levelResolver
#print axioms GQ2.Dyadic.MProcyclicExact.pushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_branches
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_via_pushed
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_T_via_pushed
#print axioms GQ2.Dyadic.MProcyclicExact.exists_resolver_resolvedFamily
#print axioms GQ2.Dyadic.MProcyclicExact.heisD1_mpcFamOf_ramified_apply
#print axioms GQ2.Dyadic.MProcyclicExact.ramifiedActionImageStokes_of_separation
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_ramified_separation

end GQ2.Dyadic.MProcyclicExact
