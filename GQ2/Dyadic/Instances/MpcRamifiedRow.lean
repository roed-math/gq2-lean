/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcRamifiedPairing
import GQ2.Dyadic.Instances.EvenMRamifiedRow

/-!
# The procyclic-`M` second-order row on ramified normal offsets

`MpcRamifiedPairing` records the residual the ramified procyclic-`M` row still owes: eight live
factors, of which four (`A²`, `[A,B]` and their hat twins) need arbitrary-base laws.  This file
performs the cancellation and reads off the row.

## The two structural facts that replace the compact computation

`MCompactRam.heisZ_mCompact_ram` cancels every `K`-twisted atom of the compact row by hand,
against a *symmetric* conjugator pair `𝓔(σ₂^m, σ₂^m; ·)`.  Here the pair is asymmetric —
`𝓔(σ₂^{p+sm}, σ₂^{sm}; ·)` — and the `p`-shift is the `ε`-visible part of the block, so that
computation does not transfer.  Two structural observations replace it and make the atom-level
bookkeeping unnecessary.

* **The two copies agree at second order.**  `A` and `Â = δ₀⁻¹Ĉ₀^{−m}` have the *same* jets
  `(−d₀, −λ₀)` and bases with the *same action* `S₂^{−sm}`; likewise `B = x₁σ₂^p` and
  `B̂ = δ₁σ₂^p`, and `C₀ = x₂σ₂^s` and `Ĉ₀ = σ₂^s`.  They differ only in their central charges —
  and neither `heisSq_general`'s value `λ(g·a)` nor `heisCommR_general`'s eight-term centre
  *reads* a charge.  So `R_lin^pc` and `R̂^pc` have equal jets **and equal charges**: the
  predicate `SameVal` below propagates exactly that through the product, and `E₂^pc`, the one
  unmatched linear factor, is dead in the ramified class too (`isDead_e2W_ram`).
* **The linear copy is jet-zero.**  `A²`, `[A,B]` and `E₀₁^pc` contribute
  `d₀ + S₂^{−sm}d₀`, `S₂^{−2sm}·(…)` and `S₂^{−(p+sm)}(…)`, and the balancing power
  `C₀^{2^α}` — which acts by `S₂^{s·2^α} = S₂^{2sm}` exactly when `α ≥ 1` — lines them up so
  that the twelve atoms cancel in six pairs.  This is where the asymmetry pays for itself: the
  outer conjugator's `p`-shift is precisely what cancels `B`'s.

Given those two, the assembly is three lines of Heisenberg algebra: with `u` jet-zero and
`SameVal u v`, the product `u·v` is jet-zero with **zero** charge, so the whole eleven-factor
`R_lin^pc·R̂^pc` is silent and the row is the plus block plus the handles:

```
z(R_{M,pc}) = λ₀(d₀) ⊕ (λ₀(d₁) + λ₁(d₀)) ⊕ Σ_j planes.
```

⚠ That is the **same** core Gram `((1,1),(1,0))` as the unramified reading
(`heisZ_mpcW_evenNormal`) and as the compact-`N` ramified row — and *not* the compact-`M`
ramified row's `((0,1),(1,1))`.  The ramified procyclic-`M` diagonal sits on `x₀`, produced by
the plus block `δ₀²`, not on `x₁`: on this row the Labute square is silent because its hat twin
repeats it.

⚠ `1 ≤ α` is **necessary**, not cosmetic.  At `α = 0` the balancing power `C₀^{2^α} = C₀`
acts by `S₂^{s}` instead of `S₂^{2sm} = S₂^{2s}`, the six pairs do not line up, and the linear
copy is not jet-zero; `α ≥ 1` is exactly the hypothesis `ramifiedActionImageStokes_of_separation`
already carries.
-/

namespace GQ2.Dyadic.MpcRam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.MProcyclicNormal

/-! ## Agreement of two Heisenberg values

The whole ramified cancellation is carried by one observation: the linear and the hat copy of the
procyclic-`M` word denote lifts that differ only in coordinates nothing downstream reads.  Two
predicates record that, one per order. -/

section Agreement

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- Bases that act alike act alike after inversion. -/
theorem smul_inv_congr {g g' : C} (hg : ∀ w : A, g • w = g' • w) (w : A) :
    g⁻¹ • w = g'⁻¹ • w := by
  rw [inv_smul_eq_iff, hg, smul_inv_smul]

/-- Bases that act alike act alike on the elementary dual. -/
theorem smul_elemDual_congr {g g' : C} (hg : ∀ w : A, g • w = g' • w) (lam : ElemDual A) :
    g • lam = g' • lam :=
  ElemDual.ext fun w ↦ by rw [ElemDual.smul_apply, ElemDual.smul_apply, smul_inv_congr hg]

/-- **First-order agreement**: equal jets and bases acting alike.  The central charges are
unconstrained — that is the point. -/
structure SameJet (u v : HeisLift A C) : Prop where
  /-- The primal jets agree. -/
  aEq : u.a = v.a
  /-- The dual jets agree. -/
  lEq : u.l = v.l
  /-- The bases act alike on the coefficient module. -/
  gEq : ∀ w : A, u.g • w = v.g • w

/-- **Second-order agreement**: `SameJet` together with equal central charges. -/
structure SameVal (u v : HeisLift A C) : Prop where
  /-- The primal jets agree. -/
  aEq : u.a = v.a
  /-- The dual jets agree. -/
  lEq : u.l = v.l
  /-- The central charges agree. -/
  zEq : u.z = v.z
  /-- The bases act alike on the coefficient module. -/
  gEq : ∀ w : A, u.g • w = v.g • w

variable {u v u' v' : HeisLift A C}

theorem SameVal.toSameJet (h : SameVal u v) : SameJet u v := ⟨h.aEq, h.lEq, h.gEq⟩

theorem SameJet.gEqInv (h : SameJet u v) (w : A) : u.g⁻¹ • w = v.g⁻¹ • w :=
  smul_inv_congr h.gEq w

theorem SameJet.gEqDual (h : SameJet u v) (lam : ElemDual A) : u.g • lam = v.g • lam :=
  smul_elemDual_congr h.gEq lam

theorem SameJet.rfl' (u : HeisLift A C) : SameJet u u := ⟨rfl, rfl, fun _ ↦ rfl⟩

theorem SameVal.rfl' (u : HeisLift A C) : SameVal u u := ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩

/-- Second-order agreement is multiplicative — every coordinate of the Heisenberg product is a
function of the two factors' jets, charges and base *actions*. -/
theorem SameVal.mul (h : SameVal u v) (h' : SameVal u' v') : SameVal (u * u') (v * v') where
  aEq := by
    show u.a + u.g • u'.a = v.a + v.g • v'.a
    rw [h.aEq, h'.aEq, h.gEq]
  lEq := by
    show u.l + u.g • u'.l = v.l + v.g • v'.l
    rw [h.lEq, h'.lEq, h.toSameJet.gEqDual]
  zEq := by
    show u.z + u'.z + u.l (u.g • u'.a) = v.z + v'.z + v.l (v.g • v'.a)
    rw [h.zEq, h'.zEq, h.lEq, h'.aEq, h.gEq]
  gEq w := by
    show (u.g * u'.g) • w = (v.g * v'.g) • w
    rw [mul_smul, mul_smul, h'.gEq, h.gEq]

/-- **Squares only read the first order.**  `heisSq_general`'s central value is `λ(g·a)`, so two
lifts agreeing at first order have squares agreeing at second order. -/
theorem SameJet.sq (h : SameJet u v) : SameVal (u * u) (v * v) where
  aEq := by
    show u.a + u.g • u.a = v.a + v.g • v.a
    rw [h.aEq, h.gEq]
  lEq := by
    show u.l + u.g • u.l = v.l + v.g • v.l
    rw [h.lEq, h.gEqDual]
  zEq := by
    show u.z + u.z + u.l (u.g • u.a) = v.z + v.z + v.l (v.g • v.a)
    rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add,
      h.lEq, h.aEq, h.gEq]
  gEq w := by
    show (u.g * u.g) • w = (v.g * v.g) • w
    rw [mul_smul, mul_smul, h.gEq, h.gEq]

/-- **Commutators only read the first order.**  None of the eight central terms of
`heisCommR_general` involves either factor's charge, so first-order agreement on both entries
gives second-order agreement of the commutators. -/
theorem SameJet.commR (h : SameJet u v) (h' : SameJet u' v') :
    SameVal (commR u u') (commR v v') := by
  rw [heisCommR_general u u', heisCommR_general v v']
  refine ⟨?_, ?_, ?_, ?_⟩
  · show -(u.g⁻¹ • u.a) - u.g⁻¹ • (u'.g⁻¹ • u'.a) + u.g⁻¹ • (u'.g⁻¹ • u.a)
        + u.g⁻¹ • (u'.g⁻¹ • (u.g • u'.a))
      = -(v.g⁻¹ • v.a) - v.g⁻¹ • (v'.g⁻¹ • v'.a) + v.g⁻¹ • (v'.g⁻¹ • v.a)
        + v.g⁻¹ • (v'.g⁻¹ • (v.g • v'.a))
    simp only [h.aEq, h'.aEq, h.gEq, h.gEqInv, h'.gEqInv]
  · show -(u.g⁻¹ • u.l) - u.g⁻¹ • (u'.g⁻¹ • u'.l) + u.g⁻¹ • (u'.g⁻¹ • u.l)
        + u.g⁻¹ • (u'.g⁻¹ • (u.g • u'.l))
      = -(v.g⁻¹ • v.l) - v.g⁻¹ • (v'.g⁻¹ • v'.l) + v.g⁻¹ • (v'.g⁻¹ • v.l)
        + v.g⁻¹ • (v'.g⁻¹ • (v.g • v'.l))
    simp only [h.lEq, h'.lEq, h.gEqDual,
      smul_elemDual_congr (smul_inv_congr h.gEq), smul_elemDual_congr (smul_inv_congr h'.gEq)]
  · show u.l u.a + u'.l u'.a + u.l (u'.g⁻¹ • u'.a) + u.l (u'.g⁻¹ • u.a) + u'.l u.a
        + u.l (u'.g⁻¹ • (u.g • u'.a)) + u'.l (u.g • u'.a) + u.l (u.g • u'.a)
      = v.l v.a + v'.l v'.a + v.l (v'.g⁻¹ • v'.a) + v.l (v'.g⁻¹ • v.a) + v'.l v.a
        + v.l (v'.g⁻¹ • (v.g • v'.a)) + v'.l (v.g • v'.a) + v.l (v.g • v'.a)
    simp only [h.aEq, h'.aEq, h.lEq, h'.lEq, h.gEq, h'.gEqInv]
  · intro w
    show _root_.GQ2.Dyadic.commR u.g u'.g • w = _root_.GQ2.Dyadic.commR v.g v'.g • w
    simp only [_root_.GQ2.Dyadic.commR, mul_smul, h.gEq, h'.gEq, h.gEqInv, h'.gEqInv]

end Agreement

end

end GQ2.Dyadic.MpcRam
