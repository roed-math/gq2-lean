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

/-- Bases that act alike act alike after taking any `ℤ`-power: acting alike is having the same
image under `MulAction.toPermHom`, which is a monoid hom. -/
theorem smul_zpow_congr {g g' : C} (hg : ∀ w : A, g • w = g' • w) (k : ℤ) (w : A) :
    (g ^ k) • w = (g' ^ k) • w := by
  have h : MulAction.toPermHom C A g = MulAction.toPermHom C A g' := Equiv.ext hg
  have h2 : MulAction.toPermHom C A (g ^ k) = MulAction.toPermHom C A (g' ^ k) := by
    rw [map_zpow, map_zpow, h]
  exact congrArg (fun u : Equiv.Perm A ↦ u w) h2

end Agreement

/-! ## Trivial-base jets

Every `δ`-block of the ramified procyclic-`M` row has a trivially-acting base — that is the
load-bearing clause of `MCompactRam.heisEvalZ_deltaCert_ram` — but a central charge nobody can
name.  `TrivJet` is `MProcyclicNormal.Triv` with the charge existentially forgotten; the row
never needs those charges, because each one is repeated inside its block and cancels. -/

section TrivJet

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The trivial-base jet**: the word denotes `⟨a, l, ·, G⟩` with `G` acting trivially. -/
def TrivJet (w : PWord X) (a : A) (l : ElemDual A) : Prop :=
  ∃ z : ZMod 2, Triv μ x y E E₂ w a l z

variable {μ x y E E₂}

theorem TrivJet.aEq {w : PWord X} {a : A} {l : ElemDual A} (hw : TrivJet μ x y E E₂ w a l) :
    (heisEvalZ μ x y E E₂ w).a = a := by
  obtain ⟨z, G, hG, -⟩ := hw
  rw [hG]

theorem TrivJet.lEq {w : PWord X} {a : A} {l : ElemDual A} (hw : TrivJet μ x y E E₂ w a l) :
    (heisEvalZ μ x y E E₂ w).l = l := by
  obtain ⟨z, G, hG, -⟩ := hw
  rw [hG]

theorem TrivJet.gTriv {w : PWord X} {a : A} {l : ElemDual A} (hw : TrivJet μ x y E E₂ w a l)
    (v : A) : (heisEvalZ μ x y E E₂ w).g • v = v := by
  obtain ⟨z, G, hG, hGa⟩ := hw
  rw [hG]
  exact hGa v

variable (μ x y E E₂)

theorem trivJet_one : TrivJet μ x y E E₂ (.one : PWord X) 0 0 := ⟨0, triv_one μ x y E E₂⟩

variable {μ x y E E₂}

theorem TrivJet.mul {u v : PWord X} {a b : A} {l m : ElemDual A}
    (hu : TrivJet μ x y E E₂ u a l) (hv : TrivJet μ x y E E₂ v b m) :
    TrivJet μ x y E E₂ (.mul u v) (a + b) (l + m) := by
  obtain ⟨zu, hu⟩ := hu
  obtain ⟨zv, hv⟩ := hv
  exact ⟨_, hu.mul hv⟩

theorem TrivJet.pair {u v : PWord X} {a b : A} {l m : ElemDual A}
    (hu : TrivJet μ x y E E₂ u a l) (hv : TrivJet μ x y E E₂ v b m) :
    TrivJet μ x y E E₂ (PWord.prodList [u, v]) (a + b) (l + m) := by
  obtain ⟨zu, hu⟩ := hu
  obtain ⟨zv, hv⟩ := hv
  exact ⟨_, hu.pair hv⟩

theorem TrivJet.triple {u v w : PWord X} {a b c : A} {l m n : ElemDual A}
    (hu : TrivJet μ x y E E₂ u a l) (hv : TrivJet μ x y E E₂ v b m)
    (hw : TrivJet μ x y E E₂ w c n) :
    TrivJet μ x y E E₂ (PWord.prodList [u, v, w]) (a + (b + c)) (l + (m + n)) := by
  rw [PWord.prodList_cons]
  exact hu.mul (hv.pair hw)

/-- **Conjugation by a pure-base word** twists both jets by `S⁻¹` and keeps the base trivially
acting (`trivAct_conjR`).  This is the rule the trivial-base calculus of `MpcPairings` is
missing, and the only one the ramified `E₀₁^pc` needs. -/
theorem TrivJet.conjPure {u g : PWord X} {a : A} {l : ElemDual A} {S : C}
    (hu : TrivJet μ x y E E₂ u a l) (hg : heisEvalZ μ x y E E₂ g = heisPure S) :
    TrivJet μ x y E E₂ (.conj u g) (S⁻¹ • a) (S⁻¹ • l) := by
  obtain ⟨z, G, hG, hGa⟩ := hu
  refine ⟨z, conjR G S, ?_, fun v ↦ mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr hGa) S) v⟩
  rw [heisEvalZ_conj, hG, hg, heisConjR_pure_right]

end TrivJet

/-! ## The letters of the procyclic-`M` row in the ramified class -/

/-- **The procyclic-`M` twist** `S₂`: the base of the atom `σ₂ = σ^{ω₂}` at the resolved
exponent.  Every conjugator of the ramified row acts by a power of it, and — unlike the
unramified reading — none of those powers acts trivially. -/
def sTwist {h : ℕ} {C : Type*} [Group C] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) : C :=
  t.σ ^ E omega2

section Letters

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

variable (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hxτ : x .tau = 0) (hyτ : y .tau = 0)
  (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0)
  (hA₂ : ∀ a : A, a + a = 0)
  (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
  (hτfpf : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v)
  (hresA : ResolverLifts E (WordLift A C)) (hresD : ResolverLifts E (WordLift (ElemDual A) C))
  (hres : ResolverLifts E C)

include hxσ hyσ in
/-- Every `σ₂`-power is the pure lift of the corresponding power of the twist — no hypothesis on
how it acts, which is exactly what the ramified reading gives up. -/
theorem heisEvalZ_sig2Zpow (k : ℤ) :
    heisEvalZ ⇑t x y E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) k)
      = heisPure (sTwist t E ^ k) := by
  rw [sTwist, heisEvalZ_zpow, heisEvalZ_sigma2W_pure t x y E E₂ hxσ hyσ, ← map_zpow]

include hxσ hyσ hx2 hy2 in
/-- `C₀ = x₂σ₂^s` is pure on ramified normal offsets: both its letters have vanishing offsets. -/
theorem heisEvalZ_c0W_ram (s' : ℕ) :
    heisEvalZ ⇑t x y E E₂ (c0W h s')
      = heisPure (t (coreLetter h 2) * sTwist t E ^ (s' : ℤ)) := by
  rw [c0W, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_one, mul_one,
    heisEvalZ_gen_of_offsets_zero ⇑t x y E E₂ _ hx2 hy2,
    heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ, map_mul]

include hxσ hyσ in
/-- `Ĉ₀ = σ₂^s` is pure. -/
theorem heisEvalZ_c0HatW_ram (s' : ℕ) :
    heisEvalZ ⇑t x y E E₂ (c0HatW h s') = heisPure (sTwist t E ^ (s' : ℤ)) :=
  heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ _

include hwild in
/-- **`C₀` and `Ĉ₀` act alike**: the wild letter `x₂` is invisible to the coefficients. -/
theorem c0W_smul_eq (s' : ℕ) (v : A) :
    (t (coreLetter h 2) * sTwist t E ^ (s' : ℤ)) • v = (sTwist t E ^ (s' : ℤ)) • v := by
  rw [mul_smul, mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 2)]

include hwild in
/-- Every power of `C₀`'s base acts by the corresponding power of the twist. -/
theorem c0W_zpow_smul (s' : ℕ) (k : ℤ) (v : A) :
    ((t (coreLetter h 2) * sTwist t E ^ (s' : ℤ)) ^ k) • v
      = (sTwist t E ^ ((s' : ℤ) * k)) • v := by
  rw [smul_zpow_congr (c0W_smul_eq t E hwild s') k, ← zpow_mul]

end Letters

end

end GQ2.Dyadic.MpcRam
