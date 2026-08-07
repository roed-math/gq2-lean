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

/-- **The six-pair cancellation.**  The linear copy's three live jets — the Labute square's
coboundary, the Labute commutator's four atoms, and the correction block's four — cancel
exactly, once the balancing power `S^{2b}` has lined the block up against the commutator.  `b` is
`sm` and `pz` is the `B`-shift `p`; the asymmetry `a = p + sm` of the outer conjugator is what
puts `-pz` on the block's atoms and lets them meet the commutator's. -/
theorem linJet_cancel (hA₂ : ∀ a : A, a + a = 0) (S : C) (b pz : ℤ) (d₀ d₁ : A) :
    (d₀ + S ^ (-b) • d₀)
      + S ^ (-(2 * b)) •
          ((S ^ b • d₀ + S ^ (b - pz) • d₁ + S ^ (b - pz) • d₀ + S ^ (-pz) • d₁)
            + S ^ (2 * b) • ((S ^ (pz + b))⁻¹ • ((S ^ b)⁻¹ • d₁ + (d₁ + d₀)) + d₀)) = 0 := by
  have h2 : ∀ a : A, (2 : ℤ) • a = 0 := fun a ↦ by rw [two_zsmul]; exact hA₂ a
  simp only [← zpow_neg, smul_add, zpow_smul_zpow_smul]
  rw [show -(2 * b) + b = -b from by ring, show -(2 * b) + (b - pz) = -b - pz from by ring,
    show -(2 * b) + -pz = -b - pz + -b from by ring,
    show -(2 * b) + (2 * b + (-(pz + b) + -b)) = -b - pz + -b from by ring,
    show -(2 * b) + (2 * b + -(pz + b)) = -b - pz from by ring,
    show -(2 * b) + 2 * b = (0 : ℤ) from by ring, zpow_zero, one_smul]
  abel_nf
  simp only [h2, add_zero]

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

theorem sameValOne_of_isDead {w : PWord X} (hw : IsDead μ x y E E₂ w) :
    SameVal (heisEvalZ μ x y E E₂ w) 1 := by
  obtain ⟨G, hG, hGa⟩ := hw
  rw [hG]
  exact ⟨rfl, rfl, rfl, fun v ↦ by rw [heisPure_g, hGa, HeisLift.one_g, one_smul]⟩

theorem TrivJet.inv {u : PWord X} {a : A} {l : ElemDual A} (hu : TrivJet μ x y E E₂ u a l) :
    TrivJet μ x y E E₂ (.inv u) (-a) (-l) := by
  obtain ⟨zu, hu⟩ := hu
  exact ⟨_, hu.inv⟩

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

include hxσ hyσ in
/-- The displayed `σ₂`-power, in both of its two shapes. -/
theorem heisEvalZ_sig2PowW (k : ℕ) :
    heisEvalZ ⇑t x y E E₂ (sig2PowW h k) = heisPure (sTwist t E ^ (k : ℤ)) := by
  match k with
  | 0 => exact heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ _
  | 1 => rw [sTwist, show sig2PowW h 1 = sigma2W from rfl,
      heisEvalZ_sigma2W_pure t x y E E₂ hxσ hyσ, Nat.cast_one, zpow_one]
  | (j + 2) => exact heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ _

/-! ### The four `σ₂`-shifted letters

`A`, `Â`, `B` and `B̂` are the letters whose base genuinely moves on the ramified reading.  Each
is a trivial-base word times a pure `σ₂`-power, so each has *nameable* jets and a base acting by
a power of the twist — with the charge left free, because `A` and `Â` carry different ones. -/

/-- **A `σ₂`-shifted letter**: nameable jets, a base acting by `S₂^k`, and a free charge. -/
def SLetter (w : PWord (Generator (2 + 2 * h))) (a : A) (l : ElemDual A) (k : ℤ) : Prop :=
  ∃ (G : C) (z : ZMod 2), heisEvalZ ⇑t x y E E₂ w = ⟨a, l, z, G⟩
    ∧ ∀ v : A, G • v = (sTwist t E ^ k) • v

variable {t x y E E₂}

theorem SLetter.aEq {w : PWord (Generator (2 + 2 * h))} {a : A} {l : ElemDual A} {k : ℤ}
    (hw : SLetter t x y E E₂ w a l k) : (heisEvalZ ⇑t x y E E₂ w).a = a := by
  obtain ⟨G, z, hG, -⟩ := hw
  rw [hG]

theorem SLetter.smul {w : PWord (Generator (2 + 2 * h))} {a : A} {l : ElemDual A} {k : ℤ}
    (hw : SLetter t x y E E₂ w a l k) (v : A) :
    (heisEvalZ ⇑t x y E E₂ w).g • v = (sTwist t E ^ k) • v := by
  obtain ⟨G, z, hG, hGa⟩ := hw
  rw [hG]
  exact hGa v

/-- **Two `σ₂`-shifted letters with the same data agree at first order** — the whole point of the
predicate.  Their charges may differ, and for `A` against `Â` they do. -/
theorem SLetter.sameJet {u v : PWord (Generator (2 + 2 * h))} {a : A} {l : ElemDual A} {k : ℤ}
    (hu : SLetter t x y E E₂ u a l k) (hv : SLetter t x y E E₂ v a l k) :
    SameJet (heisEvalZ ⇑t x y E E₂ u) (heisEvalZ ⇑t x y E E₂ v) where
  aEq := by rw [hu.aEq, hv.aEq]
  lEq := by
    obtain ⟨G, z, hG, -⟩ := hu
    obtain ⟨G', z', hG', -⟩ := hv
    rw [hG, hG']
  gEq w := by rw [hu.smul, hv.smul]

variable (t x y E E₂)

/-- A trivial-base word times a pure-base `σ₂`-power is a `σ₂`-shifted letter. -/
theorem sLetter_pairPure {u g : PWord (Generator (2 + 2 * h))} {a : A} {l : ElemDual A}
    {S : C} {k : ℤ} (hu : TrivJet ⇑t x y E E₂ u a l)
    (hg : heisEvalZ ⇑t x y E E₂ g = heisPure S)
    (hk : ∀ v : A, S • v = (sTwist t E ^ k) • v) :
    SLetter t x y E E₂ (PWord.prodList [u, g]) a l k := by
  obtain ⟨z, G, hG, hGa⟩ := hu
  refine ⟨G * S, z, ?_, fun v ↦ by rw [mul_smul, hk, hGa]⟩
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_one, mul_one, hG, hg, heisMul_of_trivial_left _ _ hGa]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show a + (0 : A) = a
    rw [add_zero]
  · show l + (0 : ElemDual A) = l
    rw [add_zero]
  · show z + 0 + l (0 : A) = z
    rw [map_zero, add_zero, add_zero]

/-! ### The `δ`-letters -/

include hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **The `δ`-letters in the ramified class**: jets `(d_i, λ_i)` and — the load-bearing clause —
a trivially-acting base.  This is `MCompactRam.heisEvalZ_deltaCert_ram` read through
`dW = deltaCert`. -/
theorem trivJet_dW_ram [Finite C] [Finite A] (i : Fin 3) :
    TrivJet ⇑t x y E E₂ (dW h i) (x (coreLetter h i)) (y (coreLetter h i)) := by
  rw [dW_eq_deltaCert]
  obtain ⟨ha, hl, hg⟩ :=
    MCompactRam.heisEvalZ_deltaCert_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres i
  exact ⟨_, _, HeisLift.ext ha hl rfl rfl, hg⟩

include hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **`δ₂` is dead in the ramified class**: pure by `isPure_dW2` — all three of its letters have
vanishing offsets — with a trivially-acting base by `trivJet_dW_ram`. -/
theorem isDead_dW2_ram [Finite C] [Finite A] : IsDead ⇑t x y E E₂ (dW h 2) :=
  isDead_of_heisTrivial (isPure_dW2 t x y E E₂ hxτ hyτ hx2 hy2)
    (trivJet_dW_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres 2).gTriv

include hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres in
theorem isDead_zW_ram [Finite C] [Finite A] (pp : ℕ) : IsDead ⇑t x y E E₂ (zW h pp) := by
  have hd2 := isDead_dW2_ram t x y E E₂ hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres
  match pp with
  | 0 => exact hd2.zpow _
  | (j + 1) =>
      refine isDead_prodList fun w hw ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hd2
      · exact hd2.conj _

include hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **The orbit-norm block `E₂^pc` is dead in the ramified class too.**  Every letter in it is a
`δ₂` or a `σ₂`-power, and `IsDead` is closed under conjugation by an *arbitrary* word — which is
what lets the `σ₂`-conjugators through even though they act nontrivially. -/
theorem isDead_e2W_ram [Finite C] [Finite A] (s' mm pp : ℕ) :
    IsDead ⇑t x y E E₂ (e2W h s' mm pp) := by
  have hd2 := isDead_dW2_ram t x y E E₂ hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres
  have hz := isDead_zW_ram t x y E E₂ hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres pp
  refine isDead_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hd2.conj _
  · refine IsDead.conj (isDead_prodList fun u hu ↦ ?_) _
    rw [orbitNormFactors_map, List.mem_map] at hu
    obtain ⟨j, -, rfl⟩ := hu
    exact hz.conj _

/-! ### The Labute letters and the boundary letters -/

include hxσ hyσ hx2 hy2 hwild in
/-- **The Labute letter `A = x₀⁻¹C₀^{−m}` in the ramified class**: the jet of `x₀⁻¹` alone, with
a base acting by `S₂^{−sm}`.  The `x₂` inside `C₀` is invisible; the `σ₂`-power is not, and that
is exactly what the unramified reading did not have to carry. -/
theorem sLetter_aW_ram (s' mm : ℕ) :
    SLetter t x y E E₂ (aW h s' mm) (-x (coreLetter h 0)) (-y (coreLetter h 0))
      (-((s' * mm : ℕ) : ℤ)) := by
  have hexp : (s' : ℤ) * (-(mm : ℤ)) = -((s' * mm : ℕ) : ℤ) := by push_cast; ring
  have hx0 : TrivJet ⇑t x y E E₂ (.gen (coreLetter h 0)) (x (coreLetter h 0))
      (y (coreLetter h 0)) :=
    ⟨0, triv_gen ⇑t x y E E₂ (coreLetter h 0)
      (mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 0))⟩
  have hg : heisEvalZ ⇑t x y E E₂ (.zpow (c0W h s') (-(mm : ℤ)))
      = heisPure ((t (coreLetter h 2) * sTwist t E ^ (s' : ℤ)) ^ (-(mm : ℤ))) := by
    rw [heisEvalZ_zpow, heisEvalZ_c0W_ram t x y E E₂ hxσ hyσ hx2 hy2 s', ← map_zpow]
  have hk : ∀ v : A, ((t (coreLetter h 2) * sTwist t E ^ (s' : ℤ)) ^ (-(mm : ℤ))) • v
      = (sTwist t E ^ (-((s' * mm : ℕ) : ℤ))) • v := fun v ↦ by
    rw [c0W_zpow_smul t E hwild s' (-(mm : ℤ)), hexp]
  rw [aW]
  exact sLetter_pairPure t x y E E₂ hx0.inv hg hk

include hxσ hyσ hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **The hat Labute letter `Â = δ₀⁻¹Ĉ₀^{−m}`**: the *same* jets and the *same* base action as
`A`, and a different charge — which is exactly what `SLetter` is designed not to record. -/
theorem sLetter_aHatW_ram [Finite C] [Finite A] (s' mm : ℕ) :
    SLetter t x y E E₂ (aHatW h s' mm) (-x (coreLetter h 0)) (-y (coreLetter h 0))
      (-((s' * mm : ℕ) : ℤ)) := by
  have hexp : (s' : ℤ) * (-(mm : ℤ)) = -((s' * mm : ℕ) : ℤ) := by push_cast; ring
  have hd0 := trivJet_dW_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres 0
  have hg : heisEvalZ ⇑t x y E E₂ (.zpow (c0HatW h s') (-(mm : ℤ)))
      = heisPure ((sTwist t E ^ (s' : ℤ)) ^ (-(mm : ℤ))) := by
    rw [heisEvalZ_zpow, heisEvalZ_c0HatW_ram t x y E E₂ hxσ hyσ s', ← map_zpow]
  have hk : ∀ v : A, ((sTwist t E ^ (s' : ℤ)) ^ (-(mm : ℤ))) • v
      = (sTwist t E ^ (-((s' * mm : ℕ) : ℤ))) • v := fun v ↦ by
    rw [← zpow_mul, hexp]
  rw [aHatW]
  exact sLetter_pairPure t x y E E₂ hd0.inv hg hk

include hxσ hyσ hwild in
/-- **The boundary letter `B = x₁σ₂^p`**, in both of the display's two shapes. -/
theorem sLetter_bW_ram (pp : ℕ) :
    SLetter t x y E E₂ (bW h pp) (x (coreLetter h 1)) (y (coreLetter h 1)) (pp : ℤ) := by
  have hx1 : TrivJet ⇑t x y E E₂ (.gen (coreLetter h 1)) (x (coreLetter h 1))
      (y (coreLetter h 1)) :=
    ⟨0, triv_gen ⇑t x y E E₂ (coreLetter h 1)
      (mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 1))⟩
  match pp with
  | 0 =>
      obtain ⟨z, G, hG, hGa⟩ := hx1
      exact ⟨G, z, hG, fun v ↦ by rw [hGa, Nat.cast_zero, zpow_zero, one_smul]⟩
  | (j + 1) =>
      rw [show bW h (j + 1)
        = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (j + 1)] from rfl]
      exact sLetter_pairPure t x y E E₂ hx1
        (heisEvalZ_sig2PowW t x y E E₂ hxσ hyσ (j + 1)) fun _ ↦ rfl

include hxσ hyσ hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **The hat boundary letter `B̂ = δ₁σ₂^p`**: the same jets and base action as `B`. -/
theorem sLetter_bHatW_ram [Finite C] [Finite A] (pp : ℕ) :
    SLetter t x y E E₂ (bHatW h pp) (x (coreLetter h 1)) (y (coreLetter h 1)) (pp : ℤ) := by
  have hd1 := trivJet_dW_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres 1
  match pp with
  | 0 =>
      obtain ⟨z, G, hG, hGa⟩ := hd1
      exact ⟨G, z, hG, fun v ↦ by rw [hGa, Nat.cast_zero, zpow_zero, one_smul]⟩
  | (j + 1) =>
      rw [show bHatW h (j + 1) = PWord.prodList [dW h 1, sig2PowW h (j + 1)] from rfl]
      exact sLetter_pairPure t x y E E₂ hd1
        (heisEvalZ_sig2PowW t x y E E₂ hxσ hyσ (j + 1)) fun _ ↦ rfl

/-! ### The correction block `E₀₁^pc`

The asymmetric conjugator pair `(σ₂^a, σ₂^b)` enters here and nowhere else.  Every letter of the
block is a `δ`, every conjugator is a pure `σ₂`-power, so `TrivJet.conjPure` carries the whole
computation and the block's jets come out as a `S₂`-twisted combination of `d₀` and `d₁`. -/

include hA₂ hwild hτfpf hTodd hresA hresD hres hxσ hyσ in
/-- **`E₀₁^pc = 𝓔(σ₂^a, σ₂^b; δ₀, δ₁)` in the ramified class**: jets twisted by the two
conjugators, base still trivially acting. -/
theorem trivJet_e01W_ram [Finite C] [Finite A] (aa bb : ℕ) :
    TrivJet ⇑t x y E E₂ (e01W h aa bb)
      ((sTwist t E ^ (aa : ℤ))⁻¹ • ((sTwist t E ^ (bb : ℤ))⁻¹ • x (coreLetter h 1)
          + (x (coreLetter h 1) + x (coreLetter h 0))) + x (coreLetter h 0))
      ((sTwist t E ^ (aa : ℤ))⁻¹ • ((sTwist t E ^ (bb : ℤ))⁻¹ • y (coreLetter h 1)
          + (y (coreLetter h 1) + y (coreLetter h 0))) + y (coreLetter h 0)) := by
  have hd := trivJet_dW_ram t x y E E₂ hA₂ hwild hτfpf hTodd hresA hresD hres
  rw [e01W]
  exact (((hd 1).conjPure (heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ (bb : ℤ))).triple (hd 1)
    (hd 0)).conjPure (heisEvalZ_sig2Zpow t x y E E₂ hxσ hyσ (aa : ℤ)) |>.pair (hd 0)

/-! ### The display and the two `D`-commutators -/

include hxσ hyσ in
/-- **Every display is a `σ`-power**: all three constructors wrap `σ` alone, so the letter `D`
denotes a pure lift with a base that commutes with the twist. -/
theorem exists_heisEvalZ_display_pure (η : EtaDisplay) :
    ∃ n : ℤ, heisEvalZ ⇑t x y E E₂ (η.toPWord (n := 2 + 2 * h)) = heisPure (t.σ ^ n) := by
  have hσ : heisEvalZ ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      = heisPure t.σ := heisEvalZ_gen_of_offsets_zero _ _ _ _ _ _ hxσ hyσ
  cases η with
  | one => exact ⟨1, by rw [show (EtaDisplay.one).toPWord = (.gen .sigma) from rfl, hσ, zpow_one]⟩
  | lit k =>
      refine ⟨k, ?_⟩
      rw [show (EtaDisplay.lit k).toPWord = (.zpow (.gen .sigma) k) from rfl, heisEvalZ_zpow, hσ,
        ← map_zpow]
  | hat num den =>
      refine ⟨E (Export.RawSpec.toZhat (.etahat num den)), ?_⟩
      rw [show (EtaDisplay.hat num den).toPWord
        = (.profPow (.gen .sigma) (Export.RawSpec.toZhat (.etahat num den))) from rfl,
        heisEvalZ_profPow, hσ, ← map_zpow]

/-- The commutator of two pure-base lifts is pure. -/
theorem heisPure_commR (g k : C) :
    commR (heisPure (A := A) g) (heisPure k) = heisPure (commR g k) := by
  rw [commR, commR, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]

/-- The commutator of two powers of one group element is trivial. -/
theorem commR_zpow_zpow (P : C) (i j : ℤ) : commR (P ^ i) (P ^ j) = 1 := by
  rw [commR, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add, ← zpow_add,
    show -i + -j + i + j = (0 : ℤ) by ring, zpow_zero]

/-- Commutators read only the two bases' actions. -/
theorem commR_smul_congr {g g' k k' : C} (hg : ∀ v : A, g • v = g' • v)
    (hk : ∀ v : A, k • v = k' • v) (v : A) : commR g k • v = commR g' k' • v := by
  simp only [commR, mul_smul, hg, hk, smul_inv_congr hg, smul_inv_congr hk]

/-- The twist is itself a `σ`-power, so every power of it is. -/
theorem sTwist_zpow (k : ℤ) : sTwist t E ^ k = t.σ ^ (E omega2 * k) := by
  rw [sTwist, ← zpow_mul]

/-- **A `σ₂`-power commutes with a `σ`-power in the action.**  This is what makes the two
`D`-commutators, and the Labute commutator, jet-twisting-free. -/
theorem commR_sTwist_smul {g k : C} (i n : ℤ) (hg : ∀ v : A, g • v = (sTwist t E ^ i) • v)
    (hk : ∀ v : A, k • v = (t.σ ^ n) • v) (v : A) : commR g k • v = v := by
  rw [commR_smul_congr hg hk v, sTwist_zpow, commR_zpow_zpow, one_smul]

/-! ### The three live jets of the linear copy -/

variable {t x y E E₂}

theorem SLetter.smulInv {w : PWord (Generator (2 + 2 * h))} {a : A} {l : ElemDual A} {k : ℤ}
    (hw : SLetter t x y E E₂ w a l k) (v : A) :
    (heisEvalZ ⇑t x y E E₂ w).g⁻¹ • v = (sTwist t E ^ (-k)) • v := by
  rw [smul_inv_congr hw.smul v, ← zpow_neg]

variable (t x y E E₂)

include hxσ hyσ hx2 hy2 hA₂ hwild in
/-- **The Labute square's jet.**  Not zero on the ramified reading: it is the coboundary
`(1 + S₂^{−sm})·d₀`. -/
theorem heisA_aSq_ram (s' mm : ℕ) :
    (heisEvalZ ⇑t x y E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ))).a
      = x (coreLetter h 0)
        + (sTwist t E ^ (-((s' * mm : ℕ) : ℤ))) • x (coreLetter h 0) := by
  have hneg : ∀ a : A, -a = a := fun a ↦ by rw [neg_eq_iff_add_eq_zero]; exact hA₂ a
  have hA := sLetter_aW_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild s' mm
  rw [heisEvalZ_zpow, zpow_natCast, pow_two, HeisLift.mul_a, hA.aEq, hA.smul, smul_neg, hneg,
    hneg]

include hxσ hyσ hx2 hy2 hwild in
/-- The Labute square's base acts by `S₂^{−2sm}` — the twist the balancing power `C₀^{2^α}` is
there to undo. -/
theorem heisG_aSq_ram (s' mm : ℕ) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ))).g • v
      = (sTwist t E ^ (-(2 * ((s' * mm : ℕ) : ℤ)))) • v := by
  have hA := sLetter_aW_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild s' mm
  rw [heisEvalZ_zpow, zpow_natCast, pow_two, HeisLift.mul_g, mul_smul, hA.smul, hA.smul,
    zpow_smul_zpow_smul, show -((s' * mm : ℕ) : ℤ) + -((s' * mm : ℕ) : ℤ)
      = -(2 * ((s' * mm : ℕ) : ℤ)) from by ring]

include hxσ hyσ hx2 hy2 hA₂ hwild in
/-- **The Labute commutator's jet**, from the fully general law: four `S₂`-twisted atoms, and the
`p`-shift of `B` visible in two of them. -/
theorem heisA_commAB_ram (s' mm pp : ℕ) :
    (heisEvalZ ⇑t x y E E₂ (.comm (aW h s' mm) (bW h pp))).a
      = (sTwist t E ^ ((s' * mm : ℕ) : ℤ)) • x (coreLetter h 0)
        + (sTwist t E ^ (((s' * mm : ℕ) : ℤ) - (pp : ℤ))) • x (coreLetter h 1)
        + (sTwist t E ^ (((s' * mm : ℕ) : ℤ) - (pp : ℤ))) • x (coreLetter h 0)
        + (sTwist t E ^ (-(pp : ℤ))) • x (coreLetter h 1) := by
  have hneg : ∀ a : A, -a = a := fun a ↦ by rw [neg_eq_iff_add_eq_zero]; exact hA₂ a
  have hA := sLetter_aW_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild s' mm
  have hB := sLetter_bW_ram t x y E E₂ hxσ hyσ hwild pp
  rw [heisEvalZ_comm, heisCommR_general]
  simp only [hA.aEq, hB.aEq, hA.smul, hA.smulInv, hB.smulInv, hneg, neg_neg,
    zpow_smul_zpow_smul, sub_eq_add_neg]
  rw [show ((s' * mm : ℕ) : ℤ) + (-(pp : ℤ) + -((s' * mm : ℕ) : ℤ)) = -(pp : ℤ) from by ring]

include hxσ hyσ hx2 hy2 hwild in
/-- The Labute commutator's base acts trivially: both entries act by powers of `σ`. -/
theorem heisG_commAB_ram (s' mm pp : ℕ) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (.comm (aW h s' mm) (bW h pp))).g • v = v := by
  have hA := sLetter_aW_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild s' mm
  have hB := sLetter_bW_ram t x y E E₂ hxσ hyσ hwild pp
  rw [heisEvalZ_comm, heisCommR_general]
  exact commR_sTwist_smul t E _ (E omega2 * (pp : ℤ)) hA.smul
    (fun w ↦ by rw [hB.smul, sTwist_zpow]) v

/-! ## The two copies, and the assembled row -/

include hxσ hyσ hx2 hy2 hxτ hyτ hA₂ hwild hτfpf hTodd hresA hresD hres in
/-- **The linear copy is jet-zero on ramified normal offsets.**

`A²` contributes `(1+S₂^{−sm})d₀`, `[A,B]` four `S₂`-twisted atoms, `E₀₁^pc` four more, and the
balancing power `C₀^{2^α}` — which acts by `S₂^{s·2^α}` — lines the last two up.  With `α ≥ 1`
that exponent is `2sm` and all twelve atoms cancel in six pairs.  The two `[·,D]` commutators and
the orbit-norm block contribute nothing at all: the first two act trivially and the third is
dead. -/
theorem heisA_mpcLinW_ram [Finite C] [Finite A] {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ)
    (η : EtaDisplay) : (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h)).a = 0 := by
  obtain ⟨n, hD⟩ := exists_heisEvalZ_display_pure t x y E E₂ hxσ hyσ η
  have hm2 : (2 : ℕ) * m α = 2 ^ α := by
    rw [m, ← pow_succ']
    congr 1
    omega
  have hbal : ((s r : ℕ) : ℤ) * ((2 ^ α : ℕ) : ℤ) = 2 * ((s r * m α : ℕ) : ℤ) := by
    rw [← hm2]
    push_cast
    ring
  have hF3 : heisEvalZ ⇑t x y E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ))
      = heisPure ((t (coreLetter h 2) * sTwist t E ^ ((s r : ℕ) : ℤ)) ^ ((2 ^ α : ℕ) : ℤ)) := by
    rw [heisEvalZ_zpow, heisEvalZ_c0W_ram t x y E E₂ hxσ hyσ hx2 hy2 (s r), ← map_zpow]
  have hF4 : heisEvalZ ⇑t x y E E₂ (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))
      = heisPure (commR (t (coreLetter h 2) * sTwist t E ^ ((s r : ℕ) : ℤ)) (t.σ ^ n)) := by
    rw [heisEvalZ_comm, heisEvalZ_c0W_ram t x y E E₂ hxσ hyσ hx2 hy2 (s r), hD, heisPure_commR]
  have hF3a : (heisEvalZ ⇑t x y E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ))).a = 0 := by
    rw [hF3, heisPure_a]
  have hF4a : (heisEvalZ ⇑t x y E E₂
      (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))).a = 0 := by
    rw [hF4, heisPure_a]
  have hF3g : ∀ v : A, (heisEvalZ ⇑t x y E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ))).g • v
      = (sTwist t E ^ (2 * ((s r * m α : ℕ) : ℤ))) • v := fun v ↦ by
    rw [hF3, heisPure_g, c0W_zpow_smul t E hwild (s r), hbal]
  have hF4g : ∀ v : A, (heisEvalZ ⇑t x y E E₂
      (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))).g • v = v := fun v ↦ by
    rw [hF4, heisPure_g]
    exact commR_sTwist_smul t E _ n (c0W_smul_eq t E hwild (s r)) (fun _ ↦ rfl) v
  have hF5 := trivJet_e01W_ram t x y E E₂ hxσ hyσ hA₂ hwild hτfpf hTodd hresA hresD hres
    (pp + s r * m α) (s r * m α)
  have hF6 : (heisEvalZ ⇑t x y E E₂ (e2W h (s r) (m α) pp)).a = 0 :=
    (isDead_e2W_ram t x y E E₂ hxτ hyτ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres
      (s r) (m α) pp).jetZero.1
  rw [mpcLinW, linFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul, heisEvalZ_one,
    HeisLift.mul_a, HeisLift.one_a, smul_zero, add_zero, zero_add, Nat.cast_add,
    hF6, hF5.aEq, hF3a, hF4a, hF3g, hF4g,
    heisA_aSq_ram t x y E E₂ hxσ hyσ hx2 hy2 hA₂ hwild,
    heisG_aSq_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild,
    heisA_commAB_ram t x y E E₂ hxσ hyσ hx2 hy2 hA₂ hwild,
    heisG_commAB_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild]
  exact linJet_cancel hA₂ (sTwist t E) _ _ _ _

include hxσ hyσ hx2 hy2 hA₂ hwild hτfpf hTodd hresA hresD hres hxτ hyτ in
/-- **The linear and hat copies agree at second order.**  Factor by factor: `A ~ Â` and `B ~ B̂`
and `C₀ ~ Ĉ₀` at first order, and `SameJet.sq`/`SameJet.commR` say that is enough for the four
live factors; `Ê₀₁^pc` *is* `E₀₁^pc`; and the linear copy's one unmatched factor `E₂^pc` is
dead. -/
theorem sameVal_lin_hat [Finite C] [Finite A] {α : ℕ} (r pp : ℕ) (η : EtaDisplay) :
    SameVal (heisEvalZ ⇑t x y E E₂ (mpcLinW α r pp η h))
      (heisEvalZ ⇑t x y E E₂ (mpcHatW α r pp η h)) := by
  have hAj := (sLetter_aW_ram t x y E E₂ hxσ hyσ hx2 hy2 hwild (s r) (m α)).sameJet
    (sLetter_aHatW_ram t x y E E₂ hxσ hyσ hA₂ hwild hτfpf hTodd hresA hresD hres (s r) (m α))
  have hBj := (sLetter_bW_ram t x y E E₂ hxσ hyσ hwild pp).sameJet
    (sLetter_bHatW_ram t x y E E₂ hxσ hyσ hA₂ hwild hτfpf hTodd hresA hresD hres pp)
  have hCj : SameJet (heisEvalZ ⇑t x y E E₂ (c0W h (s r)))
      (heisEvalZ ⇑t x y E E₂ (c0HatW h (s r))) := by
    rw [heisEvalZ_c0W_ram t x y E E₂ hxσ hyσ hx2 hy2 (s r),
      heisEvalZ_c0HatW_ram t x y E E₂ hxσ hyσ (s r)]
    exact ⟨rfl, rfl, c0W_smul_eq t E hwild (s r)⟩
  have h1 : SameVal (heisEvalZ ⇑t x y E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ)))
      (heisEvalZ ⇑t x y E E₂ (.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ))) := by
    rw [heisEvalZ_zpow, heisEvalZ_zpow, zpow_natCast, zpow_natCast, pow_two, pow_two]
    exact hAj.sq
  have h2 : SameVal (heisEvalZ ⇑t x y E E₂ (.comm (aW h (s r) (m α)) (bW h pp)))
      (heisEvalZ ⇑t x y E E₂ (.comm (aHatW h (s r) (m α)) (bHatW h pp))) := by
    rw [heisEvalZ_comm, heisEvalZ_comm]
    exact hAj.commR hBj
  have h3 : SameVal (heisEvalZ ⇑t x y E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ)))
      (heisEvalZ ⇑t x y E E₂ (.zpow (c0HatW h (s r)) ((2 ^ α : ℕ) : ℤ))) := by
    rw [heisEvalZ_zpow, heisEvalZ_zpow, heisEvalZ_c0W_ram t x y E E₂ hxσ hyσ hx2 hy2 (s r),
      heisEvalZ_c0HatW_ram t x y E E₂ hxσ hyσ (s r), ← map_zpow, ← map_zpow]
    exact ⟨rfl, rfl, rfl, fun v ↦ smul_zpow_congr (c0W_smul_eq t E hwild (s r)) _ v⟩
  have h4 : SameVal (heisEvalZ ⇑t x y E E₂ (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h))))
      (heisEvalZ ⇑t x y E E₂ (.comm (c0HatW h (s r)) (η.toPWord (n := 2 + 2 * h)))) := by
    rw [heisEvalZ_comm, heisEvalZ_comm]
    exact hCj.commR (SameJet.rfl' _)
  have h6 : SameVal (heisEvalZ ⇑t x y E E₂ (e2W h (s r) (m α) pp) * 1) 1 := by
    rw [mul_one]
    exact sameValOne_of_isDead (isDead_e2W_ram t x y E E₂ hxτ hyτ hx2 hy2 hA₂ hwild hτfpf
      hTodd hresA hresD hres (s r) (m α) pp)
  rw [mpcLinW, mpcHatW, linFactors, hatFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul, heisEvalZ_one]
  exact h1.mul (h2.mul (h3.mul (h4.mul ((SameVal.rfl' _).mul h6))))

end Letters

end

end GQ2.Dyadic.MpcRam
