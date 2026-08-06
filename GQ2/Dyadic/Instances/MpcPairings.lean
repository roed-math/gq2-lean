/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Instances.MpcUnramifiedBranch

/-!
# The second-order pairings of the corrected procyclic-`M` row

`MpcUnramifiedBranch.uniformPushedHsimp_of_pairings` closes the procyclic-`M` uniform pushed
residue modulo three second-order statements.  This file computes the procyclic-`M` word's
**second-order (Stokes) row on even normal offsets** and discharges the two that live there.

## The mechanism: everything but three factors is dead

On even normal coordinates the offsets vanish at `σ`, `τ` **and** `x₂`
(`evenNormal_sigma`, `evenNormal_tau`, `evenNormal_coreLetter` at `i = 2`).  That makes a large
part of the thirteen-factor word *second-order invisible*:

* every `σ`-carrying letter — `σ₂ = σ^{ω₂}`, its powers, `Ĉ₀`, and the `η̂`-display `D` — has
  **vanishing offsets**, so it denotes a pure-base lift `⟨0,0,0,g⟩` (`heisPure`);
* on the unramified branch every `δ`-letter is second-order **trivial**
  (`Certificates.MCompact.heisF_deltaCert_trivial`, which is exactly the `x_τ = y_τ = 0`,
  `e ≡ 1 (mod 4)` statement) and has a trivially-acting base;
* `x₂` itself is pure, so `C₀ = x₂σ₂^s` is;
* and the `S₂`-triviality of a simple unramified coefficient makes every one of those bases act
  trivially.

The predicate `IsDead` below packages "pure lift with a trivially-acting base"; it is closed
under products, inverses, `ℤ`- and profinite powers, conjugation by an **arbitrary** lift and
commutation with an arbitrary lift on the left.  Only three factors of `R_{M,pc}` escape it:

```
A² ↦ y₀(x₀),   [A,B] ↦ y₀(x₁) + y₁(x₀),   H_h ↦ Σ_j planes,
```

so the row is the compact core Gram `((1,1),(1,0))` plus the `h` hyperbolic handle planes —
the same matrix `heisEta1_mCompactFam_normal` produces, as the shape correction predicted.

## What this file discharges

* `MProcyclicExact.unramifiedNormalPairingIsCompact` — the generic unramified sub-branch's
  second-order residue, unconditionally in the coefficient;
* `MProcyclicExact.ramifiedNormalPairingSeparates` is **not** here: see the module note at the
  end of the file for the precise obstruction (the ramified reading loses `hS₂`, so `B = x₁σ₂^p`
  and `A = x₀⁻¹C₀^{−m}` both acquire moving bases and the commutator law of `EvenHeisPure` no
  longer applies on either side).

The two-copy cancellation of WMP-c is *not* used: on these offsets the hat copy is dead outright,
one factor at a time, which is stronger and needs no `Sh_M` transport.
-/

namespace GQ2.Dyadic.MProcyclicNormal

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count

/-! ## Two pure-lift rules the `EvenHeisPure` toolkit is missing -/

section PureRules

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- `[x,y] = x⁻¹·x^y`, the regrouping that turns a commutator into a conjugate. -/
theorem commR_eq_inv_mul_conjR {G : Type*} [Group G] (u v : G) :
    commR u v = u⁻¹ * conjR u v := by
  rw [commR, conjR, mul_assoc, mul_assoc, mul_assoc]

/-- **Conjugation by a pure-base lift** twists both jets by `S⁻¹` and leaves the central charge
alone — no hypothesis at all on the conjugand's base.  This is what lets a `σ₂`-conjugated
`δ`-letter be handled on a ramified coefficient, where `heisConjR_of_trivial` does not apply. -/
theorem heisConjR_pure_right (P : HeisLift A C) (S : C) :
    conjR P (heisPure (A := A) S) = ⟨S⁻¹ • P.a, S⁻¹ • P.l, P.z, conjR P.g S⟩ := by
  rw [conjR, ← map_inv, heisPure_mul]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show S⁻¹ • P.a + (S⁻¹ * P.g) • (0 : A) = _
    rw [smul_zero, add_zero]
  · show S⁻¹ • P.l + (S⁻¹ * P.g) • (0 : ElemDual A) = _
    rw [smul_zero, add_zero]
  · show P.z + 0 + (S⁻¹ • P.l) ((S⁻¹ * P.g) • (0 : A)) = _
    rw [smul_zero, map_zero, add_zero, add_zero]
  · show S⁻¹ * P.g * S = conjR P.g S
    rw [conjR, mul_assoc]

/-- **Conjugating a trivially-acting pure lift by an arbitrary lift keeps it pure.**  Both
`s`-offsets enter `heisConjR_of_trivial` only through the mixed pairing, and each of those
pairings has a zero slot. -/
theorem heisConjR_pure_left {G : C} (hG : ∀ a : A, G • a = a) (Q : HeisLift A C) :
    conjR (heisPure (A := A) G) Q = heisPure (conjR G Q.g) := by
  rw [heisConjR_of_trivial _ _ hG]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show Q.g⁻¹ • (0 : A) = 0
    rw [smul_zero]
  · show Q.g⁻¹ • (0 : ElemDual A) = 0
    rw [smul_zero]
  · show (0 : ZMod 2) + Q.l (0 : A) + (0 : ElemDual A) Q.a = 0
    rw [map_zero, ElemDual.zero_apply, add_zero, add_zero]

/-- **The commutator of a trivially-acting pure lift with an arbitrary lift is pure.**  Both
jets cancel against the conjugate's, and the central charge never appears — so a factor like
`[C₀, D]`, whose left entry is pure and whose right entry is the `η̂`-display with an arbitrary
base, contributes nothing at second order. -/
theorem heisCommR_pure_left {G : C} (hG : ∀ a : A, G • a = a) (Q : HeisLift A C) :
    commR (heisPure (A := A) G) Q = heisPure (commR G Q.g) := by
  rw [commR_eq_inv_mul_conjR, heisConjR_pure_left hG, ← map_inv, ← map_mul,
    commR_eq_inv_mul_conjR]

/-- The base of a commutator with a trivially-acting entry acts trivially. -/
theorem commR_smul_of_trivial_left {G K : C} (hG : ∀ a : A, G • a = a) (a : A) :
    commR G K • a = a := by
  have hGi : ∀ b : A, G⁻¹ • b = b := fun b ↦ inv_smul_eq_iff.mpr (hG b).symm
  rw [commR, mul_smul, mul_smul, mul_smul, hG, inv_smul_smul, hGi]

end PureRules

/-! ## Second-order dead words

A word is **dead** at a given offset pair when it denotes a pure-base lift whose base acts
trivially — equivalently, when it lies in `Certificates.MCompact.heisTrivial` *and* its base is
in `trivAct`.  Dead words contribute neither jet nor central charge to any product they sit in,
and the class is closed under every `PWord` constructor the procyclic-`M` word uses. -/

section Dead

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Second-order dead**: the word denotes `⟨0, 0, 0, G⟩` with `G` acting trivially. -/
def IsDead (w : PWord X) : Prop :=
  ∃ G : C, heisEvalZ μ x y E E₂ w = heisPure G ∧ ∀ a : A, G • a = a

variable {μ x y E E₂}

theorem IsDead.jetZero {w : PWord X} (hw : IsDead μ x y E E₂ w) :
    heisEvalZ μ x y E E₂ w ∈ heisJetZero A C := by
  obtain ⟨G, hG, -⟩ := hw
  rw [hG]
  exact heisPure_mem_jetZero G

theorem IsDead.z {w : PWord X} (hw : IsDead μ x y E E₂ w) :
    (heisEvalZ μ x y E E₂ w).z = 0 := by
  obtain ⟨G, hG, -⟩ := hw
  rw [hG]
  rfl

theorem IsDead.smul {w : PWord X} (hw : IsDead μ x y E E₂ w) (a : A) :
    (heisEvalZ μ x y E E₂ w).g • a = a := by
  obtain ⟨G, hG, hGa⟩ := hw
  rw [hG]
  exact hGa a

variable (μ x y E E₂)

theorem isDead_one : IsDead μ x y E E₂ (.one : PWord X) :=
  ⟨1, rfl, fun a ↦ one_smul _ a⟩

theorem isDead_gen {i : X} (hx : x i = 0) (hy : y i = 0) (ht : ∀ a : A, μ i • a = a) :
    IsDead μ x y E E₂ (.gen i) :=
  ⟨μ i, heisEvalZ_gen_of_offsets_zero μ x y E E₂ i hx hy, ht⟩

variable {μ x y E E₂}

theorem IsDead.mul {u v : PWord X} (hu : IsDead μ x y E E₂ u) (hv : IsDead μ x y E E₂ v) :
    IsDead μ x y E E₂ (.mul u v) := by
  obtain ⟨G, hG, hGa⟩ := hu
  obtain ⟨H, hH, hHa⟩ := hv
  exact ⟨G * H, by rw [heisEvalZ_mul, hG, hH, map_mul], fun a ↦ by rw [mul_smul, hHa, hGa]⟩

theorem IsDead.inv {u : PWord X} (hu : IsDead μ x y E E₂ u) : IsDead μ x y E E₂ (.inv u) := by
  obtain ⟨G, hG, hGa⟩ := hu
  exact ⟨G⁻¹, by rw [heisEvalZ_inv, hG, map_inv],
    fun a ↦ inv_smul_eq_iff.mpr (hGa a).symm⟩

theorem IsDead.zpow {u : PWord X} (hu : IsDead μ x y E E₂ u) (k : ℤ) :
    IsDead μ x y E E₂ (.zpow u k) := by
  obtain ⟨G, hG, hGa⟩ := hu
  exact ⟨G ^ k, by rw [heisEvalZ_zpow, hG, map_zpow],
    fun a ↦ mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hGa) k) a⟩

theorem IsDead.profPow {u : PWord X} (hu : IsDead μ x y E E₂ u) (γ : Zhat) :
    IsDead μ x y E E₂ (.profPow u γ) := by
  obtain ⟨G, hG, hGa⟩ := hu
  exact ⟨G ^ E γ, by rw [heisEvalZ_profPow, hG, map_zpow],
    fun a ↦ mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hGa) _) a⟩

/-- Conjugating a dead word by an **arbitrary** word leaves it dead: both jets and the charge
are already zero, and the base only gets conjugated. -/
theorem IsDead.conj {u : PWord X} (hu : IsDead μ x y E E₂ u) (g : PWord X) :
    IsDead μ x y E E₂ (.conj u g) := by
  obtain ⟨G, hG, hGa⟩ := hu
  refine ⟨conjR G (heisEvalZ μ x y E E₂ g).g, ?_, ?_⟩
  · rw [heisEvalZ_conj, hG, heisConjR_pure_left hGa]
  · exact fun a ↦ mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr hGa) _) a

/-- Commuting a dead word with an **arbitrary** word on the left leaves it dead. -/
theorem IsDead.commLeft {u : PWord X} (hu : IsDead μ x y E E₂ u) (v : PWord X) :
    IsDead μ x y E E₂ (.comm u v) := by
  obtain ⟨G, hG, hGa⟩ := hu
  refine ⟨commR G (heisEvalZ μ x y E E₂ v).g, ?_, ?_⟩
  · rw [heisEvalZ_comm, hG, heisCommR_pure_left hGa]
  · exact fun a ↦ commR_smul_of_trivial_left hGa a

theorem isDead_prodList {l : List (PWord X)} (hl : ∀ w ∈ l, IsDead μ x y E E₂ w) :
    IsDead μ x y E E₂ (PWord.prodList l) := by
  induction l with
  | nil => exact isDead_one μ x y E E₂
  | cons w ws ih =>
      rw [PWord.prodList_cons]
      exact (hl w List.mem_cons_self).mul (ih fun u hu ↦ hl u (List.mem_cons_of_mem _ hu))

/-- The compact-`M` file's `heisTrivial` membership, plus a trivially-acting base, *is*
deadness — a second-order trivial lift is `⟨0,0,0,g⟩` on the nose. -/
theorem isDead_of_heisTrivial {w : PWord X}
    (hw : heisEvalZ μ x y E E₂ w ∈ Certificates.MCompact.heisTrivial A C)
    (hg : ∀ a : A, (heisEvalZ μ x y E E₂ w).g • a = a) : IsDead μ x y E E₂ w :=
  ⟨_, HeisLift.ext hw.1 hw.2.1 hw.2.2 rfl, hg⟩

end Dead

/-! ## The procyclic-`M` letters on even normal offsets, unramified reading -/

section Letters

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- With the offsets vanishing at `σ`, the `σ₂`-atom is the pure lift of the resolved
`2`-primary power — **no** hypothesis on the resolver or on how `σ₂` acts. -/
theorem heisEvalZ_sigma2W_pure (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    heisEvalZ ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h)))
      = heisPure (t.σ ^ E omega2) := by
  have hgen : heisEvalZ ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      = heisPure t.σ := heisEvalZ_gen_of_offsets_zero _ _ _ _ _ _ hxσ hyσ
  show heisEvalZ ⇑t x y E E₂ (.profPow (.gen .sigma) omega2) = _
  rw [heisEvalZ_profPow, hgen, ← map_zpow]

variable (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hxτ : x .tau = 0) (hyτ : y .tau = 0)
  (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0)
  (hA₂ : ∀ a : A, a + a = 0)
  (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
  (hS₂ : ∀ v : A, (t.σ ^ E omega2) • v = v)

include hxσ hyσ hS₂ in
theorem isDead_sigma2W : IsDead ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h))) :=
  ⟨_, heisEvalZ_sigma2W_pure t x y E E₂ hxσ hyσ, hS₂⟩

include hxσ hyσ hS₂ in
theorem isDead_sig2PowW (k : ℕ) : IsDead ⇑t x y E E₂ (sig2PowW h k) := by
  match k with
  | 0 => exact (isDead_sigma2W t x y E E₂ hxσ hyσ hS₂).zpow _
  | 1 => exact isDead_sigma2W t x y E E₂ hxσ hyσ hS₂
  | (j + 2) => exact (isDead_sigma2W t x y E E₂ hxσ hyσ hS₂).zpow _

include hx2 hy2 hwild in
theorem isDead_x2 : IsDead ⇑t x y E E₂ (.gen (coreLetter h 2)) :=
  isDead_gen _ _ _ _ _ hx2 hy2 (mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 2))

include hxσ hyσ hx2 hy2 hwild hS₂ in
theorem isDead_c0W (s' : ℕ) : IsDead ⇑t x y E E₂ (c0W h s') := by
  refine isDead_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact isDead_x2 t x y E E₂ hx2 hy2 hwild
  · exact (isDead_sigma2W t x y E E₂ hxσ hyσ hS₂).zpow _

include hxσ hyσ hS₂ in
theorem isDead_c0HatW (s' : ℕ) : IsDead ⇑t x y E E₂ (c0HatW h s') :=
  (isDead_sigma2W t x y E E₂ hxσ hyσ hS₂).zpow _

variable {e : ℕ}

include hxτ hyτ hA₂ hwild hτ in
/-- **The `δ`-letters are dead at the unramified reading on `τ`-free offsets** — the compact-`M`
statement `heisF_deltaCert_trivial`, transported through `dW = deltaCert` (which is `rfl`). -/
theorem isDead_dW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (i : Fin 3) :
    IsDead ⇑t x y E E₂ (dW h i) := by
  rw [dW_eq_deltaCert]
  exact isDead_of_heisTrivial
    (Certificates.MCompact.heisF_deltaCert_trivial t x y E E₂ hA₂ hwild hτ hxτ hyτ hE he i)
    (Certificates.MCompact.heisF_deltaCert_trivAct t x y E E₂ hwild hτ i)

include hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ in
theorem isDead_aHatW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (s' mm : ℕ) :
    IsDead ⇑t x y E E₂ (aHatW h s' mm) := by
  refine isDead_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact (isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he 0).inv
  · exact (isDead_c0HatW t x y E E₂ hxσ hyσ hS₂ s').zpow _

include hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ in
theorem isDead_bHatW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (pp : ℕ) :
    IsDead ⇑t x y E E₂ (bHatW h pp) := by
  match pp with
  | 0 => exact isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he 1
  | (j + 1) =>
      refine isDead_prodList fun w hw ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he 1
      · exact isDead_sig2PowW t x y E E₂ hxσ hyσ hS₂ _

include hxτ hyτ hA₂ hwild hτ in
theorem isDead_e01W (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (aa bb : ℕ) :
    IsDead ⇑t x y E E₂ (e01W h aa bb) := by
  have hd := isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  refine isDead_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · refine IsDead.conj (isDead_prodList fun u hu ↦ ?_) _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact (hd 1).conj _
    · exact hd 1
    · exact hd 0
  · exact hd 0

include hxτ hyτ hA₂ hwild hτ in
theorem isDead_zW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (pp : ℕ) :
    IsDead ⇑t x y E E₂ (zW h pp) := by
  have hd := isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  match pp with
  | 0 => exact (hd 2).zpow _
  | (j + 1) =>
      refine isDead_prodList fun w hw ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hd 2
      · exact (hd 2).conj _

include hxτ hyτ hA₂ hwild hτ in
theorem isDead_e2W (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (s' mm pp : ℕ) :
    IsDead ⇑t x y E E₂ (e2W h s' mm pp) := by
  have hd := isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  have hz := isDead_zW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he pp
  refine isDead_prodList fun w hw ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hd 2).conj _
  · refine IsDead.conj (isDead_prodList fun u hu ↦ ?_) _
    rw [orbitNormFactors_map, List.mem_map] at hu
    obtain ⟨j, -, rfl⟩ := hu
    exact hz.conj _

include hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ in
/-- **The whole hat copy is dead** on even normal offsets: `Â`, `B̂`, `Ĉ₀` and `Ê₀₁` are, and
`heisTrivial` is closed under squares, commutators and powers. -/
theorem isDead_mpcHatW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (α r pp : ℕ)
    (η : EtaDisplay) : IsDead ⇑t x y E E₂ (mpcHatW α r pp η h) := by
  refine isDead_prodList fun w hw ↦ ?_
  simp only [hatFactors, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact (isDead_aHatW t x y E E₂ hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ hE he _ _).zpow _
  · exact (isDead_aHatW t x y E E₂ hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ hE he _ _).commLeft _
  · exact (isDead_c0HatW t x y E E₂ hxσ hyσ hS₂ _).zpow _
  · exact (isDead_c0HatW t x y E E₂ hxσ hyσ hS₂ _).commLeft _
  · exact isDead_e01W t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he _ _

end Letters

end

end GQ2.Dyadic.MProcyclicNormal
