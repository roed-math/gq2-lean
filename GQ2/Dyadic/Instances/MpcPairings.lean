/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Instances.EvenScalarSeparation
import GQ2.Dyadic.Instances.MpcUnramifiedBranch
import GQ2.Dyadic.Instances.NpcUnramifiedScalar

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

## The scalar reading

The scalar sub-branch keeps `x_σ` and `y_σ` free, so `IsDead` is too strong there; `Triv w a l z`
records the full trivial-base value instead, with the same closure calculus.  The `δ`-letters are
still dead (that needs only `x_τ = y_τ = 0`), so `E₀₁^pc`, `E₂^pc` and the plus block are still
silent, and — because `m = 2^{α−1}` and `C(2^α,2)` are even for `α ≥ 2` — so is the **entire hat
copy**.  What survives is

```
y₀(x₀) ⊕ (y₀(x₁) + y₁(x₀)) ⊕ p·(x₀,x_σ) ⊕ n_η·(x₂,x_σ) ⊕ Σ_j planes,
```

the compact scalar core plus two `σ`-hyperbolic planes with the conjugator exponents as
coefficients.  Left nondegeneracy needs `n_η` **odd** and nothing else — the exact analogue of
the procyclic-`N` row's unit hypothesis, and for the same reason: at an even `n_η` the `(a_σ,x₂)`
plane collapses and `(0,0,0,d₂,0)` is a left kernel vector.

## What this file discharges

* `MProcyclicExact.unramifiedNormalPairingIsCompact` — the generic unramified sub-branch's
  second-order residue, unconditionally in `(α, r, p, η, h, q)` and in the coefficient;
* `MProcyclicExact.scalarActionImageStokes_of_oddJet` — the scalar sub-branch's, for `α ≥ 2`
  and every display with an odd second-order jet, hence `scalarActionImageStokes_one` (the
  `η = 1` row, i.e. merge gate 9's: `ℚ₂(√−10)`, `ℚ₂(√10)`, the one-handle instance) and
  `scalarActionImageStokes_lit` unconditionally;
* hence `MProcyclicExact.uniformPushedHsimp_of_ramified_one`, the `η = 1` row's uniform pushed
  residue on the **single** remaining input.

`MProcyclicExact.RamifiedNormalPairingSeparates` is **not** here.  The obstruction is precise:
on the ramified reading `hS₂` is gone, so `A = x₀⁻¹C₀^{−m}` acts by `S₂^{−sm}` and
`B = x₁σ₂^p` by `S₂^{p}` — neither base is trivial, and `EvenHeisPure`'s one-sided commutator
law `heisCommR_of_trivial_right` (which is what carries the compact-`M` ramified row) needs the
*right* factor's base trivial.  A fully general commutator law is needed first; its central
value is

```
λ(a) + μ(b) + λ(k⁻¹b) + λ(k⁻¹a) + μ(a) + λ(k⁻¹gb) + μ(gb) + λ(gb)
```

for `p = (a,λ,z,g)`, `r = (b,μ,w,k)` in characteristic two, which specializes correctly to
`heisCommR_of_trivial_right` at `k = 1`.

The two-copy cancellation of WMP-c is *not* used anywhere here: on both readings the hat copy is
silent factor by factor, which is stronger and needs no `Sh_M` transport.
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

/-! ### Trivial-base values

On the **scalar** branch every letter's base acts trivially, but the `σ`-offsets no longer
vanish, so `IsDead` is too strong.  `Triv w a l z` records the full second-order value of a word
with a trivially-acting base; it is closed under every constructor by the trivial-base laws of
`Word/Stokes.lean`, and `IsDead w ↔ Triv w 0 0 0`. -/

variable (μ x y E E₂)

/-- **The trivial-base second-order value**: jets `a`, `l`, charge `z`, trivially-acting base. -/
def Triv (w : PWord X) (a : A) (l : ElemDual A) (z : ZMod 2) : Prop :=
  ∃ G : C, heisEvalZ μ x y E E₂ w = ⟨a, l, z, G⟩ ∧ ∀ v : A, G • v = v

variable {μ x y E E₂}

theorem IsDead.triv {w : PWord X} (hw : IsDead μ x y E E₂ w) :
    Triv μ x y E E₂ w 0 0 0 := hw

theorem Triv.isDead {w : PWord X} (hw : Triv μ x y E E₂ w 0 0 0) :
    IsDead μ x y E E₂ w := hw

theorem Triv.zEq {w : PWord X} {a : A} {l : ElemDual A} {z : ZMod 2}
    (hw : Triv μ x y E E₂ w a l z) : (heisEvalZ μ x y E E₂ w).z = z := by
  obtain ⟨G, hG, -⟩ := hw
  rw [hG]

theorem Triv.jetZero {w : PWord X} {z : ZMod 2} (hw : Triv μ x y E E₂ w 0 0 z) :
    heisEvalZ μ x y E E₂ w ∈ heisJetZero A C := by
  obtain ⟨G, hG, -⟩ := hw
  rw [hG]
  exact ⟨rfl, rfl⟩

variable (μ x y E E₂)

theorem triv_one : Triv μ x y E E₂ (.one : PWord X) 0 0 0 := isDead_one μ x y E E₂

theorem triv_gen (i : X) (ht : ∀ v : A, μ i • v = v) :
    Triv μ x y E E₂ (.gen i) (x i) (y i) 0 := ⟨μ i, rfl, ht⟩

variable {μ x y E E₂}

theorem Triv.mul {u v : PWord X} {a b : A} {l m : ElemDual A} {z w : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (hv : Triv μ x y E E₂ v b m w) :
    Triv μ x y E E₂ (.mul u v) (a + b) (l + m) (z + w + l b) := by
  obtain ⟨G, hG, hGa⟩ := hu
  obtain ⟨H, hH, hHa⟩ := hv
  exact ⟨G * H, by rw [heisEvalZ_mul, hG, hH, heisMul_of_trivial_left _ _ hGa],
    fun c ↦ by rw [mul_smul, hHa, hGa]⟩

theorem Triv.inv {u : PWord X} {a : A} {l : ElemDual A} {z : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) : Triv μ x y E E₂ (.inv u) (-a) (-l) (z + l a) := by
  obtain ⟨G, hG, hGa⟩ := hu
  have hGi : ∀ c : A, G⁻¹ • c = c := fun c ↦ inv_smul_eq_iff.mpr (hGa c).symm
  refine ⟨G⁻¹, ?_, hGi⟩
  rw [heisEvalZ_inv, hG]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -(G⁻¹ • a) = _
    rw [hGi]
  · show -(G⁻¹ • l) = _
    rw [smul_elemDual_of_trivial hGi]
  · rfl

theorem Triv.npow {u : PWord X} {a : A} {l : ElemDual A} {z : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (k : ℕ) :
    Triv μ x y E E₂ (.zpow u (k : ℤ)) (k • a) (k • l) (k • z + (k.choose 2) • l a) := by
  obtain ⟨G, hG, hGa⟩ := hu
  exact ⟨G ^ k, by rw [heisEvalZ_zpow, hG, zpow_natCast, heisPow_of_trivial _ hGa k],
    fun c ↦ mem_trivAct.mp (pow_mem (mem_trivAct.mpr hGa) k) c⟩

theorem Triv.zpowNeg {u : PWord X} {a : A} {l : ElemDual A} {z : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (k : ℕ) :
    Triv μ x y E E₂ (.zpow u (-(k : ℤ))) (-(k • a)) (-(k • l))
      (k • z + (k.choose 2) • l a + (k • l) (k • a)) := by
  obtain ⟨G, hG, hGa⟩ := hu
  have hGk : ∀ c : A, (G ^ k) • c = c := fun c ↦
    mem_trivAct.mp (pow_mem (mem_trivAct.mpr hGa) k) c
  have hGki : ∀ c : A, (G ^ k)⁻¹ • c = c := fun c ↦ inv_smul_eq_iff.mpr (hGk c).symm
  refine ⟨(G ^ k)⁻¹, ?_, hGki⟩
  rw [heisEvalZ_zpow, zpow_neg, zpow_natCast, hG, heisPow_of_trivial _ hGa k]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -((G ^ k)⁻¹ • (k • a)) = _
    rw [hGki]
  · show -((G ^ k)⁻¹ • (k • l)) = _
    rw [smul_elemDual_of_trivial hGki]
  · rfl

theorem Triv.profPow {u : PWord X} {a : A} {l : ElemDual A} {z : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) {k : ℕ} {γ : Zhat} (hE : E γ = (k : ℤ)) :
    Triv μ x y E E₂ (.profPow u γ) (k • a) (k • l) (k • z + (k.choose 2) • l a) := by
  obtain ⟨G, hG, hGa⟩ := hu
  exact ⟨G ^ k, by rw [heisEvalZ_profPow, hE, hG, zpow_natCast, heisPow_of_trivial _ hGa k],
    fun c ↦ mem_trivAct.mp (pow_mem (mem_trivAct.mpr hGa) k) c⟩

theorem Triv.comm {u v : PWord X} {a b : A} {l m : ElemDual A} {z w : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (hv : Triv μ x y E E₂ v b m w) :
    Triv μ x y E E₂ (.comm u v) 0 0 (l b + m a) := by
  obtain ⟨G, hG, hGa⟩ := hu
  obtain ⟨H, hH, hHa⟩ := hv
  exact ⟨commR G H, by rw [heisEvalZ_comm, hG, hH, heisCommR_of_trivial _ _ hGa hHa],
    fun c ↦ commR_smul_of_trivial_left hGa c⟩

theorem Triv.conj {u g : PWord X} {a b : A} {l m : ElemDual A} {z w : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (hg : Triv μ x y E E₂ g b m w) :
    Triv μ x y E E₂ (.conj u g) a l (z + m a + l b) := by
  obtain ⟨G, hG, hGa⟩ := hu
  obtain ⟨H, hH, hHa⟩ := hg
  have hHi : ∀ c : A, H⁻¹ • c = c := fun c ↦ inv_smul_eq_iff.mpr (hHa c).symm
  refine ⟨conjR G H, ?_, fun c ↦ mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr hGa) H) c⟩
  rw [heisEvalZ_conj, hG, hH, heisConjR_of_trivial _ _ hGa]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show H⁻¹ • a = _
    rw [hHi]
  · show H⁻¹ • l = _
    rw [smul_elemDual_of_trivial hHi]
  · rfl

/-- The two-element `prodList` in `Triv` form — the shape every displayed factor takes. -/
theorem Triv.pair {u v : PWord X} {a b : A} {l m : ElemDual A} {z w : ZMod 2}
    (hu : Triv μ x y E E₂ u a l z) (hv : Triv μ x y E E₂ v b m w) :
    Triv μ x y E E₂ (PWord.prodList [u, v]) (a + b) (l + m) (z + w + l b) := by
  have hmul := hu.mul (hv.mul (triv_one μ x y E E₂))
  have hz : z + (w + 0 + m 0) + l (b + 0) = z + w + l b := by
    rw [add_zero, map_zero, add_zero, add_zero]
  rw [PWord.prodList, PWord.prodList, PWord.prodList, ← hz]
  simpa only [add_zero] using hmul

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

/-! ### The two live factors of the linear copy -/

include hxσ hyσ hx2 hy2 hwild hS₂ in
/-- **The Labute letter `A = x₀⁻¹C₀^{−m}` on even normal offsets**: the jet of `x₀⁻¹` alone.
`C₀ = x₂σ₂^s` is dead here — `x₂` and `σ` both carry zero offsets — so it can contribute neither
a jet nor a charge, and (unlike the ramified reading) its base acts trivially. -/
theorem heisEvalZ_aW_unram (s' mm : ℕ) :
    ∃ G : C, heisEvalZ ⇑t x y E E₂ (aW h s' mm)
        = ⟨-x (coreLetter h 0), -y (coreLetter h 0),
            y (coreLetter h 0) (x (coreLetter h 0)), G⟩ ∧ ∀ a : A, G • a = a := by
  obtain ⟨Gc, hGc, hGca⟩ :=
    (isDead_c0W t x y E E₂ hxσ hyσ hx2 hy2 hwild hS₂ s').zpow (-(mm : ℤ))
  have h0i := mem_trivAct.mp (inv_mem (Certificates.trivAct_coreLetter t hwild 0))
  have hinv : heisEvalZ ⇑t x y E E₂ (.inv (.gen (coreLetter h 0)))
      = ⟨-x (coreLetter h 0), -y (coreLetter h 0),
          y (coreLetter h 0) (x (coreLetter h 0)), (t (coreLetter h 0))⁻¹⟩ := by
    rw [heisEvalZ_inv, heisEvalZ_gen]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t (coreLetter h 0))⁻¹ • x (coreLetter h 0)) = _
      rw [h0i]
    · show -((t (coreLetter h 0))⁻¹ • y (coreLetter h 0)) = _
      rw [smul_elemDual_of_trivial h0i]
    · show (0 : ZMod 2) + y (coreLetter h 0) (x (coreLetter h 0)) = _
      rw [zero_add]
  refine ⟨(t (coreLetter h 0))⁻¹ * Gc, ?_, fun a ↦ by rw [mul_smul, hGca, h0i]⟩
  rw [aW, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_one, mul_one, hGc, hinv]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show -x (coreLetter h 0) + (t (coreLetter h 0))⁻¹ • (0 : A) = _
    rw [smul_zero, add_zero]
  · show -y (coreLetter h 0) + (t (coreLetter h 0))⁻¹ • (0 : ElemDual A) = _
    rw [smul_zero, add_zero]
  · show y (coreLetter h 0) (x (coreLetter h 0)) + 0
        + (-y (coreLetter h 0)) ((t (coreLetter h 0))⁻¹ • (0 : A)) = _
    rw [smul_zero, map_zero, add_zero, add_zero]

include hxσ hyσ hwild hS₂ in
/-- **The boundary letter `B = x₁σ₂^p` on even normal offsets**: the jet of `x₁` alone, in both
of the display's two shapes. -/
theorem heisEvalZ_bW_unram (pp : ℕ) :
    ∃ G : C, heisEvalZ ⇑t x y E E₂ (bW h pp)
        = ⟨x (coreLetter h 1), y (coreLetter h 1), 0, G⟩ ∧ ∀ a : A, G • a = a := by
  have h1 := mem_trivAct.mp (Certificates.trivAct_coreLetter t hwild 1)
  match pp with
  | 0 => exact ⟨t (coreLetter h 1), rfl, h1⟩
  | (j + 1) =>
      obtain ⟨Gs, hGs, hGsa⟩ := isDead_sig2PowW t x y E E₂ hxσ hyσ hS₂ (j + 1)
      refine ⟨t (coreLetter h 1) * Gs, ?_, fun a ↦ by rw [mul_smul, hGsa, h1]⟩
      rw [show bW h (j + 1)
            = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (j + 1)] from rfl,
        PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
        heisEvalZ_mul, heisEvalZ_one, mul_one, heisEvalZ_gen, hGs]
      refine HeisLift.ext ?_ ?_ ?_ rfl
      · show x (coreLetter h 1) + t (coreLetter h 1) • (0 : A) = _
        rw [smul_zero, add_zero]
      · show y (coreLetter h 1) + t (coreLetter h 1) • (0 : ElemDual A) = _
        rw [smul_zero, add_zero]
      · show (0 : ZMod 2) + 0 + y (coreLetter h 1) (t (coreLetter h 1) • (0 : A)) = _
        rw [smul_zero, map_zero, add_zero, add_zero]

include hxσ hyσ hx2 hy2 hA₂ hwild hS₂ in
/-- **Factor 1 — `A²`.**  Jet-zero (the exponent is the literal `2`) with the `x₀`-diagonal as
its charge. -/
theorem heisEvalZ_aSq_unram (s' mm : ℕ) :
    heisEvalZ ⇑t x y E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ)) ∈ heisJetZero A C ∧
      (heisEvalZ ⇑t x y E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ))).z
        = y (coreLetter h 0) (x (coreLetter h 0)) := by
  obtain ⟨G, hG, hGa⟩ := heisEvalZ_aW_unram t x y E E₂ hxσ hyσ hx2 hy2 hwild hS₂ s' mm
  have hbase : ∀ a : A, (heisEvalZ ⇑t x y E E₂ (aW h s' mm)).g • a = a := by
    rw [hG]; exact hGa
  have hval : heisEvalZ ⇑t x y E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 0)), G ^ (2 : ℕ)⟩ := by
    rw [heisEvalZ_zpow, zpow_natCast, heisPow_of_trivial _ hbase 2, hG]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · exact even_nsmul_eq_zero hA₂ (by decide) _
    · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero (by decide) _
    · show (2 : ℕ) • y (coreLetter h 0) (x (coreLetter h 0))
          + ((2 : ℕ).choose 2) • (-y (coreLetter h 0)) (-x (coreLetter h 0)) = _
      rw [nsmul_zmod2_even (by decide), zero_add, Nat.choose_self, one_nsmul,
        ElemDual.neg_apply, map_neg, neg_neg]
  rw [hval]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

include hxσ hyσ hx2 hy2 hwild hS₂ in
/-- **Factor 2 — `[A,B]`.**  Both bases act trivially at the unramified reading, so the
two-sided commutator law applies and the value is the plain hyperbolic cross. -/
theorem heisEvalZ_commAB_unram (s' mm pp : ℕ) :
    heisEvalZ ⇑t x y E E₂ (.comm (aW h s' mm) (bW h pp)) ∈ heisJetZero A C ∧
      (heisEvalZ ⇑t x y E E₂ (.comm (aW h s' mm) (bW h pp))).z
        = y (coreLetter h 0) (x (coreLetter h 1))
          + y (coreLetter h 1) (x (coreLetter h 0)) := by
  obtain ⟨G, hG, hGa⟩ := heisEvalZ_aW_unram t x y E E₂ hxσ hyσ hx2 hy2 hwild hS₂ s' mm
  obtain ⟨H, hH, hHa⟩ := heisEvalZ_bW_unram t x y E E₂ hxσ hyσ hwild hS₂ pp
  have hbA : ∀ a : A, (heisEvalZ ⇑t x y E E₂ (aW h s' mm)).g • a = a := by rw [hG]; exact hGa
  have hbB : ∀ a : A, (heisEvalZ ⇑t x y E E₂ (bW h pp)).g • a = a := by rw [hH]; exact hHa
  have hval : heisEvalZ ⇑t x y E E₂ (.comm (aW h s' mm) (bW h pp))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 1))
            + y (coreLetter h 1) (x (coreLetter h 0)), commR G H⟩ := by
    rw [heisEvalZ_comm, heisCommR_of_trivial _ _ hbA hbB, hG, hH]
    refine HeisLift.ext rfl rfl ?_ rfl
    show (-y (coreLetter h 0)) (x (coreLetter h 1))
        + y (coreLetter h 1) (-x (coreLetter h 0)) = _
    rw [ElemDual.neg_apply, map_neg, CharTwo.neg_eq, CharTwo.neg_eq]
  rw [hval]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-! ### The handle tail -/

omit hxσ hyσ hxτ hyτ hx2 hy2 hA₂ hτ hS₂ in
include hwild in
theorem jetZero_of_mem_handleTailW {w : PWord (Generator (2 + 2 * h))}
    (hw : w ∈ handleTailW h) : heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
  obtain rfl := eq_handlesW_of_mem_handleTail hw
  exact Certificates.MCompact.heisF_handlesW_mem t x y E E₂ hwild

omit hxσ hyσ hxτ hyτ hx2 hy2 hA₂ hτ hS₂ in
include hwild in
/-- The handle tail's central charges sum to the `h` identity-operator hyperbolic planes — the
list-of-sums twin of `Certificates.MCompact.heisEvalZ_handleTailW`. -/
theorem sum_z_handleTailW :
    (((handleTailW h).map fun w ↦ (heisEvalZ ⇑t x y E E₂ w).z)).sum
      = ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  cases h with
  | zero => rw [handleTailW]; simp
  | succ n =>
      rw [handleTailW]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Certificates.MCompact.heisF_handlesW_z t x y E E₂ hwild

/-! ## The assembled second-order row on even normal offsets -/

set_option maxHeartbeats 1600000 in
include hxσ hyσ hxτ hyτ hx2 hy2 hA₂ hwild hτ hS₂ in
/-- **The corrected procyclic-`M` second-order row on even normal offsets, unramified
reading**:

```
y₀(x₀) ⊕ (y₀(x₁) + y₁(x₀)) ⊕ Σ_j planes,
```

the compact core Gram `((1,1),(1,0))` plus the `h` standard hyperbolic handle planes.

Eleven of the thirteen factors are **dead** — `C₀^{2^α}` and `[C₀,D]` because `C₀ = x₂σ₂^s` has
vanishing offsets, `E₀₁^pc`, `E₂^pc` and the whole plus block because every `δ`-letter is
second-order trivial at `e ≡ 1 (mod 4)`, and the *entire* hat copy because it is built from
`δ`-letters and `σ₂`-powers alone.  So no shadow cancellation is needed: the two live factors
are the Labute square and the Labute commutator, and they carry the whole core matrix. -/
theorem heisZ_mpcW_evenNormal (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (α r pp : ℕ) (η : EtaDisplay) :
    (heisEvalZ ⇑t x y E E₂ (mpcW α r pp η h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hd := isDead_dW t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  have hc0 := isDead_c0W t x y E E₂ hxσ hyσ hx2 hy2 hwild hS₂
  have hc0h := isDead_c0HatW t x y E E₂ hxσ hyσ hS₂
  have hah := isDead_aHatW t x y E E₂ hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ hE he
  have hbh := isDead_bHatW t x y E E₂ hxσ hyσ hxτ hyτ hA₂ hwild hτ hS₂ hE he
  have he01 := isDead_e01W t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  have he2 := isDead_e2W t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
  have hsq := heisEvalZ_aSq_unram t x y E E₂ hxσ hyσ hx2 hy2 hA₂ hwild hS₂ (s r) (m α)
  have hcm := heisEvalZ_commAB_unram t x y E E₂ hxσ hyσ hx2 hy2 hwild hS₂ (s r) (m α) pp
  have hmem : ∀ w ∈ (linFactors α r pp η h ++ hatFactors α r pp η h ++
      [PWord.zpow (dW h 0) ((2 : ℕ) : ℤ), PWord.comm (dW h 0) (dW h 1)] ++ handleTailW h),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    rw [List.mem_append, List.mem_append, List.mem_append] at hw
    rcases hw with ((hlin | hhat) | hplus) | htail
    · simp only [linFactors, List.mem_cons, List.not_mem_nil, or_false] at hlin
      rcases hlin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsq.1
      · exact hcm.1
      · exact ((hc0 _).zpow _).jetZero
      · exact ((hc0 _).commLeft _).jetZero
      · exact (he01 _ _).jetZero
      · exact (he2 _ _ _).jetZero
    · simp only [hatFactors, List.mem_cons, List.not_mem_nil, or_false] at hhat
      rcases hhat with rfl | rfl | rfl | rfl | rfl
      · exact ((hah _ _).zpow _).jetZero
      · exact ((hah _ _).commLeft _).jetZero
      · exact ((hc0h _).zpow _).jetZero
      · exact ((hc0h _).commLeft _).jetZero
      · exact (he01 _ _).jetZero
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hplus
      rcases hplus with rfl | rfl
      · exact ((hd 0).zpow _).jetZero
      · exact ((hd 0).commLeft _).jetZero
    · exact jetZero_of_mem_handleTailW t x y E E₂ hwild htail
  rw [mpcW, (heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2, List.map_append, List.map_append,
    List.map_append, List.sum_append, List.sum_append, List.sum_append,
    sum_z_handleTailW t x y E E₂ hwild]
  simp only [linFactors, hatFactors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hsq.2, hcm.2, ((hc0 _).zpow _).z, ((hc0 _).commLeft _).z, (he01 _ _).z, (he2 _ _ _).z,
    ((hah _ _).zpow _).z, ((hah _ _).commLeft _).z, ((hc0h _).zpow _).z,
    ((hc0h _).commLeft _).z, ((hd 0).zpow _).z, ((hd 0).commLeft _).z, add_zero]

end Letters

/-! ## The procyclic-`M` second-order row at a completely trivial action

The scalar sub-branch reads the row with a **free `sigma`-coordinate**: with every generator
acting trivially the bottom differential vanishes, so `x_σ` and `y_σ` survive in a normal
cochain.  Every `δ`-letter is still dead (that only needs `x_τ = y_τ = 0` and `e ≡ 1 (mod 4)`),
so `E₀₁^pc`, `E₂^pc` and the plus block are still silent; what wakes up is the `σ`-content of
`C₀ = x₂σ₂^s`, `B = x₁σ₂^p`, `Ĉ₀`, `B̂` and the `η̂`-display.

Two hypotheses beyond the unramified ones do all the collapsing, and both are `α ≥ 2`:
`m = 2^{α−1}` is even, which kills the whole hat copy and `A`'s `C₀`-tail, and `C(2^α, 2)` is
even, which kills `C₀^{2^α}` and `Ĉ₀^{2^α}`.  At `α = 1` neither holds and the row is different.
-/

section Scalar

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

variable (hA₂ : ∀ a : A, a + a = 0)
  (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
  (hxτ : x .tau = 0) (hyτ : y .tau = 0)

variable {e : ℕ}

include hA₂ htriv in
/-- **`σ₂` has the plain `σ`-jets and no charge** at a trivial action on the honest resolver
class: the exponent `e` is odd, so it is invisible on the jets, and `C(e,2)` is even. -/
theorem triv_sigma2W (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    Triv ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h))) (x .sigma) (y .sigma) 0 := by
  have h0 : Triv ⇑t x y E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      (x .sigma) (y .sigma) 0 := triv_gen _ _ _ _ _ _ (htriv _)
  have h1 : Triv ⇑t x y E E₂ (sigma2W : PWord (Generator (2 + 2 * h)))
      (e • x .sigma) (e • y .sigma) (e • (0 : ZMod 2) + (e.choose 2) • y .sigma (x .sigma)) :=
    h0.profPow hE
  rwa [Certificates.MCompact.nsmul_self_of_odd hA₂ (odd_of_mod_four_eq_one he),
    Certificates.MCompact.nsmul_self_of_odd ElemDual.add_self_eq_zero
      (odd_of_mod_four_eq_one he),
    smul_zero, zero_add, nsmul_zmod2_even (choose_two_even_of_mod_four he)] at h1

include hA₂ htriv in
/-- `σ₂^k` at a trivial action, in the display's two shapes. -/
theorem triv_sig2PowW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (k : ℕ) :
    ∃ Z, Triv ⇑t x y E E₂ (sig2PowW h k) (k • x .sigma) (k • y .sigma) Z := by
  have h2 := triv_sigma2W t x y E E₂ hA₂ htriv hE he
  match k with
  | 0 => exact ⟨_, h2.npow 0⟩
  | 1 =>
      refine ⟨0, ?_⟩
      rw [one_nsmul, one_nsmul]
      exact h2
  | (j + 2) => exact ⟨_, h2.npow (j + 2)⟩

include hA₂ htriv hxτ hyτ in
/-- The `δ`-letters are dead at a trivial action too — `heisF_deltaCert_trivial` needs only the
`τ`-free offsets and the honest resolver class. -/
theorem triv_dW (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (i : Fin 3) :
    Triv ⇑t x y E E₂ (dW h i) 0 0 0 :=
  (isDead_dW t x y E E₂ hxτ hyτ hA₂ (fun _ v ↦ htriv _ v) (fun v ↦ htriv _ v) hE he i).triv

set_option maxHeartbeats 3200000 in
include hA₂ htriv hxτ hyτ in
/-- **The corrected procyclic-`M` second-order row at a completely trivial action, with a free
`sigma`-coordinate and `tau`-free offsets** (`α ≥ 2`):

```
y₀(x₀) ⊕ (y₀(x₁) + y₁(x₀)) ⊕ p·(x₀,x_σ) ⊕ n_η·(x₂,x_σ) ⊕ Σ_j planes.
```

The compact scalar core `((1,1),(1,0))` on `(x₀,x₁)`, plus two `sigma`-hyperbolic planes whose
coefficients are the conjugator exponents `p` and `n_η` read modulo `2` — the analogue of
`NProcyclicUnram.heisZ_npc_scalar_free`, with `2^r` there replaced by `p` here.

The **entire hat copy is silent**: `Â`'s two halves are a dead `δ₀` and an even power of `Ĉ₀`,
so `Â` is jet-zero and both `Â²` and `[Â,B̂]` vanish, while `Ĉ₀^{2^α}` dies on `C(2^α,2)` and
`[Ĉ₀,D]` on the symmetry of the `σ`-pairing.  So no shadow cancellation is used here either. -/
theorem heisZ_mpcW_scalar {α r pp : ℕ} {η : EtaDisplay} {nn : ℕ} {zη : ZMod 2}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (hα : 2 ≤ α)
    (hη : Triv ⇑t x y E E₂ (η.toPWord (n := 2 + 2 * h))
      (nn • x .sigma) (nn • y .sigma) zη) :
    (heisEvalZ ⇑t x y E E₂ (mpcW α r pp η h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + pp • (y (coreLetter h 0) (x .sigma) + y .sigma (x (coreLetter h 0)))
        + nn • (y (coreLetter h 2) (x .sigma) + y .sigma (x (coreLetter h 2)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v := fun _ v ↦ htriv _ v
  have hτ : ∀ v : A, t.τ • v = v := fun v ↦ htriv _ v
  have hmE : Even (m α) := Words.MCompact.even_mOf hα
  have h2m : (2 : ℕ) ^ α = 2 * m α := two_pow_eq_two_mul_m (by omega)
  have h2aE : Even ((2 : ℕ) ^ α) := by rw [h2m]; exact even_two_mul _
  have hc2aE : Even (((2 : ℕ) ^ α).choose 2) := by
    rw [h2m, Nat.choose_two_right,
      show 2 * m α * (2 * m α - 1) = m α * (2 * m α - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
    exact hmE.mul_right _
  have hg0 : Triv ⇑t x y E E₂ (.gen (coreLetter h 0))
      (x (coreLetter h 0)) (y (coreLetter h 0)) 0 := triv_gen _ _ _ _ _ _ (htriv _)
  have hg1 : Triv ⇑t x y E E₂ (.gen (coreLetter h 1))
      (x (coreLetter h 1)) (y (coreLetter h 1)) 0 := triv_gen _ _ _ _ _ _ (htriv _)
  have hg2 : Triv ⇑t x y E E₂ (.gen (coreLetter h 2))
      (x (coreLetter h 2)) (y (coreLetter h 2)) 0 := triv_gen _ _ _ _ _ _ (htriv _)
  have h2 := triv_sigma2W t x y E E₂ hA₂ htriv hE he
  have hd := triv_dW t x y E E₂ hA₂ htriv hxτ hyτ hE he
  obtain ⟨Zc, hc0⟩ : ∃ Z, Triv ⇑t x y E E₂ (c0W h (s r))
      (x (coreLetter h 2) + (s r) • x .sigma)
      (y (coreLetter h 2) + (s r) • y .sigma) Z := ⟨_, hg2.pair (h2.npow (s r))⟩
  obtain ⟨Zch, hch⟩ : ∃ Z, Triv ⇑t x y E E₂ (c0HatW h (s r))
      ((s r) • x .sigma) ((s r) • y .sigma) Z := ⟨_, h2.npow (s r)⟩
  obtain ⟨ZA, hA⟩ : ∃ Z, Triv ⇑t x y E E₂ (aW h (s r) (m α))
      (-x (coreLetter h 0)) (-y (coreLetter h 0)) Z := by
    have hraw := (hg0.inv).pair (hc0.zpowNeg (m α))
    simp only [even_nsmul_eq_zero hA₂ hmE, even_nsmul_eq_zero ElemDual.add_self_eq_zero hmE,
      neg_zero, add_zero, zero_add, map_zero] at hraw
    exact ⟨_, hraw⟩
  obtain ⟨ZAh, hAh⟩ : ∃ Z, Triv ⇑t x y E E₂ (aHatW h (s r) (m α)) 0 0 Z := by
    have hraw := ((hd 0).inv).pair (hch.zpowNeg (m α))
    simp only [even_nsmul_eq_zero hA₂ hmE, even_nsmul_eq_zero ElemDual.add_self_eq_zero hmE,
      neg_zero, add_zero, zero_add, map_zero] at hraw
    exact ⟨_, hraw⟩
  obtain ⟨ZB, hB⟩ : ∃ Z, Triv ⇑t x y E E₂ (bW h pp)
      (x (coreLetter h 1) + pp • x .sigma) (y (coreLetter h 1) + pp • y .sigma) Z := by
    match pp with
    | 0 => exact ⟨0, by rw [zero_nsmul, zero_nsmul, add_zero, add_zero]; exact hg1⟩
    | (j + 1) =>
        obtain ⟨Zs, hs⟩ := triv_sig2PowW t x y E E₂ hA₂ htriv hE he (j + 1)
        exact ⟨_, hg1.pair hs⟩
  obtain ⟨bh, mh, ZBh, hBh⟩ : ∃ b' m' Z, Triv ⇑t x y E E₂ (bHatW h pp) b' m' Z := by
    match pp with
    | 0 => exact ⟨_, _, _, hd 1⟩
    | (j + 1) =>
        obtain ⟨Zs, hs⟩ := triv_sig2PowW t x y E E₂ hA₂ htriv hE he (j + 1)
        exact ⟨_, _, _, (hd 1).pair hs⟩
  have hf1 : Triv ⇑t x y E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ)) 0 0
      ((2 : ℕ) • ZA + ((2 : ℕ).choose 2) • (-y (coreLetter h 0)) (-x (coreLetter h 0))) := by
    have hraw := hA.npow 2
    rwa [even_nsmul_eq_zero hA₂ (by decide),
      even_nsmul_eq_zero ElemDual.add_self_eq_zero (by decide)] at hraw
  have hf2 := hA.comm hB
  have hf3 : Triv ⇑t x y E E₂ (.zpow (c0W h (s r)) (((2 : ℕ) ^ α : ℕ) : ℤ)) 0 0
      (((2 : ℕ) ^ α) • Zc + (((2 : ℕ) ^ α).choose 2)
        • (y (coreLetter h 2) + (s r) • y .sigma)
            (x (coreLetter h 2) + (s r) • x .sigma)) := by
    have hraw := hc0.npow ((2 : ℕ) ^ α)
    rwa [even_nsmul_eq_zero hA₂ h2aE,
      even_nsmul_eq_zero ElemDual.add_self_eq_zero h2aE] at hraw
  have hf4 := hc0.comm hη
  have hf5 := (isDead_e01W t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he
    (pp + s r * m α) (s r * m α)).triv
  have hf6 := (isDead_e2W t x y E E₂ hxτ hyτ hA₂ hwild hτ hE he (s r) (m α) pp).triv
  have hf7 : Triv ⇑t x y E E₂ (.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ)) 0 0
      ((2 : ℕ) • ZAh + ((2 : ℕ).choose 2) • (0 : ElemDual A) (0 : A)) := by
    have hraw := hAh.npow 2
    rwa [smul_zero, smul_zero] at hraw
  have hf8 := hAh.comm hBh
  have hf9 : Triv ⇑t x y E E₂ (.zpow (c0HatW h (s r)) (((2 : ℕ) ^ α : ℕ) : ℤ)) 0 0
      (((2 : ℕ) ^ α) • Zch + (((2 : ℕ) ^ α).choose 2)
        • ((s r) • y .sigma) ((s r) • x .sigma)) := by
    have hraw := hch.npow ((2 : ℕ) ^ α)
    rwa [even_nsmul_eq_zero hA₂ h2aE,
      even_nsmul_eq_zero ElemDual.add_self_eq_zero h2aE] at hraw
  have hf10 := hch.comm hη
  have hf12 : Triv ⇑t x y E E₂ (.zpow (dW h 0) ((2 : ℕ) : ℤ)) 0 0
      ((2 : ℕ) • (0 : ZMod 2) + ((2 : ℕ).choose 2) • (0 : ElemDual A) (0 : A)) := by
    have hraw := (hd 0).npow 2
    rwa [smul_zero, smul_zero] at hraw
  have hf13 := (hd 0).comm (hd 1)
  have hmem : ∀ w ∈ (linFactors α r pp η h ++ hatFactors α r pp η h ++
      [PWord.zpow (dW h 0) ((2 : ℕ) : ℤ), PWord.comm (dW h 0) (dW h 1)] ++ handleTailW h),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    rw [List.mem_append, List.mem_append, List.mem_append] at hw
    rcases hw with ((hlin | hhat) | hplus) | htail
    · simp only [linFactors, List.mem_cons, List.not_mem_nil, or_false] at hlin
      rcases hlin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hf1.jetZero
      · exact hf2.jetZero
      · exact hf3.jetZero
      · exact hf4.jetZero
      · exact hf5.jetZero
      · exact hf6.jetZero
    · simp only [hatFactors, List.mem_cons, List.not_mem_nil, or_false] at hhat
      rcases hhat with rfl | rfl | rfl | rfl | rfl
      · exact hf7.jetZero
      · exact hf8.jetZero
      · exact hf9.jetZero
      · exact hf10.jetZero
      · exact hf5.jetZero
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hplus
      rcases hplus with rfl | rfl
      · exact hf12.jetZero
      · exact hf13.jetZero
    · exact jetZero_of_mem_handleTailW t x y E E₂ hwild htail
  rw [mpcW, (heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2, List.map_append, List.map_append,
    List.map_append, List.sum_append, List.sum_append, List.sum_append,
    sum_z_handleTailW t x y E E₂ hwild]
  simp only [linFactors, hatFactors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hf1.zEq, hf2.zEq, hf3.zEq, hf4.zEq, hf5.zEq, hf6.zEq, hf7.zEq, hf8.zEq, hf9.zEq, hf10.zEq,
    hf12.zEq, hf13.zEq]
  simp only [nsmul_zmod2_even (show Even 2 by decide), nsmul_zmod2_even h2aE,
    nsmul_zmod2_even hc2aE, ElemDual.zero_apply, smul_zero, zero_add, add_zero,
    ElemDual.add_apply, ElemDual.neg_apply, map_add, map_neg, map_zero, map_nsmul,
    Certificates.Npc.elemDual_nsmul_apply, CharTwo.neg_eq, smul_add, smul_smul,
    Nat.choose_self, one_nsmul]
  rw [mul_comm (s r) nn]
  generalize y (coreLetter h 0) (x (coreLetter h 0)) = c₁
  generalize y (coreLetter h 0) (x (coreLetter h 1)) = c₂
  generalize pp • y (coreLetter h 0) (x .sigma) = c₃
  generalize y (coreLetter h 1) (x (coreLetter h 0)) = c₄
  generalize pp • y .sigma (x (coreLetter h 0)) = c₅
  generalize nn • y (coreLetter h 2) (x .sigma) = c₆
  generalize (nn * s r) • y .sigma (x .sigma) = c₇
  generalize nn • y .sigma (x (coreLetter h 2)) = c₈
  generalize (∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j)))) = c₉
  revert c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉
  decide

end Scalar

/-! ## The traced pairing of the resolved family on even normal coordinates -/

section Pairing

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The traced pairing of the procyclic-`M` family at an arbitrary resolver pair is the sum of
the tame and the wild second-order values. -/
theorem heisEta1_mpcFamOf_apply (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (α r pp q : ℕ) (η : EtaDisplay) :
    heisEta1 ⇑t (mpcFamOf α r pp h q η E E₂) x y
      = (heisEvalZ ⇑t x y E E₂ (Certificates.tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y E E₂ (mpcW α r pp η h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two,
    show mpcFamOf α r pp h q η E E₂ 0
      = heisToFree E E₂ (Certificates.tameRelW (2 + 2 * h) q) from rfl,
    show mpcFamOf α r pp h q η E E₂ 1 = heisToFree E E₂ (mpcW α r pp η h) from rfl,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`M` traced pairing on even normal coordinates, unramified reading**: the
compact core Gram `((1,1),(1,0))` plus the `h` standard hyperbolic handle planes.  The tame
relator contributes nothing — a normal cochain vanishes on `sigma` and `tau`. -/
theorem heisEta1_mpcFamOf_evenNormal (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) {e α r pp q : ℕ} {η : EtaDisplay}
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hS₂ : ∀ v : A, (t.σ ^ E omega2) • v = v)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (mpcFamOf α r pp h q η E E₂)
        (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
      = lam₀ (d₀ + d₁) + lam₁ d₀ + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  rw [heisEta1_mpcFamOf_apply t _ _ E E₂ α r pp q η,
    heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂ (by simp) (by simp) (by simp)
      (by simp),
    zero_add,
    heisZ_mpcW_evenNormal t _ _ E E₂ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) hA₂ hwild hτ hS₂ hE he α r pp η]
  simp only [evenNormal_coreLetter, evenNormal_handleU, evenNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_add]
  abel

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`M` traced pairing on scalar normal coordinates** (`α ≥ 2`): the compact
scalar core on `(x₀,x₁)` plus the two `sigma`-hyperbolic planes with coefficients `p` and
`n_η`.  The tame relator is `(σ,τ)`-supported and a scalar normal cochain is `τ`-free. -/
theorem heisEta1_mpcFamOf_scalarNormal (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) {e α r pp q nn : ℕ} {η : EtaDisplay}
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (hα : 2 ≤ α) (hq : Even q)
    (hη : ∀ (u : Generator (2 + 2 * h) → A) (w : Generator (2 + 2 * h) → ElemDual A),
      ∃ zη, Triv ⇑t u w E E₂ (η.toPWord (n := 2 + 2 * h))
        (nn • u .sigma) (nn • w .sigma) zη)
    (p : ScalarParam h A) (rr : ScalarParam h (ElemDual A)) :
    heisEta1 ⇑t (mpcFamOf α r pp h q η E E₂)
        (evenScalarNormalP h p) (evenScalarNormalP h rr)
      = rr.2.1 p.2.1 + (rr.2.1 p.2.2.1 + rr.2.2.1 p.2.1)
        + pp • (rr.2.1 p.1 + rr.1 p.2.1)
        + nn • (rr.2.2.2.1 p.1 + rr.1 p.2.2.2.1)
        + ∑ j, (rr.2.2.2.2 (j, 0) (p.2.2.2.2 (j, 1))
            + rr.2.2.2.2 (j, 1) (p.2.2.2.2 (j, 0))) := by
  obtain ⟨zη, hηp⟩ := hη (evenScalarNormalP h p) (evenScalarNormalP h rr)
  have htame : (heisEvalZ ⇑t (evenScalarNormalP h p) (evenScalarNormalP h rr) E E₂
      (Certificates.tameRelW (2 + 2 * h) q)).z = 0 := by
    rw [Certificates.heisZ_tameRelW_unram t _ _ E E₂ hA₂ (fun v ↦ htriv _ v) hq]
    simp [evenScalarNormalP]
  rw [heisEta1_mpcFamOf_apply t _ _ E E₂ α r pp q η, htame, zero_add,
    heisZ_mpcW_scalar t _ _ E E₂ hA₂ htriv (by simp [evenScalarNormalP])
      (by simp [evenScalarNormalP]) hE he hα hηp]
  simp only [evenScalarNormalP, evenScalarNormal_coreLetter, evenScalarNormal_sigma,
    evenScalarNormal_handleU, evenScalarNormal_handleV, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

set_option maxHeartbeats 1600000 in
/-- **Left nondegeneracy of the procyclic-`M` scalar pairing at an odd display exponent.**  Four
core rows are consulted in turn — `ν₁` for `d₀`, `ν₂` for `a_σ`, `ν₀` for `d₁` and `b_σ` for
`d₂` — and a handle coordinate closes the remaining case.

⚠ `Odd nn` is **necessary**: at an even display exponent nothing in the Gram sees `a_σ` or `d₂`
except through `p`, and the `(a_σ, d₂)` plane degenerates. -/
theorem mpc_scalarNormal_pairing_separates_left [Finite A] (t : Marking (2 + 2 * h) C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e α r pp q nn : ℕ} {η : EtaDisplay}
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (hα : 2 ≤ α) (hq : Even q) (hnn : Odd nn)
    (hη : ∀ (u : Generator (2 + 2 * h) → A) (w : Generator (2 + 2 * h) → ElemDual A),
      ∃ zη, Triv ⇑t u w E E₂ (η.toPWord (n := 2 + 2 * h))
        (nn • u .sigma) (nn • w .sigma) zη)
    (p : ScalarParam h A) (hp : p ≠ 0) :
    ∃ rr : ScalarParam h (ElemDual A),
      heisEta1 ⇑t (mpcFamOf α r pp h q η E E₂)
        (evenScalarNormalP h p) (evenScalarNormalP h rr) ≠ 0 := by
  classical
  have heval := heisEta1_mpcFamOf_scalarNormal (α := α) (r := r) (pp := pp) (q := q) t E E₂
    hA₂ htriv hE he hα hq hη p
  by_cases hd₀ : p.2.1 = 0
  · by_cases hσ : p.1 = 0
    · by_cases hd₁ : p.2.2.1 = 0
      · by_cases hd₂ : p.2.2.2.1 = 0
        · have hz : p.2.2.2.2 ≠ 0 := fun hz ↦
            hp (Prod.ext hσ (Prod.ext hd₀ (Prod.ext hd₁ (Prod.ext hd₂ (by simpa using hz)))))
          obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hz
          obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
          fin_cases k
          · refine ⟨(0, 0, 0, 0, Pi.single (j, 1) lam), ?_⟩
            rw [heval, hd₀, hσ, hd₁, hd₂]
            have hsum : ∑ b, ((Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
                  (p.2.2.2.2 (b, 1))
                + (Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 1)
                  (p.2.2.2.2 (b, 0))) = lam (p.2.2.2.2 (j, 0)) := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hbj
                simp [hbj]
              · simp
            rw [hsum]
            simpa using hlam
          · refine ⟨(0, 0, 0, 0, Pi.single (j, 0) lam), ?_⟩
            rw [heval, hd₀, hσ, hd₁, hd₂]
            have hsum : ∑ b, ((Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
                  (p.2.2.2.2 (b, 1))
                + (Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 1)
                  (p.2.2.2.2 (b, 0))) = lam (p.2.2.2.2 (j, 1)) := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hbj
                simp [hbj]
              · simp
            rw [hsum]
            simpa using hlam
        · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₂
          refine ⟨(lam, 0, 0, 0, 0), ?_⟩
          rw [heval, hd₀, hσ, hd₁]
          simpa [nsmul_zmod2_odd hnn] using hlam
      · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₁
        refine ⟨(0, lam, 0, 0, 0), ?_⟩
        rw [heval, hd₀, hσ]
        simpa using hlam
    · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hσ
      refine ⟨(0, 0, 0, lam, 0), ?_⟩
      rw [heval, hd₀]
      simpa [nsmul_zmod2_odd hnn] using hlam
  · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₀
    refine ⟨(0, 0, lam, 0, 0), ?_⟩
    rw [heval]
    simpa using hlam

end Pairing

/-! ## The display's second-order jet -/

section DisplayJet

/-- **An odd display jet**: at every trivially-acting marking and every resolver the display
denotes `σ^{nn}` for one fixed odd `nn`, so its second-order jets are `nn` times the
`σ`-offsets.  This — and not any condition on the branch — is what the scalar sub-branch needs
from `η`: at an even jet the `(a_σ, d₂)` plane of the scalar Gram degenerates. -/
def OddDisplayJet (d : EtaDisplay) (nn : ℕ) : Prop :=
  Odd nn ∧ ∀ {h : ℕ} {C : Type} [Group C] {A : Type} [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
    (∀ a : A, a + a = 0) → (∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) →
    ∀ (u : Generator (2 + 2 * h) → A) (w : Generator (2 + 2 * h) → ElemDual A),
      ∃ zη, Triv ⇑t u w E E₂ (d.toPWord (n := 2 + 2 * h)) (nn • u .sigma) (nn • w .sigma) zη

/-- The bare-`σ` display has jet `1` — the `η = 1` row (`ℚ₂(√−10)`, `ℚ₂(√10)`, the one-handle
instance), i.e. merge gate 9's. -/
theorem oddDisplayJet_one : OddDisplayJet .one 1 := by
  refine ⟨odd_one, ?_⟩
  intro h C _ A _ _ t E E₂ _ htriv u w
  refine ⟨0, ?_⟩
  rw [one_nsmul, one_nsmul]
  exact triv_gen _ _ _ _ _ _ (htriv _)

/-- A literal odd display has jet `|k|`: the jets of `σ^k` are `k` times the `σ`-offsets, and in
characteristic two only `|k|`'s parity survives. -/
theorem oddDisplayJet_lit {k : ℤ} (hk : Odd k) : OddDisplayJet (.lit k) k.natAbs := by
  refine ⟨Int.natAbs_odd.mpr hk, ?_⟩
  intro h C _ A _ _ t E E₂ hA₂ htriv u w
  have hσ : Triv ⇑t u w E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
      (u .sigma) (w .sigma) 0 := triv_gen _ _ _ _ _ _ (htriv _)
  obtain ⟨n, hn, hkn⟩ : ∃ n : ℕ, n = k.natAbs ∧ (k = (n : ℤ) ∨ k = -(n : ℤ)) :=
    ⟨k.natAbs, rfl, Int.natAbs_eq k⟩
  rw [show (EtaDisplay.lit k).toPWord (n := 2 + 2 * h)
    = .zpow (.gen Generator.sigma) k from rfl, ← hn]
  rcases hkn with hk' | hk'
  · rw [hk']
    exact ⟨_, hσ.npow n⟩
  · have hraw := hσ.zpowNeg n
    rw [show -(n • u .sigma) = n • u .sigma from (neg_eq_iff_add_eq_zero.mpr (hA₂ _)),
      show -(n • w .sigma) = n • w .sigma from
        (neg_eq_iff_add_eq_zero.mpr (ElemDual.add_self_eq_zero _))] at hraw
    rw [hk']
    exact ⟨_, hraw⟩

/-- **The display's second-order jet at one fixed resolver.**

`OddDisplayJet` names `nn` *before* the resolver, which is right for `.one` (`nn = 1`) and
`.lit k` (`nn = |k|`) and **impossible** for `.hat num den`: that display is
`σ ^ᶻ η̂`, so its jet is the resolver's own value at the `η̂` node, and the resolver the branch
builds is `npcResolver (4·exponent C₀) ⟨num,den⟩` — module-dependent.  This is the
resolver-relative form the scalar sub-branch actually consumes. -/
def OddJetAt (d : EtaDisplay) (E : Zhat → ℤ) (nn : ℕ) : Prop :=
  Odd nn ∧ ∀ {h : ℕ} {C : Type} [Group C] {A : Type} [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E₂ : ℤ_[2] → ℤ),
    (∀ a : A, a + a = 0) → (∀ (g : Generator (2 + 2 * h)) (v : A), t g • v = v) →
    ∀ (u : Generator (2 + 2 * h) → A) (w : Generator (2 + 2 * h) → ElemDual A),
      ∃ zη, Triv ⇑t u w E E₂ (d.toPWord (n := 2 + 2 * h)) (nn • u .sigma) (nn • w .sigma) zη

/-- A resolver-uniform odd jet is in particular an odd jet at every single resolver. -/
theorem OddDisplayJet.oddJetAt {d : EtaDisplay} {nn : ℕ} (hd : OddDisplayJet d nn)
    (E : Zhat → ℤ) : OddJetAt d E nn :=
  ⟨hd.1, fun t E₂ hA₂ htriv u w ↦ hd.2 t E E₂ hA₂ htriv u w⟩

/-- **The `η̂` display's jet at its own resolver** is `n_η = 1 + padicOmega2Exp(η − 1, N)`, odd
exactly because the display denotes a `2`-adic unit.  This is the *same* arithmetic input the
procyclic-`N` scalar row consumes (`NProcyclicUnram.odd_npcResolver_toZhat_of_oneUnit`), and
the reason is the same: both rows see `η` only through the parity of that resolver value. -/
theorem oddJetAt_hat {num den : ℤ} (z : ℤ_[2])
    (hz : (EtaData.mk num den).toPadic = 1 + 2 * z) (N : ℕ) :
    OddJetAt (.hat num den) (npcResolver N ⟨num, den⟩)
      (1 + padicOmega2Exp ((EtaData.mk num den).toPadic - 1) N) := by
  refine ⟨NProcyclicUnram.odd_npcResolver_toZhat_of_oneUnit z hz N, ?_⟩
  intro h C _ A _ _ t E₂ _ htriv u w
  rw [show (EtaDisplay.hat num den).toPWord (n := 2 + 2 * h)
    = .profPow (.gen Generator.sigma) ((⟨num, den⟩ : EtaData).toZhat) from rfl]
  exact ⟨_, (triv_gen _ _ _ _ _ _ (htriv _)).profPow (npcResolver_toZhat N ⟨num, den⟩)⟩

end DisplayJet

end

end GQ2.Dyadic.MProcyclicNormal

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.MProcyclicNormal

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- **Every display's resolved family is `mpcFamOf` at a resolver correct in the acting group
itself**, with its `ω₂`-value named.  This is the base-group companion of
`exists_resolver_resolvedFamily`, which resolves in the `WordLift` levels; the second-order row
needs the base level, because `σ₂`'s *action* is what has to be identified. -/
theorem exists_resolver_base {alpha r pp h q : ℕ} (d : EtaDisplay)
    {C : Type*} [Group C] [Finite C] :
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
      resolvedFamily alpha r pp h q d (4 * Monoid.exponent C) = mpcFamOf alpha r pp h q d E E₂
        ∧ ResolverLifts E C
        ∧ E omega2 = ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ) := by
  have hconst : ResolverLifts (fun _ ↦ ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ)) C := by
    intro p
    rw [zpow_natCast]
    exact powOmega2_pow_eq p ((Monoid.order_dvd_exponent p).trans ⟨4, by ring⟩)
      (fourMulExponent_ne_zero_and_even C).1
  cases d with
  | one => exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm, hconst, rfl⟩
  | lit k => exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm, hconst, rfl⟩
  | hat num den =>
      refine ⟨_, _, rfl, ?_, npcResolver_omega2 _ _⟩
      intro p
      rw [npcResolver_omega2, zpow_natCast]
      exact powOmega2_pow_eq p ((Monoid.order_dvd_exponent p).trans ⟨4, by ring⟩)
        (fourMulExponent_ne_zero_and_even C).1

set_option maxHeartbeats 1600000 in
/-- **The generic unramified sub-branch's second-order residue, discharged.**

On every simple `tau`-unramified elementary coefficient the procyclic-`M` traced pairing on even
normal coordinates is the compact core Gram plus the `h` hyperbolic handle planes.  The `η`
display never appears: the two factors it sits in, `[C₀,D]` and `[Ĉ₀,D]`, both have a *pure*
left entry, so `heisCommR_pure_left` kills them whatever `D` evaluates to.  Nor does `α`, `r` or
`p`: every letter carrying them is dead on these offsets. -/
theorem unramifiedNormalPairingIsCompact {alpha r pp h q : ℕ} {d : EtaDisplay} :
    UnramifiedNormalPairingIsCompact alpha r pp h q d := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ d₀ d₁ z lam₀ lam₁ mu
  set C₀ := ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M with hC₀
  set t := actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M with htdef
  obtain ⟨E, E₂, hfam, hres, hEω⟩ :=
    exists_resolver_base (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) (C := C₀) d
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := fun m ↦ hτ m
  have hS₂ : ∀ m : M, (t.σ ^ E omega2) • m = m := by
    intro m
    rw [hres t.σ]
    exact actionImage_sigma_powOmega2_smul_trivial hM₂ hsimple hτ m
  rw [hfam]
  exact heisEta1_mpcFamOf_evenNormal t E E₂ hM₂ hwild hτ' hS₂ hEω
    (omega2Exp_fourMulExponent_mod_four C₀) d₀ d₁ z lam₀ lam₁ mu

/-- The base-level resolver of `exists_resolver_base`, together with the two `WordLift`-level
resolvers of `exists_resolver_resolvedFamily`: the scalar branch needs both at once, and they
have to be the *same* `E`. -/
theorem exists_resolver_full {alpha r pp h q : ℕ} (d : EtaDisplay)
    {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
    {B : Type*} [AddCommGroup B] [DistribMulAction C B]
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0) :
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
      resolvedFamily alpha r pp h q d (4 * Monoid.exponent C) = mpcFamOf alpha r pp h q d E E₂
        ∧ ResolverLifts E (WordLift A C) ∧ ResolverLifts E (WordLift B C)
        ∧ E omega2 = ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ) := by
  cases d with
  | one =>
      exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
        resolverLifts_uniformWordLift_ramified hA₂, resolverLifts_uniformWordLift_ramified hB₂,
        rfl⟩
  | lit k =>
      exact ⟨_, _, (mpcFamOf_const _ _ _ _ _ _ _).symm,
        resolverLifts_uniformWordLift_ramified hA₂, resolverLifts_uniformWordLift_ramified hB₂,
        rfl⟩
  | hat num den =>
      exact ⟨_, _, rfl, NProcyclic.resolverLifts_npcResolver_wordLift hA₂ ⟨num, den⟩,
        NProcyclic.resolverLifts_npcResolver_wordLift hB₂ ⟨num, den⟩, npcResolver_omega2 _ _⟩

/-- **`exists_resolver_full` with the display's second-order jet appended, at the same `E`.**

This is where the display case-split has to happen.  For `.one` and `.lit` the jet is a constant
(`1`, `|k|`) and can be named in advance; for `.hat num den` it is the *resolver's own value* at
the `η̂` node, `1 + padicOmega2Exp(η − 1, 4·exponent C)`, so it cannot be named before `C` is —
which is why `OddDisplayJet` alone cannot reach the `.hat` display.  Everything downstream
consumes only this package. -/
def ResolverJetSupply (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (A : Type) [AddCommGroup A] [DistribMulAction C A]
    (B : Type) [AddCommGroup B] [DistribMulAction C B],
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (nn : ℕ),
      resolvedFamily alpha r pp h q d (4 * Monoid.exponent C) = mpcFamOf alpha r pp h q d E E₂
        ∧ ResolverLifts E (WordLift A C) ∧ ResolverLifts E (WordLift B C)
        ∧ E omega2 = ((omega2Exp (4 * Monoid.exponent C) : ℕ) : ℤ)
        ∧ MProcyclicNormal.OddJetAt d E nn

/-- A resolver-uniform odd jet supplies the package at every resolver — the `.one` and `.lit`
route. -/
theorem resolverJetSupply_of_oddDisplayJet {alpha r pp h q : ℕ} {d : EtaDisplay} {nn : ℕ}
    (hjet : MProcyclicNormal.OddDisplayJet d nn) : ResolverJetSupply alpha r pp h q d := by
  intro C _ _ A _ _ B _ _ hA₂ hB₂
  obtain ⟨E, E₂, hfam, hliftA, hliftB, hEω⟩ :=
    exists_resolver_full (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      (C := C) (A := A) (B := B) d hA₂ hB₂
  exact ⟨E, E₂, nn, hfam, hliftA, hliftB, hEω, hjet.oddJetAt E⟩

/-- **The `η̂` display supplies the package too**, at the two-valued resolver
`npcResolver N ⟨num, den⟩` it already resolves at, with `n_η = 1 + padicOmega2Exp(η − 1, N)`.
The `2`-adic unit hypothesis is the only extra input, and it is the same one the procyclic-`N`
scalar row consumes. -/
theorem resolverJetSupply_hat {alpha r pp h q : ℕ} {num den : ℤ} (z : ℤ_[2])
    (hz : (EtaData.mk num den).toPadic = 1 + 2 * z) :
    ResolverJetSupply alpha r pp h q (.hat num den) := by
  intro C _ _ A _ _ B _ _ hA₂ hB₂
  exact ⟨_, _, _, rfl, NProcyclic.resolverLifts_npcResolver_wordLift hA₂ ⟨num, den⟩,
    NProcyclic.resolverLifts_npcResolver_wordLift hB₂ ⟨num, den⟩, npcResolver_omega2 _ _,
    MProcyclicNormal.oddJetAt_hat z hz (4 * Monoid.exponent C)⟩

set_option maxHeartbeats 3200000 in
/-- **The scalar sub-branch of the procyclic-`M` unramified obligation, from the display's
jet.**  With every generator acting trivially the complex is the scalar one — `d⁰ = 0`, `d¹` the
`tau`-pivot of rank one, five blocks of normal coordinates — and the traced pairing separates
them as soon as the display's second-order jet at the branch's own resolver is odd.

⚠ Both hypotheses are real.  `α ≥ 2` is what makes `m = 2^{α−1}` and `C(2^α,2)` even, hence the
hat copy silent; at `α = 1` the row acquires the extra atom `γ(c)` from `C₀^{2}`.  And the odd
jet is what makes the `(a_σ, x₂)` plane nondegenerate, exactly as `NpcUnramifiedScalar`'s unit
hypothesis does for the procyclic-`N` row. -/
theorem scalarActionImageStokes_of_supply {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 2 ≤ alpha) (hqe : Even q) (hsupply : ResolverJetSupply alpha r pp h q d) :
    ScalarActionImageStokes alpha r pp h q d := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ hσ
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  set C₀ := ActionImage (2 + 2 * h) q (mpcW alpha r pp d h) M with hC₀
  set t := actionImageMarking (2 + 2 * h) q (mpcW alpha r pp d h) M with htdef
  obtain ⟨E, E₂, nn, hfam, hliftM, hliftD, hEω, hjet⟩ := hsupply C₀ M (ElemDual M) hM₂ hM₂D
  have hlv := levelResolver (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) d
    (by omega) hqe
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
  have htriv : ∀ (g : Generator (2 + 2 * h)) (m : M), t g • m = m :=
    marking_smul_trivial_of_split t hwild hτ' hσ
  have htrivD : ∀ (g : Generator (2 + 2 * h)) (lam : ElemDual M), t g • lam = lam :=
    fun g lam ↦ elemDual_smul_eq_self (htriv g) lam
  rw [hfam] at hend hr
  rw [hfam]
  exact evenScalarStokesDuality_of_separation t _ hM₂ hr hend
    (heisD0_eq_zero_of_split t htriv) (heisD0_eq_zero_of_split t htrivD)
    (MProcyclicUnram.heisD1_mpcFamOf_tauRow_of_split (alpha := alpha) (r := r) (pp := pp)
      t E E₂ hliftM hM₂ (by omega) hqe htriv)
    (MProcyclicUnram.heisD1_mpcFamOf_tauRow_of_split (A := ElemDual M) (alpha := alpha) (r := r)
      (pp := pp) t E E₂ hliftD hM₂D (by omega) hqe htrivD)
    (fun p hp ↦ MProcyclicNormal.mpc_scalarNormal_pairing_separates_left
      (α := alpha) (r := r) (pp := pp) (q := q) t E E₂ hM₂ htriv hEω
      (omega2Exp_fourMulExponent_mod_four C₀) hα hqe hjet.1
      (fun u w ↦ hjet.2 t E₂ hM₂ htriv u w) p hp)

/-- **The scalar sub-branch from a resolver-uniform odd jet** — the `.one` and `.lit` route,
unchanged. -/
theorem scalarActionImageStokes_of_oddJet {alpha r pp h q : ℕ} {d : EtaDisplay} {nn : ℕ}
    (hα : 2 ≤ alpha) (hqe : Even q) (hjet : MProcyclicNormal.OddDisplayJet d nn) :
    ScalarActionImageStokes alpha r pp h q d :=
  scalarActionImageStokes_of_supply hα hqe (resolverJetSupply_of_oddDisplayJet hjet)

/-- **The scalar residue on the `η = 1` row** — merge gate 9's display, so `ℚ₂(√−10)`,
`ℚ₂(√10)` and the one-handle instance. -/
theorem scalarActionImageStokes_one {alpha r pp h q : ℕ} (hα : 2 ≤ alpha) (hqe : Even q) :
    ScalarActionImageStokes alpha r pp h q .one :=
  scalarActionImageStokes_of_oddJet hα hqe MProcyclicNormal.oddDisplayJet_one

/-- **The scalar residue on a literal odd display.** -/
theorem scalarActionImageStokes_lit {alpha r pp h q : ℕ} {k : ℤ} (hα : 2 ≤ alpha)
    (hqe : Even q) (hk : Odd k) : ScalarActionImageStokes alpha r pp h q (.lit k) :=
  scalarActionImageStokes_of_oddJet hα hqe (MProcyclicNormal.oddDisplayJet_lit hk)

/-- **The scalar residue on the genuine `η̂` display**, under the display's `2`-adic unit
hypothesis — the same one `NpcDisplayFor.exists_toPadic_eq_one_add_two_mul` discharges
campaign-side for the procyclic-`N` row. -/
theorem scalarActionImageStokes_hat {alpha r pp h q : ℕ} {num den : ℤ} (z : ℤ_[2])
    (hα : 2 ≤ alpha) (hqe : Even q) (hz : (EtaData.mk num den).toPadic = 1 + 2 * z) :
    ScalarActionImageStokes alpha r pp h q (.hat num den) :=
  scalarActionImageStokes_of_supply hα hqe (resolverJetSupply_hat z hz)

/-- **The procyclic-`M` uniform pushed residue on the selected row, on two second-order inputs**
— the generic unramified pairing is now a theorem. -/
theorem uniformPushedHsimp_of_two {alpha r pp h q : ℕ} {d : EtaDisplay} {eta : ℤ_[2]ˣ}
    (hα : 1 ≤ alpha) (hqe : Even q) (hd : d.RepresentsUnit eta)
    (hsc : ScalarActionImageStokes alpha r pp h q d)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_pairings hα hqe hd unramifiedNormalPairingIsCompact hsc hsep

/-- **The `η = 1` row's uniform pushed residue, on the single ramified input.**  Two of the
three second-order residues of `uniformPushedHsimp_of_pairings` are discharged; what is left is
exactly the ramified normal pairing. -/
theorem uniformPushedHsimp_of_ramified_one {alpha r pp h q : ℕ} (hα : 2 ≤ alpha) (hqe : Even q)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q .one) :
    UniformPushedHsimp alpha r pp h q .one :=
  uniformPushedHsimp_of_residues_one (by omega) hqe unramifiedNormalPairingIsCompact
    (scalarActionImageStokes_one hα hqe) hsep

/-- **The `η̂`-display row's uniform pushed residue, on the single ramified input**, under the
display's `2`-adic unit hypothesis.  The `.hat` twin of `uniformPushedHsimp_of_ramified_one`. -/
theorem uniformPushedHsimp_of_ramified_hat {alpha r pp h q : ℕ} {num den : ℤ} (z : ℤ_[2])
    (hα : 2 ≤ alpha) (hqe : Even q) (hz : (EtaData.mk num den).toPadic = 1 + 2 * z)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q (.hat num den)) :
    UniformPushedHsimp alpha r pp h q (.hat num den) :=
  uniformPushedHsimp_of_residues_hat num den (by omega) hqe unramifiedNormalPairingIsCompact
    (scalarActionImageStokes_hat z hα hqe hz) hsep

end

end GQ2.Dyadic.MProcyclicExact

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.MProcyclicNormal.commR_eq_inv_mul_conjR
#print axioms GQ2.Dyadic.MProcyclicNormal.heisConjR_pure_right
#print axioms GQ2.Dyadic.MProcyclicNormal.heisConjR_pure_left
#print axioms GQ2.Dyadic.MProcyclicNormal.heisCommR_pure_left
#print axioms GQ2.Dyadic.MProcyclicNormal.commR_smul_of_trivial_left
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.mul
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.inv
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.zpow
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.profPow
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.conj
#print axioms GQ2.Dyadic.MProcyclicNormal.IsDead.commLeft
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_prodList
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_of_heisTrivial
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEvalZ_sigma2W_pure
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_sigma2W
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_sig2PowW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_c0W
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_c0HatW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_dW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_aHatW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_bHatW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_e01W
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_zW
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_e2W
#print axioms GQ2.Dyadic.MProcyclicNormal.isDead_mpcHatW
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEvalZ_aW_unram
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEvalZ_bW_unram
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEvalZ_aSq_unram
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEvalZ_commAB_unram
#print axioms GQ2.Dyadic.MProcyclicNormal.sum_z_handleTailW
#print axioms GQ2.Dyadic.MProcyclicNormal.heisZ_mpcW_evenNormal
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEta1_mpcFamOf_apply
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEta1_mpcFamOf_evenNormal
#print axioms GQ2.Dyadic.MProcyclicNormal.triv_sigma2W
#print axioms GQ2.Dyadic.MProcyclicNormal.triv_sig2PowW
#print axioms GQ2.Dyadic.MProcyclicNormal.triv_dW
#print axioms GQ2.Dyadic.MProcyclicNormal.heisZ_mpcW_scalar
#print axioms GQ2.Dyadic.MProcyclicNormal.heisEta1_mpcFamOf_scalarNormal
#print axioms GQ2.Dyadic.MProcyclicNormal.mpc_scalarNormal_pairing_separates_left
#print axioms GQ2.Dyadic.MProcyclicNormal.oddDisplayJet_one
#print axioms GQ2.Dyadic.MProcyclicNormal.oddDisplayJet_lit
#print axioms GQ2.Dyadic.MProcyclicNormal.OddDisplayJet.oddJetAt
#print axioms GQ2.Dyadic.MProcyclicNormal.oddJetAt_hat
#print axioms GQ2.Dyadic.MProcyclicExact.exists_resolver_base
#print axioms GQ2.Dyadic.MProcyclicExact.exists_resolver_full
#print axioms GQ2.Dyadic.MProcyclicExact.resolverJetSupply_of_oddDisplayJet
#print axioms GQ2.Dyadic.MProcyclicExact.resolverJetSupply_hat
#print axioms GQ2.Dyadic.MProcyclicExact.unramifiedNormalPairingIsCompact
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_of_supply
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_of_oddJet
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_one
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_lit
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_hat
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_two
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_ramified_one
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_ramified_hat

end AxiomAudit
