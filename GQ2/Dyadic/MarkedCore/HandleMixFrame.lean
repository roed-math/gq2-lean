/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixEquiv

@[expose] public section

/-!
# Handle mixing, step 3: the frame action, and the Eichler normalisation

**Ticket HM3** of the dyadic campaign (lane MC), implementing the `HandleMixLift` spike memo
`docs/dyadic/handlemixlift-spike.md` §5 (the frame action and the 2-adic parameter) and §7's
third row.  HM1 (`HandleMix.lean`) landed the algebraic ingredients — the handle-block splitting,
the two commutator expansions, and the **exact transvections with 2-adic exponents**; HM2
(`HandleMixEquiv.lean`) assembled the mixing substitution into honest continuous automorphisms
`dmMixEquiv`, `dnMixEquiv` of the presented cores together with the abelian collapse of its four
words.  This file computes what those automorphisms do on the **frame** — the abelianization
coordinates — and performs memo §5's Eichler normalisation, ending at the statement memo §5.3's
ν-clearing recipe consumes: **every 2-adic Eichler coefficient is realized**.

Repo conventions as in the two upstream files: `x ^ g = g⁻¹xg` (`GQ2.conjP`),
`[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`); HM1's naming convention for the `τ` family and its relatives
(**a Lean name's suffix is the letter that MOVES**, whereas the memo's subscript is the letter
whose power is used: `frameTauU j k` moves `ū_j` by `k·v̄_j` and so is the memo's `τ_{v_j}(k)`).

## The frame, in the absence of MC3/MC4

Memo §1.1 writes the frame action against MC3/MC4's `MDecomposition`/`NDecomposition`, whose
field `e` is a chosen isomorphism `D^{ab} ≅ Multiplicative (ZMod 2 × ℤ₂ × ℤ₂ × ℤ₂ × ℤ₂^{2h})`.
Those structures are **not** landed (MC3/MC4 are owner-gated), and HM3 does not need them: a
frame coordinate is a *character*, i.e. a monoid hom out of the core into a commutative group,
and the frame action of an automorphism `Ψ` is what precomposition with `Ψ` does to the tuple of
its values on the generators.  So the file works with

* **`frameMix`** (§1) — the frame action of `Φ_j`, multiplicative, valued in any `CommGroup A`;
  it is `handleMixMark` read commutatively, i.e. exactly HM2's abelian collapse.  The two
  bridges `frame_dmMixEquiv`/`frame_dnMixEquiv` say that any monoid-hom-like `f` into a
  commutative group sees `Φ_j` as `frameMix`.
* **the additive frame** (§2 onward) — `Fin (coreRank h) → M` for a `ℤ_[2]`-module `M`, which is
  the linear-algebra form memo §5 is written in (`M = ℤ_[2]` is the ν-frame, §6).  Additive
  notation is what makes the 2-adic coefficient a *scalar* rather than a `zpowZtwo` exponent,
  and §6 pays the bridge back: HM1's group-level `τ`'s with `k : ℤ_[2]` induce **exactly**
  `frameTauU`/`frameTauV`, by `map_zpowZtwo` (`GQ2/ZtwoPowering.lean:444`).

A substitution acts on markings, so composites read **innermost-first**: `frameMat j T₁ ∘
frameMat j T₂ = frameMat j (T₁ * T₂)`.  Read as automorphisms of the core the assignment is
therefore an anti-homomorphism; since every statement below is an explicit computation, this
only fixes which order the displays are written in.

## Contents, and the memo section each part serves

* **§1 The frame action of `Φ_j`** (memo §5.1's table row for `Φ_j`).  `frameMix` and its seven
  rows; `handleMixMark_eq_frameMix` (HM2's `handleMixD_comm`/`handleMixU_comm` in one line);
  `frame_dmMixEquiv`, `frame_dnMixEquiv` and the two moved rows per core.  The moved letters
  both pick up `c̄ − v̄_j`, so the mod-2 cup condition `k ≡ k′` of memo §2 holds identically —
  HM2's recorded Lean-confirmed collapse.

* **§2 The handle plane, and the exact transvections** (memo §5.1).  `frameMat j T` — the action
  of a 2×2 matrix on the `j`-th handle pair of an additive frame — with `frameMat_one`,
  `frameMat_mul` (so `frameMat j` *is* the `SL₂` dictionary), and the named instances

  | Lean | matrix | memo | frame action |
  |---|---|---|---|
  | `frameTauU j k` | `planeElemU k` | `τ_{v_j}(k)` | `ū_j ↦ ū_j + k·v̄_j` |
  | `frameTauV j k` | `planeElemV k` | `τ_{u_j}(k)` | `v̄_j ↦ v̄_j + k·ū_j` |
  | `frameTauD k` | — | `τ_c(k)` | `d̄ ↦ d̄ + k·c̄` |
  | `frameS j`, `frameSinv j` | `planeS`, `planeSinv` | `S_j` (§4.4) | `ū_j ↦ v̄_j`, `v̄_j ↦ −ū_j` |
  | `frameTheta j w` | `planeDiag w` | `θ_w = diag(w,w⁻¹)` | `ū_j ↦ w·ū_j`, `v̄_j ↦ w⁻¹·v̄_j` |

  `frameS_eq_tau` is memo §4.4's `S_j := τ_{v_j}(1)∘τ_{u_j}(−1)∘τ_{v_j}(1)`.  `frameTauD` is the
  one core-side transvection both relators admit (HM1's `mWord_tau_d`/`nWord_tau_d`); there is
  no `frameTauC`, and that absence is memo §6.4's residue 2, not an oversight.

* **§3 The Eichler elements, `N² = 0`, and `E_j^n = 1 + nN`** (memo §5.2, §4.4).
  `frameNilpU`/`frameNilpV` are the two nilpotent parts and `frameEichlerU j x`,
  `frameEichlerV j x` are `1 + xN`, `1 + xN'`:

  ```
  E_j  = frameEichlerU j 1 :  d̄ ↦ d̄ − v̄_j ,   ū_j ↦ ū_j + c̄     (c̄, v̄_j fixed)
  E'_j = frameEichlerV j 1 :  d̄ ↦ d̄ + ū_j ,   v̄_j ↦ v̄_j + c̄     (c̄, ū_j fixed)
  ```

  with `frameNilpU_frameNilpU`/`frameNilpV_frameNilpV` the literal `N² = 0` (both nilpotents
  land in `⟨c̄, v̄_j⟩` resp. `⟨c̄, ū_j⟩`, on which they vanish),
  `frameEichlerU_frameEichlerU : E^x ∘ E^y = E^{x+y}` its usable form, and
  `frameEichlerU_iterate : (E_j)^[n] = 1 + nN` memo §5.2's `E_j^n = 1 + nN` for integer `n`.
  `frameEichlerU_one_eq` is the normalisation `E_j = τ_c(−1) ∘ τ_{v_j}(1) ∘ Φ_j` that turns
  HM2's `Φ_j` into the **pure** Eichler element, and `frameEichlerV_eq_conj` is memo §4.4's
  second family `E'_j = S_j⁻¹ ∘ E_j ∘ S_j`.

* **§4 The 2-adic parameter** (memo §5.2).  `frameTheta_frameEichlerU_frameTheta` is the
  conjugation identity

  ```
  θ_w⁻¹ ∘ E_j^x ∘ θ_w  =  E_j^{w⁻¹·x} ,
  ```

  `exists_natCast_mul_unitInv` is memo §5.2's `{n·w⁻¹ : n ∈ ℕ, w ∈ ℤ₂ˣ} = ℤ₂` (every `x ∈ ℤ₂`
  is `2^{v(x)}·unit`, `PadicInt.unitCoeff_spec`), and the two headline theorems
  `exists_frameEichlerU_theta_conj`, `exists_frameEichlerV_theta_conj` combine them: **for every
  `x : ℤ_[2]` the Eichler element with coefficient `x` is an integer power of `E_j` conjugated by
  a `θ_w`** — memo §5.2's "every 2-adic coefficient is realized by an exact automorphism", with
  no compactness of `Aut(D_P)` and no B8.

* **§5 `SL₂ = E₂` over `ℤ₂`** (memo §5.1's parenthesis, memo §5.3's input).  `planeDiag_eq` is
  the five-factor Bruhat-type factorization `θ_w = τ_{v_j}(w)·τ_{u_j}(−w⁻¹)·τ_{v_j}(w−1)·
  τ_{u_j}(1)·τ_{v_j}(−1)`, which is the **only** instance memo §5.2 consumes;
  `mem_closure_planeElemSet_of_det_eq_one` is the general fact (mathlib has no
  elementary-generation theorem for `SL₂` over a ring, so the 2×2 local-ring argument is given:
  `IsLocalRing.isUnit_or_isUnit_of_isUnit_add` on `det = a·d − b·c = 1` makes `a` or `b` a unit,
  and one right multiplication by `τ_{u_j}(1)` reduces the second case to the first); and
  `frameMatEnd_mem_closure` transfers any such factorization to the frame through the monoid hom
  `frameMatEnd j` (whose two generating families are `frameTauU j k` and `frameTauV j k`), and
  `frameTheta_mem_closure` is the `θ_w` instance in that form.

* **§6 The ν-frame** (what HM4 reads).  `nuFrame f m = fun i => toAdd (f (m i))` for a
  `Multiplicative ℤ_[2]`-valued character `f`, together with the four theorems that identify the
  frame action of the *group-level* moves with §2–§3's linear maps:
  `nuFrame_tau_handleU`, `nuFrame_tau_handleV` and `nuFrame_tau_three` (HM1's
  `mRelWord_tau_handleU`- and `mWord_tau_d`-style updates, with `k : ℤ_[2]`) and
  `nuFrame_handleMixMark` (HM2's `Φ_j`), plus the two per-core corollaries
  `nuFrame_dmMixEquiv`, `nuFrame_dnMixEquiv`.

## What HM4 consumes from here

The ν-clearing of memo §5.3 needs, per handle `j` and per 2-adic coefficient, a frame map in
`A(P,h)` and its effect on `ν'`.  This file realizes the frame-level half of that generating set:

* the **`ū_j`-clearing family**: `exists_frameEichlerU_theta_conj` supplies, for every
  `x : ℤ_[2]`, an `n : ℕ` and `w : ℤ_[2]ˣ` with
  `frameTheta j w⁻¹ ∘ (frameEichlerU j 1)^[n] ∘ frameTheta j w = frameEichlerU j x`, and
  `frameEichlerU_three`/`_handleU_self`/`_handleU_of_ne`/`_handleV`/`_two` are its rows: only
  `d̄` and `ū_j` move, `d̄` by `−x·v̄_j` and `ū_j` by `x·c̄`.  So `ν'(ū_j) ↦ ν'(ū_j) + x·ν'(c̄)`,
  which clears `ν'(ū_j)` at `x = −ν'(ū_j)/ν'(c̄)` when `ν'(c̄) ∈ ℤ₂ˣ` (memo §5.3 step 1, and
  memo §6.4's residue 2 is exactly that unit hypothesis on the `M` side).
* the **`v̄_j`-clearing family**: `exists_frameEichlerV_theta_conj` and the `frameEichlerV` rows,
  which fix `ū_j` — so memo §5.3's step 2 does not undo step 1.
* the **group-level realization**: `nuFrame_tau_handleU`/`_handleV`/`_three` and
  `nuFrame_handleMixMark` are the dictionary between HM1/HM2's automorphisms and these linear
  maps — the three `τ` rows are exactly the ones `frameEichlerU_one_eq`, `frameS_eq_tau` and
  `planeDiag_eq` compose, so every element of the §4 family is covered; assembling the `τ`'s into
  `ContinuousMulEquiv`s (HM1 gives their relator invariance, HM2's `thetaEquiv` pattern gives
  the assembly recipe) is HM4's first step, and this file's §6 is what turns each assembled
  automorphism into its frame row.

## Axiom hygiene

Every declaration prints within **std-3** (`propext`, `Classical.choice`, `Quot.sound`), and the
§1–§5 frame calculus — which is pure module and matrix algebra — within less.  **No census axiom
is reachable, in particular no B8** (`PeripheralCyclotomicAction`): memo V4's claim that the
2-adic parameter needs neither the peripheral action nor compactness of `Aut(D_P)` is measured
here rather than asserted, since the only 2-adic input is `zpowZtwo` (§6) and the only
`SL₂`-input is the explicit factorization of §5.  The census stays at 11.

## Deviations from the memo (recorded)

* **Family.**  As in HM2, the element realized is memo §4.4's `Φ^M_j` (the rank-four cores'
  prefixes contain `c` and not `d`), so the moved letters are `d` and `u_j`, not the memo §4.1
  display's `a` and `u_j`.  Consequently the memo's `E_j := τ_{v_j}(1) ∘ τ_σ(1) ∘ Φ_j` becomes
  `frameEichlerU j 1 = τ_c(−1) ∘ τ_{v_j}(1) ∘ Φ_j` and its `c̄`-coefficient is `+1` where the
  memo's `σ̄`-coefficient is `−1`.  Both are "the" pure Eichler element: the family of §4
  realizes **every** coefficient, so the sign convention is immaterial downstream.
* **`E'_j`.**  Memo §4.4 defines `E'_j := τ_{u_j}(−1) ∘ (S_j ∘ Φ_j ∘ S_j⁻¹)` and displays the
  frame action `ā ↦ ā − σ̄ + ū_j`, `v̄_j ↦ v̄_j − σ̄`.  The extra `τ_{u_j}(−1)` normalisation is
  dropped here: the plain conjugate `frameEichlerV j x = S_j⁻¹ ∘ E_j^x ∘ S_j` already fixes
  `ū_j` (which is what memo §5.3 step 2 uses) and its `d̄`-row is the clean `d̄ ↦ d̄ + x·ū_j`.
* **`MDecomposition`.**  Stated against characters rather than against a chosen frame
  isomorphism `e`, for the reason given above; the `e`-row form of any statement below is
  obtained by taking `f = (coordinate of e) ∘ abMk`.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 The frame action of `Φ_j`  (memo §5.1)

HM2's `handleMixMark` becomes linear on a commutative target: every `ζ_j`-conjugate dies and
both moved letters pick up `c̄ − v̄_j`.  That is the row of memo §5.1's table for `Φ_j`, and it
is the only input §3's Eichler normalisation needs from the word calculus. -/

section FrameMix

variable {G : Type*} {h : ℕ}

/-- **A two-slot update is invisible away from its two slots** — the missing generic row of
HM2's `handleMixUpdate` API (its named rows cover the core letters and the handles). -/
theorem handleMixUpdate_of_ne (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G)
    {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (h3 : i ≠ 3) :
    handleMixUpdate j m wd wu i = m i := by
  rw [handleMixUpdate, Function.update_of_ne hU, Function.update_of_ne h3]

end FrameMix

/-! ### Two index facts about the core letter `2`

The letter `c` sits at index `2` and every Eichler direction of §3 reads it, so the two
inequalities separating `2` from `3` and from the handle letters are used throughout. -/

/-- The core letter `2` sits below the handle letters. -/
theorem coreVal_two_lt {h : ℕ} : ((2 : Fin (coreRank h)) : ℕ) < 4 := by
  rw [coreVal_two]; omega

/-- The core letters `2` and `3` are distinct. -/
theorem coreTwo_ne_three {h : ℕ} : (2 : Fin (coreRank h)) ≠ 3 := by
  intro hc
  have hv : ((2 : Fin (coreRank h)) : ℕ) = ((3 : Fin (coreRank h)) : ℕ) := by rw [hc]
  rw [coreVal_two, coreVal_three] at hv
  omega

section FrameMixComm

variable {A : Type*} [CommGroup A] {h : ℕ}

/-- **The frame action of `Φ_j`** (memo §5.1's table): on a *commutative* target the mixing
substitution of HM2 collapses to the two-slot linear update

```
d̄ ↦ d̄ + c̄ − v̄_j ,      ū_j ↦ ū_j + c̄ − v̄_j
```

with `c̄`, `v̄_j`, the other handles and the remaining core letters fixed.  Both moved letters
pick up the *same* correction `c̄ − v̄_j`, which is why memo §2's mod-2 cup condition `k ≡ k′`
holds identically and `Φ_j` is already `E_j`-like. -/
def frameMix (j : Fin h) (m : Fin (coreRank h) → A) : Fin (coreRank h) → A :=
  handleMixUpdate j m (m 2 * m 3 * (m (handleIdxV j))⁻¹)
    (m (handleIdxU j) * m 2 * (m (handleIdxV j))⁻¹)

variable (j : Fin h) (m : Fin (coreRank h) → A)

/-- **HM2's abelian collapse, in one line**: the mixing substitution *is* the frame action. -/
theorem handleMixMark_eq_frameMix : handleMixMark j m = frameMix j m := by
  rw [handleMixMark, frameMix, handleMixD_comm, handleMixU_comm]

@[simp] theorem frameMix_zero : frameMix j m 0 = m 0 := handleMixUpdate_zero _ _ _ _

@[simp] theorem frameMix_one : frameMix j m 1 = m 1 := handleMixUpdate_one _ _ _ _

@[simp] theorem frameMix_two : frameMix j m 2 = m 2 := handleMixUpdate_two _ _ _ _

/-- The `d̄`-row of memo §5.1's table: `d̄ ↦ d̄ + c̄ − v̄_j`. -/
@[simp] theorem frameMix_three : frameMix j m 3 = m 2 * m 3 * (m (handleIdxV j))⁻¹ :=
  handleMixUpdate_three _ _ _ _

/-- The `ū_j`-row of memo §5.1's table: `ū_j ↦ ū_j + c̄ − v̄_j`. -/
@[simp] theorem frameMix_handleU_self :
    frameMix j m (handleIdxU j) = m (handleIdxU j) * m 2 * (m (handleIdxV j))⁻¹ :=
  handleMixUpdate_handleU_self _ _ _ _

theorem frameMix_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    frameMix j m (handleIdxU i) = m (handleIdxU i) :=
  handleMixUpdate_handleU_of_ne _ _ _ _ hij

@[simp] theorem frameMix_handleV (i : Fin h) : frameMix j m (handleIdxV i) = m (handleIdxV i) :=
  handleMixUpdate_handleV _ _ _ _ _

theorem frameMix_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (h3 : i ≠ 3) :
    frameMix j m i = m i :=
  handleMixUpdate_of_ne _ _ _ _ hU h3

end FrameMixComm

/-! ### Reading the frame action off HM2's automorphisms

A frame coordinate is a character, so the frame action of `dmMixEquiv`/`dnMixEquiv` is what any
monoid-hom-like map into a commutative group does to the generator values. -/

section FrameMixEquiv

variable {A : Type*} [CommGroup A] (α h : ℕ) (j : Fin h)

/-- **The frame action of `Φ_j` on `D_{M,α,h}`** (memo §5.1): every character into a commutative
group sees HM2's mixing automorphism as `frameMix`. -/
theorem frame_dmMixEquiv {F : Type*} [FunLike F (DM α h : Type) A]
    [MonoidHomClass F (DM α h : Type) A] (f : F) (i : Fin (coreRank h)) :
    f (dmMixEquiv α h j (dmGen α h i)) = frameMix j (fun i => f (dmGen α h i)) i := by
  rw [dmMixEquiv_gen, map_handleMixMark, handleMixMark_eq_frameMix]

/-- The moved core letter of `D_M`, at the frame level: `d̄ ↦ d̄ + c̄ − v̄_j`. -/
theorem frame_dmMixEquiv_dmD {F : Type*} [FunLike F (DM α h : Type) A]
    [MonoidHomClass F (DM α h : Type) A] (f : F) :
    f (dmMixEquiv α h j (dmD α h))
      = f (dmC α h) * f (dmD α h) * (f (dmGen α h (handleIdxV j)))⁻¹ := by
  rw [dmC, dmD, frame_dmMixEquiv, frameMix_three]

/-- The moved handle letter of `D_M`, at the frame level: `ū_j ↦ ū_j + c̄ − v̄_j`. -/
theorem frame_dmMixEquiv_handleU {F : Type*} [FunLike F (DM α h : Type) A]
    [MonoidHomClass F (DM α h : Type) A] (f : F) :
    f (dmMixEquiv α h j (dmGen α h (handleIdxU j)))
      = f (dmGen α h (handleIdxU j)) * f (dmC α h) * (f (dmGen α h (handleIdxV j)))⁻¹ := by
  rw [dmC, frame_dmMixEquiv, frameMix_handleU_self]

/-- **The frame action of `Φ_j` on `D_{N,α,h}`** (memo §4.4: for `N` both families apply). -/
theorem frame_dnMixEquiv {F : Type*} [FunLike F (DN α h : Type) A]
    [MonoidHomClass F (DN α h : Type) A] (f : F) (i : Fin (coreRank h)) :
    f (dnMixEquiv α h j (dnGen α h i)) = frameMix j (fun i => f (dnGen α h i)) i := by
  rw [dnMixEquiv_gen, map_handleMixMark, handleMixMark_eq_frameMix]

/-- The moved core letter of `D_N`, at the frame level: `x̄₂ ↦ x̄₂ + σ̄ − v̄_j`. -/
theorem frame_dnMixEquiv_dnX2 {F : Type*} [FunLike F (DN α h : Type) A]
    [MonoidHomClass F (DN α h : Type) A] (f : F) :
    f (dnMixEquiv α h j (dnX2 α h))
      = f (dnSigma α h) * f (dnX2 α h) * (f (dnGen α h (handleIdxV j)))⁻¹ := by
  rw [dnSigma, dnX2, frame_dnMixEquiv, frameMix_three]

/-- The moved handle letter of `D_N`, at the frame level: `ū_j ↦ ū_j + σ̄ − v̄_j`. -/
theorem frame_dnMixEquiv_handleU {F : Type*} [FunLike F (DN α h : Type) A]
    [MonoidHomClass F (DN α h : Type) A] (f : F) :
    f (dnMixEquiv α h j (dnGen α h (handleIdxU j)))
      = f (dnGen α h (handleIdxU j)) * f (dnSigma α h) * (f (dnGen α h (handleIdxV j)))⁻¹ := by
  rw [dnSigma, frame_dnMixEquiv, frameMix_handleU_self]

end FrameMixEquiv

/-! ## §2 The handle plane, and the exact transvections  (memo §5.1)

Memo §5 is linear algebra on the frame, so from here on a frame is an additive
`Fin (coreRank h) → M` with `M` a `ℤ_[2]`-module — the form in which the 2-adic coefficient is a
*scalar*.  §6 pays the bridge back to the group-level `zpowZtwo` exponents.

The intra-handle moves all act through the `j`-th handle plane `⟨ū_j, v̄_j⟩`, so they are packaged
once, as the action of a 2×2 matrix; `frameMat_one` and `frameMat_mul` make `frameMat j` the
`SL₂(ℤ_[2])`-dictionary that §5 needs. -/

/-! ### The 2×2 matrices of the handle plane -/

/-- `E(k)`, memo §5.1's `τ_{v_j}(k)` as a matrix: the letter that MOVES is `u_j`. -/
noncomputable def planeElemU (k : ℤ_[2]) : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![1, k; 0, 1]

/-- `F(k)`, memo §5.1's `τ_{u_j}(k)` as a matrix: the letter that MOVES is `v_j`. -/
noncomputable def planeElemV (k : ℤ_[2]) : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![1, 0; k, 1]

/-- Memo §4.4's intra-handle `S`-move `ū_j ↦ v̄_j`, `v̄_j ↦ −ū_j`. -/
noncomputable def planeS : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![0, 1; -1, 0]

/-- The inverse `S`-move `ū_j ↦ −v̄_j`, `v̄_j ↦ ū_j`. -/
noncomputable def planeSinv : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![0, -1; 1, 0]

/-- Memo §5.2's `θ_w = diag(w, w⁻¹)`, the intra-handle unit rescaling. -/
noncomputable def planeDiag (w : ℤ_[2]ˣ) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  !![(w : ℤ_[2]), 0; 0, ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2])]

@[simp] theorem planeS_mul_planeSinv : planeS * planeSinv = 1 := by
  rw [planeS, planeSinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

@[simp] theorem planeSinv_mul_planeS : planeSinv * planeS = 1 := by
  rw [planeS, planeSinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem planeElemU_mul_planeElemU (k l : ℤ_[2]) :
    planeElemU k * planeElemU l = planeElemU (k + l) := by
  rw [planeElemU, planeElemU, planeElemU, Matrix.mul_fin_two]
  norm_num [add_comm]

theorem planeElemV_mul_planeElemV (k l : ℤ_[2]) :
    planeElemV k * planeElemV l = planeElemV (k + l) := by
  rw [planeElemV, planeElemV, planeElemV, Matrix.mul_fin_two]
  norm_num [add_comm]

@[simp] theorem planeElemU_zero : planeElemU 0 = 1 := by
  rw [planeElemU]; exact Matrix.one_fin_two.symm

@[simp] theorem planeElemV_zero : planeElemV 0 = 1 := by
  rw [planeElemV]; exact Matrix.one_fin_two.symm

@[simp] theorem planeElemU_det (k : ℤ_[2]) : (planeElemU k).det = 1 := by
  rw [planeElemU, Matrix.det_fin_two]
  norm_num

@[simp] theorem planeElemV_det (k : ℤ_[2]) : (planeElemV k).det = 1 := by
  rw [planeElemV, Matrix.det_fin_two]
  norm_num

theorem planeDiag_mul_planeDiag (w₁ w₂ : ℤ_[2]ˣ) :
    planeDiag w₁ * planeDiag w₂ = planeDiag (w₁ * w₂) := by
  rw [planeDiag, planeDiag, planeDiag, Matrix.mul_fin_two]
  norm_num [mul_comm]

@[simp] theorem planeDiag_one : planeDiag 1 = 1 := by
  rw [planeDiag, Matrix.one_fin_two]
  norm_num

/-- Memo §4.4's `S_j = τ_{v_j}(1) ∘ τ_{u_j}(−1) ∘ τ_{v_j}(1)`, at matrix level. -/
theorem planeS_eq : planeS = planeElemU 1 * planeElemV (-1) * planeElemU 1 := by
  rw [planeElemU, planeElemV, planeS, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-! ### The matrix action on a frame -/

section FrameMat

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {h : ℕ}

/-- **The action of a 2×2 matrix on the `j`-th handle plane** of an additive frame: the two
handle coordinates transform by `T` and every other coordinate is fixed.  Memo §5.1's "the last
two [transvections] generate `SL₂(ℤ₂)` on each handle plane" is `frameMat_mul` plus §5. -/
noncomputable def frameMat (j : Fin h) (T : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  Function.update
    (Function.update m (handleIdxU j) (T 0 0 • m (handleIdxU j) + T 0 1 • m (handleIdxV j)))
    (handleIdxV j) (T 1 0 • m (handleIdxU j) + T 1 1 • m (handleIdxV j))

variable (j : Fin h) (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) (m : Fin (coreRank h) → M)

@[simp] theorem frameMat_handleU_self :
    frameMat j T m (handleIdxU j) = T 0 0 • m (handleIdxU j) + T 0 1 • m (handleIdxV j) := by
  rw [frameMat, Function.update_of_ne (handleIdxU_ne_handleIdxV j j), Function.update_self]

@[simp] theorem frameMat_handleV_self :
    frameMat j T m (handleIdxV j) = T 1 0 • m (handleIdxU j) + T 1 1 • m (handleIdxV j) := by
  rw [frameMat, Function.update_self]

theorem frameMat_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (hV : i ≠ handleIdxV j) :
    frameMat j T m i = m i := by
  rw [frameMat, Function.update_of_ne hV, Function.update_of_ne hU]

theorem frameMat_of_val_lt {i : Fin (coreRank h)} (hi : (i : ℕ) < 4) : frameMat j T m i = m i :=
  frameMat_of_ne _ _ _ (Ne.symm (handleIdxU_ne_of_val_lt j hi))
    (Ne.symm (handleIdxV_ne_of_val_lt j hi))

@[simp] theorem frameMat_two : frameMat j T m 2 = m 2 :=
  frameMat_of_val_lt _ _ _ (by rw [coreVal_two]; omega)

@[simp] theorem frameMat_three : frameMat j T m 3 = m 3 :=
  frameMat_of_val_lt _ _ _ (by rw [coreVal_three]; omega)

theorem frameMat_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    frameMat j T m (handleIdxU i) = m (handleIdxU i) :=
  frameMat_of_ne _ _ _ (fun hc => hij (handleIdxU_injective hc)) (handleIdxU_ne_handleIdxV i j)

theorem frameMat_handleV_of_ne {i : Fin h} (hij : i ≠ j) :
    frameMat j T m (handleIdxV i) = m (handleIdxV i) :=
  frameMat_of_ne _ _ _ (Ne.symm (handleIdxU_ne_handleIdxV j i))
    (fun hc => hij (handleIdxV_injective hc))

@[simp] theorem frameMat_one : frameMat j (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) m = m := by
  funext i
  by_cases hU : i = handleIdxU j
  · subst hU; simp
  by_cases hV : i = handleIdxV j
  · subst hV; simp
  exact frameMat_of_ne _ _ _ hU hV

/-- **The matrix action is multiplicative** — the `SL₂` dictionary.  Substitutions compose
innermost-first, so this is a homomorphism in the natural order. -/
theorem frameMat_mul (T₁ T₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    frameMat j (T₁ * T₂) m = frameMat j T₁ (frameMat j T₂ m) := by
  funext i
  by_cases hU : i = handleIdxU j
  · subst hU
    simp only [frameMat_handleU_self, frameMat_handleV_self, Matrix.mul_apply, Fin.sum_univ_two]
    module
  by_cases hV : i = handleIdxV j
  · subst hV
    simp only [frameMat_handleU_self, frameMat_handleV_self, Matrix.mul_apply, Fin.sum_univ_two]
    module
  rw [frameMat_of_ne _ _ _ hU hV, frameMat_of_ne _ _ _ hU hV, frameMat_of_ne _ _ _ hU hV]

end FrameMat

/-! ### The named intra-handle moves (memo §5.1, §4.4, §5.2) -/

section FrameTau

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {h : ℕ}

/-- **Memo §5.1's `τ_{v_j}(k)`** at the frame level: `ū_j ↦ ū_j + k·v̄_j`.  HM1's
`handleWord_tau_u`/`mRelWord_tau_handleU` is its group-level realization, exact for every
`k : ℤ_[2]`; §6's `nuFrame_tau_handleU` is the bridge. -/
noncomputable def frameTauU (j : Fin h) (k : ℤ_[2]) (m : Fin (coreRank h) → M) :
    Fin (coreRank h) → M := frameMat j (planeElemU k) m

/-- **Memo §5.1's `τ_{u_j}(k)`** at the frame level: `v̄_j ↦ v̄_j + k·ū_j`. -/
noncomputable def frameTauV (j : Fin h) (k : ℤ_[2]) (m : Fin (coreRank h) → M) :
    Fin (coreRank h) → M := frameMat j (planeElemV k) m

/-- **Memo §4.4's intra-handle `S`-move** `S_j`: `ū_j ↦ v̄_j`, `v̄_j ↦ −ū_j`. -/
noncomputable def frameS (j : Fin h) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  frameMat j planeS m

/-- The inverse `S`-move. -/
noncomputable def frameSinv (j : Fin h) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  frameMat j planeSinv m

/-- **Memo §5.2's `θ_w = diag(w, w⁻¹)`** at the frame level: `ū_j ↦ w·ū_j`, `v̄_j ↦ w⁻¹·v̄_j`. -/
noncomputable def frameTheta (j : Fin h) (w : ℤ_[2]ˣ) (m : Fin (coreRank h) → M) :
    Fin (coreRank h) → M := frameMat j (planeDiag w) m

variable (j : Fin h) (m : Fin (coreRank h) → M)

@[simp] theorem frameTauU_handleU_self (k : ℤ_[2]) :
    frameTauU j k m (handleIdxU j) = m (handleIdxU j) + k • m (handleIdxV j) := by
  rw [frameTauU, frameMat_handleU_self, planeElemU]
  norm_num

@[simp] theorem frameTauU_handleV_self (k : ℤ_[2]) :
    frameTauU j k m (handleIdxV j) = m (handleIdxV j) := by
  rw [frameTauU, frameMat_handleV_self, planeElemU]
  norm_num

theorem frameTauU_of_ne (k : ℤ_[2]) {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j)
    (hV : i ≠ handleIdxV j) : frameTauU j k m i = m i :=
  frameMat_of_ne _ _ _ hU hV

@[simp] theorem frameTauV_handleV_self (k : ℤ_[2]) :
    frameTauV j k m (handleIdxV j) = m (handleIdxV j) + k • m (handleIdxU j) := by
  rw [frameTauV, frameMat_handleV_self, planeElemV]
  norm_num [add_comm]

@[simp] theorem frameTauV_handleU_self (k : ℤ_[2]) :
    frameTauV j k m (handleIdxU j) = m (handleIdxU j) := by
  rw [frameTauV, frameMat_handleU_self, planeElemV]
  norm_num

theorem frameTauV_of_ne (k : ℤ_[2]) {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j)
    (hV : i ≠ handleIdxV j) : frameTauV j k m i = m i :=
  frameMat_of_ne _ _ _ hU hV

@[simp] theorem frameS_handleU_self : frameS j m (handleIdxU j) = m (handleIdxV j) := by
  rw [frameS, frameMat_handleU_self, planeS]
  norm_num

@[simp] theorem frameS_handleV_self : frameS j m (handleIdxV j) = -m (handleIdxU j) := by
  rw [frameS, frameMat_handleV_self, planeS]
  norm_num

theorem frameS_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (hV : i ≠ handleIdxV j) :
    frameS j m i = m i := frameMat_of_ne _ _ _ hU hV

@[simp] theorem frameSinv_handleU_self : frameSinv j m (handleIdxU j) = -m (handleIdxV j) := by
  rw [frameSinv, frameMat_handleU_self, planeSinv]
  norm_num

@[simp] theorem frameSinv_handleV_self : frameSinv j m (handleIdxV j) = m (handleIdxU j) := by
  rw [frameSinv, frameMat_handleV_self, planeSinv]
  norm_num

theorem frameSinv_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (hV : i ≠ handleIdxV j) :
    frameSinv j m i = m i := frameMat_of_ne _ _ _ hU hV

@[simp] theorem frameTheta_handleU_self (w : ℤ_[2]ˣ) :
    frameTheta j w m (handleIdxU j) = (w : ℤ_[2]) • m (handleIdxU j) := by
  rw [frameTheta, frameMat_handleU_self, planeDiag]
  norm_num

@[simp] theorem frameTheta_handleV_self (w : ℤ_[2]ˣ) :
    frameTheta j w m (handleIdxV j) = ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) • m (handleIdxV j) := by
  rw [frameTheta, frameMat_handleV_self, planeDiag]
  norm_num

theorem frameTheta_of_ne (w : ℤ_[2]ˣ) {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j)
    (hV : i ≠ handleIdxV j) : frameTheta j w m i = m i := frameMat_of_ne _ _ _ hU hV

/-- The `τ_{v_j}` family is a one-parameter group of frame maps (memo §5.1: the exponent is a
`zpowZtwo`, so the group is `ℤ_[2]` and not just `ℤ`). -/
theorem frameTauU_frameTauU (k l : ℤ_[2]) :
    frameTauU j k (frameTauU j l m) = frameTauU j (k + l) m := by
  rw [frameTauU, frameTauU, frameTauU, ← frameMat_mul, planeElemU_mul_planeElemU]

theorem frameTauV_frameTauV (k l : ℤ_[2]) :
    frameTauV j k (frameTauV j l m) = frameTauV j (k + l) m := by
  rw [frameTauV, frameTauV, frameTauV, ← frameMat_mul, planeElemV_mul_planeElemV]

@[simp] theorem frameTauU_zero : frameTauU j 0 m = m := by
  rw [frameTauU, planeElemU_zero, frameMat_one]

@[simp] theorem frameTauV_zero : frameTauV j 0 m = m := by
  rw [frameTauV, planeElemV_zero, frameMat_one]

/-- `S_j⁻¹ ∘ S_j = id`. -/
@[simp] theorem frameSinv_frameS : frameSinv j (frameS j m) = m := by
  rw [frameSinv, frameS, ← frameMat_mul, planeSinv_mul_planeS, frameMat_one]

/-- `S_j ∘ S_j⁻¹ = id`. -/
@[simp] theorem frameS_frameSinv : frameS j (frameSinv j m) = m := by
  rw [frameSinv, frameS, ← frameMat_mul, planeS_mul_planeSinv, frameMat_one]

/-- **Memo §4.4's `S_j := τ_{v_j}(1) ∘ τ_{u_j}(−1) ∘ τ_{v_j}(1)`**: the `S`-move is a composite
of exact transvections, hence an honest automorphism of the core. -/
theorem frameS_eq_tau : frameS j m = frameTauU j 1 (frameTauV j (-1) (frameTauU j 1 m)) := by
  rw [frameS, frameTauU, frameTauV, frameTauU, ← frameMat_mul, ← frameMat_mul, planeS_eq]

theorem frameTheta_frameTheta (w₁ w₂ : ℤ_[2]ˣ) :
    frameTheta j w₁ (frameTheta j w₂ m) = frameTheta j (w₁ * w₂) m := by
  rw [frameTheta, frameTheta, frameTheta, ← frameMat_mul, planeDiag_mul_planeDiag]

@[simp] theorem frameTheta_one : frameTheta j 1 m = m := by
  rw [frameTheta, planeDiag_one, frameMat_one]

@[simp] theorem frameTheta_inv_frameTheta (w : ℤ_[2]ˣ) :
    frameTheta j w⁻¹ (frameTheta j w m) = m := by
  rw [frameTheta_frameTheta, inv_mul_cancel, frameTheta_one]

end FrameTau

/-! ## §3 The Eichler elements, `N² = 0`, and `E_j^n = 1 + nN`  (memo §5.2, §4.4)

Memo §5.2's normalisation `E_j := τ_{v_j}(1) ∘ τ_σ(1) ∘ Φ_j` turns `Φ_j`'s frame action into a
**single** Eichler direction: with the rank-four families' letters (HM2's family swap) it is
`E_j = τ_c(−1) ∘ τ_{v_j}(1) ∘ Φ_j`, moving `d̄` by `−v̄_j` and `ū_j` by `+c̄`.  Its nilpotent part
`N` lands in `⟨c̄, v̄_j⟩`, where `N` vanishes — that is `N² = 0`, and hence `E_j^n = 1 + nN`. -/
/-! ### `Φ_j` and the two nilpotent parts, additively

None of these needs the `ℤ_[2]`-module structure: `Φ_j`'s frame action is a sum of coordinates,
and each nilpotent part is a *single* Eichler direction with coefficient one. -/

section EichlerBase

variable {M : Type*} [AddCommGroup M] {h : ℕ}

/-- **The frame action of `Φ_j`, additively**: `d̄ ↦ d̄ + c̄ − v̄_j`, `ū_j ↦ ū_j + c̄ − v̄_j`.  This
is §1's `frameMix` in the additive notation memo §5 uses (`frameMix_ofAdd`). -/
def frameMixAdd (j : Fin h) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  handleMixUpdate j m (m 2 + m 3 - m (handleIdxV j))
    (m (handleIdxU j) + m 2 - m (handleIdxV j))

/-- **The nilpotent part `N` of memo §5.2's `E_j`**: it sends `d̄ ↦ −v̄_j` and `ū_j ↦ c̄`, and
kills every other coordinate — in particular `c̄` and `v̄_j`, which is `N² = 0`. -/
def frameNilpU (j : Fin h) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  handleMixUpdate j (0 : Fin (coreRank h) → M) (-m (handleIdxV j)) (m 2)

/-- **The nilpotent part `N'` of memo §4.4's second family `E'_j`**: it sends `d̄ ↦ ū_j` and
`v̄_j ↦ c̄`, and kills every other coordinate — in particular `c̄` and `ū_j`. -/
def frameNilpV (j : Fin h) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  Function.update (Function.update (0 : Fin (coreRank h) → M) 3 (m (handleIdxU j)))
    (handleIdxV j) (m 2)

variable (j : Fin h) (m : Fin (coreRank h) → M)

@[simp] theorem frameMixAdd_three :
    frameMixAdd j m 3 = m 2 + m 3 - m (handleIdxV j) := handleMixUpdate_three _ _ _ _

@[simp] theorem frameMixAdd_handleU_self :
    frameMixAdd j m (handleIdxU j) = m (handleIdxU j) + m 2 - m (handleIdxV j) :=
  handleMixUpdate_handleU_self _ _ _ _

@[simp] theorem frameMixAdd_two : frameMixAdd j m 2 = m 2 := handleMixUpdate_two _ _ _ _

@[simp] theorem frameMixAdd_handleV (i : Fin h) :
    frameMixAdd j m (handleIdxV i) = m (handleIdxV i) := handleMixUpdate_handleV _ _ _ _ _

theorem frameMixAdd_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (h3 : i ≠ 3) :
    frameMixAdd j m i = m i := handleMixUpdate_of_ne _ _ _ _ hU h3

/-- **§1's frame action, read additively** — the bridge that lets §3–§5 work in a `ℤ_[2]`-module
while §1 keeps HM2's multiplicative statement. -/
theorem frameMix_ofAdd (i : Fin (coreRank h)) :
    frameMix j (fun i => (ofAdd (m i) : Multiplicative M)) i = ofAdd (frameMixAdd j m i) := by
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [frameMix_handleU_self, frameMixAdd_handleU_self, ofAdd_sub, ofAdd_add, div_eq_mul_inv]
  by_cases h3 : i = 3
  · subst h3
    rw [frameMix_three, frameMixAdd_three, ofAdd_sub, ofAdd_add, div_eq_mul_inv]
  rw [frameMix_of_ne _ _ hU h3, frameMixAdd_of_ne _ _ hU h3]

@[simp] theorem frameNilpU_three : frameNilpU j m 3 = -m (handleIdxV j) :=
  handleMixUpdate_three _ _ _ _

@[simp] theorem frameNilpU_handleU_self : frameNilpU j m (handleIdxU j) = m 2 :=
  handleMixUpdate_handleU_self _ _ _ _

theorem frameNilpU_of_ne {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j) (h3 : i ≠ 3) :
    frameNilpU j m i = 0 := handleMixUpdate_of_ne _ _ _ _ hU h3

@[simp] theorem frameNilpU_two : frameNilpU j m 2 = 0 :=
  frameNilpU_of_ne _ _ (handleIdxU_ne_of_val_lt j coreVal_two_lt).symm coreTwo_ne_three

@[simp] theorem frameNilpU_handleV (i : Fin h) : frameNilpU j m (handleIdxV i) = 0 :=
  handleMixUpdate_handleV _ _ _ _ _

@[simp] theorem frameNilpV_three : frameNilpV j m 3 = m (handleIdxU j) := by
  rw [frameNilpV, Function.update_of_ne (Ne.symm (handleIdxV_ne_three j)), Function.update_self]

@[simp] theorem frameNilpV_handleV_self : frameNilpV j m (handleIdxV j) = m 2 :=
  Function.update_self _ _ _

theorem frameNilpV_of_ne {i : Fin (coreRank h)} (hV : i ≠ handleIdxV j) (h3 : i ≠ 3) :
    frameNilpV j m i = 0 := by
  rw [frameNilpV, Function.update_of_ne hV, Function.update_of_ne h3]
  rfl

@[simp] theorem frameNilpV_two : frameNilpV j m 2 = 0 :=
  frameNilpV_of_ne _ _ (handleIdxV_ne_of_val_lt j coreVal_two_lt).symm coreTwo_ne_three

@[simp] theorem frameNilpV_handleU (i : Fin h) : frameNilpV j m (handleIdxU i) = 0 :=
  frameNilpV_of_ne _ _ (handleIdxU_ne_handleIdxV i j) (handleIdxU_ne_three i)

/-! ### `N² = 0` (memo §5.2) -/

/-- **`N² = 0`**: memo §5.2's nilpotency, verbatim.  `N` lands in `⟨c̄, v̄_j⟩` — the two
coordinates it reads — and vanishes there. -/
@[simp] theorem frameNilpU_frameNilpU : frameNilpU j (frameNilpU j m) = 0 := by
  funext i
  by_cases hU : i = handleIdxU j
  · subst hU; rw [frameNilpU_handleU_self, frameNilpU_two]; rfl
  by_cases h3 : i = 3
  · subst h3; rw [frameNilpU_three, frameNilpU_handleV, neg_zero]; rfl
  rw [frameNilpU_of_ne _ _ hU h3]; rfl

/-- **`N'² = 0`** — the mirror, for memo §4.4's second family. -/
@[simp] theorem frameNilpV_frameNilpV : frameNilpV j (frameNilpV j m) = 0 := by
  funext i
  by_cases hV : i = handleIdxV j
  · subst hV; rw [frameNilpV_handleV_self, frameNilpV_two]; rfl
  by_cases h3 : i = 3
  · subst h3; rw [frameNilpV_three, frameNilpV_handleU]; rfl
  rw [frameNilpV_of_ne _ _ hV h3]; rfl

end EichlerBase

/-! ### The two Eichler families `E_j^x`, `(E'_j)^x` -/

section Eichler

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {h : ℕ}

/-- **Memo §5.1's `τ_c(k)`** at the frame level: `d̄ ↦ d̄ + k·c̄` (the letter that MOVES is `d`).
HM1's `mWord_tau_d`/`nWord_tau_d` is its group-level realization; there is no `frameTauC`,
because `c^{2^α}` blocks every transvection moving `c` — memo §6.4's residue 2. -/
noncomputable def frameTauD (k : ℤ_[2]) (m : Fin (coreRank h) → M) : Fin (coreRank h) → M :=
  Function.update m 3 (m 3 + k • m 2)

/-- **`E_j^x = 1 + xN`** (memo §5.2), for an arbitrary 2-adic coefficient `x`. -/
noncomputable def frameEichlerU (j : Fin h) (x : ℤ_[2]) (m : Fin (coreRank h) → M) :
    Fin (coreRank h) → M := fun i => m i + x • frameNilpU j m i

/-- **`(E'_j)^x = 1 + xN'`** (memo §4.4, §5.3 step 2). -/
noncomputable def frameEichlerV (j : Fin h) (x : ℤ_[2]) (m : Fin (coreRank h) → M) :
    Fin (coreRank h) → M := fun i => m i + x • frameNilpV j m i

variable (j : Fin h) (m : Fin (coreRank h) → M)

@[simp] theorem frameTauD_three (k : ℤ_[2]) : frameTauD k m 3 = m 3 + k • m 2 :=
  Function.update_self _ _ _

theorem frameTauD_of_ne (k : ℤ_[2]) {i : Fin (coreRank h)} (h3 : i ≠ 3) :
    frameTauD k m i = m i := Function.update_of_ne h3 _ _

@[simp] theorem frameTauD_two (k : ℤ_[2]) : frameTauD k m 2 = m 2 :=
  frameTauD_of_ne _ _ coreTwo_ne_three

/-- The `d̄`-row of memo §5.1's `E_j`: `d̄ ↦ d̄ − x·v̄_j`. -/
@[simp] theorem frameEichlerU_three (x : ℤ_[2]) :
    frameEichlerU j x m 3 = m 3 - x • m (handleIdxV j) := by
  rw [frameEichlerU, frameNilpU_three, smul_neg, ← sub_eq_add_neg]

/-- The `ū_j`-row of memo §5.1's `E_j`: `ū_j ↦ ū_j + x·c̄`. -/
@[simp] theorem frameEichlerU_handleU_self (x : ℤ_[2]) :
    frameEichlerU j x m (handleIdxU j) = m (handleIdxU j) + x • m 2 := by
  rw [frameEichlerU, frameNilpU_handleU_self]

theorem frameEichlerU_of_ne (x : ℤ_[2]) {i : Fin (coreRank h)} (hU : i ≠ handleIdxU j)
    (h3 : i ≠ 3) : frameEichlerU j x m i = m i := by
  rw [frameEichlerU, frameNilpU_of_ne _ _ hU h3, smul_zero, add_zero]

@[simp] theorem frameEichlerU_two (x : ℤ_[2]) : frameEichlerU j x m 2 = m 2 := by
  rw [frameEichlerU, frameNilpU_two, smul_zero, add_zero]

@[simp] theorem frameEichlerU_handleV (x : ℤ_[2]) (i : Fin h) :
    frameEichlerU j x m (handleIdxV i) = m (handleIdxV i) := by
  rw [frameEichlerU, frameNilpU_handleV, smul_zero, add_zero]

theorem frameEichlerU_handleU_of_ne (x : ℤ_[2]) {i : Fin h} (hij : i ≠ j) :
    frameEichlerU j x m (handleIdxU i) = m (handleIdxU i) :=
  frameEichlerU_of_ne _ _ _ (fun hc => hij (handleIdxU_injective hc)) (handleIdxU_ne_three i)

/-- The `d̄`-row of memo §4.4's `E'_j`: `d̄ ↦ d̄ + x·ū_j`. -/
@[simp] theorem frameEichlerV_three (x : ℤ_[2]) :
    frameEichlerV j x m 3 = m 3 + x • m (handleIdxU j) := by
  rw [frameEichlerV, frameNilpV_three]

/-- The `v̄_j`-row of memo §4.4's `E'_j`: `v̄_j ↦ v̄_j + x·c̄`. -/
@[simp] theorem frameEichlerV_handleV_self (x : ℤ_[2]) :
    frameEichlerV j x m (handleIdxV j) = m (handleIdxV j) + x • m 2 := by
  rw [frameEichlerV, frameNilpV_handleV_self]

theorem frameEichlerV_of_ne (x : ℤ_[2]) {i : Fin (coreRank h)} (hV : i ≠ handleIdxV j)
    (h3 : i ≠ 3) : frameEichlerV j x m i = m i := by
  rw [frameEichlerV, frameNilpV_of_ne _ _ hV h3, smul_zero, add_zero]

@[simp] theorem frameEichlerV_two (x : ℤ_[2]) : frameEichlerV j x m 2 = m 2 := by
  rw [frameEichlerV, frameNilpV_two, smul_zero, add_zero]

/-- **`E'_j` fixes `ū_j`** — the reason memo §5.3's step 2 does not undo step 1. -/
@[simp] theorem frameEichlerV_handleU (x : ℤ_[2]) (i : Fin h) :
    frameEichlerV j x m (handleIdxU i) = m (handleIdxU i) := by
  rw [frameEichlerV, frameNilpV_handleU, smul_zero, add_zero]

@[simp] theorem frameEichlerU_zero : frameEichlerU j 0 m = m := by
  funext i; rw [frameEichlerU, zero_smul, add_zero]

@[simp] theorem frameEichlerV_zero : frameEichlerV j 0 m = m := by
  funext i; rw [frameEichlerV, zero_smul, add_zero]

/-- `E_j^x` fixes the two coordinates `N` reads, so the nilpotent part is unchanged. -/
@[simp] theorem frameNilpU_frameEichlerU (x : ℤ_[2]) :
    frameNilpU j (frameEichlerU j x m) = frameNilpU j m := by
  rw [frameNilpU, frameNilpU, frameEichlerU_two, frameEichlerU_handleV]

@[simp] theorem frameNilpV_frameEichlerV (x : ℤ_[2]) :
    frameNilpV j (frameEichlerV j x m) = frameNilpV j m := by
  rw [frameNilpV, frameNilpV, frameEichlerV_two, frameEichlerV_handleU]

/-- **`(1 + xN)(1 + yN) = 1 + (x+y)N`** — `N² = 0` in the form the ν-clearing uses. -/
theorem frameEichlerU_frameEichlerU (x y : ℤ_[2]) :
    frameEichlerU j x (frameEichlerU j y m) = frameEichlerU j (x + y) m := by
  funext i
  rw [frameEichlerU, frameNilpU_frameEichlerU, frameEichlerU, frameEichlerU, add_smul]
  abel

theorem frameEichlerV_frameEichlerV (x y : ℤ_[2]) :
    frameEichlerV j x (frameEichlerV j y m) = frameEichlerV j (x + y) m := by
  funext i
  rw [frameEichlerV, frameNilpV_frameEichlerV, frameEichlerV, frameEichlerV, add_smul]
  abel

/-- `E_j^{−x}` inverts `E_j^x`, so `{E_j^x}` is a one-parameter *group* of frame maps and memo
§5.2's integer powers include the negative ones. -/
@[simp] theorem frameEichlerU_neg_frameEichlerU (x : ℤ_[2]) :
    frameEichlerU j (-x) (frameEichlerU j x m) = m := by
  rw [frameEichlerU_frameEichlerU, neg_add_cancel, frameEichlerU_zero]

@[simp] theorem frameEichlerV_neg_frameEichlerV (x : ℤ_[2]) :
    frameEichlerV j (-x) (frameEichlerV j x m) = m := by
  rw [frameEichlerV_frameEichlerV, neg_add_cancel, frameEichlerV_zero]

/-- **`E_j^n = 1 + nN`** (memo §5.2), for integer — here natural — exponents: iterating the
substitution `n` times is the automorphism's `n`-th power.  With
`frameEichlerU_neg_frameEichlerU` this covers every `n ∈ ℤ`. -/
theorem frameEichlerU_iterate (n : ℕ) :
    (frameEichlerU j (1 : ℤ_[2]))^[n] m = frameEichlerU j (n : ℤ_[2]) m := by
  induction n generalizing m with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, frameEichlerU_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, frameEichlerU_frameEichlerU, Nat.cast_succ, add_comm]

theorem frameEichlerV_iterate (n : ℕ) :
    (frameEichlerV j (1 : ℤ_[2]))^[n] m = frameEichlerV j (n : ℤ_[2]) m := by
  induction n generalizing m with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, frameEichlerV_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, frameEichlerV_frameEichlerV, Nat.cast_succ, add_comm]

/-! ### The normalisation, and the second family -/

/-- **The Eichler normalisation** (memo §5.2's `E_j := τ_{v_j}(1) ∘ τ_σ(1) ∘ Φ_j`, in the
rank-four families' letters): composing HM2's `Φ_j` with two exact transvections cancels the
`c̄ − v̄_j` correction on each moved letter and leaves the **pure** Eichler element. -/
theorem frameEichlerU_one_eq :
    frameEichlerU j (1 : ℤ_[2]) m = frameTauD (-1) (frameTauU j 1 (frameMixAdd j m)) := by
  funext i
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [frameEichlerU_handleU_self, frameTauD_of_ne _ _ (handleIdxU_ne_three j),
      frameTauU_handleU_self, frameMixAdd_handleU_self, frameMixAdd_handleV, one_smul, one_smul]
    abel
  by_cases h3 : i = 3
  · subst h3
    rw [frameEichlerU_three, frameTauD_three,
      frameTauU_of_ne _ _ _ (Ne.symm (handleIdxU_ne_three j)) (Ne.symm (handleIdxV_ne_three j)),
      frameTauU_of_ne _ _ _ (handleIdxU_ne_of_val_lt j coreVal_two_lt).symm
        (handleIdxV_ne_of_val_lt j coreVal_two_lt).symm,
      frameMixAdd_three, frameMixAdd_two, neg_smul, one_smul, one_smul]
    abel
  by_cases hV : i = handleIdxV j
  · subst hV
    rw [frameEichlerU_handleV, frameTauD_of_ne _ _ (handleIdxV_ne_three j),
      frameTauU_handleV_self, frameMixAdd_handleV]
  rw [frameEichlerU_of_ne _ _ _ hU h3, frameTauD_of_ne _ _ h3, frameTauU_of_ne _ _ _ hU hV,
    frameMixAdd_of_ne _ _ hU h3]

/-- **Memo §4.4's second Eichler family**: `E'_j` is the intra-handle `S`-move conjugate of
`E_j`, at every coefficient.  Since `S_j` is a composite of exact transvections
(`frameS_eq_tau`), this makes `E'_j` an honest automorphism of the core too. -/
theorem frameEichlerV_eq_conj (x : ℤ_[2]) :
    frameEichlerV j x m = frameSinv j (frameEichlerU j x (frameS j m)) := by
  funext i
  by_cases h3 : i = 3
  · subst h3
    rw [frameEichlerV_three,
      frameSinv_of_ne _ _ (Ne.symm (handleIdxU_ne_three j)) (Ne.symm (handleIdxV_ne_three j)),
      frameEichlerU_three, frameS_handleV_self,
      frameS_of_ne _ _ (Ne.symm (handleIdxU_ne_three j)) (Ne.symm (handleIdxV_ne_three j)),
      smul_neg, sub_neg_eq_add]
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [frameEichlerV_handleU, frameSinv_handleU_self, frameEichlerU_handleV,
      frameS_handleV_self, neg_neg]
  by_cases hV : i = handleIdxV j
  · subst hV
    rw [frameEichlerV_handleV_self, frameSinv_handleV_self, frameEichlerU_handleU_self,
      frameS_handleU_self, frameS_of_ne _ _ (handleIdxU_ne_of_val_lt j coreVal_two_lt).symm
        (handleIdxV_ne_of_val_lt j coreVal_two_lt).symm]
  rw [frameEichlerV_of_ne _ _ _ hV h3, frameSinv_of_ne _ _ hU hV,
    frameEichlerU_of_ne _ _ _ hU h3, frameS_of_ne _ _ hU hV]

end Eichler

/-! ## §4 The 2-adic parameter  (memo §5.2)

`E_j` is *integral*: its coefficient is `1`, and integer powers give the integers.  Memo §5.2
reaches every 2-adic coefficient without any compactness argument by conjugating with the
intra-handle unit rescaling `θ_w = diag(w, w⁻¹)`, which is itself a product of the exact
transvections (§5): conjugation multiplies the coefficient by `w⁻¹`, and

```
{ n·w⁻¹ : n ∈ ℕ, w ∈ ℤ₂ˣ }  =  ℤ₂
```

because every `x ∈ ℤ₂` is `2^{v(x)}` times a unit. -/

section TwoAdic

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {h : ℕ}

/-- **Memo §5.2's `θ_w`-conjugation identity**: `θ_w⁻¹ ∘ E_j^x ∘ θ_w = E_j^{w⁻¹·x}`.  The two
coefficients move together (the `d̄`-row picks up `w⁻¹` from `θ_w`'s `v̄_j`-row, the `ū_j`-row
from `θ_w⁻¹`'s), so memo §2's mod-2 cup condition survives every rescaling. -/
theorem frameTheta_frameEichlerU_frameTheta (j : Fin h) (w : ℤ_[2]ˣ) (x : ℤ_[2])
    (m : Fin (coreRank h) → M) :
    frameTheta j w⁻¹ (frameEichlerU j x (frameTheta j w m))
      = frameEichlerU j (((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * x) m := by
  have hwi : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (w : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  funext i
  by_cases h3 : i = 3
  · subst h3
    rw [frameTheta_of_ne _ _ _ (handleIdxU_ne_three j).symm (handleIdxV_ne_three j).symm,
      frameEichlerU_three, frameEichlerU_three, frameTheta_handleV_self,
      frameTheta_of_ne _ _ _ (handleIdxU_ne_three j).symm (handleIdxV_ne_three j).symm,
      smul_smul, mul_comm]
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [frameTheta_handleU_self, frameEichlerU_handleU_self, frameEichlerU_handleU_self,
      frameTheta_handleU_self, frameTheta_of_ne _ _ _
      (handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega)).symm
      (handleIdxV_ne_of_val_lt j (by rw [coreVal_two]; omega)).symm, smul_add, smul_smul,
      smul_smul, hwi, one_smul]
  by_cases hV : i = handleIdxV j
  · subst hV
    rw [frameTheta_handleV_self, frameEichlerU_handleV, frameEichlerU_handleV,
      frameTheta_handleV_self, smul_smul, inv_inv, mul_comm, hwi, one_smul]
  rw [frameTheta_of_ne _ _ _ hU hV, frameEichlerU_of_ne _ _ _ hU h3,
    frameEichlerU_of_ne _ _ _ hU h3, frameTheta_of_ne _ _ _ hU hV]

/-- **Memo §5.2's `{n·w⁻¹ : n ∈ ℤ, w ∈ ℤ₂ˣ} = ℤ₂`**: every 2-adic integer is a *natural* number
times the inverse of a unit, because `x = 2^{v(x)}·unit` (`PadicInt.unitCoeff_spec`). -/
theorem exists_natCast_mul_unitInv (x : ℤ_[2]) :
    ∃ (n : ℕ) (w : ℤ_[2]ˣ), ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (n : ℤ_[2]) = x := by
  by_cases hx : x = 0
  · exact ⟨0, 1, by rw [hx, Nat.cast_zero, mul_zero]⟩
  refine ⟨2 ^ x.valuation, (PadicInt.unitCoeff hx)⁻¹, ?_⟩
  rw [inv_inv, Nat.cast_pow, Nat.cast_ofNat]
  exact (PadicInt.unitCoeff_spec hx).symm

/-- **Every 2-adic Eichler coefficient is realized** (memo §5.2's conclusion): the family
`{ θ_w⁻¹ ∘ E_j^n ∘ θ_w : n ∈ ℕ, w ∈ ℤ₂ˣ }` — integer powers of the integral element `E_j`,
conjugated by the intra-handle unit rescalings — exhausts `{ E_j^x : x ∈ ℤ₂ }`.  No compactness
of `Aut(D_P)` is used, and no new axiom: `E_j` is HM2's `Φ_j` normalised by HM1's exact
transvections, and `θ_w` is a product of the same (§5). -/
theorem exists_frameEichlerU_theta_conj (j : Fin h) (x : ℤ_[2]) :
    ∃ (n : ℕ) (w : ℤ_[2]ˣ), ∀ m : Fin (coreRank h) → M,
      frameTheta j w⁻¹ ((frameEichlerU j (1 : ℤ_[2]))^[n] (frameTheta j w m))
        = frameEichlerU j x m := by
  obtain ⟨n, w, hnw⟩ := exists_natCast_mul_unitInv x
  refine ⟨n, w, fun m => ?_⟩
  rw [frameEichlerU_iterate, frameTheta_frameEichlerU_frameTheta, hnw]

/-- The `v̄_j`-side mirror (memo §5.3 step 2): the `S`-move conjugate of the family above
realizes every coefficient of `E'_j` too. -/
theorem exists_frameEichlerV_theta_conj (j : Fin h) (x : ℤ_[2]) :
    ∃ (n : ℕ) (w : ℤ_[2]ˣ), ∀ m : Fin (coreRank h) → M,
      frameSinv j (frameTheta j w⁻¹
          ((frameEichlerU j (1 : ℤ_[2]))^[n] (frameTheta j w (frameS j m))))
        = frameEichlerV j x m := by
  obtain ⟨n, w, hnw⟩ := exists_frameEichlerU_theta_conj (M := M) j x
  refine ⟨n, w, fun m => ?_⟩
  rw [hnw, ← frameEichlerV_eq_conj]

end TwoAdic

/-! ## §5 `SL₂ = E₂` over `ℤ₂`  (memo §5.1's parenthesis, memo §5.3's input)

Memo §5.2 needs `θ_w ∈ SL₂(ℤ₂)` to be a product of the exact transvections of §5.1, citing
"elementary matrices generate `SL₂` over a local ring".  Mathlib has no such theorem for a
general ring, so it is proved here for the 2×2 case over `ℤ_[2]` — the only case the memo uses —
by the local-ring row reduction.  The instance actually consumed is the explicit factorization
`planeDiag_eq`, so nothing downstream depends on the general statement. -/

/-- **The five-factor factorization of `θ_w`** (memo §5.2): `diag(w, w⁻¹) =
E(w)·F(−w⁻¹)·E(w−1)·F(1)·E(−1)`, stated for an arbitrary pair `u·v = 1` so that the proof is a
polynomial identity modulo that one relation. -/
theorem planeDiag_eq_aux {u v : ℤ_[2]} (huv : u * v = 1) :
    !![u, 0; 0, v]
      = planeElemU u * planeElemV (-v) * planeElemU (u - 1) * planeElemV 1 * planeElemU (-1) := by
  rw [planeElemU, planeElemU, planeElemU, planeElemV, planeElemV, Matrix.mul_fin_two,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine Matrix.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;> simp
  · linear_combination u * huv
  · linear_combination -huv
  · linear_combination huv
  · ring

/-- **`θ_w` is a product of five exact transvections** — memo §5.2's "`θ_w ∈ SL₂(ℤ₂)`, hence a
product of the exact transvections `τ_{u_j}`, `τ_{v_j}` of §5.1 with 2-adic exponents". -/
theorem planeDiag_eq (w : ℤ_[2]ˣ) :
    planeDiag w = planeElemU (w : ℤ_[2]) * planeElemV (-((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
      * planeElemU ((w : ℤ_[2]) - 1) * planeElemV 1 * planeElemU (-1) := by
  rw [planeDiag]
  exact planeDiag_eq_aux (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

/-- The elementary transvections of the handle plane — memo §5.1's two intra-handle rows. -/
noncomputable def planeElemSet : Set (Matrix (Fin 2) (Fin 2) ℤ_[2]) :=
  Set.range planeElemU ∪ Set.range planeElemV

theorem planeElemU_mem (k : ℤ_[2]) : planeElemU k ∈ planeElemSet :=
  Set.mem_union_left _ ⟨k, rfl⟩

theorem planeElemV_mem (k : ℤ_[2]) : planeElemV k ∈ planeElemSet :=
  Set.mem_union_right _ ⟨k, rfl⟩

theorem planeDiag_mem_closure (w : ℤ_[2]ˣ) :
    planeDiag w ∈ Submonoid.closure planeElemSet := by
  rw [planeDiag_eq]
  exact mul_mem (mul_mem (mul_mem (mul_mem
    (Submonoid.subset_closure (planeElemU_mem _)) (Submonoid.subset_closure (planeElemV_mem _)))
    (Submonoid.subset_closure (planeElemU_mem _))) (Submonoid.subset_closure (planeElemV_mem _)))
    (Submonoid.subset_closure (planeElemU_mem _))

/-- The first case of the row reduction: a determinant-one matrix whose `(0,0)` entry is a unit
factors as `F(c·a⁻¹)·diag(a, a⁻¹)·E(a⁻¹·b)`. -/
theorem mem_closure_planeElemSet_of_isUnit {T : Matrix (Fin 2) (Fin 2) ℤ_[2]} (hT : T.det = 1)
    (a : ℤ_[2]ˣ) (ha : (a : ℤ_[2]) = T 0 0) : T ∈ Submonoid.closure planeElemSet := by
  have hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hT
  have hai : (a : ℤ_[2]) * ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet' : (a : ℤ_[2]) * T 1 1 - T 0 1 * T 1 0 = 1 := by rw [ha]; exact hdet
  have hfac : T = planeElemV (T 1 0 * ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * planeDiag a
      * planeElemU (((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * T 0 1) := by
    rw [planeElemU, planeElemV, planeDiag, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i k => ?_
    fin_cases i <;> fin_cases k <;> simp
    · exact ha.symm
    · linear_combination (-(T 1 1)) * hai + ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hdet'
  rw [hfac]
  exact mul_mem (mul_mem (Submonoid.subset_closure (planeElemV_mem _)) (planeDiag_mem_closure a))
    (Submonoid.subset_closure (planeElemU_mem _))

/-- **`SL₂(ℤ₂) = E₂(ℤ₂)`**: every determinant-one 2×2 matrix over `ℤ_[2]` is a product of
elementary transvections.  Local-ring argument: `a·d − b·c = 1` is a unit, so
`IsLocalRing.isUnit_or_isUnit_of_isUnit_add` makes `a` or `b` one; in the second case one right
multiplication by `F(1)` replaces `a` by the unit `a + b` and reduces to the first. -/
theorem mem_closure_planeElemSet_of_det_eq_one {T : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hT : T.det = 1) : T ∈ Submonoid.closure planeElemSet := by
  have hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hT
  have hsum : IsUnit (T 0 0 * T 1 1 + -(T 0 1 * T 1 0)) := by
    rw [← sub_eq_add_neg, hdet]; exact isUnit_one
  by_cases ha : IsUnit (T 0 0)
  · exact mem_closure_planeElemSet_of_isUnit hT ha.unit ha.unit_spec
  have hb : IsUnit (T 0 1) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) ha
    · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).mp h)
  have hab : IsUnit (T 0 0 + T 0 1) := by
    by_contra hc
    have hkey : IsUnit (T 0 0 + T 0 1 + -T 0 0) := by
      rw [show T 0 0 + T 0 1 + -T 0 0 = T 0 1 from by ring]; exact hb
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hkey with h | h
    · exact hc h
    · exact ha ((IsUnit.neg_iff _).mp h)
  have hT' : (T * planeElemV 1).det = 1 := by rw [Matrix.det_mul, hT, planeElemV_det, mul_one]
  have h00 : (T * planeElemV 1) 0 0 = T 0 0 + T 0 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, planeElemV]
    norm_num
  have hmem : T * planeElemV 1 ∈ Submonoid.closure planeElemSet :=
    mem_closure_planeElemSet_of_isUnit hT' hab.unit (by rw [hab.unit_spec, h00])
  have hfac : T = T * planeElemV 1 * planeElemV (-1) := by
    rw [Matrix.mul_assoc, planeElemV_mul_planeElemV, add_neg_cancel, planeElemV_zero, mul_one]
  rw [hfac]
  exact mul_mem hmem (Submonoid.subset_closure (planeElemV_mem _))

/-! ### Transferring a factorization to the frame -/

section FrameMatEnd

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {h : ℕ}

/-- `frameMat j` as a monoid hom into the endomorphism monoid of frames — the dictionary that
carries a matrix factorization to a composite of frame maps.  `frameMatEnd_planeElemU` and
`frameMatEnd_planeElemV` identify the two generating families with memo §5.1's transvections. -/
noncomputable def frameMatEnd (j : Fin h) :
    Matrix (Fin 2) (Fin 2) ℤ_[2] →* Function.End (Fin (coreRank h) → M) where
  toFun := frameMat j
  map_one' := funext (frameMat_one j)
  map_mul' T₁ T₂ := funext fun m => frameMat_mul j m T₁ T₂

@[simp] theorem frameMatEnd_apply (j : Fin h) (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    frameMatEnd (M := M) j T = frameMat j T := rfl

@[simp] theorem frameMatEnd_planeElemU (j : Fin h) (k : ℤ_[2]) :
    frameMatEnd (M := M) j (planeElemU k) = frameTauU j k := rfl

@[simp] theorem frameMatEnd_planeElemV (j : Fin h) (k : ℤ_[2]) :
    frameMatEnd (M := M) j (planeElemV k) = frameTauV j k := rfl

@[simp] theorem frameMatEnd_planeDiag (j : Fin h) (w : ℤ_[2]ˣ) :
    frameMatEnd (M := M) j (planeDiag w) = frameTheta j w := rfl

theorem frameMatEnd_image_planeElemSet (j : Fin h) :
    frameMatEnd (M := M) j '' planeElemSet
      = Set.range (fun k => frameMatEnd (M := M) j (planeElemU k))
        ∪ Set.range (fun k => frameMatEnd (M := M) j (planeElemV k)) := by
  rw [planeElemSet, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- **Every `SL₂(ℤ₂)` element acts on the handle plane through the exact transvections**: the
frame-level form of §5's theorem, obtained by pushing the matrix factorization through the monoid
hom `frameMatEnd j`.  The two generating families are `frameTauU j k` and `frameTauV j k`
(`frameMatEnd_planeElemU`, `frameMatEnd_planeElemV`), and memo §5.2 consumes only the `θ_w`
instance, whose factorization is `planeDiag_eq`. -/
theorem frameMatEnd_mem_closure (j : Fin h) {T : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hT : T.det = 1) :
    frameMatEnd (M := M) j T ∈ Submonoid.closure
      (Set.range (fun k => frameMatEnd (M := M) j (planeElemU k))
        ∪ Set.range (fun k => frameMatEnd (M := M) j (planeElemV k))) := by
  have hmap : Submonoid.map (frameMatEnd (M := M) j) (Submonoid.closure planeElemSet)
      = Submonoid.closure (Set.range (fun k => frameMatEnd (M := M) j (planeElemU k))
        ∪ Set.range (fun k => frameMatEnd (M := M) j (planeElemV k))) := by
    rw [MonoidHom.map_mclosure, frameMatEnd_image_planeElemSet]
  rw [← hmap]
  exact ⟨T, mem_closure_planeElemSet_of_det_eq_one hT, rfl⟩

/-- `θ_w` at the frame level, as a product of the exact transvections (memo §5.2's consumed
instance of §5). -/
theorem frameTheta_mem_closure (j : Fin h) (w : ℤ_[2]ˣ) :
    frameMatEnd (M := M) j (planeDiag w) ∈ Submonoid.closure
      (Set.range (fun k => frameMatEnd (M := M) j (planeElemU k))
        ∪ Set.range (fun k => frameMatEnd (M := M) j (planeElemV k))) := by
  refine frameMatEnd_mem_closure j ?_
  rw [planeDiag, Matrix.det_fin_two]
  norm_num [← Units.val_mul]

end FrameMatEnd

/-! ## §6 The ν-frame — what HM4 reads

The ν-clearing of memo §5.3 runs on `ν' : D_P → Multiplicative ℤ_[2]`, so the frame that matters
is `M = ℤ_[2]`, read off a marking by `toAdd ∘ ν'`.  The three theorems below identify the frame
action of the *group-level* moves with §2–§3's linear maps; `map_zpowZtwo`
(`GQ2/ZtwoPowering.lean:444`) is what makes HM1's 2-adic exponents land on the nose. -/

section NuFrameDef

variable {P : Type*} {h : ℕ}

/-- **The ν-frame of a marking**: the additive frame vector a `Multiplicative ℤ_[2]`-valued
character reads off the letters.  Multiplicativity of `f` is not part of the definition — it is
a hypothesis of the three identification theorems below. -/
def nuFrame (f : P → Multiplicative ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → ℤ_[2] := fun i => toAdd (f (m i))

@[simp] theorem nuFrame_apply (f : P → Multiplicative ℤ_[2]) (m : Fin (coreRank h) → P)
    (i : Fin (coreRank h)) : nuFrame f m i = toAdd (f (m i)) := rfl

end NuFrameDef

section NuFrameMix

variable {P : Type*} [Group P] {h : ℕ}

/-- **The frame action of HM2's `Φ_j`** on the ν-frame is memo §5.1's row for `Φ_j`, additively:
`d̄ ↦ d̄ + c̄ − v̄_j`, `ū_j ↦ ū_j + c̄ − v̄_j`. -/
theorem nuFrame_handleMixMark {F : Type*} [FunLike F P (Multiplicative ℤ_[2])]
    [MonoidHomClass F P (Multiplicative ℤ_[2])] (f : F) (m : Fin (coreRank h) → P) (j : Fin h) :
    nuFrame f (handleMixMark j m) = frameMixAdd j (nuFrame f m) := by
  funext i
  rw [nuFrame_apply, map_handleMixMark, handleMixMark_eq_frameMix]
  exact congrArg toAdd (frameMix_ofAdd j (nuFrame f m) i)

end NuFrameMix

section NuFrame

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- A character turns a 2-adic power into a 2-adic multiple — `map_zpowZtwo` composed with
`SectionThree.zpowZtwo_ofAdd`. -/
theorem toAdd_map_zpowZtwo (hP : IsProP 2 P)
    (f : ContinuousMonoidHom P (Multiplicative ℤ_[2])) (x : P) (k : ℤ_[2]) :
    toAdd (f (zpowZtwo hP x k)) = k * toAdd (f x) := by
  rw [map_zpowZtwo hP PropOneOne.isProP_two_multPadicInt,
    show f x = ofAdd (toAdd (f x)) from rfl, SectionThree.zpowZtwo_ofAdd, mul_comm]
  rfl

/-- **The frame action of HM1's `τ_{v_j}(k)`** (`mRelWord_tau_handleU`, `handleWord_tau_u`): the
group-level update `u_j ↦ v_j^k·u_j`, exact for every `k : ℤ_[2]`, induces `frameTauU j k` — the
row `ū_j ↦ ū_j + k·v̄_j` of memo §5.1. -/
theorem nuFrame_tau_handleU (hP : IsProP 2 P)
    (f : ContinuousMonoidHom P (Multiplicative ℤ_[2])) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    nuFrame f (Function.update m (handleIdxU j)
        (zpowZtwo hP (m (handleIdxV j)) k * m (handleIdxU j)))
      = frameTauU j k (nuFrame f m) := by
  funext i
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [nuFrame_apply, Function.update_self, frameTauU_handleU_self, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo hP]
    show _ = toAdd (f (m (handleIdxU j))) + k • toAdd (f (m (handleIdxV j)))
    rw [smul_eq_mul, add_comm]
  by_cases hV : i = handleIdxV j
  · subst hV
    rw [nuFrame_apply, Function.update_of_ne hU, frameTauU_handleV_self, nuFrame_apply]
  rw [nuFrame_apply, Function.update_of_ne hU, frameTauU_of_ne _ _ _ hU hV, nuFrame_apply]

/-- **The frame action of HM1's `τ_{u_j}(k)`** (`mRelWord_tau_handleV`, `handleWord_tau_v`):
`v_j ↦ u_j^k·v_j` induces `frameTauV j k`, the row `v̄_j ↦ v̄_j + k·ū_j`. -/
theorem nuFrame_tau_handleV (hP : IsProP 2 P)
    (f : ContinuousMonoidHom P (Multiplicative ℤ_[2])) (m : Fin (coreRank h) → P) (j : Fin h)
    (k : ℤ_[2]) :
    nuFrame f (Function.update m (handleIdxV j)
        (zpowZtwo hP (m (handleIdxU j)) k * m (handleIdxV j)))
      = frameTauV j k (nuFrame f m) := by
  funext i
  by_cases hV : i = handleIdxV j
  · subst hV
    rw [nuFrame_apply, Function.update_self, frameTauV_handleV_self, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo hP]
    show _ = toAdd (f (m (handleIdxV j))) + k • toAdd (f (m (handleIdxU j)))
    rw [smul_eq_mul, add_comm]
  by_cases hU : i = handleIdxU j
  · subst hU
    rw [nuFrame_apply, Function.update_of_ne hV, frameTauV_handleU_self, nuFrame_apply]
  rw [nuFrame_apply, Function.update_of_ne hV, frameTauV_of_ne _ _ _ hU hV, nuFrame_apply]

/-- **The frame action of HM1's `τ_c(k)`** (`mWord_tau_d`, `nWord_tau_d`): the group-level update
`d ↦ c^k·d` induces `frameTauD k`, the row `d̄ ↦ d̄ + k·c̄`.  This is the core-side transvection the
Eichler normalisation `frameEichlerU_one_eq` uses, so HM4 needs it next to the two handle rows. -/
theorem nuFrame_tau_three (hP : IsProP 2 P)
    (f : ContinuousMonoidHom P (Multiplicative ℤ_[2])) (m : Fin (coreRank h) → P) (k : ℤ_[2]) :
    nuFrame f (Function.update m 3 (zpowZtwo hP (m 2) k * m 3)) = frameTauD k (nuFrame f m) := by
  funext i
  by_cases h3 : i = 3
  · subst h3
    rw [nuFrame_apply, Function.update_self, frameTauD_three, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo hP]
    show _ = toAdd (f (m 3)) + k • toAdd (f (m 2))
    rw [smul_eq_mul, add_comm]
  rw [nuFrame_apply, Function.update_of_ne h3, frameTauD_of_ne _ _ h3, nuFrame_apply]

end NuFrame

section NuFrameCores

variable (α h : ℕ) (j : Fin h)

/-- **What HM4 reads on `D_M`**: precomposing a ν-character with HM2's mixing automorphism acts
on the frame as `frameMixAdd j`. -/
theorem nuFrame_dmMixEquiv
    (f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (fun i => dmMixEquiv α h j (dmGen α h i))
      = frameMixAdd j (nuFrame f (dmGen α h)) := by
  rw [← nuFrame_handleMixMark]
  exact congrArg (nuFrame f) (funext fun i => dmMixEquiv_gen α h j i)

/-- **What HM4 reads on `D_N`**. -/
theorem nuFrame_dnMixEquiv
    (f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (fun i => dnMixEquiv α h j (dnGen α h i))
      = frameMixAdd j (nuFrame f (dnGen α h)) := by
  rw [← nuFrame_handleMixMark]
  exact congrArg (nuFrame f) (funext fun i => dnMixEquiv_gen α h j i)

end NuFrameCores

end MarkedCore

end Dyadic

end GQ2
