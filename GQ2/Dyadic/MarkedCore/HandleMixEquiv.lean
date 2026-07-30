/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMix

@[expose] public section

/-!
# Handle mixing, step 2: the mixing automorphism `Φ_j` of the marked cores

**Ticket HM2** of the dyadic campaign (lane MC), implementing the `HandleMixLift` spike memo
`docs/dyadic/handlemixlift-spike.md` §4 (the construction) and §7's second row.  HM1
(`GQ2/Dyadic/MarkedCore/HandleMix.lean`) landed the three algebraic ingredient families; this
file assembles them into an honest **continuous automorphism of each presented marked core**,

```
Φ_j : D_{M,α,h} ≅ D_{M,α,h} ,        Φ_j : D_{N,α,h} ≅ D_{N,α,h}
```

realizing memo §6.4's handle↔core mixing element at every handle index `j < h`, with **no new
axiom, no B8 and no appeal to compactness of `Aut(D_P)`** (memo V4).  Repo conventions
throughout: `x ^ g = g⁻¹xg` (`GQ2.conjP`), `[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`).

## The construction (memo §4.1, §4.4)

Both rank-four relators are a **prefix times a surface part**,

```
mRelWord α m = (a²·[a,b]·c^{2^α}) · [c,d] · ∏_{i<h}[u_i,v_i]
nRelWord α m = (a^{2+2^α}·[a,b])  · [c,d] · ∏_{i<h}[u_i,v_i]
```

with `(a, b, c, d) = (m 0, m 1, m 2, m 3)` and the handles keyed by `handleIdxU`/`handleIdxV`.
The prefix contains `c` (for `M`, in the factor `c^{2^α}`; memo §5.1's `τ_a` ✗ row) but **never
`d`**, so memo §6.1's hypothesis holds with `[y,z] = [c,d]` and `W`-disjoint letter `d`.  The
mixing element is memo §4.4's `Φ^M_j` — the unique short solution of memo §8's search — written
here with `ζ_j = ∏_{i<j}[u_i,v_i]` (`handleMixZeta`, HM1's `handlePrefix`):

```
Φ_j(d)    =  c · d · ζ_j · (v_j⁻¹)^{u_j} · ζ_j⁻¹          (handleMixD)
Φ_j(u_j)  =  u_j · (c^d)^{ζ_j} · (v_j⁻¹)^{u_j}            (handleMixU)
Φ_j(x)    =  x   for every other letter                    (handleMixUpdate)
```

so `Φ_j` fixes `a`, `b`, `c`, `v_j` and every handle other than the `j`-th **literally**; in
particular it fixes the prefix literally, which is the structural point of memo §4.3.  The
two-sided inverse of memo §4.2 is again explicit, and again moves only `d` and `u_j`:

```
Φ_j⁻¹(d)    =  d · ζ_j · (v_j)^{u_j} · ζ_j⁻¹ · (c⁻¹)^d     (handleMixInvD)
Φ_j⁻¹(u_j)  =  v_j · u_j · ((c⁻¹)^d)^{ζ_j}                 (handleMixInvU)
```

## Contents, and the memo section each part serves

* **§1 The four substitution words** (memo §4.1/§4.4 and §4.2) as plain group-valued
  functions of `(c, d, u_j, v_j, ζ_j)`, their naturality, and the **five reduced-word
  identities** that carry the whole ticket:

  | Lean | memo | content |
  |---|---|---|
  | `commP_handleMixD_mul` | §4.1 | `[c,Φd]·ζ·[Φu,v] = [c,d]·ζ·[u,v]` — the relator identity |
  | `handleMixInvD_handleMixD`, `handleMixInvU_handleMixD` | §4.2 | `Φ⁻¹∘Φ = id` on `d`, `u_j` |
  | `handleMixD_handleMixInvD`, `handleMixU_handleMixInvD` | §4.2 | `Φ∘Φ⁻¹ = id` on `d`, `u_j` |

  Each is `simp only [defs, commP, conjP]; group` — memo §8's promise that "`group` plus the
  two expansion lemmas discharge them without search", confirmed by HM1's acceptance probe.

* **§2 The substitution on markings.**  `handleMixUpdate` (the two-letter update at `3` and
  `handleIdxU j`, with its full index-bookkeeping API), `handleMixZeta`, then
  `handleMixMark` = `Φ_j` and `handleMixInvMark` = `Φ_j⁻¹` on markings, with naturality
  (`map_handleMixMark`), the **two relator identities**

  ```
  mRelWord α (handleMixMark j m) = mRelWord α m        nRelWord α (…) = nRelWord α m
  ```

  (memo §4.1's `Φ_j(P) = P`, at general handle count `h` **and** general handle index `j`), and
  the **two marking-level composition identities** `handleMixInvMark j (handleMixMark j m) = m`
  and its mirror.  `handleWord_update_split` is the reusable shape HM3 also wants.

* **§3 The `thetaEquiv`-pattern assembly** (`GQ2/AnabelianBridge/Construction.lean:864/880/929`).
  `dmMixHom`/`dnMixHom` and their inverses come from MC2's `mLiftHom`/`nLiftHom` — so
  continuity is free, and the substitution's respect for the relator (§2) is exactly the
  `hrel` argument.  Hom-extensionality (`dm_hom_ext`/`dn_hom_ext`, i.e. MC2's
  `presPro2_hom_ext`) turns §2's marking identities into the two composite identities, and
  `continuousMulEquivOfBijective` (`GQ2/Reconstruction.lean:44`) delivers

  ```
  dmMixEquiv α h j : ContinuousMulEquiv (DM α h) (DM α h)
  dnMixEquiv α h j : ContinuousMulEquiv (DN α h) (DN α h)
  ```

  together with the generator-value lemmas.

## What HM3 consumes from here

* The two equivs `dmMixEquiv α h j`, `dnMixEquiv α h j` and their inverses' generator values,
  via the `*_apply`/`*_gen` simp lemmas and the six named rows per core: `dmMixEquiv_dmA`,
  `dmMixEquiv_dmB`, `dmMixEquiv_dmC`, `dmMixEquiv_dmD`, `dmMixEquiv_handleU_self`,
  `dmMixEquiv_handleU_of_ne`, `dmMixEquiv_handleV` (mirrored as `dnMixEquiv_dnX0`,
  `dnMixEquiv_dnX1`, `dnMixEquiv_dnSigma`, `dnMixEquiv_dnX2`, …).
* The **abelian collapse** of the four words (§1, `handleMixD_comm` and friends), which is the
  frame action HM3 computes: every `ζ`-conjugate dies, leaving

  ```
  d̄ ↦ d̄ + c̄ − v̄_j ,   ū_j ↦ ū_j + c̄ − v̄_j ,   c̄, v̄_j, the other handles fixed
  ```

  i.e. memo §5.2's nilpotent `N` (visibly `N² = 0`: `N` lands in `⟨c̄, v̄_j⟩`, on which it
  vanishes), before the `τ_σ`/`τ_{v_j}` normalisation that turns `Φ_j` into the pure Eichler
  element `E_j`.
* `handleWord_update_split` and the `handleMixUpdate` index API, for `E_j`, `E'_j` and `S_j`
  (memo §4.4, §5.1) — those are composites of `Φ_j` with HM1's `τ` family and update the same
  two slots.
* The four word-level composition identities of §1, which make every composite in memo §5.2's
  `θ_w E_j θ_w⁻¹` invertible without re-running Nielsen reduction.

## Axiom hygiene

Every declaration in this file prints within **std-3** (`propext`, `Classical.choice`,
`Quot.sound`), and most within a subset: the four substitution words and their naturality
lemmas need only `propext`, `handleMixZeta`/`map_handleMixZeta` only `propext` and `Quot.sound`.
**No census axiom is reachable** — in particular **no B8** (`PeripheralCyclotomicAction`), which
is memo V4 measured rather than asserted: the whole construction runs on the free-group word
calculus plus MC2's universal property, so it needs neither the peripheral action nor
compactness of `Aut(D_P)`.  The census stays at 11.

## Deviations from the memo (recorded)

* The memo displays the **L**-family element (`Φ_j(a) = a^σ·δ_j⁻¹`, prefix `x₀^{σ²}x₀`, moving
  the *first* letter of the commutator pair).  `DM`/`DN` are the rank-four families, whose
  prefixes contain `c` and not `d`, so the element realized here is memo §4.4's `Φ^M_j`, which
  moves the *second* letter.  Memo §4.4: for `N` both families apply (`W_N` shares no letter
  with `[c,d]`), and the `M`-form is the one that also covers `M`; one definition therefore
  serves both cores, and the L family is out of scope for this file (its core is
  `GQ2/Dyadic/SqCore/`).
* The memo's inverse display (§4.2) is the L-family inverse at `h = 1`, `j = 0`.  The
  `M`-family inverse at general `(h, j)` is derived here (§1) and verified in Lean by the two
  composition identities; the shapes match the memo's up to the family swap.
-/

namespace GQ2

namespace Dyadic

namespace MarkedCore

/-! ## §1 The four substitution words  (memo §4.1, §4.4, §4.2)

`Φ_j` moves exactly two letters, so it is carried by two words; the same holds for `Φ_j⁻¹`.
All four are functions of the five group elements `c`, `d`, `u_j`, `v_j` and `ζ_j` — no handle
indexing yet, which is what lets `group` see them as free-group identities. -/

section MixWords

variable {G : Type*} [Group G]

/-- **`Φ_j(d) = c·d·ζ_j·(v_j⁻¹)^{u_j}·ζ_j⁻¹`** (memo §4.4).  The correction word is a
*conjugate* of `v_j⁻¹`, not the bare letter: that replacement is what cancels the triple
commutator `[[σ,v₁],u₁]` of memo §3. -/
def handleMixD (c d u v z : G) : G := c * d * z * conjP v⁻¹ u * z⁻¹

/-- **`Φ_j(u_j) = u_j·(c^d)^{ζ_j}·(v_j⁻¹)^{u_j}`** (memo §4.4). -/
def handleMixU (c d u v z : G) : G := u * conjP (conjP c d) z * conjP v⁻¹ u

/-- **`Φ_j⁻¹(d) = d·ζ_j·(v_j)^{u_j}·ζ_j⁻¹·(c⁻¹)^d`** — the `d`-row of memo §4.2's explicit
two-sided inverse, in the `M`-family normalisation. -/
def handleMixInvD (c d u v z : G) : G := d * z * conjP v u * z⁻¹ * conjP c⁻¹ d

/-- **`Φ_j⁻¹(u_j) = v_j·u_j·((c⁻¹)^d)^{ζ_j}`** — the `u_j`-row of memo §4.2's inverse. -/
def handleMixInvU (c d u v z : G) : G := v * u * conjP (conjP c⁻¹ d) z

/-! ### The relator identity (memo §4.1)

This is `Φ_j(P) = P` in local form: the surface part of both relators is `[c,d]·ζ_j·[u_j,v_j]`
times a block `w` that `Φ_j` does not touch, and `Φ_j` fixes it letter for letter. -/

/-- **The mixing identity** (memo §4.1, §4.4): `[c, Φd]·ζ·[Φu, v] = [c,d]·ζ·[u,v]`, with a
trailing block `w` carried along so the statement matches `handleWord_split`'s
parenthesisation exactly.  This one identity *is* memo §4's construction. -/
theorem commP_handleMixD_mul (c d u v z w : G) :
    commP c (handleMixD c d u v z) * (z * commP (handleMixU c d u v z) v * w)
      = commP c d * (z * commP u v * w) := by
  simp only [handleMixD, handleMixU, commP, conjP]
  group

/-! ### The two-sided inverse (memo §4.2)

Memo §4.2 obtains the inverse by Nielsen reduction of the image tuple and records that both
composites are the identity **on the nose in the free group**, not merely modulo `⟨⟨P⟩⟩`.  The
four identities below are that statement, and they are what §3's assembly needs *before*
descending to the presented core. -/

/-- `Φ_j⁻¹ ∘ Φ_j = id` on the letter `d`. -/
theorem handleMixInvD_handleMixD (c d u v z : G) :
    handleMixInvD c (handleMixD c d u v z) (handleMixU c d u v z) v z = d := by
  simp only [handleMixInvD, handleMixD, handleMixU, conjP]
  group

/-- `Φ_j⁻¹ ∘ Φ_j = id` on the letter `u_j`. -/
theorem handleMixInvU_handleMixD (c d u v z : G) :
    handleMixInvU c (handleMixD c d u v z) (handleMixU c d u v z) v z = u := by
  simp only [handleMixInvU, handleMixD, handleMixU, conjP]
  group

/-- `Φ_j ∘ Φ_j⁻¹ = id` on the letter `d`. -/
theorem handleMixD_handleMixInvD (c d u v z : G) :
    handleMixD c (handleMixInvD c d u v z) (handleMixInvU c d u v z) v z = d := by
  simp only [handleMixInvD, handleMixInvU, handleMixD, conjP]
  group

/-- `Φ_j ∘ Φ_j⁻¹ = id` on the letter `u_j`. -/
theorem handleMixU_handleMixInvD (c d u v z : G) :
    handleMixU c (handleMixInvD c d u v z) (handleMixInvU c d u v z) v z = u := by
  simp only [handleMixInvD, handleMixInvU, handleMixU, conjP]
  group

end MixWords

/-! ### Abelian collapse of the four words — the frame action (memo §5.2)

The `mWord_comm`/`handlePrefix_comm` pattern: on a commutative group every `conjP` is trivial,
so the four words collapse to the linear data HM3's frame computation consumes,

```
Φ_j  :  d̄ ↦ d̄ + c̄ − v̄_j ,   ū_j ↦ ū_j + c̄ − v̄_j
Φ_j⁻¹:  d̄ ↦ d̄ − c̄ + v̄_j ,   ū_j ↦ ū_j − c̄ + v̄_j
```

with `c̄`, `v̄_j` and every other letter fixed.  The nilpotent part visibly squares to zero (it
lands in `⟨c̄, v̄_j⟩`, where it vanishes), which is memo §5.2's `N² = 0`; and the intervening
block `ζ_j` is invisible, as it must be. -/

section MixWordsAbelian

variable {G : Type*} [CommGroup G]

/-- **Abelian collapse of `Φ_j(d)`**: `d̄ ↦ d̄ + c̄ − v̄_j` (memo §5.2). -/
theorem handleMixD_comm (c d u v z : G) : handleMixD c d u v z = c * d * v⁻¹ := by
  simp [handleMixD, conjP, mul_comm, mul_left_comm, mul_assoc]

/-- **Abelian collapse of `Φ_j(u_j)`**: `ū_j ↦ ū_j + c̄ − v̄_j` (memo §5.2). -/
theorem handleMixU_comm (c d u v z : G) : handleMixU c d u v z = u * c * v⁻¹ := by
  simp [handleMixU, conjP, mul_comm, mul_left_comm, mul_assoc]

/-- **Abelian collapse of `Φ_j⁻¹(d)`**: `d̄ ↦ d̄ − c̄ + v̄_j`. -/
theorem handleMixInvD_comm (c d u v z : G) : handleMixInvD c d u v z = d * v * c⁻¹ := by
  simp [handleMixInvD, conjP, mul_comm, mul_left_comm, mul_assoc]

/-- **Abelian collapse of `Φ_j⁻¹(u_j)`**: `ū_j ↦ ū_j − c̄ + v̄_j`. -/
theorem handleMixInvU_comm (c d u v z : G) : handleMixInvU c d u v z = v * u * c⁻¹ := by
  simp [handleMixInvU, conjP, mul_comm, mul_assoc]

end MixWordsAbelian

/-! ### Naturality of the four words

All four use only `*`, `⁻¹` and `conjP`, so they push through any monoid-hom-like map — the
`map_drWord`/`map_handlePrefix` pattern. -/

section MixWordsNaturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]

theorem map_handleMixD (φ : F) (c d u v z : G) :
    φ (handleMixD c d u v z) = handleMixD (φ c) (φ d) (φ u) (φ v) (φ z) := by
  simp only [handleMixD, conjP, map_mul, map_inv]

theorem map_handleMixU (φ : F) (c d u v z : G) :
    φ (handleMixU c d u v z) = handleMixU (φ c) (φ d) (φ u) (φ v) (φ z) := by
  simp only [handleMixU, conjP, map_mul, map_inv]

theorem map_handleMixInvD (φ : F) (c d u v z : G) :
    φ (handleMixInvD c d u v z) = handleMixInvD (φ c) (φ d) (φ u) (φ v) (φ z) := by
  simp only [handleMixInvD, conjP, map_mul, map_inv]

theorem map_handleMixInvU (φ : F) (c d u v z : G) :
    φ (handleMixInvU c d u v z) = handleMixInvU (φ c) (φ d) (φ u) (φ v) (φ z) := by
  simp only [handleMixInvU, conjP, map_mul, map_inv]

end MixWordsNaturality

/-! ## §2 The substitution on markings

`Φ_j` updates a marking `m : Fin (coreRank h) → G` in exactly two slots: the core letter `3`
(the letter `d`, absent from both prefixes) and the handle letter `handleIdxU j`.  Everything
below is the bookkeeping that turns the five word identities of §1 into statements about
`mRelWord`/`nRelWord`. -/

section MixUpdate

variable {G : Type*} {h : ℕ}

/-- A core letter below index `3` is not the letter `3`. -/
private theorem core_ne_three {i : Fin (coreRank h)} (hi : (i : ℕ) < 3) :
    i ≠ (3 : Fin (coreRank h)) := by
  intro hc
  rw [hc, coreVal_three] at hi
  omega

/-- Handle letters are never the letter `3`. -/
theorem handleIdxU_ne_three (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 3 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_three]; omega)

/-- Handle letters are never the letter `3`. -/
theorem handleIdxV_ne_three (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 3 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_three]; omega)

/-- **The two-slot update** underlying `Φ_j` and `Φ_j⁻¹`: replace the core letter `d = m 3` by
`wd` and the handle letter `u_j = m (handleIdxU j)` by `wu`, leaving the other `coreRank h − 2`
letters alone.  The two slots are distinct (`handleIdxU_ne_three`), so the order of the two
`Function.update`s is immaterial. -/
def handleMixUpdate (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G) :
    Fin (coreRank h) → G :=
  Function.update (Function.update m 3 wd) (handleIdxU j) wu

variable (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G)

@[simp] theorem handleMixUpdate_zero : handleMixUpdate j m wd wu 0 = m 0 := by
  rw [handleMixUpdate,
    Function.update_of_ne (Ne.symm (handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega))),
    Function.update_of_ne (core_ne_three (by rw [coreVal_zero]; omega))]

@[simp] theorem handleMixUpdate_one : handleMixUpdate j m wd wu 1 = m 1 := by
  rw [handleMixUpdate,
    Function.update_of_ne (Ne.symm (handleIdxU_ne_of_val_lt j (by rw [coreVal_one]; omega))),
    Function.update_of_ne (core_ne_three (by rw [coreVal_one]; omega))]

@[simp] theorem handleMixUpdate_two : handleMixUpdate j m wd wu 2 = m 2 := by
  rw [handleMixUpdate,
    Function.update_of_ne (Ne.symm (handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega))),
    Function.update_of_ne (core_ne_three (by rw [coreVal_two]; omega))]

@[simp] theorem handleMixUpdate_three : handleMixUpdate j m wd wu 3 = wd := by
  rw [handleMixUpdate, Function.update_of_ne (Ne.symm (handleIdxU_ne_three j)),
    Function.update_self]

@[simp] theorem handleMixUpdate_handleU_self :
    handleMixUpdate j m wd wu (handleIdxU j) = wu := by
  rw [handleMixUpdate, Function.update_self]

theorem handleMixUpdate_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    handleMixUpdate j m wd wu (handleIdxU i) = m (handleIdxU i) := by
  rw [handleMixUpdate, Function.update_of_ne fun hc => hij (handleIdxU_injective hc),
    Function.update_of_ne (handleIdxU_ne_three i)]

@[simp] theorem handleMixUpdate_handleV (i : Fin h) :
    handleMixUpdate j m wd wu (handleIdxV i) = m (handleIdxV i) := by
  rw [handleMixUpdate, Function.update_of_ne (handleIdxU_ne_handleIdxV j i).symm,
    Function.update_of_ne (handleIdxV_ne_three i)]

/-- The handle-`U` marking function of a two-slot update is a one-slot update. -/
theorem handleMixUpdate_comp_U :
    (fun i => handleMixUpdate j m wd wu (handleIdxU i))
      = Function.update (fun i => m (handleIdxU i)) j wu := by
  have hm : (fun i => Function.update m 3 wd (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i => Function.update_of_ne (handleIdxU_ne_three i) _ _
  rw [handleMixUpdate, update_handleIdxU_comp_U, hm]

/-- The handle-`V` marking function of a two-slot update is untouched. -/
theorem handleMixUpdate_comp_V :
    (fun i => handleMixUpdate j m wd wu (handleIdxV i)) = fun i => m (handleIdxV i) := by
  rw [handleMixUpdate, update_handleIdxU_comp_V]
  exact funext fun i => Function.update_of_ne (handleIdxV_ne_three i) _ _

end MixUpdate

/-! ### Naturality and the relator shapes -/

section MixUpdateNaturality

variable {F G H : Type*} [FunLike F G H] {h : ℕ}

/-- A two-slot update commutes with post-composition. -/
theorem map_handleMixUpdate (φ : F) (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G)
    (i : Fin (coreRank h)) :
    φ (handleMixUpdate j m wd wu i)
      = handleMixUpdate j (fun i => φ (m i)) (φ wd) (φ wu) i := by
  simp only [handleMixUpdate, Function.apply_update fun _ => φ]

end MixUpdateNaturality

section MixRelWord

variable {G : Type*} [Group G] {h : ℕ}

/-- **Structure of a two-slot update of the `M_α` relator**: the first three core letters are
untouched, the fourth becomes `wd`, and the handle block sees a one-slot update at `j`. -/
theorem mRelWord_handleMixUpdate (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G) :
    mRelWord α (handleMixUpdate j m wd wu)
      = mWord α (m 0) (m 1) (m 2) wd *
        handleWord (Function.update (fun i => m (handleIdxU i)) j wu)
          (fun i => m (handleIdxV i)) := by
  rw [mRelWord, handleMixUpdate_comp_U, handleMixUpdate_comp_V, handleMixUpdate_zero,
    handleMixUpdate_one, handleMixUpdate_two, handleMixUpdate_three]

/-- **Structure of a two-slot update of the `N_α` relator**. -/
theorem nRelWord_handleMixUpdate (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) (wd wu : G) :
    nRelWord α (handleMixUpdate j m wd wu)
      = nWord α (m 0) (m 1) (m 2) wd *
        handleWord (Function.update (fun i => m (handleIdxU i)) j wu)
          (fun i => m (handleIdxV i)) := by
  rw [nRelWord, handleMixUpdate_comp_U, handleMixUpdate_comp_V, handleMixUpdate_zero,
    handleMixUpdate_one, handleMixUpdate_two, handleMixUpdate_three]

/-- **`handleWord` of a one-slot handle update, split at that slot** (HM1's `handleWord_split`
with the `handlePrefix`/`handleSuffix` congruences already applied): the two untouched blocks
do not see the update.  This is the shape memo §4.1 is written against, and HM3's `E_j`, `E'_j`
and `S_j` reuse it verbatim. -/
theorem handleWord_update_split (u v : Fin h → G) (j : Fin h) (w : G) :
    handleWord (Function.update u j w) v
      = handlePrefix u v (j : ℕ) * commP w (v j) * handleSuffix u v ((j : ℕ) + 1) := by
  rw [handleWord_split (Function.update u j w) v j, Function.update_self]
  refine congrArg₂ (· * ·) (congrArg (· * commP w (v j)) ?_) ?_
  · refine handlePrefix_congr _ fun i hi => ?_
    have hij : i ≠ j := fun hc => by rw [hc] at hi; omega
    rw [Function.update_of_ne hij]
  · refine handleSuffix_congr _ fun i hi => ?_
    have hij : i ≠ j := fun hc => by rw [hc] at hi; omega
    rw [Function.update_of_ne hij]

/-- **The surface part is fixed** (memo §4.1, at general `h` and general `j`): the mixing
substitution changes `[c,d]` and the `j`-th handle, and the two changes cancel. -/
theorem commP_mul_handleWord_handleMix (c d : G) (u v : Fin h → G) (j : Fin h) :
    commP c (handleMixD c d (u j) (v j) (handlePrefix u v (j : ℕ))) *
        handleWord
          (Function.update u j (handleMixU c d (u j) (v j) (handlePrefix u v (j : ℕ)))) v
      = commP c d * handleWord u v := by
  rw [handleWord_update_split, handleWord_split u v j]
  exact commP_handleMixD_mul _ _ _ _ _ _

end MixRelWord

/-! ### `Φ_j` and `Φ_j⁻¹` on markings -/

section MixMark

variable {G : Type*} [Group G] {h : ℕ}

/-- **`ζ_j = ∏_{i<j}[u_i,v_i]`** read off a marking (memo §4.1's intervening handle block). -/
def handleMixZeta (m : Fin (coreRank h) → G) (j : Fin h) : G :=
  handlePrefix (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) (j : ℕ)

/-- **`Φ_j` as a substitution on markings** (memo §4.4): the two-slot update by the two words
of §1. -/
def handleMixMark (j : Fin h) (m : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  handleMixUpdate j m
    (handleMixD (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j))
    (handleMixU (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j))

/-- **`Φ_j⁻¹` as a substitution on markings** (memo §4.2). -/
def handleMixInvMark (j : Fin h) (m : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  handleMixUpdate j m
    (handleMixInvD (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j))
    (handleMixInvU (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j))

variable (j : Fin h) (m : Fin (coreRank h) → G)

@[simp] theorem handleMixMark_zero : handleMixMark j m 0 = m 0 := handleMixUpdate_zero _ _ _ _
@[simp] theorem handleMixMark_one : handleMixMark j m 1 = m 1 := handleMixUpdate_one _ _ _ _
@[simp] theorem handleMixMark_two : handleMixMark j m 2 = m 2 := handleMixUpdate_two _ _ _ _

@[simp] theorem handleMixMark_three :
    handleMixMark j m 3
      = handleMixD (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j) :=
  handleMixUpdate_three _ _ _ _

@[simp] theorem handleMixMark_handleU_self :
    handleMixMark j m (handleIdxU j)
      = handleMixU (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j) :=
  handleMixUpdate_handleU_self _ _ _ _

theorem handleMixMark_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    handleMixMark j m (handleIdxU i) = m (handleIdxU i) :=
  handleMixUpdate_handleU_of_ne _ _ _ _ hij

@[simp] theorem handleMixMark_handleV (i : Fin h) :
    handleMixMark j m (handleIdxV i) = m (handleIdxV i) :=
  handleMixUpdate_handleV _ _ _ _ _

@[simp] theorem handleMixInvMark_zero : handleMixInvMark j m 0 = m 0 :=
  handleMixUpdate_zero _ _ _ _
@[simp] theorem handleMixInvMark_one : handleMixInvMark j m 1 = m 1 :=
  handleMixUpdate_one _ _ _ _
@[simp] theorem handleMixInvMark_two : handleMixInvMark j m 2 = m 2 :=
  handleMixUpdate_two _ _ _ _

@[simp] theorem handleMixInvMark_three :
    handleMixInvMark j m 3
      = handleMixInvD (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j) :=
  handleMixUpdate_three _ _ _ _

@[simp] theorem handleMixInvMark_handleU_self :
    handleMixInvMark j m (handleIdxU j)
      = handleMixInvU (m 2) (m 3) (m (handleIdxU j)) (m (handleIdxV j)) (handleMixZeta m j) :=
  handleMixUpdate_handleU_self _ _ _ _

theorem handleMixInvMark_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    handleMixInvMark j m (handleIdxU i) = m (handleIdxU i) :=
  handleMixUpdate_handleU_of_ne _ _ _ _ hij

@[simp] theorem handleMixInvMark_handleV (i : Fin h) :
    handleMixInvMark j m (handleIdxV i) = m (handleIdxV i) :=
  handleMixUpdate_handleV _ _ _ _ _

/-- **`ζ_j` is fixed by any two-slot update at `j`** (memo §4.3: `Φ_j` moves only letters the
intervening block does not contain).  `handlePrefix_congr` is HM1's lemma that makes this one
line. -/
@[simp] theorem handleMixZeta_handleMixUpdate (wd wu : G) :
    handleMixZeta (handleMixUpdate j m wd wu) j = handleMixZeta m j := by
  rw [handleMixZeta, handleMixZeta, handleMixUpdate_comp_U, handleMixUpdate_comp_V]
  refine handlePrefix_congr _ fun i hi => ?_
  have hij : i ≠ j := fun hc => by rw [hc] at hi; omega
  rw [Function.update_of_ne hij]

/-- **`Φ_j⁻¹ ∘ Φ_j = id` on markings** — memo §4.2's first composite, from the two word
identities of §1. -/
theorem handleMixInvMark_handleMixMark : handleMixInvMark j (handleMixMark j m) = m := by
  funext i
  by_cases hiU : i = handleIdxU j
  · subst hiU
    rw [handleMixInvMark_handleU_self, handleMixMark, handleMixZeta_handleMixUpdate,
      handleMixUpdate_two, handleMixUpdate_three, handleMixUpdate_handleU_self,
      handleMixUpdate_handleV, handleMixInvU_handleMixD]
  by_cases hi3 : i = 3
  · subst hi3
    rw [handleMixInvMark_three, handleMixMark, handleMixZeta_handleMixUpdate,
      handleMixUpdate_two, handleMixUpdate_three, handleMixUpdate_handleU_self,
      handleMixUpdate_handleV, handleMixInvD_handleMixD]
  rw [handleMixInvMark, handleMixUpdate, Function.update_of_ne hiU,
    Function.update_of_ne hi3, handleMixMark, handleMixUpdate, Function.update_of_ne hiU,
    Function.update_of_ne hi3]

/-- **`Φ_j ∘ Φ_j⁻¹ = id` on markings** — memo §4.2's second composite. -/
theorem handleMixMark_handleMixInvMark : handleMixMark j (handleMixInvMark j m) = m := by
  funext i
  by_cases hiU : i = handleIdxU j
  · subst hiU
    rw [handleMixMark_handleU_self, handleMixInvMark, handleMixZeta_handleMixUpdate,
      handleMixUpdate_two, handleMixUpdate_three, handleMixUpdate_handleU_self,
      handleMixUpdate_handleV, handleMixU_handleMixInvD]
  by_cases hi3 : i = 3
  · subst hi3
    rw [handleMixMark_three, handleMixInvMark, handleMixZeta_handleMixUpdate,
      handleMixUpdate_two, handleMixUpdate_three, handleMixUpdate_handleU_self,
      handleMixUpdate_handleV, handleMixD_handleMixInvD]
  rw [handleMixMark, handleMixUpdate, Function.update_of_ne hiU,
    Function.update_of_ne hi3, handleMixInvMark, handleMixUpdate, Function.update_of_ne hiU,
    Function.update_of_ne hi3]

end MixMark

/-! ### `Φ_j(P) = P` — the word-level obligation of HM2 (memo §4.1) -/

section MixMarkRelator

variable {G : Type*} [Group G] {h : ℕ}

/-- **`Φ_j` fixes the `M_α` relator** — memo §4.1's `Φ_j(P) = P`, at general handle count `h`
and general handle index `j`.  This, and its `N`-mirror, is the word-level obligation of
HM2. -/
theorem mRelWord_handleMixMark (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) :
    mRelWord α (handleMixMark j m) = mRelWord α m := by
  have key := commP_mul_handleWord_handleMix (m 2) (m 3)
    (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j
  rw [handleMixMark, mRelWord_handleMixUpdate, mRelWord, handleMixZeta, mWord, mWord, mul_assoc,
    key, ← mul_assoc]

/-- **`Φ_j` fixes the `N_α` relator** (memo §4.1, §4.4: for `N` the prefix shares no letter
with `[c,d]`, so this is the easy case). -/
theorem nRelWord_handleMixMark (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) :
    nRelWord α (handleMixMark j m) = nRelWord α m := by
  have key := commP_mul_handleWord_handleMix (m 2) (m 3)
    (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) j
  rw [handleMixMark, nRelWord_handleMixUpdate, nRelWord, handleMixZeta, nWord, nWord, mul_assoc,
    key, ← mul_assoc]

/-- **`Φ_j⁻¹` fixes the `M_α` relator** too — read off `Φ_j` at the substituted marking
(memo §4.2: both composites are the identity in the free group, so the inverse is a relator
automorphism for the same reason `Φ_j` is). -/
theorem mRelWord_handleMixInvMark (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) :
    mRelWord α (handleMixInvMark j m) = mRelWord α m := by
  rw [← mRelWord_handleMixMark α j (handleMixInvMark j m), handleMixMark_handleMixInvMark]

/-- **`Φ_j⁻¹` fixes the `N_α` relator**. -/
theorem nRelWord_handleMixInvMark (α : ℕ) (j : Fin h) (m : Fin (coreRank h) → G) :
    nRelWord α (handleMixInvMark j m) = nRelWord α m := by
  rw [← nRelWord_handleMixMark α j (handleMixInvMark j m), handleMixMark_handleMixInvMark]

end MixMarkRelator

/-! ### Naturality of the two substitutions

The naturality lemmas are what turn the marking-level composition identities above into the
*hom-level* composition identities of §3: pushing `Φ_j⁻¹` through the word `Φ_j(x_i)` replaces
each letter by its `Φ_j⁻¹`-image, i.e. composes the two substitutions. -/

section MixMarkNaturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H] {h : ℕ}

theorem map_handleMixZeta (φ : F) (m : Fin (coreRank h) → G) (j : Fin h) :
    φ (handleMixZeta m j) = handleMixZeta (fun i => φ (m i)) j := by
  rw [handleMixZeta, map_handlePrefix, handleMixZeta]

theorem map_handleMixMark (φ : F) (j : Fin h) (m : Fin (coreRank h) → G)
    (i : Fin (coreRank h)) :
    φ (handleMixMark j m i) = handleMixMark j (fun i => φ (m i)) i := by
  simp only [handleMixMark, map_handleMixUpdate, map_handleMixD, map_handleMixU,
    map_handleMixZeta]

theorem map_handleMixInvMark (φ : F) (j : Fin h) (m : Fin (coreRank h) → G)
    (i : Fin (coreRank h)) :
    φ (handleMixInvMark j m i) = handleMixInvMark j (fun i => φ (m i)) i := by
  simp only [handleMixInvMark, map_handleMixUpdate, map_handleMixInvD, map_handleMixInvU,
    map_handleMixZeta]

end MixMarkNaturality

/-! ## §3 The assembly into `ContinuousMulEquiv` (the `thetaEquiv` pattern)

`GQ2/AnabelianBridge/Construction.lean:864/880/929` builds the shear `Θ_b` of `D₀` in exactly
this shape: a `d0Lift` out of a marking that respects the relator, an explicit inverse, the two
composites by hom-extensionality, and `continuousMulEquivOfBijective` at the end.  Here MC2's
`mLiftHom`/`nLiftHom` supply the lift and `dm_hom_ext`/`dn_hom_ext` the extensionality, so
**continuity is free** — memo §4.2's "the two-sided inverse is available *before* descending to
`D_P`" is what makes that work. -/

section Assembly

variable (α h : ℕ) (j : Fin h)

/-! ### The `M_α` core -/

/-- **`Φ_j` on `D_{M,α,h}`** (memo §4.4): the continuous endomorphism classified by the mixing
substitution.  The relator hypothesis is `mRelWord_handleMixMark` — memo §4.1's `Φ_j(P) = P`. -/
noncomputable def dmMixHom : ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (handleMixMark j (dmGen α h))
    (by rw [mRelWord_handleMixMark]; exact dm_relation α h)

/-- **`Φ_j⁻¹` on `D_{M,α,h}`** (memo §4.2). -/
noncomputable def dmMixInvHom : ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (handleMixInvMark j (dmGen α h))
    (by rw [mRelWord_handleMixInvMark]; exact dm_relation α h)

@[simp] theorem dmMixHom_gen (i : Fin (coreRank h)) :
    dmMixHom α h j (dmGen α h i) = handleMixMark j (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

@[simp] theorem dmMixInvHom_gen (i : Fin (coreRank h)) :
    dmMixInvHom α h j (dmGen α h i) = handleMixInvMark j (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

/-- `Φ_j⁻¹ ∘ Φ_j = id` on `D_M`. -/
theorem dmMixInvHom_dmMixHom (x : (DM α h : Type)) :
    dmMixInvHom α h j (dmMixHom α h j x) = x := by
  have hgen : (fun i => dmMixInvHom α h j (dmGen α h i)) = handleMixInvMark j (dmGen α h) :=
    funext fun i => dmMixInvHom_gen α h j i
  have hext : (dmMixInvHom α h j).comp (dmMixHom α h j)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DM α h : Type) (DM α h : Type)) := by
    refine dm_hom_ext _ _ fun i => ?_
    show dmMixInvHom α h j (dmMixHom α h j (dmGen α h i)) = dmGen α h i
    rw [dmMixHom_gen, map_handleMixMark, hgen, handleMixMark_handleMixInvMark]
  exact DFunLike.congr_fun hext x

/-- `Φ_j ∘ Φ_j⁻¹ = id` on `D_M`. -/
theorem dmMixHom_dmMixInvHom (x : (DM α h : Type)) :
    dmMixHom α h j (dmMixInvHom α h j x) = x := by
  have hgen : (fun i => dmMixHom α h j (dmGen α h i)) = handleMixMark j (dmGen α h) :=
    funext fun i => dmMixHom_gen α h j i
  have hext : (dmMixHom α h j).comp (dmMixInvHom α h j)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DM α h : Type) (DM α h : Type)) := by
    refine dm_hom_ext _ _ fun i => ?_
    show dmMixHom α h j (dmMixInvHom α h j (dmGen α h i)) = dmGen α h i
    rw [dmMixInvHom_gen, map_handleMixInvMark, hgen, handleMixInvMark_handleMixMark]
  exact DFunLike.congr_fun hext x

/-- **The mixing automorphism of `D_{M,α,h}`** (memo §4, V3): a *continuous* automorphism of
the presented core realizing memo §6.4's handle↔core mixing element at the handle index `j`,
fixing the relator on the nose and needing no new axiom. -/
noncomputable def dmMixEquiv : ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  continuousMulEquivOfBijective (dmMixHom α h j)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dmMixInvHom α h j, dmMixInvHom_dmMixHom α h j, dmMixHom_dmMixInvHom α h j⟩)

@[simp] theorem dmMixEquiv_apply (x : (DM α h : Type)) :
    dmMixEquiv α h j x = dmMixHom α h j x := rfl

@[simp] theorem dmMixEquiv_gen (i : Fin (coreRank h)) :
    dmMixEquiv α h j (dmGen α h i) = handleMixMark j (dmGen α h) i := dmMixHom_gen α h j i

/-! #### The generator rows of `Φ_j` on `D_M` (what HM3 reads) -/

@[simp] theorem dmMixEquiv_dmA : dmMixEquiv α h j (dmA α h) = dmA α h := by
  rw [dmA, dmMixEquiv_gen, handleMixMark_zero]

@[simp] theorem dmMixEquiv_dmB : dmMixEquiv α h j (dmB α h) = dmB α h := by
  rw [dmB, dmMixEquiv_gen, handleMixMark_one]

@[simp] theorem dmMixEquiv_dmC : dmMixEquiv α h j (dmC α h) = dmC α h := by
  rw [dmC, dmMixEquiv_gen, handleMixMark_two]

/-- The moved core letter: `Φ_j(D) = C₀·D·ζ_j·(v_j⁻¹)^{u_j}·ζ_j⁻¹`. -/
@[simp] theorem dmMixEquiv_dmD :
    dmMixEquiv α h j (dmD α h)
      = handleMixD (dmC α h) (dmD α h) (dmGen α h (handleIdxU j)) (dmGen α h (handleIdxV j))
          (handleMixZeta (dmGen α h) j) := by
  rw [dmC, dmD, dmMixEquiv_gen, handleMixMark_three]

/-- The moved handle letter: `Φ_j(u_j) = u_j·(C₀^D)^{ζ_j}·(v_j⁻¹)^{u_j}`. -/
@[simp] theorem dmMixEquiv_handleU_self :
    dmMixEquiv α h j (dmGen α h (handleIdxU j))
      = handleMixU (dmC α h) (dmD α h) (dmGen α h (handleIdxU j)) (dmGen α h (handleIdxV j))
          (handleMixZeta (dmGen α h) j) := by
  rw [dmC, dmD, dmMixEquiv_gen, handleMixMark_handleU_self]

theorem dmMixEquiv_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    dmMixEquiv α h j (dmGen α h (handleIdxU i)) = dmGen α h (handleIdxU i) := by
  rw [dmMixEquiv_gen, handleMixMark_handleU_of_ne _ _ hij]

@[simp] theorem dmMixEquiv_handleV (i : Fin h) :
    dmMixEquiv α h j (dmGen α h (handleIdxV i)) = dmGen α h (handleIdxV i) := by
  rw [dmMixEquiv_gen, handleMixMark_handleV]

/-! ### The `N_α` core -/

/-- **`Φ_j` on `D_{N,α,h}`** (memo §4.4). -/
noncomputable def dnMixHom : ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (handleMixMark j (dnGen α h))
    (by rw [nRelWord_handleMixMark]; exact dn_relation α h)

/-- **`Φ_j⁻¹` on `D_{N,α,h}`** (memo §4.2). -/
noncomputable def dnMixInvHom : ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (handleMixInvMark j (dnGen α h))
    (by rw [nRelWord_handleMixInvMark]; exact dn_relation α h)

@[simp] theorem dnMixHom_gen (i : Fin (coreRank h)) :
    dnMixHom α h j (dnGen α h i) = handleMixMark j (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnMixInvHom_gen (i : Fin (coreRank h)) :
    dnMixInvHom α h j (dnGen α h i) = handleMixInvMark j (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

/-- `Φ_j⁻¹ ∘ Φ_j = id` on `D_N`. -/
theorem dnMixInvHom_dnMixHom (x : (DN α h : Type)) :
    dnMixInvHom α h j (dnMixHom α h j x) = x := by
  have hgen : (fun i => dnMixInvHom α h j (dnGen α h i)) = handleMixInvMark j (dnGen α h) :=
    funext fun i => dnMixInvHom_gen α h j i
  have hext : (dnMixInvHom α h j).comp (dnMixHom α h j)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DN α h : Type) (DN α h : Type)) := by
    refine dn_hom_ext _ _ fun i => ?_
    show dnMixInvHom α h j (dnMixHom α h j (dnGen α h i)) = dnGen α h i
    rw [dnMixHom_gen, map_handleMixMark, hgen, handleMixMark_handleMixInvMark]
  exact DFunLike.congr_fun hext x

/-- `Φ_j ∘ Φ_j⁻¹ = id` on `D_N`. -/
theorem dnMixHom_dnMixInvHom (x : (DN α h : Type)) :
    dnMixHom α h j (dnMixInvHom α h j x) = x := by
  have hgen : (fun i => dnMixHom α h j (dnGen α h i)) = handleMixMark j (dnGen α h) :=
    funext fun i => dnMixHom_gen α h j i
  have hext : (dnMixHom α h j).comp (dnMixInvHom α h j)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DN α h : Type) (DN α h : Type)) := by
    refine dn_hom_ext _ _ fun i => ?_
    show dnMixHom α h j (dnMixInvHom α h j (dnGen α h i)) = dnGen α h i
    rw [dnMixInvHom_gen, map_handleMixInvMark, hgen, handleMixInvMark_handleMixMark]
  exact DFunLike.congr_fun hext x

/-- **The mixing automorphism of `D_{N,α,h}`** (memo §4.4: for `N` the prefix `x₀^{2+2^α}[x₀,x₁]`
shares no letter with the surface part `[σ,x₂]·∏[u_j,v_j]`, so `N` is the easy case). -/
noncomputable def dnMixEquiv : ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  continuousMulEquivOfBijective (dnMixHom α h j)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dnMixInvHom α h j, dnMixInvHom_dnMixHom α h j, dnMixHom_dnMixInvHom α h j⟩)

@[simp] theorem dnMixEquiv_apply (x : (DN α h : Type)) :
    dnMixEquiv α h j x = dnMixHom α h j x := rfl

@[simp] theorem dnMixEquiv_gen (i : Fin (coreRank h)) :
    dnMixEquiv α h j (dnGen α h i) = handleMixMark j (dnGen α h) i := dnMixHom_gen α h j i

/-! #### The generator rows of `Φ_j` on `D_N` (what HM3 reads) -/

@[simp] theorem dnMixEquiv_dnX0 : dnMixEquiv α h j (dnX0 α h) = dnX0 α h := by
  rw [dnX0, dnMixEquiv_gen, handleMixMark_zero]

@[simp] theorem dnMixEquiv_dnX1 : dnMixEquiv α h j (dnX1 α h) = dnX1 α h := by
  rw [dnX1, dnMixEquiv_gen, handleMixMark_one]

@[simp] theorem dnMixEquiv_dnSigma : dnMixEquiv α h j (dnSigma α h) = dnSigma α h := by
  rw [dnSigma, dnMixEquiv_gen, handleMixMark_two]

/-- The moved core letter: `Φ_j(x₂) = σ·x₂·ζ_j·(v_j⁻¹)^{u_j}·ζ_j⁻¹`. -/
@[simp] theorem dnMixEquiv_dnX2 :
    dnMixEquiv α h j (dnX2 α h)
      = handleMixD (dnSigma α h) (dnX2 α h) (dnGen α h (handleIdxU j))
          (dnGen α h (handleIdxV j)) (handleMixZeta (dnGen α h) j) := by
  rw [dnSigma, dnX2, dnMixEquiv_gen, handleMixMark_three]

/-- The moved handle letter: `Φ_j(u_j) = u_j·(σ^{x₂})^{ζ_j}·(v_j⁻¹)^{u_j}`. -/
@[simp] theorem dnMixEquiv_handleU_self :
    dnMixEquiv α h j (dnGen α h (handleIdxU j))
      = handleMixU (dnSigma α h) (dnX2 α h) (dnGen α h (handleIdxU j))
          (dnGen α h (handleIdxV j)) (handleMixZeta (dnGen α h) j) := by
  rw [dnSigma, dnX2, dnMixEquiv_gen, handleMixMark_handleU_self]

theorem dnMixEquiv_handleU_of_ne {i : Fin h} (hij : i ≠ j) :
    dnMixEquiv α h j (dnGen α h (handleIdxU i)) = dnGen α h (handleIdxU i) := by
  rw [dnMixEquiv_gen, handleMixMark_handleU_of_ne _ _ hij]

@[simp] theorem dnMixEquiv_handleV (i : Fin h) :
    dnMixEquiv α h j (dnGen α h (handleIdxV i)) = dnGen α h (handleIdxV i) := by
  rw [dnMixEquiv_gen, handleMixMark_handleV]

end Assembly

end MarkedCore

end Dyadic

end GQ2
