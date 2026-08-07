/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.UVFrames

/-!
# W44 — ⚠ all three Eichler ansätze are **refuted**

`SqCore/LamFrames.lean` cut the whole `h ≥ 1` residual down to one word equation per family: at
every selected marking and every handle, some dressing weights kill the relator on `sqEichFrame`
(§3, `SqEichRelWord`), or on the transposed `sqEichFrameT` (§6, `SqEichRelWordT`), or on *one of
the two* (§6, `SqEichRelWordMix`).  **All three equations are false for `h ≥ 1`.**

## The obstruction, in one line

Each family dresses its four moved slots by powers of a **single** letter, and that letter is one
of the two it moved.  Send `D_sq h` to a group where that letter dies: the dressings all die with
it, the four dressed slots fall back to their undressed values, and the `j`-th handle commutator
collapses (`[U·V^d, V] ↦ [U, 1] = 1`, resp. `[U, V·U^d] ↦ [1, V] = 1`).  What is left is the bare
core word — which the relator says is the *inverse* of that very commutator, so it is `≠ 1`
exactly when the commutator was.

Killing `V = v_j·w^{−s}` needs `v_j ↦ w^{s}`, and killing `U = w^{−t}·u_j` needs `u_j ↦ w^{t}`.
Neither is possible at row `0` (it would force the handle commutator trivial and the relator
would not hold), and **both** are possible at row `1`.  That is the whole content of §3:

| family | dies whenever | witness |
|---|---|---|
| `sqEichFrame` (`V`-dressed) | `ν'(v_j) = 1`, any `ν'(u_j)` | `u_j ↦ sr 1`, `v_j ↦ sr 0` |
| `sqEichFrameT` (`U`-dressed) | `ν'(u_j) = 1`, any `ν'(v_j)` | `u_j ↦ sr 0`, `v_j ↦ sr 1` |

so at the selected marking `nuSel h j 1 1` — *both* rows equal to `1` — **neither** family works,
and the mix falls with them (`not_sqEichRelWordMix`).

Concretely the target is the order-8 group `D₄ ≅ Heis(𝔽₂)`, marked `σ ↦ sr 0`, `x₀ ↦ 1`,
`x₁ ↦ r 1`, `u_j ↦ a`, `v_j ↦ b`, every other letter `↦ 1`, for any `a, b` with `[a, b] = r 2`.
The pivot `w = σ·x₀^{−c₀}` goes to `sr 0` with no fact about `c₀` used (`x₀ ↦ 1`, `1^{c₀} = 1`),
and the relator holds because the core word also goes to `r 2`.

## ⭐ The test does **not** transpose

The homomorphism that kills the `V`-family at `nuSel h j 0 1` leaves the transposed family
standing at that very marking, and does so *for a reason*: there `ν'(u_j) = 0`, so `U ↦ sr 1 ≠ 1`
and the `U`-dressings survive.  At `(f, f', d) = (0, 1, d)` the surviving dressing puts `sr 1`
into the `x₀`-slot, the core word `sqWord (sr 0) (sr 1) (r 1)` is `1`, the handle commutator
`[sr 1, (sr 1)^d]` is `1`, and the whole relator dies
(`exists_hom_refuting_sqEichFrame_not_sqEichFrameT`).  So §3's second refutation is genuinely a
*new* obstruction at a *new* marking, not the old one in disguise; the two are transverse, which
is precisely why the mix needs `nuSel h j 1 1`.

## ⚠ What died, and what did **not**

* **Dead**: `sqEichFrame`, `sqEichFrameT`, and their disjunction, as ansätze for the residual —
  not merely "at the class-two-forced parameters" but at *every* weight triple.  So neither
  failure is a near miss to be fixed by a correction term.
* **Not dead**: `SqLamMarkTransitivity h` itself.  `sqLamMarkTransitivity_iff_frames` quantifies
  over **all** five-word frames; this file kills two explicitly parametrised families and their
  union, which is a set of measure zero among frames.
* ⚠ **Also dead, and by a *different* mechanism**: the two-letter widening `sqEichFrameUV` of
  `SqCore/UVFrames.lean`, which dresses each moved slot by `U^k V^l` and contains both families
  above as slices.  §3's collapse genuinely cannot reach it, but §7's can — see below.
* **Not dead**: the Eichler *idea*, and in particular the widening named in `LamFrames` §4 —
  dress the four moved slots by **arbitrary** `λ`-trivial, `ν'`-trivial elements rather than by
  words in the two cleared letters.  That costs nothing on any row (§2a's proofs are verbatim) and
  needs only its own surjectivity check, and **neither** mechanism reaches it: §3's collapse needs
  the dressings to lie in the kernel of the test homomorphism, and §7's needs them to lie in the
  procyclic `⟨z⟩` — both of which words in `U` and `V` guarantee and an arbitrary dressing does
  not.

## Contents

* **§1** the target `D₄` as a pro-2 group, `handleWord_eq_single`, `commP_one_left/right`;
* **§2** the two-parameter refuting marking `refMark h j a b`, its relator, and `refHom`;
* **§3** the images of the pivot, `V`, `U`, both frames, and the three refutations;
* **§4** ⭐ the non-transposing test;
* **§5** stress pins, **§6** committed axiom prints;
* **§7** ⭐ the **collapse lemma** — identify the two cleared letters onto an involution — stated
  for an arbitrary pro-2 target, an arbitrary selected marking and every weight tuple;
* **§8** its `D₈` instance: `not_sqEichRelWordUV`, and one homomorphism refuting all three
  families at the single marking `nuSel h j 1 1`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide` (the `decide` calls are all on the order-8 group
`D₄` or the order-16 group `D₈`).  Every declaration prints **std-3**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The target, and a handle-block evaluation

The refutation needs one nonabelian pro-2 group in which everything is decidable.  The smallest
one that works is `D₄ ≅ Heis(𝔽₂)`, order 8, with the discrete topology: a finite 2-group is
pro-2 (`isProP_of_isPGroup`), and every other instance the lift needs is automatic for a finite
discrete group. -/

section Target

local instance instTopologicalSpaceD4 : TopologicalSpace (DihedralGroup 4) := ⊥
local instance instDiscreteTopologyD4 : DiscreteTopology (DihedralGroup 4) := ⟨rfl⟩

/-- `D₄` is pro-2: every element has order dividing `4`. -/
theorem isProP_two_dihedral4 : IsProP 2 (DihedralGroup 4) :=
  isProP_of_isPGroup fun g => ⟨2, by revert g; decide⟩

/-- A handle block in which only the `j`-th commutator survives **is** that commutator. -/
theorem handleWord_eq_single {G : Type*} [Group G] {h : ℕ} (u v : Fin h → G) (j : Fin h)
    (hne : ∀ i : Fin h, i ≠ j → commP (u i) (v i) = 1) :
    handleWord u v = commP (u j) (v j) := by
  have hpre : handlePrefix u v (j : ℕ) = 1 := by
    rw [handlePrefix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hne i fun hc => absurd (mem_take_finRange hi) (by rw [hc]; omega)
  have hsuf : handleSuffix u v ((j : ℕ) + 1) = 1 := by
    rw [handleSuffix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hne i fun hc => absurd (mem_drop_finRange hi) (by rw [hc]; omega)
  rw [handleWord_split u v j, hpre, hsuf, one_mul, mul_one]

/-- A commutator with `1` is trivial — the shape every collapsed handle block takes. -/
private theorem commP_one_right {G : Type*} [Group G] (x : G) : commP x 1 = 1 := by
  simp [commP]

/-- …and on the other side. -/
private theorem commP_one_left {G : Type*} [Group G] (x : G) : commP 1 x = 1 := by
  simp [commP]

/-! ## §2 The refuting markings

One two-parameter family of markings does every refutation below.  Send `σ ↦ sr 0`, `x₀ ↦ 1`,
`x₁ ↦ r 1` — so the pivot `w = σ·x₀^{−c₀}` goes to `sr 0` whatever `c₀` is — and put the two
handle letters at *arbitrary* values `a, b` whose commutator is the central `r 2`.  The relator
then holds, because the core word also goes to `r 2`.

Which family dies is decided by *which* of the two cleared letters this marking sends to `1`:
`V = v_j·w^{−s}` dies iff `b = w^{s}`, and `U = w^{−t}·u_j` dies iff `a = w^{t}`.  Since `[a, b]`
must stay `≠ 1`, neither can happen at row `0`; both happen at row `1`, with `a` resp. `b` equal
to `sr 0`. -/

/-- `σ`'s value, and the pivot's: a reflection. -/
private abbrev refS : DihedralGroup 4 := DihedralGroup.sr 0

/-- The other reflection.  `[refQ, refS] = [refS, refQ] = r 2 ≠ 1`. -/
private abbrev refQ : DihedralGroup 4 := DihedralGroup.sr 1

/-- `x₁`'s value: a rotation of order four, so `refY ^ 2 = r 2` is the same central element. -/
private abbrev refY : DihedralGroup 4 := DihedralGroup.r 1

variable {h : ℕ} {j : Fin h} {a b : DihedralGroup 4}

/-- **The refuting marking**: `σ ↦ refS`, `x₀ ↦ 1`, `x₁ ↦ refY`, `u_j ↦ a`, `v_j ↦ b`, and `1` on
every other letter. -/
private def refMark (h : ℕ) (j : Fin h) (a b : DihedralGroup 4) :
    Fin (sqRank h) → DihedralGroup 4 :=
  fun i =>
    if (i : ℕ) = 0 then refS else
    if (i : ℕ) = 2 then refY else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then a else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then b else 1

@[simp] private theorem refMark_zero : refMark h j a b 0 = refS := by
  simp only [refMark, sqVal_zero]
  norm_num

@[simp] private theorem refMark_one : refMark h j a b 1 = 1 := by
  simp only [refMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem refMark_two : refMark h j a b 2 = refY := by
  simp only [refMark, sqVal_two]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem refMark_handleU : refMark h j a b (sqHandleIdxU j) = a := by
  simp only [refMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem refMark_handleV : refMark h j a b (sqHandleIdxV j) = b := by
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem refMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    refMark h j a b (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem refMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    refMark h j a b (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Every handle but the `j`-th contributes nothing. -/
private theorem commP_refMark_ne {j' : Fin h} (hne : j' ≠ j) :
    commP (refMark h j a b (sqHandleIdxU j')) (refMark h j a b (sqHandleIdxV j')) = 1 := by
  rw [refMark_handleU_ne hne, refMark_handleV_ne hne, commP_one_right]

/-- **The refuting marking kills the relator**: `C ↦ r 2` and `[a, b] = r 2` cancel. -/
private theorem sqRelWord_refMark (h : ℕ) (j : Fin h)
    (hab : commP a b = DihedralGroup.r 2) : sqRelWord (refMark h j a b) = 1 := by
  rw [sqRelWord, handleWord_eq_single _ _ j fun i hi => commP_refMark_ne hi, refMark_zero,
    refMark_one, refMark_two, refMark_handleU, refMark_handleV, hab]
  decide

/-- The two commutator facts the family is built on. -/
private theorem commP_refQ_refS : commP refQ refS = DihedralGroup.r 2 := by decide

private theorem commP_refS_refQ : commP refS refQ = DihedralGroup.r 2 := by decide

/-- The refuting hom `D_sq h → D₄`. -/
private noncomputable def refHom (h : ℕ) (j : Fin h) (a b : DihedralGroup 4)
    (hab : commP a b = DihedralGroup.r 2) :
    ContinuousMonoidHom (DSq h : Type) (DihedralGroup 4) :=
  sqLiftHom h isProP_two_dihedral4 (refMark h j a b) (sqRelWord_refMark h j hab)

@[simp] private theorem refHom_gen (hab : commP a b = DihedralGroup.r 2) (i : Fin (sqRank h)) :
    refHom h j a b hab (sqGen h i) = refMark h j a b i :=
  sqLiftHom_gen _ _ _ _ i

/-! ## §3 The frames die

`x₀ ↦ 1` makes the pivot's `x₀`-leg vanish for *any* exponent (`zpowZtwo_one_base`), so
`w ↦ refS` with no fact about `c₀`.  Then:

* `b = refS` and `ν'(v_j) = 1` makes **`V ↦ 1`**, which kills every `V`-dressing and the `j`-th
  handle commutator at once — the `V`-family collapses to the bare core word;
* `a = refS` and `ν'(u_j) = 1` makes **`U ↦ 1`**, and the transposed family collapses the same way.

In both cases what survives is the core word `sqWord (sr 0) 1 (r 1) = r 2 ≠ 1` — which is exactly
the *inverse* of the handle commutator that just vanished. -/

/-- The pivot goes to `refS`. -/
private theorem refHom_sqPivot (hab : commP a b = DihedralGroup.r 2) :
    refHom h j a b hab (sqPivot h) = refS := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, dsqX0, refHom_gen, refMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, refHom_gen, refMark_zero]

/-- **`V` dies** when the `v`-letter sits at the pivot's image and the `v`-row is `1`: the
`V`-family's `v`-slot is the letter it moved. -/
private theorem refHom_sqEichV (hab : commP a refS = DihedralGroup.r 2) (t : ℤ_[2]) :
    refHom h j a refS hab (sqEichV h (nuSel h j t 1) j) = 1 := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4,
    refHom_sqPivot, nuSel_handleV, toAdd_ofAdd, zpowZtwo_one_exp, refHom_gen, refMark_handleV,
    mul_inv_cancel]

/-- **`U` dies** when the `u`-letter sits at the pivot's image and the `u`-row is `1`: the
transposed family's `u`-slot is the letter *it* moved. -/
private theorem refHom_sqEichU (hab : commP refS b = DihedralGroup.r 2) (s : ℤ_[2]) :
    refHom h j refS b hab (sqEichU h (nuSel h j 1 s) j) = 1 := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4,
    refHom_sqPivot, nuSel_handleU, toAdd_ofAdd, zpowZtwo_one_exp, refHom_gen, refMark_handleU,
    inv_mul_cancel]

/-- `U` goes to `refQ` at `ν'(u_j) = 0`: no pivot power is subtracted. -/
private theorem refHom_sqEichU_zero (hab : commP refQ refS = DihedralGroup.r 2) (s : ℤ_[2]) :
    refHom h j refQ refS hab (sqEichU h (nuSel h j 0 s) j) = refQ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4,
    refHom_sqPivot, nuSel_handleU, toAdd_ofAdd, SectionThree.zpowZtwo_zero, inv_one, one_mul,
    refHom_gen, refMark_handleU]

variable {e e' d : ℤ_[2]}

/-- Every `V`-dressing dies with `V`. -/
private theorem refHom_dressV (hab : commP a refS = DihedralGroup.r 2) (t : ℤ_[2])
    (x : (DSq h : Type)) (k : ℤ_[2]) :
    refHom h j a refS hab (x * zpowZtwo (isProP_DSq h) (sqEichV h (nuSel h j t 1) j) k)
      = refHom h j a refS hab x := by
  rw [map_mul, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, refHom_sqEichV,
    zpowZtwo_one_base, mul_one]

/-- Every `U`-dressing dies with `U`. -/
private theorem refHom_dressU (hab : commP refS b = DihedralGroup.r 2) (s : ℤ_[2])
    (x : (DSq h : Type)) (k : ℤ_[2]) :
    refHom h j refS b hab (x * zpowZtwo (isProP_DSq h) (sqEichU h (nuSel h j 1 s) j) k)
      = refHom h j refS b hab x := by
  rw [map_mul, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, refHom_sqEichU,
    zpowZtwo_one_base, mul_one]

/-- **The `V`-family's relator does not die**: it lands on the central `r 2`, at *every* `ν'(u_j)`
and every `(e, e', d)`. -/
private theorem refHom_sqRelWord_sqEichFrame (hab : commP a refS = DihedralGroup.r 2)
    (t : ℤ_[2]) :
    refHom h j a refS hab (sqRelWord (sqEichFrame h (nuSel h j t 1) j e e' d))
      = DihedralGroup.r 2 := by
  have hzero : refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d 0) = refS := by
    rw [sqEichFrame_zero, refHom_dressV, dsqSigma, refHom_gen, refMark_zero]
  have hone : refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d 1) = 1 := by
    rw [sqEichFrame_one, refHom_dressV, dsqX0, refHom_gen, refMark_one]
  have htwo : refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d 2) = refY := by
    rw [sqEichFrame_two, refHom_dressV, dsqX1, refHom_gen, refMark_two]
  have hV : refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d (sqHandleIdxV j))
      = 1 := by
    rw [sqEichFrame_handleV, refHom_sqEichV]
  have hne : ∀ i : Fin h, i ≠ j →
      commP (refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d (sqHandleIdxU i)))
        (refHom h j a refS hab (sqEichFrame h (nuSel h j t 1) j e e' d (sqHandleIdxV i))) = 1 := by
    intro i hi
    rw [sqEichFrame_handleU_ne hi, sqEichFrame_handleV_ne hi, refHom_gen, refHom_gen,
      refMark_handleU_ne hi, refMark_handleV_ne hi, commP_one_right]
  rw [map_sqRelWord, sqRelWord, handleWord_eq_single _ _ j hne, hzero, hone, htwo, hV,
    commP_one_right]
  decide

/-- **The transposed family's relator does not die either**: same collapse, with `U` in place of
`V`, at *every* `ν'(v_j)` and every `(f, f', d)`. -/
private theorem refHom_sqRelWord_sqEichFrameT (hab : commP refS b = DihedralGroup.r 2)
    (s : ℤ_[2]) :
    refHom h j refS b hab (sqRelWord (sqEichFrameT h (nuSel h j 1 s) j e e' d))
      = DihedralGroup.r 2 := by
  have hzero : refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d 0) = refS := by
    rw [sqEichFrameT_zero, refHom_dressU, dsqSigma, refHom_gen, refMark_zero]
  have hone : refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d 1) = 1 := by
    rw [sqEichFrameT_one, refHom_dressU, dsqX0, refHom_gen, refMark_one]
  have htwo : refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d 2) = refY := by
    rw [sqEichFrameT_two, refHom_dressU, dsqX1, refHom_gen, refMark_two]
  have hU : refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d (sqHandleIdxU j))
      = 1 := by
    rw [sqEichFrameT_handleU, refHom_sqEichU]
  have hne : ∀ i : Fin h, i ≠ j →
      commP (refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d (sqHandleIdxU i)))
        (refHom h j refS b hab (sqEichFrameT h (nuSel h j 1 s) j e e' d (sqHandleIdxV i)))
        = 1 := by
    intro i hi
    rw [sqEichFrameT_handleU_ne hi, sqEichFrameT_handleV_ne hi, refHom_gen, refHom_gen,
      refMark_handleU_ne hi, refMark_handleV_ne hi, commP_one_right]
  rw [map_sqRelWord, sqRelWord, handleWord_eq_single _ _ j hne, hzero, hone, htwo, hU,
    commP_one_left]
  decide

/-- ⚠ **The refutation of the `V`-family.**  Whenever the selected marking has `ν'(v_j) = 1` the
Eichler frame kills the relator for **no** `(e, e', d)`, at any `ν'(u_j)`. -/
theorem not_sqRelWord_sqEichFrame_nuSel_one (h : ℕ) (j : Fin h) (t e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame h (nuSel h j t 1) j e e' d) ≠ 1 := by
  intro hone
  have h1 : refHom h j refQ refS commP_refQ_refS
      (sqRelWord (sqEichFrame h (nuSel h j t 1) j e e' d)) = 1 := by
    rw [hone, map_one]
  rw [refHom_sqRelWord_sqEichFrame] at h1
  exact absurd h1 (by decide)

/-- ⚠ **The refutation.**  At the selected marking `nuSel h j 0 1` the Eichler frame kills the
relator for **no** `(e, e', d)`. -/
theorem not_sqRelWord_sqEichFrame_nuSel (h : ℕ) (j : Fin h) (e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame h (nuSel h j 0 1) j e e' d) ≠ 1 :=
  not_sqRelWord_sqEichFrame_nuSel_one h j 0 e e' d

/-- ⚠ **The refutation of the transposed family.**  Whenever the selected marking has
`ν'(u_j) = 1` the transposed frame kills the relator for **no** `(f, f', d)`, at any `ν'(v_j)`.
The mechanism is the mirror image: `U` is the letter *that* family moved, and every one of its
slots is dressed by a power of it. -/
theorem not_sqRelWord_sqEichFrameT_nuSel (h : ℕ) (j : Fin h) (s f f' d : ℤ_[2]) :
    sqRelWord (sqEichFrameT h (nuSel h j 1 s) j f f' d) ≠ 1 := by
  intro hone
  have h1 : refHom h j refS refQ commP_refS_refQ
      (sqRelWord (sqEichFrameT h (nuSel h j 1 s) j f f' d)) = 1 := by
    rw [hone, map_one]
  rw [refHom_sqRelWord_sqEichFrameT] at h1
  exact absurd h1 (by decide)

/-- ⚠ **`SqEichRelWord h` is false at every `h ≥ 1`.**  The five-word Eichler ansatz of
`LamFrames` §2 does not discharge the residual. -/
theorem not_sqEichRelWord {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := by
  intro H
  obtain ⟨e, e', d, hrel⟩ := H (nuSel h ⟨0, hh⟩ 0 1) ⟨0, hh⟩ nuSel_sigma nuSel_x0
  exact not_sqRelWord_sqEichFrame_nuSel h ⟨0, hh⟩ e e' d hrel

/-- ⚠ **`SqEichRelWordT h` is false at every `h ≥ 1`.**  The transposed ansatz of `LamFrames` §5
does not discharge the residual either. -/
theorem not_sqEichRelWordT {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWordT h := by
  intro H
  obtain ⟨f, f', d, hrel⟩ := H (nuSel h ⟨0, hh⟩ 1 0) ⟨0, hh⟩ nuSel_sigma nuSel_x0
  exact not_sqRelWord_sqEichFrameT_nuSel h ⟨0, hh⟩ 0 f f' d hrel

/-- ⚠⚠ **`SqEichRelWordMix h` is false at every `h ≥ 1`.**  At the selected marking
`nuSel h j 1 1` — *both* handle rows equal to `1` — neither family kills the relator, so the
disjunction of `LamFrames` §6 fails too.  Two different homomorphisms are needed: the one that
kills the `V`-family sends `v_j` to the pivot's image, the one that kills the transposed family
sends `u_j` there, and no single marking of `D₄` can do both while keeping `[u_j, v_j] ≠ 1`. -/
theorem not_sqEichRelWordMix {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWordMix h := by
  intro H
  rcases H (nuSel h ⟨0, hh⟩ 1 1) ⟨0, hh⟩ nuSel_sigma nuSel_x0 with
    ⟨e, e', d, hrel⟩ | ⟨f, f', d, hrel⟩
  · exact not_sqRelWord_sqEichFrame_nuSel_one h ⟨0, hh⟩ 1 e e' d hrel
  · exact not_sqRelWord_sqEichFrameT_nuSel h ⟨0, hh⟩ 1 f f' d hrel

/-! ## §4 ⭐ The test does **not** transpose

The homomorphism that kills the `V`-family at `nuSel h j 0 1` leaves the transposed family
standing at that very marking.  There `ν'(u_j) = 0`, so `U ↦ refQ ≠ 1` and the `U`-dressings
*survive*; taking the `x₀`-weight `f' = 1` puts `refQ` into the `x₀`-slot, and the core word
`sqWord (sr 0) (sr 1) (r 1)` is `1` — while the handle commutator is `[refQ, refQ^d] = 1` for
every `d`.  So the whole relator dies.

This is the honest content of "the transposed family is what that test cannot see": §3's
refutation of the transposed family needed a **different** homomorphism and a **different**
marking, and the two obstructions are genuinely transverse (which is what forces `nuSel h j 1 1`
for the mix). -/

/-- The `2`-adic exponent `2` is `1 + 1`, so a square is a square. -/
private theorem zpowZtwo_two {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P) (x : P) :
    zpowZtwo hP x 2 = x * x := by
  rw [show (2 : ℤ_[2]) = 1 + 1 by norm_num, zpowZtwo_add, zpowZtwo_one_exp]

/-- ⭐ **The refuting homomorphism of §3 does not kill the transposed family.**  One `D₄`-marking
refutes every `(e, e', d)` of the `V`-family at `nuSel h j 0 1` and simultaneously *satisfies* the
transposed relator identity there, at `(f, f', d) = (0, 1, d)` for every `d`. -/
theorem exists_hom_refuting_sqEichFrame_not_sqEichFrameT (h : ℕ) (j : Fin h) :
    ∃ φ : ContinuousMonoidHom (DSq h : Type) (DihedralGroup 4),
      (∀ e e' d : ℤ_[2], φ (sqRelWord (sqEichFrame h (nuSel h j 0 1) j e e' d)) ≠ 1) ∧
        ∀ d : ℤ_[2], φ (sqRelWord (sqEichFrameT h (nuSel h j 0 1) j 0 1 d)) = 1 := by
  refine ⟨refHom h j refQ refS commP_refQ_refS, fun e e' d hc => ?_, fun d => ?_⟩
  · rw [refHom_sqRelWord_sqEichFrame] at hc
    exact absurd hc (by decide)
  · have hU : refHom h j refQ refS commP_refQ_refS (sqEichU h (nuSel h j 0 1) j) = refQ :=
      refHom_sqEichU_zero _ 1
    have hV : refHom h j refQ refS commP_refQ_refS (sqEichV h (nuSel h j 0 1) j) = 1 :=
      refHom_sqEichV _ 0
    have hpow : ∀ k : ℤ_[2],
        refHom h j refQ refS commP_refQ_refS
            (zpowZtwo (isProP_DSq h) (sqEichU h (nuSel h j 0 1) j) k)
          = zpowZtwo isProP_two_dihedral4 refQ k := by
      intro k
      rw [map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, hU]
    have hzero : refHom h j refQ refS commP_refQ_refS
        (sqEichFrameT h (nuSel h j 0 1) j 0 1 d 0) = refS := by
      rw [sqEichFrameT_zero, map_mul, hpow, SectionThree.zpowZtwo_zero, mul_one, dsqSigma,
        refHom_gen, refMark_zero]
    have hone : refHom h j refQ refS commP_refQ_refS
        (sqEichFrameT h (nuSel h j 0 1) j 0 1 d 1) = refQ := by
      rw [sqEichFrameT_one, map_mul, hpow, zpowZtwo_one_exp, dsqX0, refHom_gen, refMark_one,
        one_mul]
    have htwo : refHom h j refQ refS commP_refQ_refS
        (sqEichFrameT h (nuSel h j 0 1) j 0 1 d 2) = refY := by
      rw [sqEichFrameT_two, map_mul, mul_one, hpow, zpowZtwo_two, dsqX1, refHom_gen, refMark_two]
      norm_num
    have hUslot : refHom h j refQ refS commP_refQ_refS
        (sqEichFrameT h (nuSel h j 0 1) j 0 1 d (sqHandleIdxU j)) = refQ := by
      rw [sqEichFrameT_handleU, hU]
    have hVslot : refHom h j refQ refS commP_refQ_refS
        (sqEichFrameT h (nuSel h j 0 1) j 0 1 d (sqHandleIdxV j))
        = zpowZtwo isProP_two_dihedral4 refQ d := by
      rw [sqEichFrameT_handleV, map_mul, hV, hpow, one_mul]
    have hne : ∀ i : Fin h, i ≠ j →
        commP (refHom h j refQ refS commP_refQ_refS
              (sqEichFrameT h (nuSel h j 0 1) j 0 1 d (sqHandleIdxU i)))
            (refHom h j refQ refS commP_refQ_refS
              (sqEichFrameT h (nuSel h j 0 1) j 0 1 d (sqHandleIdxV i))) = 1 := by
      intro i hi
      rw [sqEichFrameT_handleU_ne hi, sqEichFrameT_handleV_ne hi, refHom_gen, refHom_gen,
        refMark_handleU_ne hi, refMark_handleV_ne hi, commP_one_right]
    rw [map_sqRelWord, sqRelWord, handleWord_eq_single _ _ j hne, hzero, hone, htwo, hUslot,
      hVslot, commP_eq_one_of_commute
        (MarkedCore.commute_zpowZtwo_self isProP_two_dihedral4 refQ d).symm, mul_one]
    decide

/-! ## §5 Stress pins -/

section StressTests

/-- Stress: the refuting marking really is a marking — the relator dies in `D₄`. -/
example (h : ℕ) (j : Fin h) : sqRelWord (refMark h j refQ refS) = 1 :=
  sqRelWord_refMark h j commP_refQ_refS

/-- Stress: and so does the transposed one, at the swapped handle values. -/
example (h : ℕ) (j : Fin h) : sqRelWord (refMark h j refS refQ) = 1 :=
  sqRelWord_refMark h j commP_refS_refQ

/-- Stress: the target is genuinely nonabelian, so the refutation is not an artefact of an
abelian shadow — the two handle values do not commute. -/
example : commP refQ refS ≠ 1 := by decide

/-- Stress: the marking used is **selected**, so it is inside `SqEichRelWord`'s binder. -/
example (h : ℕ) (j : Fin h) :
    nuSel h j 0 1 (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧
      nuSel h j 0 1 (dsqX0 h) = ofAdd (0 : ℤ_[2]) := ⟨nuSel_sigma, nuSel_x0⟩

/-- Stress: the refuted marking is *not* the standard one — its `v_j`-row is `1`, and at the
standard marking the ansatz does work (`sqEichFrame_nuSq_zero`). -/
example (h : ℕ) (j : Fin h) : nuSel h j 0 1 (sqGen h (sqHandleIdxV j)) = ofAdd (1 : ℤ_[2]) :=
  nuSel_handleV

/-- Stress: the frame form of the residual is untouched — it is a characterization over *all*
frames, and this file refutes one family. -/
example (h : ℕ) : SqLamMarkTransitivity h ↔
    ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
          Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
            (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
              ∀ i, nu' (m i) = nuSq h (sqGen h i) := sqLamMarkTransitivity_iff_frames

/-- Stress: `h = 0` is untouched — there is no handle to refute at. -/
example : SqEichRelWord 0 := fun _ j _ _ => absurd j.isLt (by omega)

example : SqEichRelWordT 0 := fun _ j _ _ => absurd j.isLt (by omega)

example : SqEichRelWordMix 0 := fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: the marking that refutes the **mix** is selected, so it too is inside the binder. -/
example (h : ℕ) (j : Fin h) :
    nuSel h j 1 1 (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧
      nuSel h j 1 1 (dsqX0 h) = ofAdd (0 : ℤ_[2]) := ⟨nuSel_sigma, nuSel_x0⟩

/-- Stress: at that marking **both** handle rows are non-zero — which is exactly what makes the
two obstructions available at once, and what a marking refuting only one family cannot have. -/
example (h : ℕ) (j : Fin h) :
    nuSel h j 1 1 (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2]) ∧
      nuSel h j 1 1 (sqGen h (sqHandleIdxV j)) = ofAdd (1 : ℤ_[2]) :=
  ⟨nuSel_handleU, nuSel_handleV⟩

/-- Stress: the residual is **not** refuted — the frame characterization stands, and the widened
ansatz of `LamFrames` §4 (dress by arbitrary `λ`-trivial, `ν'`-trivial elements) is not touched by
any of this, because §3's collapse needs the dressings to lie in the kernel. -/
example (h : ℕ) (H : SqLamMarkTransitivity h) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_lamMarkTransitivity H

end StressTests

/-! ## §6 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable, and no `native_decide`. -/

section AxiomPins

#print axioms isProP_two_dihedral4
#print axioms handleWord_eq_single
#print axioms not_sqRelWord_sqEichFrame_nuSel
#print axioms not_sqRelWord_sqEichFrame_nuSel_one
#print axioms not_sqRelWord_sqEichFrameT_nuSel
#print axioms not_sqEichRelWord
#print axioms not_sqEichRelWordT
#print axioms not_sqEichRelWordMix
#print axioms exists_hom_refuting_sqEichFrame_not_sqEichFrameT

end AxiomPins

end Target

/-! ## §7 ⭐ The collapse lemma: **identify** the two cleared letters

`SqCore/UVFrames.lean` builds `sqEichFrameUV`, which dresses each moved slot by `U^k V^l` rather
than by powers of one letter, and which literally **contains** both families of §3 as slices
(`sqEichFrameUV_eq_sqEichFrame`, `sqEichFrameUV_eq_sqEichFrameT`).  §3's mechanism cannot reach
it: that collapse needs every dressing to lie in `ker φ`, and `U^k V^l` lies in `ker φ` only if
`φ` kills *both* letters, which forces `[φ(u_j), φ(v_j)] = 1` and makes the test vacuous.

⭐ **The mechanism that does reach it is different, and strictly more general: instead of killing
a letter, identify the two.**  Suppose a test homomorphism `φ` sends `U` and `V` to one and the
same **involution** `z`.  Then, at *every* weight tuple,

* each dressing `U^k V^l ↦ z^{k+l} ∈ {1, z}` — the four core dressings collapse to two bits, not
  to nothing, so `z` is free to be `≠ 1`;
* the `x₁`-slot's dressing `U^{2f'}V^{2e'} ↦ z^{2(f'+e')} = 1` outright, since `z² = 1`;
* both handle slots land in the abelian `{1, z}`, so the handle block dies with no hypothesis on
  the two extra parameters `d, d'` at all.

What is left is `sqWord (φσ·z^α) (φx₀·z^β) (φx₁)` over the **two** bits `(α, β)`
(`sqRelWord_sqEichFrameUV_collapse`), so a target in which none of those four values is `1`
refutes the whole family in one stroke.

This **subsumes** §3: killing a letter is the degenerate case `z = 1`, and the condition that
makes the test bite (`[φ(u_j), φ(v_j)] ≠ 1`) is exactly what an involution `z ≠ 1` supplies
without the letter having to die. -/

section Collapse

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- **A `ℤ₂`-power of an involution is the involution or the identity.**  This is the arithmetic
half of the collapse: it is what turns a four-parameter dressing into two bits. -/
theorem zpowZtwo_of_involution {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P) {x : P}
    (hx : x * x = 1) (k : ℤ_[2]) : zpowZtwo hP x k = 1 ∨ zpowZtwo hP x k = x := by
  have heven : ∀ m : ℤ_[2], zpowZtwo hP x (2 * m) = 1 := by
    intro m
    rw [← zpowZtwo_zpowZtwo hP x 2 m, zpowZtwo_two hP x, hx, zpowZtwo_one_base]
  by_cases hk : (2 : ℤ_[2]) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    exact Or.inl (heven m)
  · obtain ⟨m, hm⟩ := two_dvd_sub_one_of_isUnit (isUnit_iff_not_two_dvd.mpr hk)
    refine Or.inr ?_
    have hk2 : k = 2 * m + 1 := by linear_combination hm
    rw [hk2, zpowZtwo_add, heven m, zpowZtwo_one_exp, one_mul]

/-- …and an **even** `ℤ₂`-power of an involution is the identity outright — which is what makes
the `x₁`-slot of a two-letter frame undressed. -/
theorem zpowZtwo_of_involution_two {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) {x : P} (hx : x * x = 1) (k : ℤ_[2]) : zpowZtwo hP x (2 * k) = 1 := by
  rw [← zpowZtwo_zpowZtwo hP x 2 k, zpowZtwo_two hP x, hx, zpowZtwo_one_base]

/-- Two elements of `{1, z}` commute. -/
private theorem commP_of_pair {P : Type*} [Group P] {z a b : P} (ha : a = 1 ∨ a = z)
    (hb : b = 1 ∨ b = z) : commP a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [commP, mul_assoc]

/-- ⭐ **The collapse lemma.**  If a homomorphism identifies the two cleared letters onto an
involution `z`, then the relator of the two-letter frame collapses — at **every** weight tuple —
to the bare core word with each of `σ` and `x₀` dressed by at most one copy of `z`, and with the
`x₁`-slot and the whole handle block undressed.

Stated for an arbitrary pro-2 target and an arbitrary selected marking, so it is the reusable
form of the mechanism: any target in which the four resulting core words all differ from `1`
refutes the family at that marking.  Note there is **no** hypothesis on `d, d'` — the two handle
parameters die with the rest, which is why the refutation reaches the full six-parameter family
and not only the `d = d' = 0` slice. -/
theorem sqRelWord_sqEichFrameUV_collapse {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (φ : ContinuousMonoidHom (DSq h : Type) P) {z : P} (hz : z * z = 1)
    (hU : φ (sqEichU h nu' j) = z) (hV : φ (sqEichV h nu' j) = z)
    (hoth : ∀ j' : Fin h, j' ≠ j →
      commP (φ (sqGen h (sqHandleIdxU j'))) (φ (sqGen h (sqHandleIdxV j'))) = 1)
    (f f' e e' d d' : ℤ_[2]) :
    ∃ a b : P, (a = φ (dsqSigma h) ∨ a = φ (dsqSigma h) * z) ∧
      (b = φ (dsqX0 h) ∨ b = φ (dsqX0 h) * z) ∧
        φ (sqRelWord (sqEichFrameUV h nu' j f f' e e' d d')) = sqWord a b (φ (dsqX1 h)) := by
  have hdU : ∀ k : ℤ_[2], φ (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k) = 1 ∨
      φ (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k) = z := fun k => by
    rw [map_zpowZtwo (isProP_DSq h) hP, hU]
    exact zpowZtwo_of_involution hP hz k
  have hdV : ∀ k : ℤ_[2], φ (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) k) = 1 ∨
      φ (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) k) = z := fun k => by
    rw [map_zpowZtwo (isProP_DSq h) hP, hV]
    exact zpowZtwo_of_involution hP hz k
  have hdU2 : ∀ k : ℤ_[2], φ (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 * k)) = 1 := fun k => by
    rw [map_zpowZtwo (isProP_DSq h) hP, hU]
    exact zpowZtwo_of_involution_two hP hz k
  have hdV2 : ∀ k : ℤ_[2], φ (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 * k)) = 1 := fun k => by
    rw [map_zpowZtwo (isProP_DSq h) hP, hV]
    exact zpowZtwo_of_involution_two hP hz k
  have hslot : ∀ (g : (DSq h : Type)) (k l : ℤ_[2]),
      φ (g * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) l) = φ g ∨
        φ (g * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) l) = φ g * z := by
    intro g k l
    rw [map_mul, map_mul]
    rcases hdU k with hk | hk <;> rcases hdV l with hl | hl <;> rw [hk, hl]
    · exact Or.inl (by rw [mul_one, mul_one])
    · exact Or.inr (by rw [mul_one])
    · exact Or.inr (by rw [mul_one])
    · exact Or.inl (by rw [mul_assoc, hz, mul_one])
  have hmemU : φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU j)) = 1 ∨
      φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU j)) = z := by
    rw [sqEichFrameUV_handleU, map_mul, hU]
    rcases hdV d with hd | hd <;> rw [hd]
    · exact Or.inr (mul_one z)
    · exact Or.inl hz
  have hmemV : φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV j)) = 1 ∨
      φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV j)) = z := by
    rw [sqEichFrameUV_handleV, map_mul, hV]
    rcases hdU d' with hd | hd <;> rw [hd]
    · exact Or.inr (mul_one z)
    · exact Or.inl hz
  have htwo : φ (sqEichFrameUV h nu' j f f' e e' d d' 2) = φ (dsqX1 h) := by
    rw [sqEichFrameUV_two, map_mul, map_mul, hdU2, hdV2, mul_one, mul_one]
  have hne : ∀ i : Fin h, i ≠ j →
      commP (φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU i)))
        (φ (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV i))) = 1 := by
    intro i hi
    rw [sqEichFrameUV_handleU_ne hi, sqEichFrameUV_handleV_ne hi]
    exact hoth i hi
  refine ⟨φ (sqEichFrameUV h nu' j f f' e e' d d' 0),
    φ (sqEichFrameUV h nu' j f f' e e' d d' 1), ?_, ?_, ?_⟩
  · rw [sqEichFrameUV_zero]; exact hslot _ f e
  · rw [sqEichFrameUV_one]; exact hslot _ f' e'
  · rw [map_sqRelWord, sqRelWord, handleWord_eq_single _ _ j hne, commP_of_pair hmemU hmemV,
      htwo, mul_one]

end Collapse

/-! ## §8 ⚠⚠ the two-letter family dies, in `D₈`

Concretely the target is `D₈ = DihedralGroup 8` (order 16, exponent 8 — `D₄` is **too small**:
there the four collapsed core words do include `1`), marked

```text
σ ↦ r 1 ,  x₀ ↦ 1 ,  x₁ ↦ r 2 ,  u_j ↦ sr 0 ,  v_j ↦ sr 2 ,  every other letter ↦ 1
```

— a marking, since `sqWord (r 1) 1 (r 2) = r 4 = [sr 0, sr 2]⁻¹`.  The pivot goes to `r 1` with no
fact about `c₀` used, and at the selected marking `nuSel h j 1 1` **both** cleared letters go to
the involution `sr 1`:  `U = w^{−1}·u_j ↦ (r 1)⁻¹·sr 0 = sr 1` and `V = v_j·w^{−1} ↦ sr 2·(r 1)⁻¹
= sr 1`.  The four surviving core words are `r 4, r 2, r 4, r 6`, none of them `1`. -/

section TargetEight

local instance instTopologicalSpaceD8 : TopologicalSpace (DihedralGroup 8) := ⊥
local instance instDiscreteTopologyD8 : DiscreteTopology (DihedralGroup 8) := ⟨rfl⟩

/-- `D₈` is pro-2: every element has order dividing `8`. -/
theorem isProP_two_dihedral8 : IsProP 2 (DihedralGroup 8) :=
  isProP_of_isPGroup fun g => ⟨3, by revert g; decide⟩

/-- `σ`'s value, and the pivot's: the rotation of order eight. -/
private abbrev uvS : DihedralGroup 8 := DihedralGroup.r 1

/-- `x₁`'s value. -/
private abbrev uvY : DihedralGroup 8 := DihedralGroup.r 2

/-- `u_j`'s value. -/
private abbrev uvA : DihedralGroup 8 := DihedralGroup.sr 0

/-- `v_j`'s value.  `[uvA, uvB] = r 4 = sqWord uvS 1 uvY`, so the relator holds. -/
private abbrev uvB : DihedralGroup 8 := DihedralGroup.sr 2

/-- ⭐ **The common image of the two cleared letters** at `nuSel h j 1 1` — an involution, and
*not* the identity.  That is the whole difference from §3. -/
private abbrev uvZ : DihedralGroup 8 := DihedralGroup.sr 1

variable {h : ℕ} {j : Fin h}

/-- **The `D₈` marking**: `σ ↦ uvS`, `x₀ ↦ 1`, `x₁ ↦ uvY`, `u_j ↦ uvA`, `v_j ↦ uvB`, and `1` on
every other letter. -/
private def uvMark (h : ℕ) (j : Fin h) : Fin (sqRank h) → DihedralGroup 8 :=
  fun i =>
    if (i : ℕ) = 0 then uvS else
    if (i : ℕ) = 2 then uvY else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then uvA else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then uvB else 1

@[simp] private theorem uvMark_zero : uvMark h j 0 = uvS := by
  simp only [uvMark, sqVal_zero]
  norm_num

@[simp] private theorem uvMark_one : uvMark h j 1 = 1 := by
  simp only [uvMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem uvMark_two : uvMark h j 2 = uvY := by
  simp only [uvMark, sqVal_two]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem uvMark_handleU : uvMark h j (sqHandleIdxU j) = uvA := by
  simp only [uvMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem uvMark_handleV : uvMark h j (sqHandleIdxV j) = uvB := by
  simp only [uvMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem uvMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    uvMark h j (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [uvMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem uvMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    uvMark h j (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [uvMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The `D₈` marking kills the relator**: `sqWord (r 1) 1 (r 2) = r 4` and `[sr 0, sr 2] = r 4`
cancel. -/
private theorem sqRelWord_uvMark (h : ℕ) (j : Fin h) : sqRelWord (uvMark h j) = 1 := by
  have hne : ∀ i : Fin h, i ≠ j →
      commP (uvMark h j (sqHandleIdxU i)) (uvMark h j (sqHandleIdxV i)) = 1 := by
    intro i hi
    rw [uvMark_handleU_ne hi, uvMark_handleV_ne hi, commP_one_right]
  rw [sqRelWord, handleWord_eq_single _ _ j hne, uvMark_zero, uvMark_one, uvMark_two,
    uvMark_handleU, uvMark_handleV]
  decide

/-- The refuting hom `D_sq h → D₈`. -/
private noncomputable def uvHom (h : ℕ) (j : Fin h) :
    ContinuousMonoidHom (DSq h : Type) (DihedralGroup 8) :=
  sqLiftHom h isProP_two_dihedral8 (uvMark h j) (sqRelWord_uvMark h j)

@[simp] private theorem uvHom_gen (i : Fin (sqRank h)) : uvHom h j (sqGen h i) = uvMark h j i :=
  sqLiftHom_gen _ _ _ _ i

/-- The pivot goes to `uvS`, with no fact about `c₀` used (`x₀ ↦ 1`). -/
private theorem uvHom_sqPivot : uvHom h j (sqPivot h) = uvS := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_dihedral8, dsqX0, uvHom_gen, uvMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, uvHom_gen, uvMark_zero]

/-- ⭐ **The two cleared letters are identified**, and onto an involution `≠ 1`. -/
private theorem uvHom_sqEichU : uvHom h j (sqEichU h (nuSel h j 1 1) j) = uvZ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral8,
    uvHom_sqPivot, nuSel_handleU, toAdd_ofAdd, zpowZtwo_one_exp, uvHom_gen, uvMark_handleU]
  decide

private theorem uvHom_sqEichV : uvHom h j (sqEichV h (nuSel h j 1 1) j) = uvZ := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral8,
    uvHom_sqPivot, nuSel_handleV, toAdd_ofAdd, zpowZtwo_one_exp, uvHom_gen, uvMark_handleV]
  decide

private theorem uvZ_sq : uvZ * uvZ = 1 := by decide

private theorem uvHom_others : ∀ j' : Fin h, j' ≠ j →
    commP (uvHom h j (sqGen h (sqHandleIdxU j'))) (uvHom h j (sqGen h (sqHandleIdxV j'))) = 1 := by
  intro j' hj'
  rw [uvHom_gen, uvHom_gen, uvMark_handleU_ne hj', uvMark_handleV_ne hj', commP_one_right]

/-- **The four surviving core words**, and none of them is `1`.  This is the whole content of the
refutation: after the collapse the family has exactly two bits left, and it misses on all four. -/
private theorem sqWord_uvSlots_ne_one {a b : DihedralGroup 8} (ha : a = uvS ∨ a = uvS * uvZ)
    (hb : b = 1 ∨ b = 1 * uvZ) : sqWord a b uvY ≠ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **The relator image is never `1`** — the collapse lemma applied at the `D₈` marking. -/
private theorem uvHom_sqRelWord_ne_one (h : ℕ) (j : Fin h) (f f' e e' d d' : ℤ_[2]) :
    uvHom h j (sqRelWord (sqEichFrameUV h (nuSel h j 1 1) j f f' e e' d d')) ≠ 1 := by
  obtain ⟨a, b, ha, hb, hval⟩ := sqRelWord_sqEichFrameUV_collapse isProP_two_dihedral8
    (uvHom h j) uvZ_sq uvHom_sqEichU uvHom_sqEichV uvHom_others f f' e e' d d'
  have hs : uvHom h j (dsqSigma h) = uvS := by rw [dsqSigma, uvHom_gen, uvMark_zero]
  have hx0 : uvHom h j (dsqX0 h) = 1 := by rw [dsqX0, uvHom_gen, uvMark_one]
  have hx1 : uvHom h j (dsqX1 h) = uvY := by rw [dsqX1, uvHom_gen, uvMark_two]
  rw [hs] at ha
  rw [hx0] at hb
  rw [hx1] at hval
  rw [hval]
  exact sqWord_uvSlots_ne_one ha hb

/-- ⚠⚠ **The refutation of the two-letter family.**  At the selected marking `nuSel h j 1 1` the
two-letter Eichler frame kills the relator for **no** weight tuple `(f, f', e, e', d, d')` — not
for the `d = d' = 0` slice, and not for any other. -/
theorem not_sqRelWord_sqEichFrameUV_nuSel (h : ℕ) (j : Fin h) (f f' e e' d d' : ℤ_[2]) :
    sqRelWord (sqEichFrameUV h (nuSel h j 1 1) j f f' e e' d d') ≠ 1 := by
  intro hone
  exact uvHom_sqRelWord_ne_one h j f f' e e' d d' (by rw [hone, map_one])

/-- ⚠⚠ **`SqEichRelWordUV h` is false at every `h ≥ 1`.**  The two-letter widening of
`SqCore/UVFrames.lean` does not discharge the residual either. -/
theorem not_sqEichRelWordUV {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWordUV h := by
  intro H
  obtain ⟨f, f', e, e', hrel⟩ := H (nuSel h ⟨0, hh⟩ 1 1) ⟨0, hh⟩ nuSel_sigma nuSel_x0
  exact not_sqRelWord_sqEichFrameUV_nuSel h ⟨0, hh⟩ f f' e e' 0 0 hrel

/-- ⭐ **One homomorphism now does all three refutations, at one marking.**  §3 needed two
`D₄`-markings and could not touch the mix at `nuSel h j 1 1` with either alone; the `D₈` test
kills the `V`-family, the transposed family and their two-letter widening simultaneously, because
all three are slices of `sqEichFrameUV` and the collapse lemma is blind to which slice. -/
theorem exists_hom_refuting_all_eichler_families (h : ℕ) (j : Fin h) :
    ∃ φ : ContinuousMonoidHom (DSq h : Type) (DihedralGroup 8),
      (∀ e e' d : ℤ_[2], φ (sqRelWord (sqEichFrame h (nuSel h j 1 1) j e e' d)) ≠ 1) ∧
        (∀ f f' d : ℤ_[2], φ (sqRelWord (sqEichFrameT h (nuSel h j 1 1) j f f' d)) ≠ 1) ∧
          ∀ f f' e e' d d' : ℤ_[2],
            φ (sqRelWord (sqEichFrameUV h (nuSel h j 1 1) j f f' e e' d d')) ≠ 1 :=
  ⟨uvHom h j, fun e e' d => by
      rw [← sqEichFrameUV_eq_sqEichFrame]; exact uvHom_sqRelWord_ne_one h j 0 0 e e' d 0,
    fun f f' d => by
      rw [← sqEichFrameUV_eq_sqEichFrameT]; exact uvHom_sqRelWord_ne_one h j f f' 0 0 0 d,
    uvHom_sqRelWord_ne_one h j⟩

/-! ### §8a Stress pins -/

section StressTestsEight

/-- Stress: the `D₈` marking really is a marking. -/
example (h : ℕ) (j : Fin h) : sqRelWord (uvMark h j) = 1 := sqRelWord_uvMark h j

/-- Stress: the target is genuinely nonabelian at the two handle values. -/
example : commP uvA uvB ≠ 1 := by decide

/-- ⭐ Stress: the common image of the two cleared letters is an involution and is **not** the
identity — the exact hypothesis §3's mechanism could never arrange. -/
example : uvZ ≠ 1 ∧ uvZ * uvZ = 1 := ⟨by decide, uvZ_sq⟩

/-- Stress: the marking used is **selected**, so it is inside `SqEichRelWordUV`'s binder. -/
example (h : ℕ) (j : Fin h) :
    nuSel h j 1 1 (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧
      nuSel h j 1 1 (dsqX0 h) = ofAdd (0 : ℤ_[2]) := ⟨nuSel_sigma, nuSel_x0⟩

/-- Stress: `h = 0` is untouched — there is no handle to refute at. -/
example : SqEichRelWordUV 0 := fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: `D₄` is genuinely too small for §7's mechanism — one of *its* four collapsed core
words **is** `1`, which is why §3 had to kill a letter instead of identifying two. -/
example : sqWord (DihedralGroup.sr 0 * DihedralGroup.sr 1) (1 * DihedralGroup.sr 1)
    (DihedralGroup.r 1 : DihedralGroup 4) = 1 := by decide

/-- Stress: the residual is **still** not refuted.  `sqLamMarkTransitivity_iff_frames` quantifies
over *all* five-word frames; §3 and §8 between them kill three explicitly parametrised families,
which remains a set of measure zero among frames.  In particular the widening named in
`LamFrames` §4 — dressing by **arbitrary** `λ`-trivial, `ν'`-trivial elements rather than by words
in `U` and `V` — is out of reach of §7's collapse, which needs the dressings to land in `⟨z⟩`. -/
example (h : ℕ) (H : SqLamMarkTransitivity h) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_lamMarkTransitivity H

end StressTestsEight

/-! ### §8b Axiom pins -/

section AxiomPinsEight

#print axioms zpowZtwo_of_involution
#print axioms zpowZtwo_of_involution_two
#print axioms sqRelWord_sqEichFrameUV_collapse
#print axioms isProP_two_dihedral8
#print axioms not_sqRelWord_sqEichFrameUV_nuSel
#print axioms not_sqEichRelWordUV
#print axioms exists_hom_refuting_all_eichler_families

end AxiomPinsEight

end TargetEight

end SqCore

end Dyadic

end GQ2
