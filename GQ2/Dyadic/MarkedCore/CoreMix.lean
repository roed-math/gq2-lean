/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixInst

@[expose] public section

/-!
# Core↔core mixing at rank four — MC1 §5.3's S3 stratum

**Ticket HM6** of the dyadic campaign (lane MC), implementing
`docs/dyadic/handlemix-core-spike.md`. Where HM1–HM5 built the **handle↔core** mixing element,
this file builds the **core↔core** ones: MC1 §3.4's families `N5`, `N6` on `D_N` and MC1 §2.4's
family `M5` on `D_M`.

Repo conventions as upstream: `x ^ g = g⁻¹xg` (`GQ2.conjP`), `[x,y] = x⁻¹y⁻¹xy` (`GQ2.commP`).

## The construction, in one paragraph

Both rank-four relators have the shape `P = w · [a,b] · z · [c,d]` with `w` a power of `a` and `z`
a power of `c` (`M_α`: `w = a²`, `z = c^{2^α}`; `N_α`: `w = a^{2+2^α}`, `z = 1`), followed by the
handle block. Two Dehn-twist families preserve it:

```
"move b and d"   b ↦ b·γ^k ,  d ↦ d·(γ^k)^{z c⁻¹}      γ = a^b · ((c^d)^{c z⁻¹})
"move b and c"   b ↦ b·δ^k ,  c ↦ c·δ^k                δ = a^b · (d⁻¹)^c     (needs z = 1)
```

Each is exact **for every `k`** — the proof is `group` plus the single fact that `γ^k` (resp.
`δ^k`) commutes with `γ` (resp. `δ`), which is `commute_zpowZtwo_self`. The first family **fixes
the letters `a` and `c`**, i.e. both letters carrying the non-commutator factors `w` and `z`, so it
survives `c^{2^α}`; the second moves `c` and therefore needs `z = 1`, which is why it is available
on `N_α` only. That asymmetry is memo §2.3, and it is the correct reading of HM's §6.5 caveat (ii):
the `c^{2^α}` factor obstructs the *second* shape, and the family `M` actually needs is of the
*first* shape.

## The 2-adic parameter is free

Unlike the handle case (HM memo §5.2, which needed the `θ_w` conjugation and `SL₂(ℤ₂) = E₂(ℤ₂)`),
each family here is a genuine one-parameter group `k ↦ T_k` inserting `γ^k` for a **fixed** word
`γ`. So `k : ℤ_[2]` costs nothing beyond HM1's `zpowZtwo` API: `zpowZtwo_add` gives
`T_k ∘ T_l = T_{k+l}`, `zpowZtwo_zero_exp` gives `T_0 = id`, and the inverse is `T_{-k}` on the
nose. **No new axiom, no B8, no compactness of `Aut`, no Labute input; census unchanged.**

## Scope, stated honestly

`MCoreMixHypothesis`/`NCoreMixHypothesis` (`HandleMixClear.lean:1162,1171`) are phrased through
`DmRealizes`/`DnRealizes`, whose first conjunct is membership in
`Submonoid.closure (dmClearAuts α h)` — the **handle** generating set. The automorphisms below are
new generators and are not in that closure, so discharging those binders *verbatim* additionally
requires widening `dmClearAuts`/`dnClearAuts`, a one-line edit in `HandleMixClear.lean` which this
ticket does not own. What is landed here is the mathematical content: the automorphisms, their
exactness, their inverses, their one-parameter-group laws and their frame action, plus
`hm6DmRealizes`/`hm6DnRealizes` against the **widened** generating set and the monotonicity lemma
that turns the landed handle rows into rows for it. See memo §5 and §6.

## Contents

* **§1** the two twist words and the two relator identities (free-group, `group`-provable);
* **§2** the `zpowZtwo` families, their one-parameter-group laws and inverses;
* **§3** the two-slot marking updates and the `mRelWord`/`nRelWord` transport;
* **§4** the `ContinuousMulEquiv` assembly on `D_M` and `D_N`, with the generator rows;
* **§5** the widened `A(P,h)` and the `hm6*Realizes` statements.
-/

namespace GQ2

namespace Dyadic

namespace MarkedCore

open scoped GQ2

/-! ## §1 The two twist words, and the two relator identities

Both identities hold for an **arbitrary** inserted element `g` commuting with the twist word — no
hypothesis at all on the prefix `w` or the interior factor `z`. That generality is what makes the
2-adic step of §2 free, and it is what lets one lemma serve `M_α` (`z = c^{2^α}`) and `N_α`
(`z = 1`). -/

section TwistWords

variable {G : Type*} [Group G]

/-- **The twisting curve of the "move `b` and `d`" family** (memo §2.2): `γ = a^b · ((c^d)^{c z⁻¹})`,
of abelian class `ā + c̄`. Its two conjugates `γ` and `γ^{z c⁻¹}` are inserted into `b` and `d`;
the letters `a` and `c` — which carry the relator's non-commutator factors `w` and `z` — are
**fixed**, which is the whole point of the construction. -/
def hm6MixBD (a b c d z : G) : G := conjP a b * conjP (conjP c d) (c * z⁻¹)

/-- **The twisting curve of the "move `b` and `c`" family** (memo §2.3): `δ = a^b · (d⁻¹)^c`, of
abelian class `ā − d̄`. This one moves the letter `c`, so it survives only when the relator has no
interior `c`-factor — i.e. on `N_α`, not on `M_α`. -/
def hm6MixBC (a b c d : G) : G := conjP a b * conjP d⁻¹ c

/-- The cancellation that both identities run on: an element commuting with the twisting curve
conjugates it to itself. -/
private theorem conj_eq_of_commute {g x : G} (hg : Commute g x) : g⁻¹ * x * g = x := by
  rw [mul_assoc, ← hg.eq, inv_mul_cancel_left]

/-- **The "move `b` and `d`" relator identity** (memo §2.2). For every `g` commuting with the
twisting curve `γ = hm6MixBD a b c d z`,

`w · [a, b·g] · z · [c, d·g^{z c⁻¹}] = w · [a,b] · z · [c,d]` .

`w` and `z` are arbitrary: the substitution moves only `b` and `d`, and neither occurs in them.
Instantiating `(w, z) = (a², c^{2^α})` gives `M_α`'s family M5, and `(a^{2+2^α}, 1)` gives `N_α`'s
family N5. -/
theorem hm6_relator_mixBD (a b c d w z g : G) (hg : Commute g (hm6MixBD a b c d z)) :
    w * commP a (b * g) * z * commP c (d * conjP g (z * c⁻¹))
      = w * commP a b * z * commP c d := by
  have hL : w * commP a (b * g) * z * commP c (d * conjP g (z * c⁻¹))
      = w * a⁻¹ * (g⁻¹ * hm6MixBD a b c d z * g) * (z * c⁻¹) := by
    simp only [hm6MixBD, commP, conjP]
    group
  rw [hL, conj_eq_of_commute hg]
  simp only [hm6MixBD, commP, conjP]
  group

/-- **The "move `b` and `c`" relator identity** (memo §2.3, HM memo §6.5's element). For every `g`
commuting with `δ = hm6MixBC a b c d`,

`w · [a, b·g] · [c·g, d] = w · [a,b] · [c,d]` .

There is no room for an interior factor between the two commutators — that is exactly the
adjacency the construction needs, and exactly what `c^{2^α}` destroys on the `M` side. -/
theorem hm6_relator_mixBC (a b c d w g : G) (hg : Commute g (hm6MixBC a b c d)) :
    w * commP a (b * g) * commP (c * g) d = w * commP a b * commP c d := by
  have hL : w * commP a (b * g) * commP (c * g) d
      = w * a⁻¹ * (g⁻¹ * hm6MixBC a b c d * g) * d := by
    simp only [hm6MixBC, commP, conjP]
    group
  rw [hL, conj_eq_of_commute hg]
  simp only [hm6MixBC, commP, conjP]
  group

/-! ### Naturality

Both words use only `*`, `⁻¹` and `conjP`, so they push through any monoid-hom-like map — the
`map_handleMixD` pattern. -/

end TwistWords

section TwistNaturality

variable {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]

theorem map_hm6MixBD (φ : F) (a b c d z : G) :
    φ (hm6MixBD a b c d z) = hm6MixBD (φ a) (φ b) (φ c) (φ d) (φ z) := by
  simp only [hm6MixBD, conjP, map_mul, map_inv]

theorem map_hm6MixBC (φ : F) (a b c d : G) :
    φ (hm6MixBC a b c d) = hm6MixBC (φ a) (φ b) (φ c) (φ d) := by
  simp only [hm6MixBC, conjP, map_mul, map_inv]

end TwistNaturality

/-! ### Abelian collapse — the frame action (memo §3.1)

On a commutative group every `conjP` is trivial, so

```
γ ↦ ā + c̄        δ ↦ ā − d̄
```

and the twists read `b̄ ↦ b̄ + k(ā + c̄)`, `d̄ ↦ d̄ + k(ā + c̄)` resp.
`b̄ ↦ b̄ + k(ā − d̄)`, `c̄ ↦ c̄ + k(ā − d̄)`. Both nilpotent parts land in `⟨ā, c̄⟩` resp.
`⟨ā, d̄⟩`, where they vanish — memo §3.1's `N² = 0`. -/

section TwistAbelian

variable {G : Type*} [CommGroup G]

@[simp] theorem hm6MixBD_comm (a b c d z : G) : hm6MixBD a b c d z = a * c := by
  simp [hm6MixBD, conjP, mul_comm, mul_left_comm]

@[simp] theorem hm6MixBC_comm (a b c d : G) : hm6MixBC a b c d = a * d⁻¹ := by
  simp [hm6MixBC, conjP, mul_comm, mul_left_comm]

end TwistAbelian

/-! ### The twisting curve is fixed by its own family

This is what makes each family a **one-parameter group**: the inserted word does not move, so the
`k`-th and `l`-th members compose to the `(k+l)`-th. It is the same `Commute` cancellation as the
relator identities. -/

section TwistFixed

variable {G : Type*} [Group G]

/-- `γ` is fixed by the "move `b` and `d`" substitution (memo §2.4's `T_k(γ) = γ`). Note `z` is
untouched because the substitution fixes the letter `c`. -/
theorem hm6MixBD_mixBD (a b c d z g : G) (hg : Commute g (hm6MixBD a b c d z)) :
    hm6MixBD a (b * g) c (d * conjP g (z * c⁻¹)) z = hm6MixBD a b c d z := by
  have hL : hm6MixBD a (b * g) c (d * conjP g (z * c⁻¹)) z
      = g⁻¹ * hm6MixBD a b c d z * g := by
    simp only [hm6MixBD, conjP]
    group
  rw [hL, conj_eq_of_commute hg]

/-- `δ` is fixed by the "move `b` and `c`" substitution. -/
theorem hm6MixBC_mixBC (a b c d g : G) (hg : Commute g (hm6MixBC a b c d)) :
    hm6MixBC a (b * g) (c * g) d = hm6MixBC a b c d := by
  have hL : hm6MixBC a (b * g) (c * g) d = g⁻¹ * hm6MixBC a b c d * g := by
    simp only [hm6MixBC, conjP]
    group
  rw [hL, conj_eq_of_commute hg]

end TwistFixed

/-! ## §2 The 2-adic families on the two core words

`zpowZtwo hP γ k` commutes with `γ` (HM1's `commute_zpowZtwo_self`), so §1 applies with
`g = zpowZtwo hP γ k` for **every** `k : ℤ_[2]`. Instantiating the prefix and the interior factor
gives the three families of memo §2.4:

| family | core | shape |
|---|---|---|
| `M5` | `M_α` | move `b`, `d`; `z = c^{2^α}` |
| `N5` | `N_α` | move `b`, `d`; `z = 1` |
| `N6` | `N_α` | move `b`, `c` | -/

section CoreFamilies

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

/-- **`M_α`'s core-mixing curve** (MC1 §2.4's family M5): the interior factor is `c^{2^α}`. -/
noncomputable def hm6CurveM (α : ℕ) (a b c d : P) : P := hm6MixBD a b c d (c ^ 2 ^ α)

/-- **`N_α`'s `p`-direction curve** (MC1 §3.4's family N5): the interior factor is trivial. -/
noncomputable def hm6CurveNp (a b c d : P) : P := hm6MixBD a b c d 1

/-- **`N_α`'s `q`-direction curve** (MC1 §3.4's family N6, HM memo §6.5's element). -/
noncomputable def hm6CurveNq (a b c d : P) : P := hm6MixBC a b c d

variable (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k l : ℤ_[2])

/-- **`M5` is exact on `mWord`, for every 2-adic `k`** (memo §2.2). The letters `a` and `c` are
fixed, so both `a²` and `c^{2^α}` survive literally. -/
theorem hm6_mWord_curveM :
    mWord α a (b * zpowZtwo hP (hm6CurveM α a b c d) k) c
        (d * conjP (zpowZtwo hP (hm6CurveM α a b c d) k) (c ^ 2 ^ α * c⁻¹))
      = mWord α a b c d :=
  hm6_relator_mixBD a b c d (a ^ 2) (c ^ 2 ^ α) _ (commute_zpowZtwo_self hP _ k)

/-- **`N5` is exact on `nWord`, for every 2-adic `k`.** -/
theorem hm6_nWord_curveNp :
    nWord α a (b * zpowZtwo hP (hm6CurveNp a b c d) k) c
        (d * conjP (zpowZtwo hP (hm6CurveNp a b c d) k) c⁻¹)
      = nWord α a b c d := by
  have h := hm6_relator_mixBD a b c d (a ^ (2 + 2 ^ α)) 1 _
    (commute_zpowZtwo_self hP (hm6MixBD a b c d 1) k)
  simpa only [nWord, hm6CurveNp, mul_one, one_mul] using h

/-- **`N6` is exact on `nWord`, for every 2-adic `k`** — HM memo §6.5's element, α- and
`h`-uniform, with the parameter now 2-adic. -/
theorem hm6_nWord_curveNq :
    nWord α a (b * zpowZtwo hP (hm6CurveNq a b c d) k) (c * zpowZtwo hP (hm6CurveNq a b c d) k) d
      = nWord α a b c d :=
  hm6_relator_mixBC a b c d (a ^ (2 + 2 ^ α)) _ (commute_zpowZtwo_self hP _ k)

/-! ### The one-parameter-group laws

The curve is fixed by its own family (§1's `hm6Mix*_mix*`), so the substitutions compose by adding
exponents. These are the statements that make `k ↦ T_k` a homomorphism `ℤ_[2] → Aut`, hence make
the 2-adic parameter free (memo §3.4). -/

theorem hm6CurveM_curveM :
    hm6CurveM α a (b * zpowZtwo hP (hm6CurveM α a b c d) k) c
        (d * conjP (zpowZtwo hP (hm6CurveM α a b c d) k) (c ^ 2 ^ α * c⁻¹))
      = hm6CurveM α a b c d :=
  hm6MixBD_mixBD a b c d (c ^ 2 ^ α) _ (commute_zpowZtwo_self hP _ k)

theorem hm6CurveNp_curveNp :
    hm6CurveNp a (b * zpowZtwo hP (hm6CurveNp a b c d) k) c
        (d * conjP (zpowZtwo hP (hm6CurveNp a b c d) k) (1 * c⁻¹))
      = hm6CurveNp a b c d :=
  hm6MixBD_mixBD a b c d 1 _ (commute_zpowZtwo_self hP _ k)

theorem hm6CurveNq_curveNq :
    hm6CurveNq a (b * zpowZtwo hP (hm6CurveNq a b c d) k) (c * zpowZtwo hP (hm6CurveNq a b c d) k) d
      = hm6CurveNq a b c d :=
  hm6MixBC_mixBC a b c d _ (commute_zpowZtwo_self hP _ k)

end CoreFamilies

/-! ## §3 The two-slot marking updates, and the relator transport

HM2's `handleMixUpdate` moves core slot `3` and a handle slot; HM6's families move **two core
slots** — `1, 3` (the letters `b, d`) for the `M5`/`N5` shape and `1, 2` (the letters `b, c`) for
the `N6` shape. The handle slots are never touched, so `handleWord` is invariant and every
statement below is `h`-uniform for free. -/

section MarkUpdate

variable {G : Type*} {h : ℕ}

/-- Distinct `Fin (coreRank h)` values from distinct `ℕ` values. -/
private theorem core_ne {i j : Fin (coreRank h)} (hij : (i : ℕ) ≠ (j : ℕ)) : i ≠ j :=
  fun hc => hij (by rw [hc])

private theorem one_ne_two : (1 : Fin (coreRank h)) ≠ 2 :=
  core_ne (by rw [coreVal_one, coreVal_two]; omega)

private theorem one_ne_three : (1 : Fin (coreRank h)) ≠ 3 :=
  core_ne (by rw [coreVal_one, coreVal_three]; omega)

private theorem zero_ne_one : (0 : Fin (coreRank h)) ≠ 1 :=
  core_ne (by rw [coreVal_zero, coreVal_one]; omega)

private theorem zero_ne_two : (0 : Fin (coreRank h)) ≠ 2 :=
  core_ne (by rw [coreVal_zero, coreVal_two]; omega)

private theorem zero_ne_three : (0 : Fin (coreRank h)) ≠ 3 :=
  core_ne (by rw [coreVal_zero, coreVal_three]; omega)

private theorem two_ne_three : (2 : Fin (coreRank h)) ≠ 3 :=
  core_ne (by rw [coreVal_two, coreVal_three]; omega)

private theorem handleU_ne_one (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 1 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_one]; omega)

private theorem handleU_ne_two (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 2 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega)

private theorem handleU_ne_three (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 3 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_three]; omega)

private theorem handleV_ne_one (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 1 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_one]; omega)

private theorem handleV_ne_two (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 2 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_two]; omega)

private theorem handleV_ne_three (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 3 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_three]; omega)

/-- **The `b,d` two-slot update**: replace core letters `1` and `3`, leave the other
`coreRank h − 2` alone. -/
def hm6UpdateBD (m : Fin (coreRank h) → G) (wb wd : G) : Fin (coreRank h) → G :=
  Function.update (Function.update m 1 wb) 3 wd

/-- **The `b,c` two-slot update**: replace core letters `1` and `2`. -/
def hm6UpdateBC (m : Fin (coreRank h) → G) (wb wc : G) : Fin (coreRank h) → G :=
  Function.update (Function.update m 1 wb) 2 wc

variable (m : Fin (coreRank h) → G) (wb wx : G)

@[simp] theorem hm6UpdateBD_zero : hm6UpdateBD m wb wx 0 = m 0 := by
  rw [hm6UpdateBD, Function.update_of_ne zero_ne_three, Function.update_of_ne zero_ne_one]

@[simp] theorem hm6UpdateBD_one : hm6UpdateBD m wb wx 1 = wb := by
  rw [hm6UpdateBD, Function.update_of_ne one_ne_three, Function.update_self]

@[simp] theorem hm6UpdateBD_two : hm6UpdateBD m wb wx 2 = m 2 := by
  rw [hm6UpdateBD, Function.update_of_ne two_ne_three, Function.update_of_ne (Ne.symm one_ne_two)]

@[simp] theorem hm6UpdateBD_three : hm6UpdateBD m wb wx 3 = wx := by
  rw [hm6UpdateBD, Function.update_self]

@[simp] theorem hm6UpdateBD_handleU (j : Fin h) :
    hm6UpdateBD m wb wx (handleIdxU j) = m (handleIdxU j) := by
  rw [hm6UpdateBD, Function.update_of_ne (handleU_ne_three j),
    Function.update_of_ne (handleU_ne_one j)]

@[simp] theorem hm6UpdateBD_handleV (j : Fin h) :
    hm6UpdateBD m wb wx (handleIdxV j) = m (handleIdxV j) := by
  rw [hm6UpdateBD, Function.update_of_ne (handleV_ne_three j),
    Function.update_of_ne (handleV_ne_one j)]

@[simp] theorem hm6UpdateBC_zero : hm6UpdateBC m wb wx 0 = m 0 := by
  rw [hm6UpdateBC, Function.update_of_ne zero_ne_two, Function.update_of_ne zero_ne_one]

@[simp] theorem hm6UpdateBC_one : hm6UpdateBC m wb wx 1 = wb := by
  rw [hm6UpdateBC, Function.update_of_ne one_ne_two, Function.update_self]

@[simp] theorem hm6UpdateBC_two : hm6UpdateBC m wb wx 2 = wx := by
  rw [hm6UpdateBC, Function.update_self]

@[simp] theorem hm6UpdateBC_three : hm6UpdateBC m wb wx 3 = m 3 := by
  rw [hm6UpdateBC, Function.update_of_ne (Ne.symm two_ne_three),
    Function.update_of_ne (Ne.symm one_ne_three)]

@[simp] theorem hm6UpdateBC_handleU (j : Fin h) :
    hm6UpdateBC m wb wx (handleIdxU j) = m (handleIdxU j) := by
  rw [hm6UpdateBC, Function.update_of_ne (handleU_ne_two j),
    Function.update_of_ne (handleU_ne_one j)]

@[simp] theorem hm6UpdateBC_handleV (j : Fin h) :
    hm6UpdateBC m wb wx (handleIdxV j) = m (handleIdxV j) := by
  rw [hm6UpdateBC, Function.update_of_ne (handleV_ne_two j),
    Function.update_of_ne (handleV_ne_one j)]

end MarkUpdate

section MarkUpdateNaturality

variable {F G H : Type*} [FunLike F G H] {h : ℕ}

theorem map_hm6UpdateBD (φ : F) (m : Fin (coreRank h) → G) (wb wd : G)
    (i : Fin (coreRank h)) :
    φ (hm6UpdateBD m wb wd i) = hm6UpdateBD (fun i => φ (m i)) (φ wb) (φ wd) i := by
  simp only [hm6UpdateBD, Function.apply_update fun _ => φ]

theorem map_hm6UpdateBC (φ : F) (m : Fin (coreRank h) → G) (wb wc : G)
    (i : Fin (coreRank h)) :
    φ (hm6UpdateBC m wb wc i) = hm6UpdateBC (fun i => φ (m i)) (φ wb) (φ wc) i := by
  simp only [hm6UpdateBC, Function.apply_update fun _ => φ]

end MarkUpdateNaturality

/-! ### The three markings, and `Φ(P) = P` on the full relator -/

section CoreMarks

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- **MC1 §2.4's family `M5` as a marking substitution**, at 2-adic parameter `k`. -/
noncomputable def hm6MarkM (hP : IsProP 2 P) (α : ℕ) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  hm6UpdateBD m (m 1 * zpowZtwo hP (hm6CurveM α (m 0) (m 1) (m 2) (m 3)) k)
    (m 3 * conjP (zpowZtwo hP (hm6CurveM α (m 0) (m 1) (m 2) (m 3)) k) (m 2 ^ 2 ^ α * (m 2)⁻¹))

/-- **MC1 §3.4's family `N5` (the `p`-direction) as a marking substitution.** -/
noncomputable def hm6MarkNp (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  hm6UpdateBD m (m 1 * zpowZtwo hP (hm6CurveNp (m 0) (m 1) (m 2) (m 3)) k)
    (m 3 * conjP (zpowZtwo hP (hm6CurveNp (m 0) (m 1) (m 2) (m 3)) k) ((m 2)⁻¹))

/-- **MC1 §3.4's family `N6` (the `q`-direction) as a marking substitution** — HM memo §6.5's
element at 2-adic parameter. -/
noncomputable def hm6MarkNq (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  hm6UpdateBC m (m 1 * zpowZtwo hP (hm6CurveNq (m 0) (m 1) (m 2) (m 3)) k)
    (m 2 * zpowZtwo hP (hm6CurveNq (m 0) (m 1) (m 2) (m 3)) k)

variable (hP : IsProP 2 P) (α : ℕ) (k : ℤ_[2]) (m : Fin (coreRank h) → P)

/-- **`Φ^{M5}_k(P_M) = P_M`** on the full relator, handles included. -/
theorem mRelWord_hm6MarkM : mRelWord α (hm6MarkM hP α k m) = mRelWord α m := by
  rw [mRelWord, mRelWord, hm6MarkM]
  simp only [hm6UpdateBD_zero, hm6UpdateBD_one, hm6UpdateBD_two, hm6UpdateBD_three,
    hm6UpdateBD_handleU, hm6UpdateBD_handleV]
  rw [hm6_mWord_curveM hP α (m 0) (m 1) (m 2) (m 3) k]

/-- **`Φ^{N5}_k(P_N) = P_N`** on the full relator. -/
theorem nRelWord_hm6MarkNp : nRelWord α (hm6MarkNp hP k m) = nRelWord α m := by
  rw [nRelWord, nRelWord, hm6MarkNp]
  simp only [hm6UpdateBD_zero, hm6UpdateBD_one, hm6UpdateBD_two, hm6UpdateBD_three,
    hm6UpdateBD_handleU, hm6UpdateBD_handleV]
  rw [hm6_nWord_curveNp hP α (m 0) (m 1) (m 2) (m 3) k]

/-- **`Φ^{N6}_k(P_N) = P_N`** on the full relator. -/
theorem nRelWord_hm6MarkNq : nRelWord α (hm6MarkNq hP k m) = nRelWord α m := by
  rw [nRelWord, nRelWord, hm6MarkNq]
  simp only [hm6UpdateBC_zero, hm6UpdateBC_one, hm6UpdateBC_two, hm6UpdateBC_three,
    hm6UpdateBC_handleU, hm6UpdateBC_handleV]
  rw [hm6_nWord_curveNq hP α (m 0) (m 1) (m 2) (m 3) k]

end CoreMarks

/-! ### The inverse substitution is the `−k` member

Each family is a one-parameter group (memo §3.4), so the inverse of `T_k` is `T_{−k}` on the nose,
in the free group and before descending to the presented core — the property HM2's assembly
pattern consumes. -/

section CoreMarksInverse

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- `x^k · x^{−k} = 1`, from `zpowZtwo_add` and `zpowZtwo_zero_exp`. -/
theorem zpowZtwo_mul_neg (hP : IsProP 2 P) (x : P) (k : ℤ_[2]) :
    zpowZtwo hP x k * zpowZtwo hP x (-k) = 1 := by
  rw [← zpowZtwo_add, add_neg_cancel, zpowZtwo_zero_exp]

/-- `conjP` is multiplicative in its first argument. -/
theorem conjP_mul_conjP {G : Type*} [Group G] (x y g : G) :
    conjP x g * conjP y g = conjP (x * y) g := by
  simp only [conjP]
  group

variable (hP : IsProP 2 P) (α : ℕ) (k : ℤ_[2]) (m : Fin (coreRank h) → P)

private theorem hm6UpdateBD_hm6UpdateBD {G : Type*} (n : Fin (coreRank h) → G)
    (wb wd wb' wd' : G) :
    hm6UpdateBD (hm6UpdateBD n wb wd) wb' wd' = hm6UpdateBD n wb' wd' := by
  simp only [hm6UpdateBD]
  rw [Function.update_comm (Ne.symm one_ne_three), Function.update_idem, Function.update_idem]

private theorem hm6UpdateBC_hm6UpdateBC {G : Type*} (n : Fin (coreRank h) → G)
    (wb wc wb' wc' : G) :
    hm6UpdateBC (hm6UpdateBC n wb wc) wb' wc' = hm6UpdateBC n wb' wc' := by
  simp only [hm6UpdateBC]
  rw [Function.update_comm (Ne.symm one_ne_two), Function.update_idem, Function.update_idem]

private theorem hm6UpdateBD_self {G : Type*} (n : Fin (coreRank h) → G) :
    hm6UpdateBD n (n 1) (n 3) = n := by
  simp only [hm6UpdateBD, Function.update_eq_self]

private theorem hm6UpdateBC_self {G : Type*} (n : Fin (coreRank h) → G) :
    hm6UpdateBC n (n 1) (n 2) = n := by
  simp only [hm6UpdateBC, Function.update_eq_self]

/-- **`Φ^{M5}_{−k} ∘ Φ^{M5}_k = id`** on markings. -/
theorem hm6MarkM_neg : hm6MarkM hP α (-k) (hm6MarkM hP α k m) = m := by
  simp only [hm6MarkM, hm6UpdateBD_zero, hm6UpdateBD_one, hm6UpdateBD_two, hm6UpdateBD_three]
  rw [hm6CurveM_curveM hP α (m 0) (m 1) (m 2) (m 3) k, hm6UpdateBD_hm6UpdateBD,
    mul_assoc (m 1), zpowZtwo_mul_neg, mul_one, mul_assoc (m 3), conjP_mul_conjP,
    zpowZtwo_mul_neg]
  simp only [conjP, inv_mul_cancel, mul_one, hm6UpdateBD_self]

/-- **`Φ^{M5}_k ∘ Φ^{M5}_{−k} = id`** — the other composite. -/
theorem hm6MarkM_neg' : hm6MarkM hP α k (hm6MarkM hP α (-k) m) = m := by
  simpa using hm6MarkM_neg hP α (-k) m

/-- **`Φ^{N5}_{−k} ∘ Φ^{N5}_k = id`** on markings. -/
theorem hm6MarkNp_neg : hm6MarkNp hP (-k) (hm6MarkNp hP k m) = m := by
  simp only [hm6MarkNp, hm6UpdateBD_zero, hm6UpdateBD_one, hm6UpdateBD_two, hm6UpdateBD_three]
  have hc := hm6CurveNp_curveNp hP (m 0) (m 1) (m 2) (m 3) k
  rw [one_mul] at hc
  rw [hc, hm6UpdateBD_hm6UpdateBD, mul_assoc (m 1), zpowZtwo_mul_neg, mul_one,
    mul_assoc (m 3), conjP_mul_conjP, zpowZtwo_mul_neg]
  simp only [conjP, inv_mul_cancel, mul_one, hm6UpdateBD_self]

theorem hm6MarkNp_neg' : hm6MarkNp hP k (hm6MarkNp hP (-k) m) = m := by
  simpa using hm6MarkNp_neg hP (-k) m

/-- **`Φ^{N6}_{−k} ∘ Φ^{N6}_k = id`** on markings. -/
theorem hm6MarkNq_neg : hm6MarkNq hP (-k) (hm6MarkNq hP k m) = m := by
  simp only [hm6MarkNq, hm6UpdateBC_zero, hm6UpdateBC_one, hm6UpdateBC_two, hm6UpdateBC_three]
  rw [hm6CurveNq_curveNq hP (m 0) (m 1) (m 2) (m 3) k, hm6UpdateBC_hm6UpdateBC,
    mul_assoc (m 1), zpowZtwo_mul_neg, mul_one, mul_assoc (m 2), zpowZtwo_mul_neg, mul_one,
    hm6UpdateBC_self]

theorem hm6MarkNq_neg' : hm6MarkNq hP k (hm6MarkNq hP (-k) m) = m := by
  simpa using hm6MarkNq_neg hP (-k) m

end CoreMarksInverse

section CoreMarksNaturality

variable {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] {h : ℕ}

variable (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)

theorem map_hm6MarkM (α : ℕ) (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (hm6MarkM hP α k m i) = hm6MarkM hQ α k (fun i => f (m i)) i := by
  simp only [hm6MarkM, map_hm6UpdateBD f, map_mul, map_zpowZtwo hP hQ, hm6CurveM, map_hm6MixBD,
    conjP, map_inv, map_pow]

theorem map_hm6MarkNp (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (hm6MarkNp hP k m i) = hm6MarkNp hQ k (fun i => f (m i)) i := by
  simp only [hm6MarkNp, map_hm6UpdateBD f, map_mul, map_zpowZtwo hP hQ, hm6CurveNp, map_hm6MixBD,
    conjP, map_inv, map_one]

theorem map_hm6MarkNq (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (hm6MarkNq hP k m i) = hm6MarkNq hQ k (fun i => f (m i)) i := by
  simp only [hm6MarkNq, map_hm6UpdateBC f, map_mul, map_zpowZtwo hP hQ, hm6CurveNq,
    map_hm6MixBC]

end CoreMarksNaturality

/-! ## §4 The assembly into `ContinuousMulEquiv` (the `thetaEquiv` pattern)

Exactly HM2's §3: a lift out of a relator-respecting marking, the `−k` member as inverse, the two
composites by hom-extensionality, and `continuousMulEquivOfBijective`. Continuity is free because
the inverse exists **in the free group**, before descending (memo §3.5). -/

section Assembly

variable (α h : ℕ) (k : ℤ_[2])

/-- **MC1 §2.4's family `M5` on `D_{M,α,h}`**, at 2-adic parameter `k`. -/
noncomputable def dmCoreMixHom : ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (hm6MarkM (isProP_DM α h) α k (dmGen α h))
    (by rw [mRelWord_hm6MarkM]; exact dm_relation α h)

/-- **MC1 §3.4's family `N5` (the `p`-direction) on `D_{N,α,h}`.** -/
noncomputable def dnCoreMixPHom : ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (hm6MarkNp (isProP_DN α h) k (dnGen α h))
    (by rw [nRelWord_hm6MarkNp]; exact dn_relation α h)

/-- **MC1 §3.4's family `N6` (the `q`-direction) on `D_{N,α,h}`** — HM memo §6.5's element. -/
noncomputable def dnCoreMixQHom : ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (hm6MarkNq (isProP_DN α h) k (dnGen α h))
    (by rw [nRelWord_hm6MarkNq]; exact dn_relation α h)

@[simp] theorem dmCoreMixHom_gen (i : Fin (coreRank h)) :
    dmCoreMixHom α h k (dmGen α h i) = hm6MarkM (isProP_DM α h) α k (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnCoreMixPHom_gen (i : Fin (coreRank h)) :
    dnCoreMixPHom α h k (dnGen α h i) = hm6MarkNp (isProP_DN α h) k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnCoreMixQHom_gen (i : Fin (coreRank h)) :
    dnCoreMixQHom α h k (dnGen α h i) = hm6MarkNq (isProP_DN α h) k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

theorem dmCoreMixHom_neg (x : (DM α h : Type)) :
    dmCoreMixHom α h (-k) (dmCoreMixHom α h k x) = x := by
  have hgen : (fun i => dmCoreMixHom α h (-k) (dmGen α h i))
      = hm6MarkM (isProP_DM α h) α (-k) (dmGen α h) :=
    funext fun i => dmCoreMixHom_gen α h (-k) i
  have hext : (dmCoreMixHom α h (-k)).comp (dmCoreMixHom α h k)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DM α h : Type) (DM α h : Type)) := by
    refine dm_hom_ext _ _ fun i => ?_
    show dmCoreMixHom α h (-k) (dmCoreMixHom α h k (dmGen α h i)) = dmGen α h i
    rw [dmCoreMixHom_gen, map_hm6MarkM _ (isProP_DM α h), hgen, hm6MarkM_neg']
  exact DFunLike.congr_fun hext x

theorem dnCoreMixPHom_neg (x : (DN α h : Type)) :
    dnCoreMixPHom α h (-k) (dnCoreMixPHom α h k x) = x := by
  have hgen : (fun i => dnCoreMixPHom α h (-k) (dnGen α h i))
      = hm6MarkNp (isProP_DN α h) (-k) (dnGen α h) :=
    funext fun i => dnCoreMixPHom_gen α h (-k) i
  have hext : (dnCoreMixPHom α h (-k)).comp (dnCoreMixPHom α h k)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DN α h : Type) (DN α h : Type)) := by
    refine dn_hom_ext _ _ fun i => ?_
    show dnCoreMixPHom α h (-k) (dnCoreMixPHom α h k (dnGen α h i)) = dnGen α h i
    rw [dnCoreMixPHom_gen, map_hm6MarkNp _ (isProP_DN α h), hgen, hm6MarkNp_neg']
  exact DFunLike.congr_fun hext x

theorem dnCoreMixQHom_neg (x : (DN α h : Type)) :
    dnCoreMixQHom α h (-k) (dnCoreMixQHom α h k x) = x := by
  have hgen : (fun i => dnCoreMixQHom α h (-k) (dnGen α h i))
      = hm6MarkNq (isProP_DN α h) (-k) (dnGen α h) :=
    funext fun i => dnCoreMixQHom_gen α h (-k) i
  have hext : (dnCoreMixQHom α h (-k)).comp (dnCoreMixQHom α h k)
      = (⟨MonoidHom.id _, continuous_id⟩ :
          ContinuousMonoidHom (DN α h : Type) (DN α h : Type)) := by
    refine dn_hom_ext _ _ fun i => ?_
    show dnCoreMixQHom α h (-k) (dnCoreMixQHom α h k (dnGen α h i)) = dnGen α h i
    rw [dnCoreMixQHom_gen, map_hm6MarkNq _ (isProP_DN α h), hgen, hm6MarkNq_neg']
  exact DFunLike.congr_fun hext x

/-- **The `M5` core-mixing automorphism of `D_{M,α,h}`** (memo §5.2): a *continuous* automorphism
realizing MC1 §2.4's family M5 at every 2-adic `B_c`, fixing the relator on the nose, with no new
axiom. This is the generator MC1 §5.3 says the `M`-side marked correction needs. -/
noncomputable def dmCoreMixEquiv : ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  continuousMulEquivOfBijective (dmCoreMixHom α h k)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dmCoreMixHom α h (-k), dmCoreMixHom_neg α h k,
        fun x => by simpa using dmCoreMixHom_neg α h (-k) x⟩)

/-- **The `N5` core-mixing automorphism of `D_{N,α,h}`** (the `p`-direction). -/
noncomputable def dnCoreMixPEquiv : ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  continuousMulEquivOfBijective (dnCoreMixPHom α h k)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dnCoreMixPHom α h (-k), dnCoreMixPHom_neg α h k,
        fun x => by simpa using dnCoreMixPHom_neg α h (-k) x⟩)

/-- **The `N6` core-mixing automorphism of `D_{N,α,h}`** (the `q`-direction) — HM memo §6.5's
element, now a theorem-backed automorphism at every 2-adic `q`. -/
noncomputable def dnCoreMixQEquiv : ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  continuousMulEquivOfBijective (dnCoreMixQHom α h k)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dnCoreMixQHom α h (-k), dnCoreMixQHom_neg α h k,
        fun x => by simpa using dnCoreMixQHom_neg α h (-k) x⟩)

@[simp] theorem dmCoreMixEquiv_gen (i : Fin (coreRank h)) :
    dmCoreMixEquiv α h k (dmGen α h i) = hm6MarkM (isProP_DM α h) α k (dmGen α h) i :=
  dmCoreMixHom_gen α h k i

@[simp] theorem dnCoreMixPEquiv_gen (i : Fin (coreRank h)) :
    dnCoreMixPEquiv α h k (dnGen α h i) = hm6MarkNp (isProP_DN α h) k (dnGen α h) i :=
  dnCoreMixPHom_gen α h k i

@[simp] theorem dnCoreMixQEquiv_gen (i : Fin (coreRank h)) :
    dnCoreMixQEquiv α h k (dnGen α h i) = hm6MarkNq (isProP_DN α h) k (dnGen α h) i :=
  dnCoreMixQHom_gen α h k i

/-! ### The generator rows: which letters move

The two fixed letters are the ones carrying the relator's non-commutator factors — `A` and `C₀`
for `M_α`, `x₀` and (for the `p`-direction) `σ`. That is the content of memo §2.2. -/

@[simp] theorem dmCoreMixEquiv_dmA : dmCoreMixEquiv α h k (dmA α h) = dmA α h := by
  rw [dmA, dmCoreMixEquiv_gen, hm6MarkM, hm6UpdateBD_zero]

@[simp] theorem dmCoreMixEquiv_dmC : dmCoreMixEquiv α h k (dmC α h) = dmC α h := by
  rw [dmC, dmCoreMixEquiv_gen, hm6MarkM, hm6UpdateBD_two]

@[simp] theorem dmCoreMixEquiv_handleU (j : Fin h) :
    dmCoreMixEquiv α h k (dmGen α h (handleIdxU j)) = dmGen α h (handleIdxU j) := by
  rw [dmCoreMixEquiv_gen, hm6MarkM, hm6UpdateBD_handleU]

@[simp] theorem dmCoreMixEquiv_handleV (j : Fin h) :
    dmCoreMixEquiv α h k (dmGen α h (handleIdxV j)) = dmGen α h (handleIdxV j) := by
  rw [dmCoreMixEquiv_gen, hm6MarkM, hm6UpdateBD_handleV]

@[simp] theorem dnCoreMixPEquiv_dnX0 : dnCoreMixPEquiv α h k (dnX0 α h) = dnX0 α h := by
  rw [dnX0, dnCoreMixPEquiv_gen, hm6MarkNp, hm6UpdateBD_zero]

@[simp] theorem dnCoreMixPEquiv_dnSigma :
    dnCoreMixPEquiv α h k (dnSigma α h) = dnSigma α h := by
  rw [dnSigma, dnCoreMixPEquiv_gen, hm6MarkNp, hm6UpdateBD_two]

@[simp] theorem dnCoreMixQEquiv_dnX0 : dnCoreMixQEquiv α h k (dnX0 α h) = dnX0 α h := by
  rw [dnX0, dnCoreMixQEquiv_gen, hm6MarkNq, hm6UpdateBC_zero]

@[simp] theorem dnCoreMixQEquiv_dnX2 : dnCoreMixQEquiv α h k (dnX2 α h) = dnX2 α h := by
  rw [dnX2, dnCoreMixQEquiv_gen, hm6MarkNq, hm6UpdateBC_three]

@[simp] theorem dnCoreMixQEquiv_handleU (j : Fin h) :
    dnCoreMixQEquiv α h k (dnGen α h (handleIdxU j)) = dnGen α h (handleIdxU j) := by
  rw [dnCoreMixQEquiv_gen, hm6MarkNq, hm6UpdateBC_handleU]

@[simp] theorem dnCoreMixQEquiv_handleV (j : Fin h) :
    dnCoreMixQEquiv α h k (dnGen α h (handleIdxV j)) = dnGen α h (handleIdxV j) := by
  rw [dnCoreMixQEquiv_gen, hm6MarkNq, hm6UpdateBC_handleV]

end Assembly

end MarkedCore

end Dyadic

end GQ2
