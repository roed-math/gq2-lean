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

end MarkedCore

end Dyadic

end GQ2
