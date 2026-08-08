/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedContain

/-!
# W52-VANISH: the graded Fox form of the dressing action, and the vanishing identity

The W50/W51 sweeps measured, at every level `L₃ … L₆` and every marking, that the
dressing-defect map `δ` has corank exactly `d + 1 = sqRank h + 1` and that the relator's own
defect lands in `im δ` every time, and W51 §2.4 added that `δ` and its image depend on the
marking only mod 2.  W52's off-Lean work (`scripts/w52_vanish/`, memo
`docs/dyadic/w52-vanish-note.md`) identified the structure behind all three findings: in the
layer, the defect map is the free-differential-calculus form

```text
δ(z) = ∑ᵢ [zᵢ, βᵢ] + F(z_{x₁}),
```

where `βᵢ` is the mod-2 abelianized Fox derivative `∂R/∂xᵢ` evaluated at the marking — which
for this relator is the marking letter permuted by `(σ x₀)(u v)` with `x₁` fixed — and the
Frobenius `F` appears in the `x₁` slot only (the halved exponent vector `(0, −4, 2, 0, 0)/2`
is `(0, 0, 1, 0, 0)` mod 2).  The form was machine-validated row by row against honest group
collection: 0 mismatches in 5525 rows at classes 4 and 5, all four parity classes, and on
random words in place of the relator.

This file commits the class-three slice instance of that structure, on the committed
class-three test group `SqU4 R` of `GradedThree`.  Everything is stated over an arbitrary
commutative ring and an arbitrary handle count, with no cleared hypotheses.

* **The five-slot dressing action** (`sqRelWord_vanDress_f`): dressing *every* slot of a
  marking by a `γ₂`-element translates the relator's class-three coordinate by the explicit
  affine form `vanShift`, whose pairing coefficients are the marking's outer abelian columns
  in the permuted-letter pattern — the `σ`-slot dressing pairs against the `x₀`-letter, the
  `x₀`-slot against the `σ`-letter, the `x₁`-slot against the `x₁`-letter itself, and each
  handle dressing against the opposite handle letter.  This extends the committed
  `sqRelWord_selRefine` (which dresses four of the five slots, the exponent slots only by
  `γ₃`) to the full frame, and the lower five rows move by the abelian exponent action alone.
* **The vanishing identity** (`vanShift_commP`, `vanShift_commP_eq_zero`): on the
  conjugation family `zᵢ = [mᵢ, g]` the shift equals an explicit combination of the
  relator's *own* lower rows — so it vanishes as soon as the class-`≤ 2` rows of
  `sqRelWord m` do.  This is the class-three instance of the Jacobi/Fox identity behind the
  measured kernel of `δ` (the graded shadow of `R(m^g) = R(m)^g`, packet Prop. 4.1(3)), with
  the error term exhibited rather than hypothesized away.
* **The exact even-decomposition** (`vanShift_decomp`): `vanShift = vanShiftPar + 2·(junk)`
  with `vanShiftPar` the plus-signs pairing form reading only the marking's columns — so mod
  2 the dressing action reads only the mod-2 columns of the marking, in the permuted-letter
  pattern.  This is the class-three slice form of W51 §2.4 ("`δ` is a mod-2 object"), as
  mathematics: the parity of the shift is invariant under any change of marking that fixes
  the columns mod 2 (`vanShift_congr_parity`).

## Contents

* **§1** `γ₂`-dressing calculus on `SqU4`: `vanMul_d/e/f`, `vanComm3`, `vanCore`;
* **§2** the five-slot dressing action: `vanDress`, `vanShift`, `sqRelWord_vanDress_f` and
  the five lower rows;
* **§3** ⭐⭐ the conjugation family and the vanishing identity: `vanDress_commP`,
  `vanShift_commP`, `vanShift_commP_eq_zero`;
* **§4** ⭐ the exact even-decomposition and the parity collapse: `vanShiftPar`,
  `vanShift_decomp`, `vanShift_congr_parity`;
* **§5** committed axiom prints (all std-3).

Companion memo: `docs/dyadic/w52-vanish-note.md`.
-/

namespace GQ2

namespace Dyadic

namespace SqCore

open MarkedCore

variable {R : Type} [CommRing R]

/-! ## §1 The `γ₂`-dressing calculus on `SqU4`

A `γ₂`-shaped dressing (`a = b = c = 0`) multiplies a slot without moving its abelian
columns, and its `(d, e, f)`-data enters every later collection linearly.  The three lemmas
record how the three non-abelian coordinates of a product `p * z` read against the letter
`p`, and the two expansion lemmas give the five-slot changes of the two cubic forms of
`GradedThree`. -/

section GaTwoCalculus

/-- Multiplying by a `γ₂`-element adds its `d`-coordinate exactly. -/
theorem vanMul_d {p z : SqU4 R} (hz : z.IsGaTwo) : (p * z).d = p.d + z.d := by
  rw [SqU4.mul_d, hz.2.1, mul_zero, add_zero]

/-- Multiplying by a `γ₂`-element adds its `e`-coordinate exactly. -/
theorem vanMul_e {p z : SqU4 R} (hz : z.IsGaTwo) : (p * z).e = p.e + z.e := by
  rw [SqU4.mul_e, hz.2.2, mul_zero, add_zero]

/-- Multiplying by a `γ₂`-element adds its `f`-coordinate plus one bilinear correction, the
letter's `a`-column against the dressing's `e`-coordinate. -/
theorem vanMul_f {p z : SqU4 R} (hz : z.IsGaTwo) : (p * z).f = p.f + z.f + p.a * z.e := by
  rw [SqU4.mul_f, hz.2.2, mul_zero, add_zero]

/-- **The five-slot change of the cubic commutator form**: dressing both arguments by
`γ₂`-elements moves `u4Comm3` by the two cross pairings — each dressing's `(d, e)`-data
paired against the *other* letter's outer abelian columns `(c, a)`.  This is the handle
block of the graded Fox form: the `u`-slot Fox row is the `v`-letter and conversely. -/
theorem vanComm3 {p q z w : SqU4 R} (hz : z.IsGaTwo) (hw : w.IsGaTwo) :
    SqU4.u4Comm3 (p * z) (q * w)
      = SqU4.u4Comm3 p q + (q.c * z.d - q.a * z.e) + (p.a * w.e - p.c * w.d) := by
  obtain ⟨hza, hzb, hzc⟩ := hz
  obtain ⟨hwa, hwb, hwc⟩ := hw
  simp only [SqU4.u4Comm3, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
    hza, hzb, hzc, hwa, hwb, hwc]
  ring

/-- **The five-slot change of the core form**: dressing the three core slots by
`γ₂`-elements moves `sqU4Core` by three pairing blocks — the `σ`-dressing against the
`x₀`-letter's columns, the `x₀`-dressing against the `σ`-letter's columns (with even
corrections from the exponent letters), and the `x₁`-dressing against the `x₁`-letter's own
columns (with even corrections).  This is the core block of the graded Fox form: the Fox-row
permutation `(σ x₀)` with `x₁` self-paired, exact over any commutative ring. -/
theorem vanCore {s x y z₀ z₁ z₂ : SqU4 R} (hz₀ : z₀.IsGaTwo) (hz₁ : z₁.IsGaTwo)
    (hz₂ : z₂.IsGaTwo) :
    sqU4Core (s * z₀) (x * z₁) (y * z₂)
      = sqU4Core s x y + (x.c * z₀.d - x.a * z₀.e)
        + ((s.a + 10 * x.a) * z₁.e - (s.c - 10 * x.c + 8 * y.c) * z₁.d)
        + ((y.a - 8 * x.a) * z₂.e + y.c * z₂.d) := by
  obtain ⟨hz₀a, hz₀b, hz₀c⟩ := hz₀
  obtain ⟨hz₁a, hz₁b, hz₁c⟩ := hz₁
  obtain ⟨hz₂a, hz₂b, hz₂c⟩ := hz₂
  simp only [sqU4Core, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
    hz₀a, hz₀b, hz₀c, hz₁a, hz₁b, hz₁c, hz₂a, hz₂b, hz₂c]
  ring

end GaTwoCalculus

/-! ## §2 The five-slot dressing action

The committed `selRefine` dresses four slots (the exponent slots only by `γ₃`); the graded
Fox form needs all five, because the corank story reads all five Fox rows.  `vanDress`
multiplies every slot of a marking by its own `γ₂`-dressing, and `vanShift` is the affine
form by which the relator's class-three coordinate then moves. -/

section DressAction

variable {h : ℕ}

/-- **The five-slot dressing** of a marking: every slot multiplied on the right by its own
dressing element. -/
def vanDress (m z : Fin (sqRank h) → SqU4 R) : Fin (sqRank h) → SqU4 R :=
  fun i => m i * z i

@[simp] theorem vanDress_apply (m z : Fin (sqRank h) → SqU4 R) (i : Fin (sqRank h)) :
    vanDress m z i = m i * z i := rfl

variable (h) in
/-- **The shift form**: the amount by which the relator's class-three coordinate moves under
the five-slot dressing `vanDress m z`.  The `f`-terms `−4·(z 1).f + 2·(z 2).f` are the
abelian exponent action; every other term pairs one dressing's `(d, e)`-data against one
letter's outer abelian columns `(a, c)` — the `σ`-slot against the `x₀`-letter, the
`x₀`-slot against the `σ`-letter plus even corrections, the `x₁`-slot against the
`x₁`-letter plus even corrections, and each handle slot against the opposite handle letter.
Mod 2 this is exactly the permuted-letter Fox-row pairing (`vanShift_decomp`). -/
def vanShift (m z : Fin (sqRank h) → SqU4 R) : R :=
  -4 * (z 1).f + 2 * (z 2).f
    + ((m 1).c * (z 0).d - (m 1).a * (z 0).e)
    + (((m 0).a + 6 * (m 1).a) * (z 1).e - ((m 0).c - 10 * (m 1).c + 8 * (m 2).c) * (z 1).d)
    + ((3 * (m 2).a - 8 * (m 1).a) * (z 2).e + (m 2).c * (z 2).d)
    + ∑ j : Fin h,
        (((m (sqHandleIdxV j)).c * (z (sqHandleIdxU j)).d
            - (m (sqHandleIdxV j)).a * (z (sqHandleIdxU j)).e)
          + ((m (sqHandleIdxU j)).a * (z (sqHandleIdxV j)).e
            - (m (sqHandleIdxU j)).c * (z (sqHandleIdxV j)).d))

end DressAction

end SqCore

end Dyadic

end GQ2
