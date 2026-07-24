/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import GQ2.StiefelWhitney

@[expose] public section

/-!
# Twisted trace forms of dyadic quadratic extensions (B9-A, node N3) and the draft axiom

Second layer of the B9-A plan (`docs/orchestration/b9a-proof-plan.md`): the quadratic extension
`k(δ)/k`, the `a`-twisted trace forms `Tr_{k(δ)/k}⟨a⟩`, and — in the clearly marked final
section — the **draft statement** of the replacement axiom `relativeStiefelWhitney_dyadic`,
kept here as a sorried `theorem` until the owner signs off (ticket T5 moves it to
`GQ2/Foundations/Axioms.lean`).

## The field construction (L-encoding decision, `docs/orchestration/b9a-t1-design.md`)

`L` is `quadExt k δ := IntermediateField.adjoin ↥k {δ}`, the adjoin over `↥k` inside `ℚ̄₂`.
No ambient `L : IntermediateField ℚ_[2] ℚ̄₂` is carried: the subgroup side of the axiom (the
`hidx`/`hUo` stabilizer encoding, reused verbatim from B9) and the field side are parametrized
by the *same* `δ`, so their compatibility is provable rather than hypothesized
(`GQ2/KummerKrullBridge.lean` machinery; see `finrank_quadExt_eq_two`).  All trace/finrank API
applies because `quadExt k δ` is an intermediate field of `ℚ̄₂/↥k`: `Algebra ↥k ↥(quadExt k δ)`
and `Algebra.trace ↥k ↥(quadExt k δ)` are found by instance search, and finite-dimensionality
over `↥k` follows from integrality of `δ` (`finiteDimensional_quadExt`).

## Contents

* `quadExt k δ` — the extension `k(δ)` of `↥k`; `isIntegral_of_sq_eq`,
  `finiteDimensional_quadExt` (proved).
* `finrank_quadExt_eq_two` — `[k(δ) : k] = 2` from the B9 index-2 stabilizer hypothesis
  (sorried; ticket T2 via `KummerKrullBridge.exists_quadratic_of_open_index_two`).
* `traceFormOne k δ` — `Tr⟨1⟩ : z ↦ Tr_{k(δ)/k}(z·z)`; `traceFormTwisted k δ a` —
  `Tr⟨a⟩ : z ↦ Tr_{k(δ)/k}(a·z·z)`.  Both are genuine `QuadraticForm ↥k ↥(quadExt k δ)`
  definitions (no sorries), built from `Algebra.traceForm` via
  `LinearMap.BilinMap.toQuadraticMap`.
* `traceFormOne_isDiagonalization`, `traceFormTwisted_isDiagonalization` — Lemma 6.16's
  diagonalizations `Tr⟨1⟩ ≃ ⟨2, 2d⟩` and `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` for `a = u + vδ`
  (sorried; ticket T2, basis `{1, δ}` and completing the square with `u ∈ kˣ`).
* `relativeStiefelWhitney_dyadic` — the draft axiom statement (sorried; ticket T5).

## Citations

Kahn, Invent. Math. 78 (1984), Théorème 2; Evens, Trans. AMS 108 (1963), Thm 1; Kozlowski,
Proc. AMS 91 (1984), Thm 1.1.  Paper: §6, eq. (111), Lemmas 6.13/6.16.
-/

namespace GQ2

-- Same relaxation as `GQ2/StiefelWhitney.lean`: the trace-form and quadratic-form instance
-- chains resolve through the `IntermediateField` instance space.
set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section TraceForms

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The extension `k(δ)` of the finite dyadic base `k`, as an intermediate field of `ℚ̄₂/↥k`.
For the B9-A setting `δ² = d ∈ kˣ` with `d` a nonsquare, this is the quadratic extension `L`
of the Evens–Kahn identity; the degree-2 fact is `finrank_quadExt_eq_two`. -/
noncomputable def quadExt (δ : ℚ̄₂) : IntermediateField ↥k ℚ̄₂ :=
  IntermediateField.adjoin ↥k {δ}

/-- A square root of an element of `k` is integral over `↥k` (monic witness `X² − d`). -/
theorem isIntegral_of_sq_eq (d : (↥k)ˣ) {δ : ℚ̄₂} (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) :
    IsIntegral ↥k δ :=
  ⟨Polynomial.X ^ 2 - Polynomial.C (d : ↥k),
    Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hδ]⟩

/-- `k(δ)` is a finite extension of `↥k` when `δ² ∈ k` — the instance input for the trace
form's nondegeneracy (`Algebra.traceForm_nondegenerate`, char 0 so separability is free). -/
theorem finiteDimensional_quadExt (d : (↥k)ˣ) {δ : ℚ̄₂} (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) :
    FiniteDimensional ↥k ↥(quadExt k δ) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_sq_eq k d hδ)

/-- **`[k(δ) : k] = 2` from the B9 subgroup encoding**: if the stabilizer of `δ` meets
`G_k = k.fixingSubgroup` in an open subgroup of index 2, then `quadExt k δ` is quadratic
over `↥k`.  This is the bridge that lets the draft axiom's field-level hypothesis `hdeg` be
discharged from the verbatim B9 hypotheses `hUo`/`hidx` at the flip (plan node N3, risk R2). -/
theorem finrank_quadExt_eq_two [FiniteDimensional ℚ_[2] k] (d : (↥k)ˣ) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂))
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup)) :
    Module.finrank ↥k ↥(quadExt k δ) = 2 :=
  sorry -- T2 (plan node N3): `KummerKrullBridge.exists_quadratic_of_open_index_two` + adjoin

/-- The **untwisted trace form** `Tr⟨1⟩` of `k(δ)/k`: the quadratic form
`z ↦ Tr_{k(δ)/k}(z·z)` over `↥k`, i.e. `Algebra.traceForm` read as a quadratic map. -/
noncomputable def traceFormOne (δ : ℚ̄₂) : QuadraticForm ↥k ↥(quadExt k δ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ↥k ↥(quadExt k δ))

@[simp] lemma traceFormOne_apply (δ : ℚ̄₂) (z : ↥(quadExt k δ)) :
    traceFormOne k δ z = Algebra.trace ↥k ↥(quadExt k δ) (z * z) := by
  simp [traceFormOne, Algebra.traceForm_apply]

/-- The **`a`-twisted trace form** `Tr⟨a⟩` of `k(δ)/k`: the quadratic form
`z ↦ Tr_{k(δ)/k}(a·z·z)` over `↥k`, from the twisted bilinear form
`(z, w) ↦ Tr(a·z·w)`.  For `a ∈ k(δ)ˣ` this is Kahn's transfer `Tr_{L/k}⟨a⟩` of the rank-1
form `⟨a⟩`. -/
noncomputable def traceFormTwisted (δ : ℚ̄₂) (a : ↥(quadExt k δ)) :
    QuadraticForm ↥k ↥(quadExt k δ) :=
  LinearMap.BilinMap.toQuadraticMap
    ((Algebra.traceForm ↥k ↥(quadExt k δ)).compl₁₂ (LinearMap.mulLeft ↥k a) LinearMap.id)

@[simp] lemma traceFormTwisted_apply (δ : ℚ̄₂) (a z : ↥(quadExt k δ)) :
    traceFormTwisted k δ a z = Algebra.trace ↥k ↥(quadExt k δ) (a * z * z) := by
  simp [traceFormTwisted, Algebra.traceForm_apply]

/-- **Lemma 6.16, first diagonalization**: `Tr⟨1⟩ ≃ ⟨2, 2d⟩` over the basis `{1, δ}`
(Gram matrix `diag(Tr 1, Tr δ²) = diag(2, 2d)`). -/
theorem traceFormOne_isDiagonalization (d : (↥k)ˣ) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2) :
    IsDiagonalization k (traceFormOne k δ) (twoUnit k) (twoUnit k * d) :=
  sorry -- T2 (plan node N3): basis {1, δ} via `IntermediateField.adjoin.powerBasis`

/-- **Lemma 6.16, second diagonalization**: for `a = u + vδ` with norm `n = u² − dv²`
(`u, n, d` units of `k`), `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` — Gram `(2u, 2vd; 2vd, 2ud)` on `{1, δ}`,
completed to squares using `u ∈ kˣ`. -/
theorem traceFormTwisted_isDiagonalization (u n d : (↥k)ˣ) (v : ↥k)
    (hn : (n : ↥k) = (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
    (a : ↥(quadExt k δ)) (ha : (a : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ) :
    IsDiagonalization k (traceFormTwisted k δ a) (twoUnit k * u) (twoUnit k * d * n * u⁻¹) :=
  sorry -- T2 (plan node N3): Gram computation on {1, δ} + complete the square

end TraceForms

/-! ## Draft axiom statement (for owner review; will move to Foundations/Axioms.lean at T5)

The B9-A replacement axiom, stated as a sorried `theorem` so that it elaborates and can be
reviewed as a compiling artifact (plan risk R3).  **It is never proved on this branch**: after
owner sign-off, ticket T5 moves the statement verbatim to `GQ2/Foundations/Axioms.lean` as an
`axiom` (census label B9) and derives today's `evensKahn_dyadic` from it, byte-identically. -/

/-- **Draft — the B9-A axiom `relativeStiefelWhitney_dyadic`** (Kahn, Invent. Math. 78 (1984),
Théorème 2 at the rank-1 form `⟨a⟩`, expanded through Evens Thm 1 / Kozlowski Thm 1.1 at
index 2; paper eq. (111), degrees ≤ 2), over an arbitrary finite dyadic base `k`.

Setting, as in B9: `k/ℚ₂` finite inside the fixed `ℚ̄₂`; `d ∈ kˣ` with `δ² = d`;
`L = k(δ) = quadExt k δ`, quadratic over `k` (`hdeg`, provable from `hidx`/`hUo` via
`finrank_quadExt_eq_two` but carried so the statement is locally Kahn's `L/k` setting);
`G_L ∩ G_k` is the stabilizer subgroup of `δ` (the verbatim B9 encoding: `hidx`, `s`, `hs`,
`htriv`, `hUo`); `a ∈ Lˣ` **arbitrary** (the new generality — B9's `a = u + vδ` disappears),
entering degree-wise through the Kummer 1-cocycle `α` of a square root `β` of `a`
(`hβ`/`hβ0`/`hαdef`/`hα`/`hαc`, verbatim B9 plumbing).  With `w₁ = swOne k`,
`w₂ = swTwo k htriv` the Stiefel–Whitney classes of `GQ2/StiefelWhitney.lean`, the two
components of Kahn's identity `w(Tr⟨a⟩) = w(Tr⟨1⟩)·(1 + cor[a] + N^{Ev}[a])` read:

* degree 1: `w₁(Tr⟨a⟩) = w₁(Tr⟨1⟩) + cor[a]`;
* degree 2: `w₂(Tr⟨a⟩) = w₂(Tr⟨1⟩) + w₁(Tr⟨1⟩) ⌣ cor[a] + N^{Ev}[a]`.

Deviations (flagged, unchanged from B9): truncation to degrees ≤ 2; `N^{Ev}` *defined* by the
two-point graph cocycle (98) (`evensNormH2`, Lemma 6.13); finite dyadic base.  Removed
relative to B9: the Lemma 6.16 diagonalization scoping — the left-hand sides are now genuine
isometry-class invariants. -/
theorem relativeStiefelWhitney_dyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (d : (↥k)ˣ)
    (δ β : AlgebraicClosure ℚ_[2])
    (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
    (a : (↥(quadExt k δ))ˣ)
    (hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : AlgebraicClosure ℚ_[2]))
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α) :
    (swOne k (traceFormTwisted k δ ↑a)
      = swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc)
    ∧ (swTwo k htriv (traceFormTwisted k δ ↑a)
      = swTwo k htriv (traceFormOne k δ)
        + swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc
        + evensNormH2 htriv hUo hidx hs α hα hαc) :=
  sorry -- T5: becomes the B9-A axiom in Foundations/Axioms.lean after owner sign-off

end GQ2
