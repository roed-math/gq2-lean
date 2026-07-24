/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.VecNotation
public import GQ2.EvensKahn

@[expose] public section

/-!
# Stiefel–Whitney classes of binary quadratic forms over finite dyadic bases (B9-A, node N1)

The B9-A plan (`docs/orchestration/b9a-proof-plan.md`) restates axiom **B9** at the
quadratic-form level: the relative Stiefel–Whitney identity needs invariants `w₁ q ∈ H¹(G_k, 𝔽₂)`
and `w₂ q ∈ H²(G_k, 𝔽₂)` *defined on isometry classes* of nondegenerate binary quadratic forms
over a finite dyadic base `k`, rather than on the fixed diagonal representatives of Lemma 6.16.
This file provides that layer.

## Design (N1 decision, recorded in `docs/orchestration/b9a-t1-design.md`)

Forms are Mathlib `QuadraticForm ↥k V` with `QuadraticMap.Equivalent` as the isometry-class
relation; the diagonal representatives are `QuadraticMap.weightedSumSquares` with **unit**
weights on the model `Fin 2 → ↥k` (`diagForm`).  This matches
`QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`, whose only friction —
`Invertible (2 : ↥k)` — vanishes in characteristic zero (the global `invertibleTwo` instance).
No bespoke light structure is needed.

* `diagForm k x y` — the diagonal binary form `⟨x, y⟩` with unit weights `x, y ∈ (↥k)ˣ`.
* `IsDiagonalization k Q x y` — `Q` is isometric to `⟨x, y⟩`.
* `swOne k Q`, `swTwo k htriv Q` — the degree-1 and degree-2 Stiefel–Whitney classes, defined by
  `Classical.choice` of a diagonalization, with values `[x] + [y]` and `[x] ⌣[htriv] [y]` in the
  base-general Kummer classes `kummerClassK` of `GQ2/EvensKahn.lean`; junk value `0` when no
  unit diagonalization exists (the repository's junk-value convention, cf. `IsDemushkin`).

## Sorried statements (nodes N2 of the plan; ticket T3)

* `exists_isDiagonalization` — a nondegenerate binary form has a unit diagonalization.
* `swOne_well_defined` — degree-1 (discriminant) invariance across diagonalizations.
* `swTwo_well_defined` — degree-2 (Delzant/Hasse) invariance.  Its cup-relation inputs are the
  B11a norm criterion; since this file must stay strictly upstream of
  `GQ2/Foundations/Axioms.lean` (the flipped axiom will live there and import this file), the
  criterion enters as the explicit hypothesis `hnorm`, instantiated by
  `hilbertSymbol_normCriterion_finiteDyadic` at the flip site (plan node N2 and risk R4).

The evaluation lemmas `swOne_diag`/`swTwo_diag` and the isometry-class congruences
`swOne_congr`/`swTwo_congr` are proved here from the two invariance statements.

## Citations

Delzant, C. R. Acad. Sci. Paris 255 (1962) (Stiefel–Whitney classes of quadratic forms in
Galois cohomology); Serre, *A Course in Arithmetic*, Ch. IV; Kahn, Invent. Math. 78 (1984).
Paper: §6, eq. (111), Lemma 6.16.  Plan: `docs/orchestration/b9a-proof-plan.md` nodes N1/N2.
-/

namespace GQ2

open ContCoh QuadraticMap

open scoped Classical

-- The `Units`/`SMulCommClass`/`Invertible 2` instance chains of the quadratic-form API resolve
-- through the `IntermediateField` instance space, which overruns the default typeclass budget.
set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section BinaryForms

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The **diagonal binary quadratic form** `⟨x, y⟩` over `↥k` with unit weights, on the model
`Fin 2 → ↥k`: the value at `v` is `x·v₀² + y·v₁²`.  Unit weights make nondegeneracy automatic
and are exactly what `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`
produces. -/
noncomputable def diagForm (x y : (↥k)ˣ) : QuadraticForm ↥k (Fin 2 → ↥k) :=
  weightedSumSquares ↥k ![x, y]

@[simp] lemma diagForm_apply (x y : (↥k)ˣ) (v : Fin 2 → ↥k) :
    diagForm k x y v = (x : ↥k) * (v 0 * v 0) + (y : ↥k) * (v 1 * v 1) := by
  simp [diagForm, Fin.sum_univ_two, Units.smul_def]

/-- `Q` **is diagonalized by the unit pair** `(x, y)`: an isometry `Q ≃ ⟨x, y⟩` onto the
diagonal model.  The Stiefel–Whitney classes below are defined by choice of such a pair;
node N2 (ticket T3) shows the resulting classes do not depend on the choice. -/
def IsDiagonalization {V : Type*} [AddCommGroup V] [Module ↥k V]
    (Q : QuadraticForm ↥k V) (x y : (↥k)ˣ) : Prop :=
  Q.Equivalent (diagForm k x y)

/-- Diagonalizations transport along isometries of forms. -/
theorem isDiagonalization_of_equivalent {V W : Type*} [AddCommGroup V] [Module ↥k V]
    [AddCommGroup W] [Module ↥k W] {Q : QuadraticForm ↥k V} {Q' : QuadraticForm ↥k W}
    {x y : (↥k)ˣ} (h : Q.Equivalent Q') (hd : IsDiagonalization k Q' x y) :
    IsDiagonalization k Q x y :=
  h.trans hd

/-- **Existence of a unit diagonalization** for a nondegenerate binary form (char 0, so no
`Invertible (2 : ↥k)` friction).  Nondegeneracy is Mathlib's `SeparatingLeft` for the
associated bilinear form, the exact hypothesis of
`QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`. -/
theorem exists_isDiagonalization {V : Type*} [AddCommGroup V] [Module ↥k V]
    (Q : QuadraticForm ↥k V) (hdim : Module.finrank ↥k V = 2)
    (hQ : (associated (R := ↥k) Q).SeparatingLeft) :
    ∃ x y : (↥k)ˣ, IsDiagonalization k Q x y :=
  sorry -- T3: `equivalent_weightedSumSquares_units_of_nondegenerate'` + `hdim` transport

/-- **Degree-1 invariance (discriminant).**  Isometric diagonal binary forms have the same
degree-1 Stiefel–Whitney class `[x] + [y]`: the discriminants differ by the square of the
change-of-basis determinant (`QuadraticForm.discr_comp`), and Kummer classes kill squares. -/
theorem swOne_well_defined {x y x' y' : (↥k)ˣ}
    (h : (diagForm k x y).Equivalent (diagForm k x' y')) :
    kummerClassK k x + kummerClassK k y = kummerClassK k x' + kummerClassK k y' :=
  sorry -- T3 (plan node N2, degree 1): discriminant invariance

/-- **Degree-2 invariance (Delzant).**  Isometric diagonal binary forms have the same cup class
`[x] ⌣ [y]`.  This is the classical binary Hasse-invariant well-definedness: a representation
lemma extracts `x' = x·a² + y·b²` from the isometry, then a chain equivalence and the cup
identities close the computation.  The cup-relation inputs (Steinberg-type identities) are
consequences of the B11a norm criterion, which enters as the hypothesis `hnorm` so that this
file stays strictly upstream of `GQ2/Foundations/Axioms.lean`; the flip (ticket T5)
instantiates `hnorm := hilbertSymbol_normCriterion_finiteDyadic k htriv`. -/
theorem swTwo_well_defined (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hnorm : ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ z w : ↥k, (b : ↥k) = z ^ 2 - (a : ↥k) * w ^ 2)
    {x y x' y' : (↥k)ˣ} (h : (diagForm k x y).Equivalent (diagForm k x' y')) :
    kummerClassK k x ⌣[htriv] kummerClassK k y
      = kummerClassK k x' ⌣[htriv] kummerClassK k y' :=
  sorry -- T3 (plan node N2, degree 2): Delzant invariance via representation + chain equivalence

/-! ## The Stiefel–Whitney classes -/

/-- The **degree-1 Stiefel–Whitney class** `w₁ Q ∈ H¹(G_k, 𝔽₂)` of a quadratic form over `↥k`:
the sum `[x] + [y]` of the base-general Kummer classes of a chosen unit diagonalization
`Q ≃ ⟨x, y⟩`; junk value `0` when no unit diagonalization exists.  Independence of the choice
is `swOne_well_defined` (node N2); the evaluation at a given diagonalization is `swOne_diag`. -/
noncomputable def swOne {V : Type*} [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V) :
    H1 k.fixingSubgroup (ZMod 2) :=
  if h : ∃ x y : (↥k)ˣ, IsDiagonalization k Q x y then
    kummerClassK k h.choose + kummerClassK k h.choose_spec.choose
  else 0

/-- The **degree-2 Stiefel–Whitney class** `w₂ Q ∈ H²(G_k, 𝔽₂)`: the cup product
`[x] ⌣[htriv] [y]` of the Kummer classes of a chosen unit diagonalization `Q ≃ ⟨x, y⟩`; junk
value `0` when no unit diagonalization exists.  Independence of the choice is
`swTwo_well_defined` (node N2); evaluation is `swTwo_diag`. -/
noncomputable def swTwo (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    {V : Type*} [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V) :
    H2 k.fixingSubgroup (ZMod 2) :=
  if h : ∃ x y : (↥k)ˣ, IsDiagonalization k Q x y then
    kummerClassK k h.choose ⌣[htriv] kummerClassK k h.choose_spec.choose
  else 0

/-- **Evaluation of `swOne` at a diagonalization**: if `Q ≃ ⟨x, y⟩` then
`w₁ Q = [x] + [y]`. -/
theorem swOne_diag {V : Type*} [AddCommGroup V] [Module ↥k V] {Q : QuadraticForm ↥k V}
    {x y : (↥k)ˣ} (hd : IsDiagonalization k Q x y) :
    swOne k Q = kummerClassK k x + kummerClassK k y := by
  have hex : ∃ x' y' : (↥k)ˣ, IsDiagonalization k Q x' y' := ⟨x, y, hd⟩
  rw [show swOne k Q
      = kummerClassK k hex.choose + kummerClassK k hex.choose_spec.choose from dif_pos hex]
  exact swOne_well_defined k
    ((hex.choose_spec.choose_spec : Q.Equivalent _).symm.trans hd)

/-- **Evaluation of `swTwo` at a diagonalization**: if `Q ≃ ⟨x, y⟩` then
`w₂ Q = [x] ⌣[htriv] [y]`.  Carries the same `hnorm` hypothesis as `swTwo_well_defined`. -/
theorem swTwo_diag (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hnorm : ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ z w : ↥k, (b : ↥k) = z ^ 2 - (a : ↥k) * w ^ 2)
    {V : Type*} [AddCommGroup V] [Module ↥k V] {Q : QuadraticForm ↥k V}
    {x y : (↥k)ˣ} (hd : IsDiagonalization k Q x y) :
    swTwo k htriv Q = kummerClassK k x ⌣[htriv] kummerClassK k y := by
  have hex : ∃ x' y' : (↥k)ˣ, IsDiagonalization k Q x' y' := ⟨x, y, hd⟩
  rw [show swTwo k htriv Q
      = kummerClassK k hex.choose ⌣[htriv] kummerClassK k hex.choose_spec.choose from
    dif_pos hex]
  exact swTwo_well_defined k htriv hnorm
    ((hex.choose_spec.choose_spec : Q.Equivalent _).symm.trans hd)

/-- `swOne` is an isometry-class invariant (node N2 consequence). -/
theorem swOne_congr {V W : Type*} [AddCommGroup V] [Module ↥k V] [AddCommGroup W] [Module ↥k W]
    {Q : QuadraticForm ↥k V} {Q' : QuadraticForm ↥k W} (h : Q.Equivalent Q') :
    swOne k Q = swOne k Q' := by
  by_cases hex : ∃ x y : (↥k)ˣ, IsDiagonalization k Q' x y
  · obtain ⟨x, y, hxy⟩ := hex
    rw [swOne_diag k (isDiagonalization_of_equivalent k h hxy), swOne_diag k hxy]
  · have hexQ : ¬∃ x y : (↥k)ˣ, IsDiagonalization k Q x y := fun ⟨x, y, hxy⟩ ↦
      hex ⟨x, y, isDiagonalization_of_equivalent k h.symm hxy⟩
    exact (dif_neg hexQ : swOne k Q = 0).trans (dif_neg hex : swOne k Q' = 0).symm

/-- `swTwo` is an isometry-class invariant (node N2 consequence).  Carries the `hnorm`
hypothesis of `swTwo_well_defined`. -/
theorem swTwo_congr (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hnorm : ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ z w : ↥k, (b : ↥k) = z ^ 2 - (a : ↥k) * w ^ 2)
    {V W : Type*} [AddCommGroup V] [Module ↥k V] [AddCommGroup W] [Module ↥k W]
    {Q : QuadraticForm ↥k V} {Q' : QuadraticForm ↥k W} (h : Q.Equivalent Q') :
    swTwo k htriv Q = swTwo k htriv Q' := by
  by_cases hex : ∃ x y : (↥k)ˣ, IsDiagonalization k Q' x y
  · obtain ⟨x, y, hxy⟩ := hex
    rw [swTwo_diag k htriv hnorm (isDiagonalization_of_equivalent k h hxy),
      swTwo_diag k htriv hnorm hxy]
  · have hexQ : ¬∃ x y : (↥k)ˣ, IsDiagonalization k Q x y := fun ⟨x, y, hxy⟩ ↦
      hex ⟨x, y, isDiagonalization_of_equivalent k h.symm hxy⟩
    exact (dif_neg hexQ : swTwo k htriv Q = 0).trans
      (dif_neg hex : swTwo k htriv Q' = 0).symm

end BinaryForms

end GQ2
