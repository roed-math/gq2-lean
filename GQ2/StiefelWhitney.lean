/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.VecNotation
public import GQ2.CupSymmetry
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

## The invariance layer (node N2 of the plan; proved by ticket T3, 2026-07-24)

* `exists_isDiagonalization` — a nondegenerate binary form has a unit diagonalization (proved).
* `swOne_well_defined` — degree-1 (discriminant) invariance across diagonalizations (proved via
  an exact Brahmagupta identity `x'y' = xy·(ad−bc)²` extracted from the isometry).
* `swTwo_well_defined` — degree-2 (Delzant/Hasse) invariance (proved: representation lemma +
  a single Steinberg instance).  Its cup-relation input is the B11a norm criterion; since this
  file is strictly upstream of `GQ2/Foundations/Axioms.lean` (the B9 axiom lives there and
  imports this file), the criterion enters as the explicit hypothesis `hnorm`, instantiated by
  `hilbertSymbol_normCriterion_finiteDyadic` at the flip site (plan node N2; owner decision Q2).
  All three are sorry-free with `#print axioms` = the standard three.

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

/-! ## Private helpers: two-torsion, cup symmetry, and Kummer-class algebra

The invariance proofs below need the 2-torsion of the `𝔽₂`-cohomology groups, symmetry of the
trivial cup pairing, and multiplicativity of `kummerClassK`.  The public forms of these lemmas
live in `GQ2/HilbertLedger.lean`, which is strictly *downstream* of this file (it imports
`GQ2/Foundations/Axioms.lean`, which will import this file at the B9-A flip, plan node N5), so
they are re-proved here as `private` lemmas — the approved default of
`docs/orchestration/b9a-t1-design.md`, owner question Q3.  Cup symmetry alone is *derived*
rather than re-proved: `GQ2/CupSymmetry.lean` is upstream, and its `cup11_comm` specializes to
the multiplication pairing on `ZMod 2`, which is its own transpose. -/

section Helpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- `H¹(G, 𝔽₂)` is 2-torsion (private re-proof; cf. `GQ2.h1_add_self` downstream). -/
private theorem h1_add_self (x : H1 G (ZMod 2)) : x + x = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    have hz : z + z = 0 := Subtype.ext (funext fun _ ↦ key _)
    show H1mk G (ZMod 2) z + H1mk G (ZMod 2) z = 0
    rw [← map_add, hz, map_zero]

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- `H²(G, 𝔽₂)` is 2-torsion (private re-proof; cf. `GQ2.h2_add_self` downstream). -/
private theorem h2_add_self (x : H2 G (ZMod 2)) : x + x = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    have hz : z + z = 0 := Subtype.ext (funext fun _ ↦ key _)
    show H2mk G (ZMod 2) z + H2mk G (ZMod 2) z = 0
    rw [← map_add, hz, map_zero]

/-- In a 2-torsion abelian group, `a + b = 0` forces `a = b`. -/
private lemma eq_of_add_eq_zero_two_torsion {M : Type*} [AddCommGroup M]
    (htor : ∀ m : M, m + m = 0) {a b : M} (h : a + b = 0) : a = b :=
  (eq_neg_of_add_eq_zero_left h).trans (neg_eq_of_add_eq_zero_left (htor b))

omit [IsTopologicalGroup G] in
/-- Symmetry of the trivial cup pairing in characteristic 2, specialized from the upstream
graded-commutativity `cup11_comm` of `GQ2/CupSymmetry.lean`: the transposed multiplication
pairing on `ZMod 2` is multiplication again (cf. `GQ2.trivialCupPairing_comm` downstream). -/
private theorem trivialCupPairing_comm (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (α β : H1 G (ZMod 2)) : α ⌣[htriv] β = β ⌣[htriv] α := by
  have hcongr : ∀ (μ₁ μ₂ : ZMod 2 →+ ZMod 2 →+ ZMod 2)
      (h₁ : ∀ (g : G) (m n : ZMod 2), μ₁ (g • m) (g • n) = g • μ₁ m n)
      (h₂ : ∀ (g : G) (m n : ZMod 2), μ₂ (g • m) (g • n) = g • μ₂ m n),
      μ₁ = μ₂ → cup11 μ₁ h₁ = cup11 μ₂ h₂ := by
    rintro μ₁ _ h₁ h₂ rfl
    rfl
  show α ⌣[htriv] β = β ⌣[htriv] α
  unfold trivialCupPairing
  rw [cup11_comm _ _ (by decide) α β,
    hcongr _ AddMonoidHom.mul _ (fun g m n ↦ by rw [htriv, htriv, htriv])
      (AddMonoidHom.ext fun m ↦ AddMonoidHom.ext fun n ↦ mul_comm n m)]

end Helpers

section KummerHelpers

open Kummer

/-- Two square roots of the same element of `ℚ̄₂` have the same Kummer cocycle (private
re-proof; cf. `GQ2.kcf_root_indep'` downstream). -/
private lemma kcf_root_indep' {α β : ℚ̄₂} (h : α ^ 2 = β ^ 2) :
    kummerCocycleFun α = kummerCocycleFun β := by
  have h2 : (α - β) * (α + β) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h' | h'
  · rw [sub_eq_zero.1 h']
  · rw [add_eq_zero_iff_eq_neg.1 h', kummerCocycleFun_neg]

/-- Kummer-cocycle additivity at a Galois element fixing both radicands (private re-proof;
cf. `GQ2.kcf_mul_of_fixed` downstream). -/
private lemma kcf_mul_of_fixed {A B γ α β : ℚ̄₂}
    (hγ : γ ^ 2 = A * B) (hα : α ^ 2 = A) (hβ : β ^ 2 = B)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    {g : GaloisGroup ℚ_[2]} (hgA : g • A = A) (hgB : g • B = B) :
    kummerCocycleFun γ g = kummerCocycleFun α g + kummerCocycleFun β g := by
  have hγαβ : kummerCocycleFun γ = kummerCocycleFun (α * β) :=
    kcf_root_indep' (by rw [hγ, mul_pow, hα, hβ])
  rw [hγαβ]
  have hmul : g • (α * β) = (g • α) * (g • β) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_mul]
  have eq1 : ∀ {x : ℚ̄₂}, g • x = -x → x ≠ 0 → kummerCocycleFun x g = 1 :=
    fun hx hx0 ↦ if_neg (fun e ↦ ne_neg_of_ne_zero hx0 (e.symm.trans hx))
  rcases two_values_of_fixed hα hgA with hga | hga <;>
    rcases two_values_of_fixed hβ hgB with hgb | hgb
  · rw [kummerCocycleFun_eq0 hga, kummerCocycleFun_eq0 hgb,
      kummerCocycleFun_eq0 (by rw [hmul, hga, hgb])]
    decide
  · rw [kummerCocycleFun_eq0 hga, eq1 hgb hβ0,
      eq1 (by rw [hmul, hga, hgb]; ring) (mul_ne_zero hα0 hβ0)]
    decide
  · rw [eq1 hga hα0, kummerCocycleFun_eq0 hgb,
      eq1 (by rw [hmul, hga, hgb]; ring) (mul_ne_zero hα0 hβ0)]
    decide
  · rw [eq1 hga hα0, eq1 hgb hβ0,
      kummerCocycleFun_eq0 (by rw [hmul, hga, hgb]; ring)]
    decide

/-- Multiplicativity of the base-general Kummer class (private re-proof; cf.
`GQ2.kummerClassK_mul` downstream). -/
private theorem kummerClassK_mul (a b : (↥k)ˣ) :
    kummerClassK k (a * b) = kummerClassK k a + kummerClassK k b := by
  have hAB : ((↑(a * b) : ↥k) : ℚ̄₂) = ((↑a : ↥k) : ℚ̄₂) * ((↑b : ↥k) : ℚ̄₂) := by
    rw [Units.val_mul, MulMemClass.coe_mul]
  unfold kummerClassK
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext g
  simp only [AddMemClass.coe_add, Pi.add_apply]
  rw [hAB]
  exact kcf_mul_of_fixed (sqrtCl_sq _) (sqrtCl_sq _) (sqrtCl_sq _)
    (sqrtCl_ne_zero (unitCoe_ne_zero k a)) (sqrtCl_ne_zero (unitCoe_ne_zero k b))
    (fixingSubgroup_smul k g.2 (a : ↥k)) (fixingSubgroup_smul k g.2 (b : ↥k))

/-- The Kummer class of `1` vanishes (private re-proof; cf. `GQ2.kummerClassK_one`
downstream). -/
private theorem kummerClassK_one : kummerClassK k (1 : (↥k)ˣ) = 0 := by
  have h := kummerClassK_mul k (1 : (↥k)ˣ) 1
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

/-- `[a⁻¹] = [a]` (private re-proof; cf. `GQ2.kummerClassK_inv` downstream). -/
private theorem kummerClassK_inv (a : (↥k)ˣ) : kummerClassK k a⁻¹ = kummerClassK k a := by
  have h := kummerClassK_mul k a a⁻¹
  rw [mul_inv_cancel, kummerClassK_one] at h
  exact add_left_cancel (h.symm.trans (h1_add_self (kummerClassK k a)).symm)

/-- `[a·a] = 0` (private re-proof; cf. `GQ2.kummerClassK_mul_self` downstream). -/
private theorem kummerClassK_mul_self (a : (↥k)ˣ) : kummerClassK k (a * a) = 0 := by
  rw [kummerClassK_mul]
  exact h1_add_self _

end KummerHelpers

/-- **Existence of a unit diagonalization** for a nondegenerate binary form (char 0, so no
`Invertible (2 : ↥k)` friction).  Nondegeneracy is Mathlib's `SeparatingLeft` for the
associated bilinear form, the exact hypothesis of
`QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`. -/
theorem exists_isDiagonalization {V : Type*} [AddCommGroup V] [Module ↥k V]
    (Q : QuadraticForm ↥k V) (hdim : Module.finrank ↥k V = 2)
    (hQ : (associated (R := ↥k) Q).SeparatingLeft) :
    ∃ x y : (↥k)ˣ, IsDiagonalization k Q x y := by
  haveI : FiniteDimensional ↥k V := FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ
  set e : Fin 2 ≃ Fin (Module.finrank ↥k V) := (finCongr hdim).symm with he
  refine ⟨w (e 0), w (e 1), hw.trans ⟨⟨LinearEquiv.funCongrLeft ↥k ↥k e, fun v ↦ ?_⟩⟩⟩
  show diagForm k (w (e 0)) (w (e 1)) (v ∘ e) = weightedSumSquares ↥k w v
  rw [diagForm_apply, weightedSumSquares_apply,
    ← Fintype.sum_equiv e (fun j ↦ w (e j) • (v (e j) * v (e j)))
      (fun i ↦ w i • (v i * v i)) (fun _ ↦ rfl),
    Fin.sum_univ_two]
  simp [Units.smul_def]

/-- **Degree-1 invariance (discriminant).**  Isometric diagonal binary forms have the same
degree-1 Stiefel–Whitney class `[x] + [y]`: the discriminants differ by the square of the
change-of-basis determinant (`QuadraticForm.discr_comp`), and Kummer classes kill squares. -/
theorem swOne_well_defined {x y x' y' : (↥k)ˣ}
    (h : (diagForm k x y).Equivalent (diagForm k x' y')) :
    kummerClassK k x + kummerClassK k y = kummerClassK k x' + kummerClassK k y' := by
  obtain ⟨τ⟩ := h.symm
  -- Evaluating the isometry at the standard basis vectors and at their sum gives the two
  -- representations and the orthogonality relation of the Gram matrix.
  have key : ∀ m : Fin 2 → ↥k,
      (x : ↥k) * (τ m 0 * τ m 0) + (y : ↥k) * (τ m 1 * τ m 1) = diagForm k x' y' m := by
    intro m
    have h0 := τ.map_app m
    rw [diagForm_apply] at h0
    exact h0
  have hx' := key ![1, 0]
  have hy' := key ![0, 1]
  have hsum := key (![1, 0] + ![0, 1])
  rw [map_add] at hsum
  simp only [diagForm_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero, zero_add] at hx' hy' hsum
  -- Polarization: the images of the two basis vectors are orthogonal for `⟨x, y⟩`.
  have horth : (x : ↥k) * (τ ![1, 0] 0 * τ ![0, 1] 0)
      + (y : ↥k) * (τ ![1, 0] 1 * τ ![0, 1] 1) = 0 := by
    apply mul_left_cancel₀ (two_ne_zero (α := ↥k))
    rw [mul_zero]
    linear_combination hsum - hx' - hy'
  -- Brahmagupta: the discriminants agree up to the square of the change-of-basis determinant.
  have hdet : (x' : ↥k) * y'
      = (x : ↥k) * y * ((τ ![1, 0] 0 * τ ![0, 1] 1 - τ ![1, 0] 1 * τ ![0, 1] 0)
        * (τ ![1, 0] 0 * τ ![0, 1] 1 - τ ![1, 0] 1 * τ ![0, 1] 0)) := by
    linear_combination
      ((x : ↥k) * (τ ![1, 0] 0 * τ ![0, 1] 0) + (y : ↥k) * (τ ![1, 0] 1 * τ ![0, 1] 1)) * horth
      - ((x : ↥k) * (τ ![0, 1] 0 * τ ![0, 1] 0) + (y : ↥k) * (τ ![0, 1] 1 * τ ![0, 1] 1)) * hx'
      - (x' : ↥k) * hy'
  set s : ↥k := τ ![1, 0] 0 * τ ![0, 1] 1 - τ ![1, 0] 1 * τ ![0, 1] 0 with hs
  have hs0 : s ≠ 0 := fun h0 ↦
    mul_ne_zero x'.ne_zero y'.ne_zero (by rw [hdet, h0, mul_zero, mul_zero])
  -- Pass to units and kill the square through the Kummer classes.
  have hu : x' * y' = x * y * (Units.mk0 s hs0 * Units.mk0 s hs0) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    exact hdet
  have hcl := congrArg (kummerClassK k) hu
  rw [kummerClassK_mul k, kummerClassK_mul k, kummerClassK_mul k, kummerClassK_mul_self k,
    add_zero] at hcl
  exact hcl.symm

set_option maxHeartbeats 800000 in
/-- **The representation step of Delzant invariance** (private): if `⟨x, y⟩` represents the
unit `x'` — say `x' = x·a² + y·b²` — then `[x] ⌣ [y] = [x'] ⌣ ([x] + [y] + [x'])`.  The main
case (`a, b ≠ 0`) is the Steinberg relation supplied by `hnorm` at `t = x·a²/x'`,
`1 − t = y·b²/x'`, expanded bilinearly and closed by cup symmetry and 2-torsion; the degenerate
cases `a = 0` / `b = 0` reduce to `[x'] = [y]` resp. `[x'] = [x]` and cup symmetry. -/
private theorem cup_eq_of_represents
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hnorm : ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ z w : ↥k, (b : ↥k) = z ^ 2 - (a : ↥k) * w ^ 2)
    (x y x' : (↥k)ˣ) (a b : ↥k)
    (hrep : (x' : ↥k) = (x : ↥k) * a ^ 2 + (y : ↥k) * b ^ 2) :
    kummerClassK k x ⌣[htriv] kummerClassK k y
      = kummerClassK k x' ⌣[htriv] (kummerClassK k x + kummerClassK k y + kummerClassK k x') := by
  by_cases ha : a = 0
  · -- `x' = y·b²`, so `[x'] = [y]` and the claim is cup symmetry.
    have hb : b ≠ 0 := fun hb ↦ x'.ne_zero (by rw [hrep, ha, hb]; ring)
    have hx'cl : kummerClassK k x' = kummerClassK k y := by
      have hx'u : x' = y * (Units.mk0 b hb * Units.mk0 b hb) := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        rw [hrep, ha]
        ring
      rw [hx'u, kummerClassK_mul k, kummerClassK_mul_self k, add_zero]
    rw [hx'cl, show kummerClassK k x + kummerClassK k y + kummerClassK k y = kummerClassK k x
      from by rw [add_assoc, h1_add_self, add_zero]]
    exact trivialCupPairing_comm htriv _ _
  · by_cases hb : b = 0
    · -- `x' = x·a²`, so `[x'] = [x]` and both sides are `[x] ⌣ [y]` on the nose.
      have hx'cl : kummerClassK k x' = kummerClassK k x := by
        have hx'u : x' = x * (Units.mk0 a ha * Units.mk0 a ha) := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_mk0]
          rw [hrep, hb]
          ring
        rw [hx'u, kummerClassK_mul k, kummerClassK_mul_self k, add_zero]
      rw [hx'cl, show kummerClassK k x + kummerClassK k y + kummerClassK k x = kummerClassK k y
        from by rw [add_comm (kummerClassK k x) (kummerClassK k y), add_assoc, h1_add_self,
          add_zero]]
    · -- Main case: Steinberg at `t = x·a²/x'`, `1 − t = y·b²/x'`.
      set t : (↥k)ˣ := x * (Units.mk0 a ha * Units.mk0 a ha) * x'⁻¹ with ht
      set u : (↥k)ˣ := y * (Units.mk0 b hb * Units.mk0 b hb) * x'⁻¹ with hu
      have hx'0 : (x' : ↥k) ≠ 0 := x'.ne_zero
      have htv : (t : ↥k) * (x' : ↥k) = (x : ↥k) * (a * a) := by
        simp only [ht, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        exact inv_mul_cancel_right₀ hx'0 _
      have huv : (u : ↥k) * (x' : ↥k) = (y : ↥k) * (b * b) := by
        simp only [hu, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        exact inv_mul_cancel_right₀ hx'0 _
      have hst : (u : ↥k) = 1 ^ 2 - (t : ↥k) * 1 ^ 2 := by
        rw [one_pow, mul_one]
        apply mul_right_cancel₀ hx'0
        rw [sub_mul, one_mul, huv, htv]
        linear_combination -hrep
      have hcup0 : kummerClassK k t ⌣[htriv] kummerClassK k u = 0 :=
        (hnorm t u).mpr ⟨1, 1, hst⟩
      have htcl : kummerClassK k t = kummerClassK k x + kummerClassK k x' := by
        rw [ht, kummerClassK_mul k, kummerClassK_mul k, kummerClassK_mul_self k, add_zero,
          kummerClassK_inv k]
      have hucl : kummerClassK k u = kummerClassK k y + kummerClassK k x' := by
        rw [hu, kummerClassK_mul k, kummerClassK_mul k, kummerClassK_mul_self k, add_zero,
          kummerClassK_inv k]
      rw [htcl, hucl] at hcup0
      simp only [map_add, AddMonoidHom.add_apply] at hcup0 ⊢
      refine eq_of_add_eq_zero_two_torsion h2_add_self ?_
      rw [← trivialCupPairing_comm htriv (kummerClassK k x) (kummerClassK k x')]
      abel_nf at hcup0 ⊢
      exact hcup0

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
      = kummerClassK k x' ⌣[htriv] kummerClassK k y' := by
  obtain ⟨τ⟩ := h.symm
  -- The isometry represents `x'` by `⟨x, y⟩`: evaluate at the first standard basis vector.
  have hrep : (x' : ↥k) = (x : ↥k) * (τ ![1, 0] 0) ^ 2 + (y : ↥k) * (τ ![1, 0] 1) ^ 2 := by
    have h0 := τ.map_app ![1, 0]
    rw [diagForm_apply] at h0
    simp only [diagForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, mul_zero, add_zero] at h0
    linear_combination -h0
  rw [cup_eq_of_represents k htriv hnorm x y x' _ _ hrep, swOne_well_defined k h,
    show kummerClassK k x' + kummerClassK k y' + kummerClassK k x'
      = kummerClassK k y' + (kummerClassK k x' + kummerClassK k x') from by abel,
    h1_add_self, add_zero]

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
