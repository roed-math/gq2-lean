/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DyadicPresentation
public import GQ2.MaxProP
public import GQ2.Reciprocity

@[expose] public section


/-!
# B3c: the canonical dyadic orientation — cyclotomic interface

Labute's classification of Demushkin groups (Theorem 8) attaches to each Demushkin group the
**canonical (dualizing) orientation character** `χ : G → U_p = ℤ_pˣ`, unique by his Theorem 4,
and — in the `q = 2` case — classifies by rank together with `Im χ`.  For the *local* group
`G_{ℚ₂}(2)` the canonical character **is** the (descended) cyclotomic character, and Labute's
**Theorem 4, case (2)** (`q = 2`, `n` odd) computes its values on the normalized generators:

  `(χ(x₁), χ(x₂), χ(x₃)) = (−1, 1, (1 − 2^f)⁻¹)`,   here `f = 2`, so `(−1, 1, (−3)⁻¹)`

— exactly the `χ_D`-row of the paper's equation (13) (Lemma 3.4/3.5), and consistent with the
B5 stress tests (`chiCyc_recip_neg4 = −1`, `chiCyc_recip_neg3 = (−3)⁻¹` in
`GQ2/Reciprocity.lean`).

## Encoding choice — interface form

Following `docs/orchestration/formalization-plan.md` §B3c, we do **not** formalize Labute's abstract
dualizing-module characterization of `χ` (his Prop. 6 — route (i), a stretch goal); instead we
state the **interface** the paper's Lemmas 3.4/3.5 actually consume: there is a choice of B4
isomorphism `ψ : G_{ℚ₂}(2) ≅ D₀` under which the descended cyclotomic character takes the
Theorem 4(2) values on the marked generators `A, S, Y`.  **Deviation flagged**: only the
interface ships; "`χ_D` is *the canonical* orientation in Labute's abstract sense" is not
formalized; the classification statement correspondingly stays at the field level.

## The bundle

`DyadicOrientation` packages:
* `equiv : G_{ℚ₂}(2) ≅ D₀` — the underlying Demushkin-group isomorphism, strengthened here by
  the orientation-value normalization;
* `chiTwo : G_{ℚ₂}(2) →* ℤ₂ˣ` continuous with `chiTwo ∘ π = χ_cyc` — the **descent** of the
  cyclotomic character through the maximal pro-2 quotient.  (The descent exists because `ℤ₂ˣ`
  is pro-2 — `(ℤ/2^k)ˣ` has order `2^{k−1}` — so `χ_cyc` kills the pro-2 kernel by
  `proPKernel_le_ker`; carrying it as data avoids adding an `IsProP 2 ℤ₂ˣ` development);
* `surjective_chiTwo` — `Im χ = ℤ₂ˣ = {±1} × U₂⁽²⁾`, the `f = 2` image invariant of
  Theorem 4(2) (the local analogue of B2's cyclotomic surjectivity);
* the three **values** `χ(A) = −1`, `χ(S) = 1`, `χ(Y) = (−3)⁻¹` under `equiv.symm` (the `−3`
  is quantified through its defining property, as in the B5 stress tests).

The axiom `GQ2.dyadicOrientation : DyadicOrientation` lives in `GQ2/Foundations/Axioms.lean`.
Stress tests below are bundle-parametrized (axiom-free): the values are consistent with the
Demushkin relation (`(−1)²·1⁴·[χS,χY] = 1` — the commutator dies in the abelian target), and
they pull back to `χ_cyc`-values on `G_{ℚ₂}` itself (the paper's full-group reading of (13)).

## Citations

Labute [2], Théorème 4 (case 2: `q = 2`, `n` odd — uniqueness and the values) and Théorème 8;
Serre [3].  Paper: Lemma 3.4, Lemma 3.5 / eq. (13), Prop. 1.1.  `docs/literature-axioms.md` B3.
-/

namespace GQ2

/-! ## The orientation bundle -/

/-- **B3c (dyadic orientation, cyclotomic interface — route (ii)).**  A B4 isomorphism
`G_{ℚ₂}(2) ≅ D₀` normalized so that the descended cyclotomic character takes Labute's
Theorem 4(2) values `(−1, 1, (−3)⁻¹)` on the marked generators `A, S, Y`.  See the module
docstring for the route decision and flagged deviations. -/
structure DyadicOrientation [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  /-- The underlying isomorphism `G_{ℚ₂}(2) ≅ D₀`. -/
  equiv : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0
  /-- The cyclotomic character, descended to the maximal pro-2 quotient. -/
  chiTwo : maxProPQuotient 2 AbsGalQ2 →* ℤ_[2]ˣ
  /-- `chiTwo` is continuous. -/
  continuous_chiTwo : Continuous chiTwo
  /-- **Descent**: `chiTwo` factors the cyclotomic character through `G_{ℚ₂} ↠ G_{ℚ₂}(2)`. -/
  chiTwo_factors : ∀ g : AbsGalQ2, chiTwo (maxProPMk 2 AbsGalQ2 g) = chiCyc g
  /-- **Image invariant** (`f = 2`): `Im χ = ℤ₂ˣ = {±1} × U₂⁽²⁾` (Labute Thm 4(2); the local
  analogue of B2). -/
  surjective_chiTwo : Function.Surjective chiTwo
  /-- Value on `A`: `χ(A) = −1`.  [paper (13), `ā`-row] -/
  chi_A : chiTwo (equiv.symm d0A) = -1
  /-- Value on `S`: `χ(S) = 1` (the unramified direction).  [paper (13), `s̄`-row] -/
  chi_S : chiTwo (equiv.symm d0S) = 1
  /-- Value on `Y`: `χ(Y) = (1 − 2²)⁻¹ = (−3)⁻¹` (the `−3` quantified through its defining
  property, as in the B5 stress tests).  [paper (13), `ȳ`-row] -/
  chi_Y : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → chiTwo (equiv.symm d0Y) = y⁻¹

/-! ## Stress tests (bundle-parametrized, axiom-free) -/

/-- Any homomorphism into a *commutative* group kills the commutator word. -/
lemma map_commP_eq_one {G H : Type*} [Group G] [CommGroup H] (f : G →* H) (x y : G) :
    f (commP x y) = 1 := by
  simp [commP, mul_comm]

section StressTests

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (O : DyadicOrientation)


/-- **Full-group reading of the `ā`-row of (13)**: any lift `g ∈ G_{ℚ₂}` of `ψ⁻¹(A)` has
`χ_cyc(g) = −1`. -/
theorem chiCyc_eq_neg_one_of_lift_A {g : AbsGalQ2}
    (hg : maxProPMk 2 AbsGalQ2 g = O.equiv.symm d0A) : chiCyc g = -1 := by
  rw [← O.chiTwo_factors, hg, O.chi_A]

/-- **Full-group reading of the `ȳ`-row of (13)**: any lift `g ∈ G_{ℚ₂}` of `ψ⁻¹(Y)` has
`χ_cyc(g) = (−3)⁻¹`. -/
theorem chiCyc_eq_inv_neg_three_of_lift_Y {g : AbsGalQ2}
    (hg : maxProPMk 2 AbsGalQ2 g = O.equiv.symm d0Y)
    (y : ℤ_[2]ˣ) (hy : (y : ℤ_[2]) = -3) : chiCyc g = y⁻¹ := by
  rw [← O.chiTwo_factors, hg, O.chi_Y y hy]


end StressTests

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (13) = ⟦eq-localmarkingorientation⟧
  * Lemma 3.4 = ⟦lem-standardorientation⟧
  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Prop 1.1 = ⟦prop-markedDem⟧
-/
