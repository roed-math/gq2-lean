import Mathlib
import GQ2.DyadicPresentation
import GQ2.MaxProP
import GQ2.Reciprocity

/-!
# B3c: the canonical dyadic orientation — cyclotomic interface  (ticket T-11, route (ii))

Labute's classification of Demushkin groups (Theorem 8) attaches to each Demushkin group the
**canonical (dualizing) orientation character** `χ : G → U_p = ℤ_pˣ`, unique by his Theorem 4,
and — in the `q = 2` case — classifies by rank together with `Im χ`.  For the *local* group
`G_{ℚ₂}(2)` the canonical character **is** the (descended) cyclotomic character, and Labute's
**Theorem 4, case (2)** (`q = 2`, `n` odd) computes its values on the normalized generators:

  `(χ(x₁), χ(x₂), χ(x₃)) = (−1, 1, (1 − 2^f)⁻¹)`,   here `f = 2`, so `(−1, 1, (−3)⁻¹)`

— exactly the `χ_D`-row of the paper's equation (13) (Lemma 3.4/3.5), and consistent with the
B5 stress tests (`chiCyc_recip_neg4 = −1`, `chiCyc_recip_neg3 = (−3)⁻¹` in
`GQ2/Reciprocity.lean`).

## Route decision (the ticket's 🔴 choice) — **route (ii), interface form**

Following `docs/formalization-plan.md` §B3c, we do **not** formalize Labute's abstract
dualizing-module characterization of `χ` (his Prop. 6 — route (i), a stretch goal); instead we
state the **interface** the paper's Lemmas 3.4/3.5 actually consume: there is a choice of B4
isomorphism `ψ : G_{ℚ₂}(2) ≅ D₀` under which the descended cyclotomic character takes the
Theorem 4(2) values on the marked generators `A, S, Y`.  **Deviation flagged**: only the
interface ships; "`χ_D` is *the canonical* orientation in Labute's abstract sense" is not
formalized (route (i) remains open; the classification statement B3b correspondingly stays at
the field level — see T-10's note in `docs/tickets.md`).

## The bundle

`DyadicOrientation` packages:
* `equiv : G_{ℚ₂}(2) ≅ D₀` — a B4 isomorphism (existence alone is axiom B4; the orientation
  axiom strengthens it with the value normalization);
* `chiTwo : G_{ℚ₂}(2) →* ℤ₂ˣ` continuous with `chiTwo ∘ π = χ_cyc` — the **descent** of the
  cyclotomic character through the maximal pro-2 quotient.  (The descent exists because `ℤ₂ˣ`
  is pro-2 — `(ℤ/2^k)ˣ` has order `2^{k−1}` — so `χ_cyc` kills the pro-2 kernel by T-05's
  `proPKernel_le_ker`; carrying it as data avoids formalizing `IsProP 2 ℤ₂ˣ`, an O-finish
  refinement flagged below);
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
  /-- A B4 isomorphism `G_{ℚ₂}(2) ≅ D₀` (its existence alone is axiom B4). -/
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
  simp only [commP, map_mul, map_inv]
  rw [mul_comm (f x)⁻¹ (f y)⁻¹]
  group

section StressTests

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (O : DyadicOrientation)

/-- **Consistency of the orientation values with the Demushkin relation**: pushing
`A²S⁴[S,Y] = 1` through `χ` gives `(−1)² · 1⁴ · 1 = 1` — the value assignment of Theorem 4(2)
respects the relator.  (Derived from the bundle, not assumed.) -/
theorem orientation_values_consistent :
    O.chiTwo (O.equiv.symm d0A) ^ 2 * O.chiTwo (O.equiv.symm d0S) ^ 4
      * commP (O.chiTwo (O.equiv.symm d0S)) (O.chiTwo (O.equiv.symm d0Y)) = 1 := by
  rw [O.chi_A, O.chi_S]
  have hcomm : commP (1 : ℤ_[2]ˣ) (O.chiTwo (O.equiv.symm d0Y)) = 1 := by
    simp [commP]
  rw [hcomm, neg_one_sq, one_pow, one_mul, mul_one]

/-- The relation-consistency check, direct route: `χ ∘ ψ⁻¹` is a homomorphism out of `D₀`, so
the relator `d0_relation` maps to `1` outright — matching `orientation_values_consistent`. -/
theorem orientation_relator_maps_to_one :
    O.chiTwo (O.equiv.symm (d0A ^ 2 * d0S ^ 4 * commP d0S d0Y)) = 1 := by
  rw [d0_relation, map_one, map_one]

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

/-- Lifts of the generators exist (the projection is onto), so the two readings above are
non-vacuous. -/
theorem exists_lift_A : ∃ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = O.equiv.symm d0A :=
  quotientMk_surjective _ _

end StressTests

end GQ2
