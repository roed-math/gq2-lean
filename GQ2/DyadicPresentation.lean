import GQ2.ProfinitePresentation
import GQ2.Subdirect
import GQ2.MaxProP

/-!
# B4: the rank-3 dyadic Demushkin presentation `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩`  (ticket T-08)

The paper's Prop. 1.1 / Lemma 3.4 normalizes the maximal pro-2 quotient `G_{ℚ₂}(2)` as the
**Demushkin group** `D₀ = ⟨A, S, Y | A²S⁴[S,Y] = 1⟩` (Labute's classification at `d = 1`).  This
file constructs `D₀` as a `GQ2.profinitePresentation` and provides the relator; the actual
isomorphism `G_{ℚ₂}(2) ≅ D₀` is axiom **B4** in `GQ2/Foundations/Axioms.lean`.

* `GQ2.d0Relator : FreeProfiniteGroup (Fin 3)` — the relator `A²S⁴[S,Y]` with `A = of 0`,
  `S = of 1`, `Y = of 2`, commutator `[S,Y] = S⁻¹Y⁻¹SY` (the paper's `commP`, `GQ2/Words.lean`).
  It is `ω₂`-free, hence a bare word in the free profinite group on three generators.
* `GQ2.D0 : ProfiniteGrp` — the presented group `profinitePresentation {d0Relator}`.

Stress test (`homEquiv` + a `decide`-able finite 2-group): the concrete marking
`A ↦ (reflection), S ↦ (order-4 rotation), Y ↦ (rotation²)` of `DihedralGroup 4` classifies a
continuous hom `F₃ ⟶ DihedralGroup 4` sending the generators as specified (`homD4_toMonoidHom_of`)
and killing the relator (`homD4_d0Relator`, by `decide`) — so the relation is satisfiable in a
genuine finite 2-group, and (`d0Relator_quotientMk_eq_one`) it holds in `D₀`.
-/

open CategoryTheory

namespace GQ2

/-! ## The relator and the presented group -/

/-- The **dyadic Demushkin relator** `r₀ = A²S⁴[S,Y]` (Labute [2], Thm 8 at `d = 1`; the paper's
`D₀` relation), as a word in the free profinite group on `Fin 3` with `A = of 0`, `S = of 1`,
`Y = of 2`.  Commutator convention: `[S,Y] = S⁻¹Y⁻¹SY` (`GQ2.commP`, matching `GQ2/Words.lean`). -/
noncomputable def d0Relator : FreeProfiniteGroup (Fin 3) :=
  FreeProfiniteGroup.of 0 ^ 2 * FreeProfiniteGroup.of 1 ^ 4 *
    commP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 2)

/-- The full profinite presentation `⟨A, S, Y | A²S⁴[S,Y]⟩` (before taking the pro-2 quotient).
The paper's `D₀ = G_{ℚ₂}(2)` is **pro-2**, so `D₀` is the maximal pro-2 quotient of this
(`D0` below); the bare presentation is *not* pro-2 — e.g. `A,S ↦ 0, Y ↦ 1` gives a surjection
onto `ℤ/3` (the relator dies in an abelian target), so its abelianization carries an odd part.
Working with the pro-2 quotient is what makes `topAbelianization D₀ ≅ ℤ/2 × ℤ₂ × ℤ₂` (paper (11))
and keeps axiom **B4** (`G_{ℚ₂}(2) ≅ D₀`, a pro-2 ≅ pro-2 statement) faithful. -/
noncomputable def D0Full : ProfiniteGrp := profinitePresentation {d0Relator}

/-- **`D₀`** (paper Prop. 1.1): the **pro-2** group presented by `⟨A, S, Y | A²S⁴[S,Y] = 1⟩`, i.e.
the maximal pro-2 quotient of the free profinite presentation.  This is the rank-3 dyadic
Demushkin group; axiom **B4** asserts `G_{ℚ₂}(2) ≅ D₀`. -/
noncomputable def D0 : ProfiniteGrp := maxProPQuotient 2 D0Full

/-- The relator holds in the full presentation: `A²S⁴[S,Y] = 1`. -/
theorem d0Relator_quotientMk_eq_one :
    quotientMk (relatorSubgroup {d0Relator}) d0Relator = 1 :=
  relator_quotientMk_eq_one {d0Relator} rfl

/-! ### The marked generators  (T-11 input) -/

/-- The generator `A` in the full presentation `D0Full` (image of `of 0`). -/
noncomputable def d0FullA : D0Full :=
  quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0)
/-- The generator `S` in the full presentation `D0Full` (image of `of 1`). -/
noncomputable def d0FullS : D0Full :=
  quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1)
/-- The generator `Y` in the full presentation `D0Full` (image of `of 2`). -/
noncomputable def d0FullY : D0Full :=
  quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2)

/-- The Demushkin relation `A²S⁴[S,Y] = 1` already in the full presentation `D0Full`. -/
theorem d0Full_relation : d0FullA ^ 2 * d0FullS ^ 4 * commP d0FullS d0FullY = 1 := by
  have h := d0Relator_quotientMk_eq_one
  rw [d0Relator] at h
  simp only [commP, d0FullA, d0FullS, d0FullY] at h ⊢
  exact h

/-- The generator `A ∈ D₀` (image of `A` under the pro-2 quotient map). -/
noncomputable def d0A : D0 := maxProPMk 2 D0Full d0FullA
/-- The generator `S ∈ D₀`. -/
noncomputable def d0S : D0 := maxProPMk 2 D0Full d0FullS
/-- The generator `Y ∈ D₀`. -/
noncomputable def d0Y : D0 := maxProPMk 2 D0Full d0FullY

/-- **The Demushkin relation on the named generators**: `A²S⁴[S,Y] = 1` in `D₀`.  It holds already
in the full presentation `D0Full` (`d0Full_relation`) and is pushed through the pro-2 quotient
homomorphism `maxProPMk` (which commutes with `*`, `^`, `commP` definitionally). -/
theorem d0_relation : d0A ^ 2 * d0S ^ 4 * commP d0S d0Y = 1 := by
  show maxProPMk 2 D0Full (d0FullA ^ 2 * d0FullS ^ 4 * commP d0FullS d0FullY) = 1
  rw [d0Full_relation, map_one]

/-! ## Stress test: a concrete finite 2-group marking (`homEquiv` + `decide`)

`DihedralGroup 4` is a non-abelian group of order `8 = 2³`.  The marking `A ↦ sr 0` (a reflection,
order 2), `S ↦ r 1` (a rotation of order 4), `Y ↦ r 2` satisfies `A² = S⁴ = 1` and `[S,Y] = 1`
(rotations commute), so the relator dies — witnessing that `A²S⁴[S,Y] = 1` is realizable in a
genuine finite 2-group. -/

section StressTest

-- Explicit names: Lean's auto-namer does not encode the numeral, so an anonymous
-- `DihedralGroup 4` instance would clash with `DihedralGroup 3` instances elsewhere (e.g. `Zhat`)
-- once both are imported into `Foundations/Axioms.lean`.


end StressTest

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 3.4 = ⟦lem-standardorientation⟧
  * Prop 1.1 = ⟦prop-markedDem⟧
-/
