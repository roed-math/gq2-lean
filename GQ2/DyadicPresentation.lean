import GQ2.ProfinitePresentation
import GQ2.Subdirect

/-!
# B4: the rank-3 dyadic Demushkin presentation `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩`  (ticket T-08)

The paper's Prop. 1.1 / Lemma 3.4 normalizes the maximal pro-2 quotient `G_{ℚ₂}(2)` as the
**Demushkin group** `D₀ = ⟨A, S, Y | A²S⁴[S,Y] = 1⟩` (Labute's classification at `d = 1`).  This file
constructs `D₀` as a `GQ2.profinitePresentation` and provides the relator; the actual isomorphism
`G_{ℚ₂}(2) ≅ D₀` is axiom **B4** in `GQ2/Foundations/Axioms.lean`.

* `GQ2.d0Relator : FreeProfiniteGroup (Fin 3)` — the relator `A²S⁴[S,Y]` with `A = of 0`, `S = of 1`,
  `Y = of 2`, commutator `[S,Y] = S⁻¹Y⁻¹SY` (the paper's `commP`, `GQ2/Words.lean`).  It is
  `ω₂`-free, hence a bare word in the free profinite group on three generators.
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

/-- **`D₀`** (paper Prop. 1.1): the profinite group presented by `⟨A, S, Y | A²S⁴[S,Y] = 1⟩`, i.e.
the free profinite group on `Fin 3` modulo the closed normal closure of `d0Relator`.  This is the
rank-3 dyadic Demushkin group; axiom **B4** asserts `G_{ℚ₂}(2) ≅ D₀`. -/
noncomputable def D0 : ProfiniteGrp := profinitePresentation {d0Relator}

/-- The relator holds in `D₀`: `A²S⁴[S,Y] = 1` in the presented group. -/
theorem d0Relator_quotientMk_eq_one :
    quotientMk (relatorSubgroup {d0Relator}) d0Relator = 1 :=
  relator_quotientMk_eq_one {d0Relator} rfl

/-! ## Stress test: a concrete finite 2-group marking (`homEquiv` + `decide`)

`DihedralGroup 4` is a non-abelian group of order `8 = 2³`.  The marking `A ↦ sr 0` (a reflection,
order 2), `S ↦ r 1` (a rotation of order 4), `Y ↦ r 2` satisfies `A² = S⁴ = 1` and `[S,Y] = 1`
(rotations commute), so the relator dies — witnessing that `A²S⁴[S,Y] = 1` is realizable in a
genuine finite 2-group. -/

section StressTest

local instance : TopologicalSpace (DihedralGroup 4) := ⊥
local instance : DiscreteTopology (DihedralGroup 4) := ⟨rfl⟩

/-- A concrete marking `Fin 3 → DihedralGroup 4`: `A ↦ sr 0`, `S ↦ r 1`, `Y ↦ r 2`. -/
def markD4 : Fin 3 → DihedralGroup 4 :=
  ![DihedralGroup.sr 0, DihedralGroup.r 1, DihedralGroup.r 2]

/-- The continuous hom `F₃ ⟶ DihedralGroup 4` classified by `markD4` (universal property of the
free profinite group, inverted). -/
noncomputable def homD4 : FreeProfiniteGroup (Fin 3) ⟶ ProfiniteGrp.of (DihedralGroup 4) :=
  (FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of (DihedralGroup 4))).symm markD4

/-- `homD4` sends each generator `of i` to `markD4 i` (the universal property is "restrict to the
generators"). -/
@[simp] theorem homD4_toMonoidHom_of (i : Fin 3) :
    homD4.hom.toMonoidHom (FreeProfiniteGroup.of i) = markD4 i :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- The relator `A²S⁴[S,Y]` maps to `1` under `homD4`: the marking satisfies the Demushkin relation
in `DihedralGroup 4` (checked by `decide`). -/
theorem homD4_d0Relator : homD4.hom.toMonoidHom d0Relator = 1 := by
  simp only [d0Relator, map_mul, map_pow, Marking.map_commP]
  rw [homD4_toMonoidHom_of, homD4_toMonoidHom_of, homD4_toMonoidHom_of]
  decide

end StressTest

end GQ2
