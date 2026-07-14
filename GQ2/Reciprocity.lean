import Mathlib
import GQ2.Statement

/-!
# B5: the local reciprocity bundle for `ℚ₂`  (ticket T-17)

This file states the paper's **local class field theory** input (leaf **B5**) as a single bundled
axiom: the existence of the arithmetic local reciprocity map `rec` and the unramified coordinate
`ν_ur`, satisfying the norm-residue property together with the two *normalizations* that the paper
fixes in Lemma 3.5 / equation (13).

Everything here is a **statement** (definitions + one axiom + stress tests); nothing about
reciprocity is *proved* (that is local CFT, absent from Mathlib — see
`docs/mathlib-cft-survey.md`, §B5).  The axiom asserts that the reciprocity data exists; the
stress tests below *derive the paper's equation (13) from it*, so a human reviewer can check the
bundle reproduces the paper's orientation/valuation rows without trusting the proof of reciprocity
itself.

## The bundle (paper Lemma 3.5, eq. (13); Prop. 1.1)

`LocalReciprocity` packages continuous homomorphisms
* `rec  : ℚ₂ˣ →* G_{ℚ₂}^{ab}`  (dense image), and
* `ν_ur : G_{ℚ₂}^{ab} →* Multiplicative ℤ₂`  (continuous, surjective),

subject to the three clauses of the plan (`docs/formalization-plan.md`, §B5):

* **(a) norm residue.** For every *finite abelian* `L/ℚ₂` inside `ℚ̄₂`, the induced map
  `ℚ₂ˣ → Gal(L/ℚ₂)` (i.e. `rec` followed by the abelianized restriction `restrictAb`) is surjective
  with kernel exactly the norm subgroup `N_{L/ℚ₂}(Lˣ)` (`normSubgroup`).  This is the
  class-formation reciprocity of **NSW [1] (7.1.1)/(7.1.5)** (finite-level
  `Gal(L/ℚ₂) ≅ ℚ₂ˣ / N Lˣ`), and is aligned with the finite-level shape of the Oxford
  ClassFieldTheory project blueprint (this repo's `ClassFieldTheory` git dependency).
* **(b) unramified normalization.** `ν_ur ∘ rec = −v₂` (`nu_ur_rec`).  Equivalently
  `ν_ur(rec 2) = −1`: `rec` sends the uniformizer `2` to *arithmetic* Frobenius, while `ν_ur` is
  normalized so that *geometric* Frobenius `= arithmetic⁻¹` has coordinate `+1` (paper's standing
  convention, line "νur is normalized geometrically"; Lemma 3.5 proof).  Reproduces
  `ν_ur(ā,s̄,ȳ) = (−2,1,0)` of (13).
* **(c) cyclotomic orientation.** `χ_cyc ∘ rec = (·)⁻¹` on units (`chiCyc_rec_unit`) and
  `χ_cyc(rec 2) = 1` (`chiCyc_rec_uniformizer`: the uniformizer acts trivially on the totally
  ramified `ℚ₂(μ_{2^∞})/ℚ₂`).  Here `χ_cyc` is **Mathlib's own** `cyclotomicCharacter … 2`
  (§clause (c) is a *convention check against the real cyclotomic character*, not an abstract
  one).  Reproduces `χ_D(ā,s̄,ȳ) = (−1,1,(−3)⁻¹)` of (13), because `χ_D = χ_cyc` for a local
  Demushkin group.

## Convention table (the #1 human-review target)

* `rec` — Lean object `LocalReciprocity.rec` — **arithmetic**: `rec(2) =` arithmetic Frobenius;
  `rec` a continuous hom into `G^{ab}` with dense image
* `ν_ur` — Lean object `LocalReciprocity.nu_ur` — **geometric**: `ν_ur(geom. Frob) = +1`, so
  `ν_ur(arith. Frob) = −1`; target `Multiplicative ℤ₂`
* `v₂` — Lean object `GQ2.v2` — `Padic.valuation`, so `v₂(2) = 1`, `v₂(unit) = 0`; clause (b) is
  `ν_ur∘rec = −v₂`
* `χ_cyc` — Lean object `GQ2.chiCyc` / `chiCycAb` — Mathlib
  `cyclotomicCharacter (AlgebraicClosure ℚ₂) 2 : g ↦ (ζ ↦ ζ^{χ(g)})`; values in `ℤ₂ˣ`
* `G^{ab}` — Lean object `GQ2.AbsGalQ2ab` — Mathlib
  `absoluteGaloisGroupAbelianization ℚ₂ = G ⧸ closure⁅G,G⁆` (topological abelianization)
* `x^g`, `[x,y]` — (inherited) — `x^g = g⁻¹xg`, `[x,y] = x⁻¹y⁻¹xy` (paper's standing conventions)

**Soundness note (a real trap, cf. the `Nat.card` bug).** `ν_ur` **must** target a *profinite* group
(`ℤ₂`), never `ℤ`: `G^{ab}` is compact, and a continuous hom from a compact group to *discrete* `ℤ`
is forced trivial — so clause (b) with target `ℤ` would be *inconsistent* (the axiom would prove
`False`).  Targeting `Multiplicative ℤ₂` (with `−v₂` embedded via `ℤ ↪ ℤ₂`) is what makes the bundle
consistent.

**Deviations flagged for review.**
* Injectivity of `rec` (true in the literature) is *not* asserted; it follows from clause (a) as `L`
  ranges over all finite abelian extensions (`⋂_L N_{L/ℚ₂}Lˣ = 1`).  We keep the bundle minimal.
* `ν_ur`, `χ_cyc` and the per-`L` restrictions are stated on the **topological abelianization**
  `G^{ab}`; `rec` lands there (its image is abelian).  `χ_cyc`/`restrictAb` factor Mathlib's
  full-group `chiCyc`/`restrictNormalHom` through `G^{ab}` (`chiCycAb_toAb`, `restrictAb_toAb`).

References: [1] Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.1.1)/(7.1.5)
(class formation ⇒ local reciprocity); [7] Serre, *Local Fields*, Ch. XI–XIII.  Paper: Turturean,
Lemma 3.5, eq. (13); Prop. 1.1.  Ticket: `docs/tickets.md` T-17.

*Note:* the axiom `GQ2.localReciprocity` itself lives in `GQ2/Foundations/Axioms.lean` (T-19
consolidation); this file holds the bundle *definition* and the axiom-free, bundle-parametrized
stress tests.
-/

open scoped Classical

namespace GQ2

noncomputable section

/-! ## The abelianized absolute Galois group and the maps out of it -/

/-- `G_{ℚ₂}^{ab}`, the **topological abelianization** of `G_{ℚ₂}`, i.e. Mathlib's
`Field.absoluteGaloisGroupAbelianization ℚ₂ = G_{ℚ₂} ⧸ closure⁅G_{ℚ₂}, G_{ℚ₂}⁆`.  This is the
genuine `Gal(ℚ₂^{ab}/ℚ₂)`; it is a topological (indeed profinite, though we do not need that)
`CommGroup`. -/
noncomputable abbrev AbsGalQ2ab : Type := Field.absoluteGaloisGroupAbelianization ℚ_[2]

/-- The closed commutator subgroup `closure⁅G_{ℚ₂}, G_{ℚ₂}⁆`;
`AbsGalQ2ab = AbsGalQ2 ⧸ commClosure`. -/
noncomputable abbrev commClosure : Subgroup AbsGalQ2 := (commutator AbsGalQ2).topologicalClosure

/-- The abelianization projection `G_{ℚ₂} ↠ G_{ℚ₂}^{ab}`. -/
noncomputable def toAb : AbsGalQ2 →* AbsGalQ2ab := QuotientGroup.mk' commClosure

/-! ### The 2-adic cyclotomic character on `G_{ℚ₂}` and its abelianization -/

/-- The 2-adic cyclotomic character `χ_cyc : G_{ℚ₂} →* ℤ₂ˣ`, `g ↦ (ζ ↦ ζ^{χ(g)})` on
`μ_{2^∞} ⊂ ℚ̄₂`.  This is **Mathlib's** `cyclotomicCharacter`, precomposed with the Galois action on
`ℚ̄₂`; clause (c) checks `rec` against exactly this map. -/
noncomputable def chiCyc : AbsGalQ2 →* ℤ_[2]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure ℚ_[2]) 2).comp
    (MulSemiringAction.toRingAut
      (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]) (AlgebraicClosure ℚ_[2]))

lemma continuous_chiCyc : Continuous chiCyc :=
  cyclotomicCharacter.continuous 2 ℚ_[2] (AlgebraicClosure ℚ_[2])

/-- `χ_cyc` kills the closed commutator subgroup (its target `ℤ₂ˣ` is a Hausdorff abelian group), so
it factors through `G_{ℚ₂}^{ab}`. -/
lemma commClosure_le_ker_chiCyc : commClosure ≤ chiCyc.ker := by
  apply Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker chiCyc)
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage continuous_chiCyc

/-- The cyclotomic character as a map out of the abelianization, `χ_cyc : G_{ℚ₂}^{ab} →* ℤ₂ˣ`. -/
noncomputable def chiCycAb : AbsGalQ2ab →* ℤ_[2]ˣ :=
  QuotientGroup.lift commClosure chiCyc
    (fun _ hx => MonoidHom.mem_ker.mp (commClosure_le_ker_chiCyc hx))

/-- **Stress test (`chiCycAb`):** `chiCycAb` factors `chiCyc` through the abelianization. -/
@[simp] lemma chiCycAb_toAb (g : AbsGalQ2) : chiCycAb (toAb g) = chiCyc g := rfl

/-! ### The 2-adic valuation on `ℚ₂ˣ` -/

/-- The 2-adic valuation `v₂ : ℚ₂ˣ → ℤ` of a unit of `ℚ₂` (`Padic.valuation`).  `v₂(2) = 1`,
`v₂(u) = 0` for a `ℤ₂`-unit `u`. -/
noncomputable def v2 (x : ℚ_[2]ˣ) : ℤ := Padic.valuation (x : ℚ_[2])

/-! ### Norm subgroups and the abelianized restriction to a finite layer -/

/-- The **norm subgroup** `N_{L/ℚ₂}(Lˣ) ≤ ℚ₂ˣ` of a finite layer `L/ℚ₂`: the image of the field norm
`Algebra.norm ℚ₂ : L →* ℚ₂` on units. -/
noncomputable def normSubgroup (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] : Subgroup ℚ_[2]ˣ :=
  (Units.map (Algebra.norm ℚ_[2] (S := L))).range

/-- Mathlib's `AlgEquiv.restrictNormalHom` for the layer `L/ℚ₂`, but with its domain presented as
`AbsGalQ2` (`= Field.absoluteGaloisGroup ℚ₂`) rather than the raw `AlgClosure ≃ₐ AlgClosure`.  These
are definitionally the same group, but the two carry *different* registered `Group` instances
(`Field.instGroupAbsoluteGaloisGroup` vs `AlgEquiv.aut`); pinning the domain to `AbsGalQ2` keeps the
`commutator`/abelianization machinery (which lives on `AbsGalQ2`) and Mathlib's restriction on the
same instance path. -/
noncomputable def restrictHom (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] :
    AbsGalQ2 →* (L ≃ₐ[ℚ_[2]] L) :=
  AlgEquiv.restrictNormalHom L

/-- For a finite **abelian** Galois layer `L/ℚ₂`, the restriction `G_{ℚ₂} → Gal(L/ℚ₂)` kills the
closed commutator subgroup, hence factors through `G_{ℚ₂}^{ab}`. -/
lemma commClosure_le_ker_restrictHom
    (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) :
    commClosure ≤ (restrictHom L).ker := by
  apply Subgroup.topologicalClosure_minimal
  · rw [show commutator AbsGalQ2 = ⁅(⊤ : Subgroup AbsGalQ2), ⊤⁆ from rfl, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hab _ _
  · exact IntermediateField.restrictNormalHom_ker L ▸ IntermediateField.fixingSubgroup_isClosed L

/-- The **abelianized restriction** `G_{ℚ₂}^{ab} → Gal(L/ℚ₂)` for a finite abelian Galois layer
`L/ℚ₂` (obtained by factoring Mathlib's `restrictNormalHom` through the abelianization). -/
noncomputable def restrictAb (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) :
    AbsGalQ2ab →* (L ≃ₐ[ℚ_[2]] L) :=
  QuotientGroup.lift commClosure (restrictHom L)
    (fun _ hx => MonoidHom.mem_ker.mp (commClosure_le_ker_restrictHom L hab hx))

/-- **Stress test (`restrictAb`):** `restrictAb` factors the restriction through the
abelianization. -/
@[simp] lemma restrictAb_toAb (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) (g : AbsGalQ2) :
    restrictAb L hab (toAb g) = restrictHom L g := rfl

/-! ### Embedding `ℤ₂ˣ` and the uniformizer into `ℚ₂ˣ` -/

/-- A `ℤ₂`-unit as a `ℚ₂`-unit, `ℤ₂ˣ ↪ ℚ₂ˣ`. -/
noncomputable def unitEmbed : ℤ_[2]ˣ →* ℚ_[2]ˣ :=
  Units.map (algebraMap ℤ_[2] ℚ_[2]).toMonoidHom

@[simp] lemma unitEmbed_val (u : ℤ_[2]ˣ) :
    ((unitEmbed u : ℚ_[2]ˣ) : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (u : ℤ_[2]) := rfl

/-- The uniformizer `2 ∈ ℚ₂ˣ`. -/
noncomputable def uniformizer : ℚ_[2]ˣ := Units.mk0 (2 : ℚ_[2]) (by norm_num)

@[simp] lemma uniformizer_val : (uniformizer : ℚ_[2]) = 2 := rfl

/-! ## The reciprocity bundle -/

/-- **B5 (local reciprocity for `ℚ₂`), the bundle.**  The arithmetic reciprocity map `rec` and the
geometric unramified coordinate `ν_ur`, with the three normalizing clauses (a)/(b)/(c).  See the
module docstring for the convention table and paper cross-references (Lemma 3.5, eq. (13)). -/
structure LocalReciprocity where
  /-- The arithmetic local reciprocity map `rec : ℚ₂ˣ →* G_{ℚ₂}^{ab}` (named `recip` to avoid the
  auto-generated recursor `LocalReciprocity.rec`). -/
  recip : ℚ_[2]ˣ →* AbsGalQ2ab
  /-- `rec` is continuous. -/
  continuous_recip : Continuous recip
  /-- `rec` has dense image (local CFT: `G^{ab}` is the profinite completion of `ℚ₂ˣ`). -/
  denseRange_recip : DenseRange recip
  /-- The unramified coordinate `ν_ur : G_{ℚ₂}^{ab} →* Multiplicative ℤ₂` (target profinite — see
  the soundness note). -/
  nu_ur : AbsGalQ2ab →* Multiplicative ℤ_[2]
  /-- `ν_ur` is continuous. -/
  continuous_nu_ur : Continuous nu_ur
  /-- `ν_ur` is surjective (`ν_ur : D ↠ ℤ₂` in the paper). -/
  surjective_nu_ur : Function.Surjective nu_ur
  /-- **(a) norm residue.** For every finite abelian Galois layer `L/ℚ₂`, the induced
  `ℚ₂ˣ → Gal(L/ℚ₂)` is surjective with kernel the norm subgroup `N_{L/ℚ₂}(Lˣ)`.
  [NSW (7.1.1)/(7.1.5)] -/
  norm_reciprocity : ∀ (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
      [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
      (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ),
      Function.Surjective ((restrictAb L hab).comp recip) ∧
        ((restrictAb L hab).comp recip).ker = normSubgroup L
  /-- **(b) unramified normalization.** `ν_ur ∘ rec = −v₂`.
  [paper (13): `ν_ur(ā,s̄,ȳ)=(−2,1,0)`] -/
  nu_ur_recip : ∀ x : ℚ_[2]ˣ,
      nu_ur (recip x) = Multiplicative.ofAdd ((-(v2 x) : ℤ) : ℤ_[2])
  /-- **(c) cyclotomic orientation, units.** `χ_cyc(rec u) = u⁻¹` for `u ∈ ℤ₂ˣ`.
  [paper (13): `χ_D(ȳ) = (−3)⁻¹`] -/
  chiCyc_recip_unit : ∀ u : ℤ_[2]ˣ, chiCycAb (recip (unitEmbed u)) = u⁻¹
  /-- **(c) cyclotomic orientation, uniformizer.** `χ_cyc(rec 2) = 1` (uniformizer trivial on the
  totally ramified `ℚ₂(μ_{2^∞})/ℚ₂`).  [paper (13): needed for `χ_D(ā) = −1`] -/
  chiCyc_recip_uniformizer : chiCycAb (recip uniformizer) = 1

/- The B5 axiom `GQ2.localReciprocity : LocalReciprocity` lives in
`GQ2/Foundations/Axioms.lean` (consolidated there by T-19). -/

/-! ## Stress tests: the bundle reproduces the paper's equation (13)

Each theorem below is stated for an *arbitrary* `R : LocalReciprocity` (so it exercises the bundle's
clauses, not the axiom, and stays at the standard three axioms).  Together they recompute the
`(ν_ur, χ_D)` rows of Lemma 3.5's equation (13) for `s̄ = rec(2)⁻¹`, `ā = rec(−4)`,
`ȳ = rec(−3)`. -/

section StressTests

variable (R : LocalReciprocity)

/-- `−4 ∈ ℚ₂ˣ`, the class `ā` of (13). -/
private noncomputable def uNeg4 : ℚ_[2]ˣ := Units.mk0 (-4 : ℚ_[2]) (by norm_num)

/-- `−3 ∈ ℚ₂ˣ`, the class `ȳ` of (13). -/
private noncomputable def uNeg3 : ℚ_[2]ˣ := Units.mk0 (-3 : ℚ_[2]) (by norm_num)

/-- **(b) at the uniformizer — the arithmetic-Frobenius normalization.** `ν_ur(rec 2) = −1`:
`rec` sends the uniformizer to arithmetic Frobenius, whose geometric coordinate is `−1`. -/
theorem nu_ur_recip_uniformizer :
    R.nu_ur (R.recip uniformizer) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
  rw [R.nu_ur_recip]
  norm_num [v2, uniformizer, Padic.valuation_p]

/-- **(b), `ā` row of (13):** `ν_ur(rec(−4)) = −2`. -/
theorem nu_ur_recip_neg4 :
    R.nu_ur (R.recip uNeg4) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2]) := by
  have hv : v2 uNeg4 = 2 := by
    simp only [v2, uNeg4, Units.val_mk0]
    rw [show (-4 : ℚ_[2]) = ((-4 : ℤ) : ℚ_[2]) by push_cast; ring, Padic.valuation_intCast,
      padicValInt, show (-4 : ℤ).natAbs = 2 ^ 2 from rfl, padicValNat.prime_pow]
    norm_cast
  rw [R.nu_ur_recip, hv]

/-- **(b), `ȳ` row of (13):** `ν_ur(rec(−3)) = 0` (`−3` is a unit). -/
theorem nu_ur_recip_neg3 :
    R.nu_ur (R.recip uNeg3) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2]) := by
  have hv : v2 uNeg3 = 0 := by
    simp only [v2, uNeg3, Units.val_mk0]
    rw [show (-3 : ℚ_[2]) = ((-3 : ℤ) : ℚ_[2]) by push_cast; ring, Padic.valuation_intCast]
    simp [padicValInt]
  rw [R.nu_ur_recip, hv]
  norm_num

/-- **(c), `ā` row of (13) — the flagship orientation check:** `χ_cyc(rec(−4)) = −1`.
Here `−4 = (−1)·2²`, so `χ_cyc(rec(−4)) = χ_cyc(rec(−1))·χ_cyc(rec 2)² = (−1)⁻¹·1 = −1`, using
clause (c) on the unit `−1` and clause (c) on the uniformizer. -/
theorem chiCyc_recip_neg4 : chiCycAb (R.recip uNeg4) = (-1 : ℤ_[2]ˣ) := by
  have hdecomp : uNeg4 = unitEmbed (-1) * uniformizer ^ 2 := by
    ext
    simp only [uNeg4, uniformizer, Units.val_mul, Units.val_pow_eq_pow_val, unitEmbed_val,
      Units.val_mk0, Units.val_neg, Units.val_one, map_neg, map_one]
    ring
  rw [hdecomp, map_mul, map_pow, map_mul, map_pow, R.chiCyc_recip_unit, R.chiCyc_recip_uniformizer]
  simp

/-- **(c), `ȳ` row of (13):** `χ_cyc(rec(−3)) = (−3)⁻¹`, with `−3` viewed as a `ℤ₂`-unit. -/
theorem chiCyc_recip_neg3 (u : ℤ_[2]ˣ) (hu : (u : ℤ_[2]) = -3) :
    chiCycAb (R.recip uNeg3) = u⁻¹ := by
  have hval : uNeg3 = unitEmbed u := by
    ext
    simp only [uNeg3, Units.val_mk0, unitEmbed_val, hu, map_neg, map_ofNat]
  rw [hval, R.chiCyc_recip_unit]


end StressTests

end

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (13) = ⟦eq-localmarkingorientation⟧
  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Prop 1.1 = ⟦prop-markedDem⟧
-/
