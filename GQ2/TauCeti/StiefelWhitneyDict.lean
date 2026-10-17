/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Identities
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2
public import GQ2.TraceForm
public import GQ2.TauCeti.GaloisDict
public import GQ2.TauCeti.CohomologyDict

@[expose] public section

/-!
# The Stiefel–Whitney dictionary between gq2 and Tau Ceti (ticket B9)

Ticket **B9** of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon
memo `docs/orchestration/tauceti-t2-recon.md` §B9).  This file is the dictionary that lets
`GQ2/TauCeti/B9.lean` rewrite Tau Ceti's relative Stiefel–Whitney identities
(`TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer`,
`TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer`) into the
`relativeStiefelWhitney_dyadic` field of `GQ2.LiteratureInputs`.  Everything lives in
`GQ2.TauCetiBridge`; Tau Ceti names are fully qualified.

## Contents

* **Binary forms** (`GQ2.swOne`/`swTwo` against Tau Ceti's `sw1`/`sw2` on diagonal
  presentations): `diagForm_eq_weightedSumSquares`,
  `isDiagonalization_iff_equivalent_weightedSumSquares` (gq2's `⟨x, y⟩` is Tau Ceti's
  `weightedSumSquares ↥k ![x, y]`), `swOne_eq_of_exists`/`swTwo_eq_of_exists` (gq2's classes
  on their *chosen* diagonalization, by `dite_eq_left`; no `hnorm`), the trace forms
  `traceFormOne_eq_traceTransfer_sq`, `traceFormTwisted_eq_traceTransfer_smul_sq`
  (`Tr⟨1⟩ = Tr_*⟨1⟩`, `Tr⟨a⟩ = Tr_*⟨a⟩` with `L = ↥(quadExt k δ)` itself), and the existence
  of diagonalizations `exists_isDiagonalization_traceFormTwisted`.
* **Cochains** (`GQ2/EvensKahn.lean` eqs. (97)–(98) against Tau Ceti's `Evens/Cochain.lean`),
  pointwise along any homomorphism `φ : G →* G'` carrying `U` onto `U'` and `α` onto `α'`:
  `evensAux_eq_evensB1`, `bS_eq_evensBs`, `corFun_eq_evensCorCochain`,
  `evensNormFun_eq_evensGraphCochain`.
* **Explicit classes**: along a continuous `Φ : G →ₜ* G'`, Tau Ceti's class of the Shapiro sum
  `evensCorCocycle` pulls back to `cont1F2 _ htriv (GQ2.corH1 …)`
  (`trivialF2Map_evensCorCocycle`) and `evensGraphCochainClass` to
  `cont2F2 _ htriv (GQ2.evensNormH2 …)` (`trivialF2Map_evensGraphCochainClass`).
* **Fields**: for a quadratic `L/K` with a root `r` of `σ a`, `galoisCor K L σ 1 (kummerClass a)`
  is the class of `evensCorCocycle` of the Kummer character at any `s ∉ G_L`
  (`galoisCor_kummerClass_eq_evensCorCocycle`) and `galoisEvens K L σ hL (kummerClass a)` the
  class `evensGraphCochainClass` (`galoisEvens_kummerClass_eq_evensGraphCochainClass`).
* **The dyadic case** at A1's `(Φ, e) = (fixingEquivAbsGal k, sepClosureEquiv k)`,
  `σ = layerEmb k (quadExt k δ)`, `r = e⁻¹ β`: `rootSign_sepClosureEquiv_symm` (Tau Ceti's root
  sign is gq2's `kummerCocycleFun`), `toAdd_galoisKummerCharacter_fixingEquivAbsGal`, and the
  two headline dictionary entries `trivialF2Map_galoisCor_kummerClass` (`corH1` vs `galoisCor`)
  and `trivialF2Map_galoisEvens_kummerClass` (`evensNormH2` vs `galoisEvens`).
* `trivialF2Map_cup_one_one`: Tau Ceti's `trivialF2Map_cup` in bidegree `(1, 1)` with the
  target degree written `2`.

## Conventions

The B9 field has no `σ`: Tau Ceti's embedding is A1's `layerEmb k (quadExt k δ)`, so no B11a
input is needed.  Transport along `Φ` is always the pointwise route (membership `iff` plus
values), never a subgroup-equality cast (memo §B9, translation 6).

Proof engineering (memo §B9, pitfalls, and `GQ2/TauCeti/B9.lean`): `rw` is avoided on terms
of Tau Ceti's `continuousCohomology`: its `kabstract` runs `isDefEq` against every `⇑f t`
subterm, and comparing `?a + ?b` or `cont1F2 _ _ (kummerClassK k ?u)` with an opaque Tau Ceti
class unfolds the `Add` instance of the cohomology object or gq2's exposed quotient cocycles
before failing, which exhausts the heartbeat budget.  Dictionary substitutions go through
`simp only` (discrimination-tree lookup) and additivity through term-mode `map_add`/`congrArg`.
-/

-- `LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)` and the quadratic-form instance chains
-- on `↥k` need more than the default budget (memo §B9; `GQ2/StiefelWhitney.lean` sets the same).
set_option synthInstance.maxHeartbeats 400000

namespace GQ2.TauCetiBridge

open CategoryTheory

universe u

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Binary forms: `swOne`/`swTwo` on chosen diagonalizations, and the trace forms -/

section Forms

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- gq2's diagonal form `⟨x, y⟩` is Tau Ceti's `weightedSumSquares ↥k ![x, y]` with the unit
weights read in `↥k`. -/
theorem diagForm_eq_weightedSumSquares (x y : (↥k)ˣ) :
    GQ2.diagForm k x y =
      QuadraticMap.weightedSumSquares ↥k fun i => ((![x, y] i : (↥k)ˣ) : ↥k) := by
  ext v
  simp [GQ2.diagForm, QuadraticMap.weightedSumSquares_apply, Units.smul_def]

/-- gq2's `IsDiagonalization k Q x y` is Tau Ceti's hypothesis shape
`Q.Equivalent (weightedSumSquares ↥k fun i => ↑(![x, y] i))`. -/
theorem isDiagonalization_iff_equivalent_weightedSumSquares {V : Type*} [AddCommGroup V]
    [Module ↥k V] (Q : QuadraticForm ↥k V) (x y : (↥k)ˣ) :
    GQ2.IsDiagonalization k Q x y ↔
      Q.Equivalent (QuadraticMap.weightedSumSquares ↥k fun i => ((![x, y] i : (↥k)ˣ) : ↥k)) := by
  rw [GQ2.IsDiagonalization, diagForm_eq_weightedSumSquares]

/-- gq2's `swOne` is the sum of the Kummer classes of its *chosen* diagonalization
(`dite_eq_left`; no well-definedness input). -/
theorem swOne_eq_of_exists {V : Type*} [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V)
    (h : ∃ x y : (↥k)ˣ, GQ2.IsDiagonalization k Q x y) :
    GQ2.swOne k Q = GQ2.kummerClassK k h.choose + GQ2.kummerClassK k h.choose_spec.choose :=
  dite_eq_left h

/-- gq2's `swTwo` is the cup product of the Kummer classes of its *chosen* diagonalization
(`dite_eq_left`; no `hnorm`). -/
theorem swTwo_eq_of_exists (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    {V : Type*} [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V)
    (h : ∃ x y : (↥k)ˣ, GQ2.IsDiagonalization k Q x y) :
    GQ2.swTwo k htriv Q =
      GQ2.kummerClassK k h.choose ⌣[htriv] GQ2.kummerClassK k h.choose_spec.choose :=
  dite_eq_left h

/-- The chosen pair of `swOne`/`swTwo` is a diagonalization. -/
theorem isDiagonalization_choose {V : Type*} [AddCommGroup V] [Module ↥k V]
    (Q : QuadraticForm ↥k V) (h : ∃ x y : (↥k)ˣ, GQ2.IsDiagonalization k Q x y) :
    GQ2.IsDiagonalization k Q h.choose h.choose_spec.choose :=
  h.choose_spec.choose_spec

variable (δ : ℚ̄₂)

/-- `Tr⟨1⟩` is Tau Ceti's trace transfer of the rank-one form `⟨1⟩ = sq` of `L = ↥(quadExt k δ)`
(not `rfl`: `QuadraticMap.traceTransfer` is not exposed). -/
theorem traceFormOne_eq_traceTransfer_sq :
    GQ2.traceFormOne k δ = QuadraticMap.traceTransfer ↥k
      (QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) :=
  QuadraticMap.traceTransfer_sq.symm

/-- `Tr⟨a⟩` is Tau Ceti's trace transfer of the rank-one form `⟨a⟩ = a • sq`
(`Tr(a·z·z)` against `Tr(a·(z·z))`). -/
theorem traceFormTwisted_eq_traceTransfer_smul_sq (a : ↥(GQ2.quadExt k δ)) :
    GQ2.traceFormTwisted k δ a = QuadraticMap.traceTransfer ↥k
      (a • QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
  ext z
  rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, smul_apply,
    QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]

variable [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)]

/-- Nondegeneracy of `Tr⟨a⟩` for a unit `a`, in the `SeparatingLeft` shape of gq2's
`exists_isDiagonalization` (Tau Ceti's `nondegenerate_traceTransfer_iff` and
`nondegenerate_smul_sq`). -/
theorem traceFormTwisted_separatingLeft (a : (↥(GQ2.quadExt k δ))ˣ) :
    (QuadraticMap.associated (R := ↥k) (GQ2.traceFormTwisted k δ ↑a)).SeparatingLeft := by
  rw [traceFormTwisted_eq_traceTransfer_smul_sq]
  exact (QuadraticMap.nondegenerate_associated_iff.mpr
    ((QuadraticMap.nondegenerate_traceTransfer_iff _).2
      (QuadraticMap.nondegenerate_smul_sq a.ne_zero))).1

/-- `Tr⟨a⟩` has a unit diagonalization when `[k(δ) : k] = 2`. -/
theorem exists_isDiagonalization_traceFormTwisted (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2)
    (a : (↥(GQ2.quadExt k δ))ˣ) :
    ∃ x y : (↥k)ˣ, GQ2.IsDiagonalization k (GQ2.traceFormTwisted k δ ↑a) x y :=
  GQ2.exists_isDiagonalization k _ hdeg (traceFormTwisted_separatingLeft k δ a)

end Forms

/-! ## The cochains of `GQ2/EvensKahn.lean` are Tau Ceti's Evens cochains, pointwise

Stated along any group homomorphism `φ : G →* G'` carrying `U ≤ G` onto `U' ≤ G'`
(`hU : φ g ∈ U' ↔ g ∈ U`) and gq2's additive `α : U → 𝔽₂` onto Tau Ceti's multiplicative
`α' : U' →* Multiplicative 𝔽₂` (`hα`).  With `φ = id` this is the identification on one group;
with `φ = Φ` it is the transport B9 needs, with no subgroup-equality cast. -/

section Cochain

variable {G G' : Type*} [Group G] [Group G'] (φ : G →* G') {U : Subgroup G} {U' : Subgroup G'}
  (s : G) (α : U → ZMod 2) (α' : U' →* Multiplicative (ZMod 2))
  (hU : ∀ g : G, φ g ∈ U' ↔ g ∈ U)
  (hα : ∀ (g : G) (hg : g ∈ U), Multiplicative.toAdd (α' ⟨φ g, (hU g).2 hg⟩) = α ⟨g, hg⟩)

include hU hα in
/-- gq2's first Shapiro component `b₁` (eq. (97)) is Tau Ceti's `evensB1`. -/
theorem evensAux_eq_evensB1 (g : G) :
    GQ2.evensAux U s α g = TauCeti.ContCohomology.evensB1 U' (φ s) α' (φ g) := by
  by_cases hg : g ∈ U
  · rw [GQ2.evensAux_of_mem α hg, TauCeti.ContCohomology.evensB1_of_mem ((hU g).2 hg),
      TauCeti.ContCohomology.evensExtend_of_mem ((hU g).2 hg), hα]
  · have hg' : φ g ∉ U' := fun h => hg ((hU g).1 h)
    rw [TauCeti.ContCohomology.evensB1_of_notMem hg', ← map_mul]
    by_cases hgs : g * s ∈ U
    · rw [GQ2.evensAux, dite_eq_right hg, dite_eq_left hgs,
        TauCeti.ContCohomology.evensExtend_of_mem ((hU _).2 hgs), hα]
    · rw [GQ2.evensAux, dite_eq_right hg, dite_eq_right hgs,
        TauCeti.ContCohomology.evensExtend_of_notMem (fun h => hgs ((hU _).1 h))]

include hU hα in
/-- gq2's second Shapiro component `b_s` is Tau Ceti's `evensBs`. -/
theorem bS_eq_evensBs (g : G) :
    GQ2.bS U s α g = TauCeti.ContCohomology.evensBs U' (φ s) α' (φ g) := by
  rw [TauCeti.ContCohomology.evensBs_apply, GQ2.bS, evensAux_eq_evensB1 φ s α α' hU hα, map_mul,
    map_inv]

include hU hα in
/-- gq2's degree-one corestriction cochain `cor(α) = b₁ + b_s` is Tau Ceti's
`evensCorCochain`. -/
theorem corFun_eq_evensCorCochain (g : G) :
    GQ2.corFun U s α g = TauCeti.ContCohomology.evensCorCochain U' (φ s) α' (φ g) := by
  rw [TauCeti.ContCohomology.evensCorCochain_apply, GQ2.corFun, evensAux_eq_evensB1 φ s α α' hU hα,
    bS_eq_evensBs φ s α α' hU hα]

include hU hα in
/-- gq2's two-point graph cocycle `ν_α` (eq. (98)) is Tau Ceti's `evensGraphCochain`. -/
theorem evensNormFun_eq_evensGraphCochain (g h : G) :
    GQ2.evensNormFun U s α (g, h) =
      TauCeti.ContCohomology.evensGraphCochain U' (φ s) α' (φ g, φ h) := by
  by_cases hg : g ∈ U
  · rw [TauCeti.ContCohomology.evensGraphCochain_of_mem ((hU g).2 hg), GQ2.evensNormFun,
      ite_eq_left hg, evensAux_eq_evensB1 φ s α α' hU hα, bS_eq_evensBs φ s α α' hU hα]
  · rw [TauCeti.ContCohomology.evensGraphCochain_of_notMem (fun h => hg ((hU g).1 h)),
      GQ2.evensNormFun, ite_eq_right hg, evensAux_eq_evensB1 φ s α α' hU hα,
      evensAux_eq_evensB1 φ s α α' hU hα, bS_eq_evensBs φ s α α' hU hα]

end Cochain

/-! ## Explicit classes: `corH1` and `evensNormH2` against Tau Ceti's cocycle classes, along `Φ` -/

section ExplicitClasses

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (Φ : G →ₜ* G')
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
  {U : Subgroup G} {U' : OpenSubgroup G'} {s : G} (α : U → ZMod 2)
  (α' : U'.toSubgroup →* Multiplicative (ZMod 2))
  (hU : ∀ g : G, Φ g ∈ U'.toSubgroup ↔ g ∈ U)
  (hα : ∀ (g : G) (hg : g ∈ U), Multiplicative.toAdd (α' ⟨Φ g, (hU g).2 hg⟩) = α ⟨g, hg⟩)
  (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
  (hαh : ∀ u v : U, α (u * v) = α u + α v) (hαc : Continuous α)
  (hU' : U'.toSubgroup.index = 2) (hs' : Φ s ∉ U') (hα' : Continuous α')

attribute [local instance] TopRep.distribMulAction

local instance continuousSMul_trivialF2_sw (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] : ContinuousSMul K (TauCeti.trivialF2 K).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 K).continuousSMul

include hU hα in
/-- Tau Ceti's Shapiro-sum cocycle `evensCorCocycle` of `(U', Φ s, α')`, pulled back along `Φ`,
is gq2's `corFun U s α` read by `toF2Z1`. -/
theorem cocyclesMap1_evensCorCocycle :
    TauCeti.ContCohomology.cocyclesMap1 G' (TauCeti.trivialF2 G').V G (TauCeti.trivialF2 G).V Φ
        TauCeti.trivialF2CoeffHom continuous_of_discreteTopology (trivialF2CoeffHom_smul' Φ)
        (TauCeti.ContCohomology.evensCorCocycle U' (Φ s) α' hU' hs' hα') =
      toF2Z1 G htriv ⟨GQ2.corFun U s α, GQ2.corFun_mem_Z1 htriv hUo hUi hs α hαh hαc⟩ := by
  apply Subtype.ext
  funext g
  refine (TauCeti.ContCohomology.cocyclesMap1_apply G' _ G _ Φ _ _ _ _ g).trans ?_
  rw [TauCeti.ContCohomology.coe_evensCorCocycle, TauCeti.trivialF2CoeffHom_apply,
    AddEquiv.apply_symm_apply, coe_toF2Z1]
  exact congrArg _ (corFun_eq_evensCorCochain (Φ : G →* G') s α α' hU hα g).symm

include hU hα in
/-- **The corestriction dictionary on explicit classes**: Tau Ceti's class of `evensCorCocycle`
(the form `galoisCor_kummerClass_eq_evensCorCocycle` produces), pulled back along `Φ`, is
gq2's `corH1` read by `cont1F2`. -/
theorem trivialF2Map_evensCorCocycle :
    TauCeti.trivialF2Map Φ 1
        ((eqToHom (congrArg (continuousCohomology 1)
            (TauCeti.ofDiscreteModule_trivialF2 G'))).hom
          (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G'
            (TauCeti.trivialF2 G').V
            (TauCeti.ContCohomology.evensCorCocycle U' (Φ s) α' hU' hs' hα'))) =
      cont1F2 G htriv (GQ2.corH1 htriv hUo hUi hs α hαh hαc) := by
  rw [trivialF2Map_eqToHom_explicitH1,
    cocyclesMap1_evensCorCocycle Φ htriv α α' hU hα hUo hUi hs hαh hαc hU' hs' hα', GQ2.corH1,
    cont1F2_H1mk]

include hU hα in
/-- Tau Ceti's graph cocycle `evensGraphCocycle` of `(U', Φ s, α')`, pulled back along `Φ`, is
gq2's `evensNormFun U s α` read by `toF2Z2`. -/
theorem cocyclesMap2_evensGraphCocycle :
    TauCeti.ContCohomology.cocyclesMap2 G' (TauCeti.trivialF2 G').V G (TauCeti.trivialF2 G).V Φ
        TauCeti.trivialF2CoeffHom continuous_of_discreteTopology (trivialF2CoeffHom_smul' Φ)
        (TauCeti.ContCohomology.evensGraphCocycle U' (Φ s) α' hU' hs' hα') =
      toF2Z2 G htriv
        ⟨GQ2.evensNormFun U s α, GQ2.evensNormFun_mem_Z2 htriv hUo hUi hs α hαh hαc⟩ := by
  apply Subtype.ext
  funext ⟨g, h⟩
  refine (TauCeti.ContCohomology.cocyclesMap2_apply G' _ G _ Φ _ _ _ _ g h).trans ?_
  rw [TauCeti.ContCohomology.coe_evensGraphCocycle, TauCeti.trivialF2CoeffHom_apply,
    AddEquiv.apply_symm_apply, coe_toF2Z2]
  exact congrArg _ (evensNormFun_eq_evensGraphCochain (Φ : G →* G') s α α' hU hα g h).symm

include hU hα in
/-- **The Evens-norm dictionary on explicit classes**: Tau Ceti's `evensGraphCochainClass`
(the form `galoisEvens_kummerClass_eq_evensGraphCochainClass` produces), pulled back along `Φ`,
is gq2's `evensNormH2` read by `cont2F2`. -/
theorem trivialF2Map_evensGraphCochainClass [LocallyCompactSpace G] [LocallyCompactSpace G'] :
    TauCeti.trivialF2Map Φ 2
        (TauCeti.ContCohomology.evensGraphCochainClass U' (Φ s) α' hU' hs' hα') =
      cont2F2 G htriv (GQ2.evensNormH2 htriv hUo hUi hs α hαh hαc) := by
  rw [TauCeti.ContCohomology.evensGraphCochainClass_def, trivialF2Map_eqToHom_explicitH2,
    cocyclesMap2_evensGraphCocycle Φ htriv α α' hU hα hUo hUi hs hαh hαc hU' hs' hα',
    GQ2.evensNormH2, cont2F2_H2mk]

end ExplicitClasses

/-! ## Tau Ceti's `galoisCor` and `galoisEvens` on a Kummer class, as explicit classes -/

section GaloisSide

variable {K L : Type} [Field K] [Field L] [Invertible (2 : L)] [Algebra K L]
  [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K) (hL : Module.finrank K L = 2) (a : Lˣ)
  (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
  (s : TauCeti.AbsoluteGaloisGroup K) (hs : s ∉ TauCeti.galoisSubgroup K L σ)

attribute [local instance] TopRep.distribMulAction

local instance continuousSMul_trivialF2_sw' (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ContinuousSMul G (TauCeti.trivialF2 G).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul

/-- **The Evens norm of a Kummer class is the class of the graph cocycle of its Kummer
character**, at any `s ∉ G_L` (`galoisEvens_def`, `galoisF2Iso_inv_kummerClass`,
`evensNormIndexTwo_homClass`, `graphClass_eq_evensGraphCochainClass`). -/
theorem galoisEvens_kummerClass_eq_evensGraphCochainClass :
    TauCeti.galoisEvens K L σ hL (TauCeti.kummerClass a) =
      TauCeti.ContCohomology.evensGraphCochainClass (TauCeti.galoisSubgroup K L σ) s
        (TauCeti.galoisKummerCharacter σ a r hr) ((TauCeti.galoisSubgroup_index K L σ).trans hL)
        hs (TauCeti.continuous_galoisKummerCharacter σ a r hr) := by
  rw [TauCeti.galoisEvens_def, TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.evensNormIndexTwo_homClass,
    TauCeti.ContCohomology.graphClass_eq_evensGraphCochainClass _ _ s hs]

/-- **The corestriction of a Kummer class is the class of the Shapiro-sum cocycle of its Kummer
character**, at any `s ∉ G_L` (`galoisCor_def`, `galoisF2Iso_inv_kummerClass`,
`homClass_eq_evensHomCocycleAmbient`, `trivialF2CorMap_explicitH1AddEquivContinuousCohomology`,
`explicitCor1_evensHomCocycleAmbient`). -/
theorem galoisCor_kummerClass_eq_evensCorCocycle [Invertible (2 : K)] :
    TauCeti.galoisCor K L σ 1 (TauCeti.kummerClass a) =
      (eqToHom (congrArg (continuousCohomology 1)
          (TauCeti.ofDiscreteModule_trivialF2 (TauCeti.AbsoluteGaloisGroup K)))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
          (TauCeti.AbsoluteGaloisGroup K) (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K)).V
          (TauCeti.ContCohomology.evensCorCocycle (TauCeti.galoisSubgroup K L σ) s
            (TauCeti.galoisKummerCharacter σ a r hr)
            ((TauCeti.galoisSubgroup_index K L σ).trans hL) hs
            (TauCeti.continuous_galoisKummerCharacter σ a r hr))) := by
  rw [TauCeti.galoisCor_def, ConcreteCategory.comp_apply,
    TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.homClass_eq_evensHomCocycleAmbient,
    TauCeti.trivialF2CorMap_explicitH1AddEquivContinuousCohomology,
    TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient _
      ((TauCeti.galoisSubgroup_index K L σ).trans hL) s hs]

end GaloisSide

/-! ## Cup products -/

section Cup

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Tau Ceti's `trivialF2Map_cup` in bidegree `(1, 1)`, with the target degree written `2` (as
it appears in the degree-two Stiefel–Whitney identity). -/
theorem trivialF2Map_cup_one_one (φ : H →ₜ* G)
    (x y : continuousCohomology 1 (TauCeti.trivialF2 G)) :
    TauCeti.trivialF2Map φ 2 ((TauCeti.trivialF2TopPairing G).cup 1 1 x y) =
      (TauCeti.trivialF2TopPairing H).cup 1 1 (TauCeti.trivialF2Map φ 1 x)
        (TauCeti.trivialF2Map φ 1 y) :=
  TauCeti.trivialF2Map_cup φ 1 1 x y

end Cup

/-! ## The dyadic case: `k`, `L = k(δ)`, `Φ = fixingEquivAbsGal k`, `σ = layerEmb k L`, `r = e⁻¹ β` -/

section Dyadic

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (δ : ℚ̄₂)

/-- A square root `β ∈ ℚ̄₂` of `a ∈ L = k(δ)` gives the square root `e⁻¹ β ∈ kˢᵉᵖ` of
`σ a = layerEmb k L a`. -/
theorem sepClosureEquiv_symm_sq_eq_layerEmb (a : ↥(GQ2.quadExt k δ)) {β : ℚ̄₂}
    (hβ : β ^ 2 = (a : ℚ̄₂)) :
    (sepClosureEquiv k).symm β ^ 2 = layerEmb k (GQ2.quadExt k δ) a := by
  apply (sepClosureEquiv k).injective
  rw [map_pow, AlgEquiv.apply_symm_apply, sepClosureEquiv_layerEmb, hβ]

variable [FiniteDimensional ℚ_[2] k]

/-- Tau Ceti's root sign of `e⁻¹ β` at `Φ g` is gq2's Kummer cocycle function of `β` at `g`
(A1's intertwining `fixingEquivAbsGal_apply_sepClosureEquiv_symm`). -/
theorem rootSign_sepClosureEquiv_symm (β : ℚ̄₂) (g : k.fixingSubgroup) :
    TauCeti.rootSign ((sepClosureEquiv k).symm β) (fixingEquivAbsGal k g) =
      GQ2.Kummer.kummerCocycleFun β (g : GQ2.Kummer.GaloisGroup ℚ_[2]) := by
  have key : fixingEquivAbsGal k g ((sepClosureEquiv k).symm β) = (sepClosureEquiv k).symm β ↔
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) • β = β := by
    rw [fixingEquivAbsGal_apply_sepClosureEquiv_symm, (sepClosureEquiv k).symm.injective.eq_iff,
      AlgEquiv.smul_def]
  by_cases h : (g : GQ2.Kummer.GaloisGroup ℚ_[2]) • β = β
  · rw [TauCeti.rootSign_of_apply_eq (key.2 h), GQ2.Kummer.kummerCocycleFun_eq0 h]
  · rw [TauCeti.rootSign_of_apply_ne (fun h' => h (key.1 h')), GQ2.Kummer.kummerCocycleFun,
      ite_eq_right h]

variable [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)]

/-- `Φ s ∉ G_L` for `s ∉ U = (stab δ).subgroupOf G_k`. -/
theorem fixingEquivAbsGal_notMem_galoisSubgroup_quadExt {s : k.fixingSubgroup}
    (hs : s ∉ (MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
      k.fixingSubgroup) :
    fixingEquivAbsGal k s ∉
      TauCeti.galoisSubgroup k (GQ2.quadExt k δ) (layerEmb k (GQ2.quadExt k δ)) :=
  fun h => hs ((fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer k δ s).1 h)

variable (a : (↥(GQ2.quadExt k δ))ˣ) {β : ℚ̄₂} (hβ : β ^ 2 = ((a : ↥(GQ2.quadExt k δ)) : ℚ̄₂))
  (α : ((MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
    k.fixingSubgroup) → ZMod 2)
  (hαdef : ∀ g, α g = GQ2.Kummer.kummerCocycleFun β
    ((g : k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]))

include hαdef in
/-- Tau Ceti's Kummer character of `a` on `G_L`, at `Φ g` for `g ∈ U`, is gq2's `α g`
(the B9 hypothesis `hαdef`). -/
theorem toAdd_galoisKummerCharacter_fixingEquivAbsGal (g : k.fixingSubgroup)
    (hg : g ∈ (MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
      k.fixingSubgroup) :
    Multiplicative.toAdd (TauCeti.galoisKummerCharacter (layerEmb k (GQ2.quadExt k δ)) a
        ((sepClosureEquiv k).symm β) (sepClosureEquiv_symm_sq_eq_layerEmb k δ a hβ)
        ⟨fixingEquivAbsGal k g,
          (fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer k δ g).2 hg⟩) =
      α ⟨g, hg⟩ := by
  rw [TauCeti.toAdd_galoisKummerCharacter, hαdef, rootSign_sepClosureEquiv_symm]

variable (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2)
  (s : k.fixingSubgroup)
  (hs : s ∉ (MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
  (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
  (hUo : IsOpen (((MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
    k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
  (hidx : ((MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
    k.fixingSubgroup).index = 2)
  (hα : ∀ g h, α (g * h) = α g + α h) (hαc : Continuous α)

include hβ hαdef hdeg in
/-- **`corH1` is `galoisCor`**: Tau Ceti's corestriction of the Kummer class of `a ∈ L = k(δ)`
along `σ = layerEmb k L`, pulled back along `Φ = fixingEquivAbsGal k`, is gq2's
`corH1 htriv hUo hidx hs α hα hαc` read by `cont1F2`. -/
theorem trivialF2Map_galoisCor_kummerClass :
    TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k)
        1 (TauCeti.galoisCor k (GQ2.quadExt k δ) (layerEmb k (GQ2.quadExt k δ)) 1
          (TauCeti.kummerClass a)) =
      cont1F2 k.fixingSubgroup htriv (GQ2.corH1 htriv hUo hidx hs α hα hαc) := by
  rw [galoisCor_kummerClass_eq_evensCorCocycle (layerEmb k (GQ2.quadExt k δ)) hdeg a _
    (sepClosureEquiv_symm_sq_eq_layerEmb k δ a hβ) (fixingEquivAbsGal k s)
    (fixingEquivAbsGal_notMem_galoisSubgroup_quadExt k δ hs)]
  exact trivialF2Map_evensCorCocycle
    (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) htriv α
    (TauCeti.galoisKummerCharacter (layerEmb k (GQ2.quadExt k δ)) a ((sepClosureEquiv k).symm β)
      (sepClosureEquiv_symm_sq_eq_layerEmb k δ a hβ))
    (fun g => fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer k δ g)
    (fun g hg => toAdd_galoisKummerCharacter_fixingEquivAbsGal k δ a hβ α hαdef g hg)
    hUo hidx hs hα hαc _ _ _

include hβ hαdef in
/-- **`evensNormH2` is `galoisEvens`**: Tau Ceti's Evens norm of the Kummer class of
`a ∈ L = k(δ)` along `σ = layerEmb k L`, pulled back along `Φ = fixingEquivAbsGal k`, is gq2's
`evensNormH2 htriv hUo hidx hs α hα hαc` read by `cont2F2`. -/
theorem trivialF2Map_galoisEvens_kummerClass :
    TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k)
        2 (TauCeti.galoisEvens k (GQ2.quadExt k δ) (layerEmb k (GQ2.quadExt k δ)) hdeg
          (TauCeti.kummerClass a)) =
      cont2F2 k.fixingSubgroup htriv (GQ2.evensNormH2 htriv hUo hidx hs α hα hαc) := by
  rw [galoisEvens_kummerClass_eq_evensGraphCochainClass (layerEmb k (GQ2.quadExt k δ)) hdeg a _
    (sepClosureEquiv_symm_sq_eq_layerEmb k δ a hβ) (fixingEquivAbsGal k s)
    (fixingEquivAbsGal_notMem_galoisSubgroup_quadExt k δ hs)]
  exact trivialF2Map_evensGraphCochainClass
    (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) htriv α
    (TauCeti.galoisKummerCharacter (layerEmb k (GQ2.quadExt k δ)) a ((sepClosureEquiv k).symm β)
      (sepClosureEquiv_symm_sq_eq_layerEmb k δ a hβ))
    (fun g => fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer k δ g)
    (fun g hg => toAdd_galoisKummerCharacter_fixingEquivAbsGal k δ a hβ α hαdef g hg)
    hUo hidx hs hα hαc _ _ _

end Dyadic

end GQ2.TauCetiBridge
