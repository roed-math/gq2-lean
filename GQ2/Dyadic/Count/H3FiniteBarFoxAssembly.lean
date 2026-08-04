/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedModTwoFoxBoundary
import GQ2.Dyadic.Count.ContinuousCochainFiniteLevel

/-!
# Finite-refinement assembly for the improved square presentation

Continuous degree-three cohomology is the direct limit of finite-quotient cohomology.  A finite
2-group quotient should therefore not be expected to have `H³ = 0` itself.  The exact target is
instead that every finite-level cocycle becomes a `d²` boundary after passage to some finer open
normal quotient.  `ContinuousCochainFiniteLevel` proves this target equivalent to
`ModTwoHThreeExact`.

This file ties that criterion to the actual improved square presentation.  Its finite Fox rows
are evaluated at the images of `SqCore.sqGen h`, and the resulting boundary square commutes under
every refinement.  Consequently the remaining finite bar--Fox calculation has one precise
output: construct `FiniteRefinementModTwoHThreeExact (SqCore.DSq h)` using these commuting rows.
Pointwise injectivity is neither used nor true (the row at the trivial quotient is zero).

Mathlib's `Rep.barResolution` is a projective resolution for an **abstract** group representation.
It supplies the algebraic bar complex and comparison theorem, but it does not carry a profinite
topology, completed group ring, or the inverse system of finite quotients.  The last section below
therefore records the missing continuous comparison in a genuinely chain-level form.  Its fields
are maps in degrees two through four and two homotopy identities valid for every cochain; no field
asserts that a cocycle has a primitive or assumes `H³ = 0`.

The resulting assembly theorem is useful in both directions.  A future construction of those
low-degree maps, together with injectivity of the already-constructed completed Fox boundary,
immediately gives the finite-refinement target.  Conversely, the coordinate theorem below shows
that the syzygy identity is not an abstract placeholder: at every chosen quotient it is literally
the quotient-natural improved Fox row from `H3FiniteLevelFoxBoundary`.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

/-- The actual improved-presentation generators in an open-normal quotient of `DSq h`. -/
def sqOpenQuotientMarking (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) ⧸ V.toSubgroup :=
  fun i ↦ QuotientGroup.mk' V.toSubgroup (sqGen h i)

/-- The actual quotient markings commute with refinement. -/
@[simp] theorem openNormalQuotientProj_sqOpenQuotientMarking
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) (i : Fin (sqRank h)) :
    openNormalQuotientProj hWV (sqOpenQuotientMarking h W i) =
      sqOpenQuotientMarking h V i := by
  change openNormalQuotientProj hWV
      (QuotientGroup.mk' W.toSubgroup (sqGen h i)) =
    QuotientGroup.mk' V.toSubgroup (sqGen h i)
  exact openNormalQuotientProj_mk hWV (sqGen h i)

/-- The finite Fox boundary for the literal improved square relator commutes from a finer
open-normal quotient to a coarser one.  This is the quotient-indexed chain-map square needed by
any finite bar--Fox construction. -/
theorem sqOpenQuotientFoxBoundary_natural
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ W.toSubgroup) Unit) :
    regularModTwoPushforward (openNormalQuotientProj hWV) (Fin (sqRank h))
        ((sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h W)).map c) =
      (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h V)).map
        (regularModTwoPushforward (openNormalQuotientProj hWV) Unit c) := by
  simpa only [openNormalQuotientProj_sqOpenQuotientMarking] using
    sqFiniteLevelModTwoFoxBoundary_natural
      (openNormalQuotientProj hWV) h (sqOpenQuotientMarking h W) c

/-- The finite-refinement bar--Fox target immediately supplies scalar `H³` exactness for the
actual improved square core. -/
theorem modTwoHThreeExact_DSq_of_finiteRefinement (h : ℕ)
    (S : FiniteRefinementModTwoHThreeExact (DSq h : Type)) :
    ModTwoHThreeExact (DSq h : Type) :=
  modTwoHThreeExact_of_finiteRefinement S

/-- Once the finite-refinement target is proved, scalarization gives the full finite-elementary
coefficient `H²` right-exactness theorem required downstream. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_finiteRefinement (h : ℕ)
    (S : FiniteRefinementModTwoHThreeExact (DSq h : Type)) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_modTwoHThreeExact h
    (modTwoHThreeExact_DSq_of_finiteRefinement h S)

/-! ## The missing low-degree finite-to-completed bar--Fox homotopy -/

/-- Finite mod-two inhomogeneous bar cochains in degree two. -/
abbrev FiniteModTwoBarCochainTwo (Q : Type) := Q × Q → ZMod 2

/-- Finite mod-two inhomogeneous bar cochains in degree three. -/
abbrev FiniteModTwoBarCochainThree (Q : Type) := Q × Q × Q → ZMod 2

/-- Finite mod-two inhomogeneous bar cochains in degree four. -/
abbrev FiniteModTwoBarCochainFour (Q : Type) := Q × Q × Q × Q → ZMod 2

/-- The finite inhomogeneous `d²` with trivial mod-two coefficients, bundled so that chain
identities can be stated without repeatedly installing the trivial action. -/
def finiteModTwoBarDTwo (Q : Type) [Group Q] :
    FiniteModTwoBarCochainTwo Q →+ FiniteModTwoBarCochainThree Q := by
  letI := trivialZModTwoAction Q
  exact dTwo Q (ZMod 2)

/-- The finite inhomogeneous `d³` with trivial mod-two coefficients. -/
def finiteModTwoBarDThree (Q : Type) [Group Q] :
    FiniteModTwoBarCochainThree Q →+ FiniteModTwoBarCochainFour Q := by
  letI := trivialZModTwoAction Q
  exact dThree (G := Q) (A := ZMod 2)

/-- The degree-three differential after the degree-two differential is zero at every finite
quotient.  This is the first chain identity needed by a bar--Fox comparison. -/
theorem finiteModTwoBarDThree_comp_dTwo (Q : Type) [Group Q] :
    (finiteModTwoBarDThree Q).comp (finiteModTwoBarDTwo Q) = 0 := by
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  letI : IsTopologicalGroup Q := inferInstance
  letI := trivialZModTwoAction Q
  letI := continuousSMul_trivialZModTwoAction (G := Q)
  exact dThree_comp_dTwo

/-- Pullback of finite two-cochains along an actual refinement quotient of `DSq h`, bundled as
an additive map. -/
def sqFiniteModTwoBarRefineTwo (h : ℕ)
    {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    FiniteModTwoBarCochainTwo ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainTwo ((DSq h : Type) ⧸ W.toSubgroup) where
  toFun := modTwoRefineTwo hWV
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Pullback of finite three-cochains along an actual refinement quotient of `DSq h`. -/
def sqFiniteModTwoBarRefineThree (h : ℕ)
    {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup) where
  toFun := modTwoRefineThree hWV
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Pullback of finite four-cochains along an actual refinement quotient of `DSq h`. -/
def sqFiniteModTwoBarRefineFour (h : ℕ)
    {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ W.toSubgroup) where
  toFun := modTwoRefineFour hWV
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Refinement is a cochain map in degrees two and three. -/
theorem finiteModTwoBarDTwo_refine
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    (finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)).comp
        (sqFiniteModTwoBarRefineTwo h hWV) =
      (sqFiniteModTwoBarRefineThree h hWV).comp
        (finiteModTwoBarDTwo ((DSq h : Type) ⧸ V.toSubgroup)) := by
  ext k p
  exact congrFun (dTwo_modTwoRefineTwo hWV k) p

/-- Refinement is a cochain map in degrees three and four. -/
theorem finiteModTwoBarDThree_refine
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    (finiteModTwoBarDThree ((DSq h : Type) ⧸ W.toSubgroup)).comp
        (sqFiniteModTwoBarRefineThree h hWV) =
      (sqFiniteModTwoBarRefineFour h hWV).comp
        (finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup)) := by
  ext c p
  exact congrFun (dThree_modTwoRefineThree hWV c) p

private abbrev SqCompletedRelationModule (h : ℕ) :=
  ModTwoCompletedRegularModule (DSq h : Type) Unit

private abbrev SqCompletedGeneratorModule (h : ℕ) :=
  ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))

/-- A low-degree finite-to-completed bar--Fox homotopy at one open-normal quotient.

For an input level `V`, the comparison is allowed to pass to a finer level `W ≤ V`.  It has
five additive chain-level components:

* a degree-lowering bar homotopy from three- to two-cochains;
* a relation syzygy valued in the **completed** relation module;
* the finite-level bar error reconstructed from the `W`-coordinate of that syzygy;
* two correction maps applied to the degree-four coboundary.

The two identities hold for every three-cochain.  In particular, neither identity asks for a
primitive of a cocycle.  When `d³ c = 0`, the correction terms vanish functorially; injectivity of
the completed Fox boundary then kills the completed syzygy. -/
structure SqFiniteToCompletedBarFoxHomotopyAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  /-- The quotient at which the comparison identity is realized. -/
  W : OpenNormalSubgroup (DSq h : Type)
  /-- The comparison may only refine the input quotient. -/
  le : W.toSubgroup ≤ V.toSubgroup
  /-- The degree-lowering bar homotopy. -/
  homotopyTwo :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainTwo ((DSq h : Type) ⧸ W.toSubgroup)
  /-- The relation syzygy, retained as a compatible family over every quotient. -/
  relationSyzygy :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      SqCompletedRelationModule h
  /-- Reconstruction of the finite bar error from the chosen syzygy coordinate. -/
  relationError :
    RegularModTwoRelationModule ((DSq h : Type) ⧸ W.toSubgroup) Unit →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  /-- The failure of the relation syzygy to lie in the completed Fox kernel factors through
  the degree-four coboundary. -/
  boundaryDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      SqCompletedGeneratorModule h
  /-- The remaining bar-comparison error also factors through the degree-four coboundary. -/
  barDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  /-- Chain-map identity at the relation syzygy. -/
  boundary_relationSyzygy : ∀ c,
    (sqCompletedModTwoFoxBoundary h).map (relationSyzygy c) =
      boundaryDefect (finiteModTwoBarDThree _ c)
  /-- Low-degree homotopy identity after actual quotient refinement. -/
  reconstruct : ∀ c,
    finiteModTwoBarDTwo _ (homotopyTwo c) +
        relationError
          (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit W
            (relationSyzygy c)) +
        barDefect (finiteModTwoBarDThree _ c) =
      sqFiniteModTwoBarRefineThree h le c

/-- A compatible low-degree bar--Fox construction consists of the preceding chain maps at every
finite input level.  This is data in `Type`, not a proposition asserting cohomological exactness. -/
abbrev SqFiniteToCompletedBarFoxAssembly (h : ℕ) :=
  ∀ V : OpenNormalSubgroup (DSq h : Type),
    SqFiniteToCompletedBarFoxHomotopyAt h V

/-- The completed syzygy identity has, at its chosen finite quotient, exactly the improved
quotient Fox row already constructed in `H3FiniteLevelFoxBoundary`.  Thus the chain datum above
cannot be satisfied by an unrelated or lookalike presentation row. -/
theorem SqFiniteToCompletedBarFoxHomotopyAt.finite_boundary_relationSyzygy
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteToCompletedBarFoxHomotopyAt h V)
    (c : FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)) :
    (sqFiniteLevelModTwoFoxBoundary h
        (fun i ↦ QuotientGroup.mk' C.W.toSubgroup (sqGen h i))).map
      (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit C.W
        (C.relationSyzygy c)) =
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) (Fin (sqRank h)) C.W
      (C.boundaryDefect (finiteModTwoBarDThree _ c)) := by
  have hcoord := congrArg
    (fun z : SqCompletedGeneratorModule h ↦
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) C.W z)
    (C.boundary_relationSyzygy c)
  simpa only [sqCompletedModTwoFoxBoundary_coordinate] using hcoord

/-- **Finite bar--Fox assembly theorem.**  If the actual completed improved-square Fox boundary
is injective, then low-degree finite-to-completed chain homotopies give the exact eventual
finite-level primitive criterion.

This proof uses no pointwise injectivity.  The syzygy is killed in the completed relation module;
only then is its chosen finite coordinate set to zero in the reconstruction identity. -/
theorem finiteRefinementModTwoHThreeExact_DSq_of_barFoxAssembly
    (h : ℕ)
    (hinjective : Function.Injective (sqCompletedModTwoFoxBoundary h).map)
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    FiniteRefinementModTwoHThreeExact (DSq h : Type) := by
  intro V c hcocycle
  let C := assembly V
  have hdThree : finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 := by
    exact hcocycle
  have hboundary :
      (sqCompletedModTwoFoxBoundary h).map (C.relationSyzygy c) = 0 := by
    rw [C.boundary_relationSyzygy, hdThree, map_zero]
  have hsyzygy : C.relationSyzygy c = 0 := by
    apply hinjective
    simpa using hboundary
  refine ⟨C.W, C.le, C.homotopyTwo c, ?_⟩
  have hreconstruct := C.reconstruct c
  rw [hdThree, map_zero, hsyzygy, map_zero, map_zero, add_zero] at hreconstruct
  simpa [finiteModTwoBarDTwo, sqFiniteModTwoBarRefineThree] using hreconstruct

/-- The preceding chain-level assembly, followed by continuous finite-quotient descent, gives
scalar continuous `H³` exactness for the improved square core. -/
theorem modTwoHThreeExact_DSq_of_barFoxAssembly
    (h : ℕ)
    (hinjective : Function.Injective (sqCompletedModTwoFoxBoundary h).map)
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    ModTwoHThreeExact (DSq h : Type) :=
  modTwoHThreeExact_of_finiteRefinement
    (finiteRefinementModTwoHThreeExact_DSq_of_barFoxAssembly h hinjective assembly)

end

end GQ2.Dyadic.Count
