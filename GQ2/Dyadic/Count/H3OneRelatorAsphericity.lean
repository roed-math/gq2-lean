/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2ProTwoScalarCDTwo
import GQ2.Dyadic.SqCore.Cores

/-!
# A continuous bar--Fox interface for one-relator pro-2 asphericity

The concrete square core is the genuine one-relator pro-2 presentation

`DSq h = presPro2 (sqRelator h)`.

Classically, a length-two resolution over the completed group ring is obtained by proving that
the Fox boundary of this presentation is injective.  Comparison with the continuous bar
resolution then kills continuous cohomology in degree three.  Neither a completed group ring nor
the continuous bar/Fox comparison is currently present in Mathlib: Mathlib's bar resolution is
the algebraic resolution of an abstract group and does not control continuity of the resulting
cochain primitives.

This file installs the smallest interface at that exact boundary.  A
`ContinuousModTwoBarFoxComparison` consists of three *additive comparison maps*:

* a degree-lowering bar homotopy;
* the relation syzygy of a continuous bar three-cochain;
* reconstruction of the bar error from a relation syzygy.

For a three-cocycle the syzygy lies in the kernel of the Fox boundary, and the comparison identity
expresses the cocycle as its homotopy coboundary plus the reconstructed syzygy error.  Thus
injectivity of the Fox boundary, and no cohomological-vanishing premise, gives an explicit
continuous two-cochain primitive.  The final theorems specialize the generic construction first
to `presPro2 r` and then definitionally to the actual `sqRelator h` presentation of `DSq h`.

The remaining theorem is now precise: construct this comparison from the completed
`F_2[[DSq h]]` Fox resolution and prove its Fox boundary injective.  Existing finite-target Fox
matrices are not that boundary (at the trivial target the augmented mod-two Fox row vanishes), so
they cannot be substituted for the completed relation-module map.
-/

namespace GQ2.ContCoh

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance : DistribMulAction G (ZMod 2) := trivialZModTwoAction G
local instance : ContinuousSMul G (ZMod 2) := continuousSMul_trivialZModTwoAction

/-! ## Continuous bar cochains in degrees two through four -/

/-- Continuous inhomogeneous mod-two bar two-cochains. -/
abbrev ContinuousModTwoCochainTwo (G : Type) [TopologicalSpace G] :=
  ContinuousMap (G × G) (ZMod 2)

/-- Continuous inhomogeneous mod-two bar three-cochains. -/
abbrev ContinuousModTwoCochainThree (G : Type) [TopologicalSpace G] :=
  ContinuousMap (G × G × G) (ZMod 2)

/-- Continuous inhomogeneous mod-two bar four-cochains. -/
abbrev ContinuousModTwoCochainFour (G : Type) [TopologicalSpace G] :=
  ContinuousMap (G × G × G × G) (ZMod 2)

/-- The explicit inhomogeneous `d²`, restricted to continuous mod-two cochains. -/
def continuousModTwoDTwo :
    ContinuousModTwoCochainTwo G →+ ContinuousModTwoCochainThree G where
  toFun f := ⟨dTwo G (ZMod 2) f, continuous_dTwo f f.continuous⟩
  map_zero' := by
    ext t
    simp
  map_add' f g := by
    ext t
    exact congrFun (map_add (dTwo G (ZMod 2)) (f : G × G → ZMod 2) g) t

/-- The explicit inhomogeneous `d³` preserves continuity. -/
theorem continuous_dThree_modTwo
    (f : G × G × G → ZMod 2) (hf : Continuous f) :
    Continuous (dThree (G := G) (A := ZMod 2) f) := by
  change Continuous (fun t : G × G × G × G ↦
    t.1 • f (t.2.1, t.2.2.1, t.2.2.2) -
      f (t.1 * t.2.1, t.2.2.1, t.2.2.2) +
      f (t.1, t.2.1 * t.2.2.1, t.2.2.2) -
      f (t.1, t.2.1, t.2.2.1 * t.2.2.2) +
      f (t.1, t.2.1, t.2.2.1))
  fun_prop

/-- The explicit inhomogeneous `d³`, restricted to continuous mod-two cochains. -/
def continuousModTwoDThree :
    ContinuousModTwoCochainThree G →+ ContinuousModTwoCochainFour G where
  toFun f := ⟨dThree (G := G) (A := ZMod 2) f, continuous_dThree_modTwo f f.continuous⟩
  map_zero' := by
    ext t
    simp
  map_add' f g := by
    ext t
    exact congrFun
      (map_add (dThree (G := G) (A := ZMod 2))
        (f : G × G × G → ZMod 2) g) t

/-! ## The completed Fox-boundary and bar-comparison interfaces -/

/-- An algebraic Fox boundary between mod-two relation and generator modules.

For the classical pro-2 asphericity theorem the carriers are completed
`F_2[[G]]`-modules and this is the completed Fox derivative of the relator.  The present
interface records precisely the linearity and `G`-equivariance used by a bar/Fox comparison;
constructing the completed modules themselves remains the concrete upstream task. -/
structure ModTwoFoxBoundary (G R X : Type)
    [Group G] [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction G R] [DistribMulAction G X] where
  /-- The relation-module-to-generator-module Fox boundary. -/
  map : R →ₗ[ZMod 2] X
  /-- Equivariance for the regular completed group action. -/
  equivariant : ∀ (g : G) (r : R), map (g • r) = g • map r

/-- Continuous bar/Fox comparison data through degree three.

This is the cochain-level output of comparing the continuous bar resolution with a length-two
one-relator Fox resolution.  It does not assert `H³ = 0`, and no field says that a cocycle has a
primitive.  Instead the two comparison identities locate the only possible failure in the
kernel of the Fox boundary. -/
structure ContinuousModTwoBarFoxComparison
    (R X : Type)
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction G R] [DistribMulAction G X]
    (fox : ModTwoFoxBoundary G R X) where
  /-- The degree-lowering component of the bar/Fox comparison homotopy. -/
  homotopyTwo : ContinuousModTwoCochainThree G →+ ContinuousModTwoCochainTwo G
  /-- The residual relation syzygy of a bar three-cochain. -/
  relationSyzygy : ContinuousModTwoCochainThree G →+ R
  /-- Reconstruction of the bar three-cochain error carried by a relation syzygy. -/
  relationError : R →+ ContinuousModTwoCochainThree G
  /-- A bar three-cocycle has a relation syzygy in the kernel of the Fox boundary. -/
  boundary_relationSyzygy : ∀ F,
    continuousModTwoDThree F = 0 → fox.map (relationSyzygy F) = 0
  /-- The bar/Fox comparison identity: cocycle equals homotopy boundary plus syzygy error. -/
  reconstruct : ∀ F, continuousModTwoDThree F = 0 →
    continuousModTwoDTwo (homotopyTwo F) + relationError (relationSyzygy F) = F

/-- Injectivity of the completed Fox boundary kills the relation syzygy and turns the explicit
bar/Fox homotopy into a continuous primitive for every mod-two three-cocycle. -/
theorem modTwoHThreeExact_of_barFoxComparison
    {R X : Type}
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction G R] [DistribMulAction G X]
    (fox : ModTwoFoxBoundary G R X)
    (comparison : ContinuousModTwoBarFoxComparison R X fox)
    (hinjective : Function.Injective fox.map) :
    ModTwoHThreeExact G := by
  intro F hFcontinuous hFcocycle
  let Fc : ContinuousModTwoCochainThree G := ⟨F, hFcontinuous⟩
  have hcycle : continuousModTwoDThree Fc = 0 := by
    ext t
    exact congrFun hFcocycle t
  have hsyzygy : comparison.relationSyzygy Fc = 0 := by
    apply hinjective
    rw [comparison.boundary_relationSyzygy Fc hcycle, map_zero]
  refine ⟨comparison.homotopyTwo Fc,
    (comparison.homotopyTwo Fc).continuous, ?_⟩
  have hreconstruct := comparison.reconstruct Fc hcycle
  rw [hsyzygy, map_zero, add_zero] at hreconstruct
  exact congrArg ContinuousMap.toFun hreconstruct

/-! ## The actual one-relator pro-2 presentation and the square core -/

/-- The relator viewed in the free pro-2 group.  This, rather than nonsquareness in the free
profinite group before pro-2 completion, is the power condition used by the classical
one-relator pro-2 asphericity theorem. -/
noncomputable def freeProTwoRelatorImage
    {n : ℕ} (r : FreeProfiniteGroup (Fin n)) :
    GQ2.maxProPQuotient 2 (FreeProfiniteGroup (Fin n)) :=
  GQ2.maxProPMk 2 (FreeProfiniteGroup (Fin n)) r

/-- The exact presentation-side non-power condition at `p = 2`. -/
def IsNonSquareInFreeProTwo
    {n : ℕ} (r : FreeProfiniteGroup (Fin n)) : Prop :=
  ¬ ∃ z, freeProTwoRelatorImage r = z ^ 2

/-- A nonsquare image in any pro-2 target proves that the relator is nonsquare in the free
pro-2 group.  This is the exact generic bridge used by finite 2-group witnesses. -/
theorem isNonSquareInFreeProTwo_of_continuous_image
    {n : ℕ} {r : FreeProfiniteGroup (Fin n)}
    {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : GQ2.IsProP 2 P)
    (f : ContinuousMonoidHom (FreeProfiniteGroup (Fin n)) P)
    (himage : ¬ ∃ z : P, f r = z ^ 2) :
    IsNonSquareInFreeProTwo r := by
  intro hsquare
  obtain ⟨z, hz⟩ := hsquare
  let fbar : ContinuousMonoidHom
      (GQ2.maxProPQuotient 2 (FreeProfiniteGroup (Fin n))) P :=
    (GQ2.maxProPHomEquiv hP).symm f
  apply himage
  refine ⟨fbar z, ?_⟩
  calc
    f r = fbar (freeProTwoRelatorImage r) := by
      exact (DFunLike.congr_fun ((GQ2.maxProPHomEquiv hP).apply_symm_apply f) r).symm
    _ = fbar (z ^ 2) := congrArg fbar hz
    _ = fbar z ^ 2 := map_pow fbar z 2

/-- The comparison interface specialized to the genuine presentation `presPro2 r`. -/
abbrev ContinuousModTwoOneRelatorFoxComparison
    {n : ℕ} (r : FreeProfiniteGroup (Fin n))
    (R X : Type)
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R X) :=
  ContinuousModTwoBarFoxComparison R X fox

/-- The classical one-relator pro-2 theorem at the remaining completed-group-ring boundary:
a relator which is not a square in the free pro-2 group has injective completed mod-two Fox
boundary.

This is deliberately separate from the concrete nonsquare theorem and from the bar comparison.
It contains no cohomology or cocycle statement. -/
structure NonSquareProTwoRelatorFoxInjectivity
    {n : ℕ} (r : FreeProfiniteGroup (Fin n))
    (R X : Type)
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R X) : Prop where
  injective : IsNonSquareInFreeProTwo r → Function.Injective fox.map

/-- A completed one-relator Fox comparison plus injectivity of its boundary gives scalar
continuous cohomological dimension at most two for the presented pro-2 group. -/
theorem modTwoHThreeExact_presPro2_of_injectiveFoxBoundary
    {n : ℕ} (r : FreeProfiniteGroup (Fin n))
    {R X : Type}
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R X)
    (comparison : ContinuousModTwoOneRelatorFoxComparison r R X fox)
    (hinjective : Function.Injective fox.map) :
    ModTwoHThreeExact (GQ2.Dyadic.MarkedCore.presPro2 r : Type) :=
  modTwoHThreeExact_of_barFoxComparison fox comparison hinjective

/-- The standard non-power route, with its three logically distinct inputs visible:

1. the concrete relator is nonsquare in the free pro-2 group;
2. the classical completed-Fox injectivity theorem;
3. the continuous bar/Fox comparison maps.

Only (1) is a word computation. -/
theorem modTwoHThreeExact_presPro2_of_nonSquare
    {n : ℕ} (r : FreeProfiniteGroup (Fin n))
    {R X : Type}
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R]
    [DistribMulAction (GQ2.Dyadic.MarkedCore.presPro2 r : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.MarkedCore.presPro2 r : Type) R X)
    (comparison : ContinuousModTwoOneRelatorFoxComparison r R X fox)
    (foxInjectivity : NonSquareProTwoRelatorFoxInjectivity r R X fox)
    (hnonsquare : IsNonSquareInFreeProTwo r) :
    ModTwoHThreeExact (GQ2.Dyadic.MarkedCore.presPro2 r : Type) :=
  modTwoHThreeExact_presPro2_of_injectiveFoxBoundary r fox comparison
    (foxInjectivity.injective hnonsquare)

/-- The exact remaining constructor for the improved square core: the relator is the actual
`sqRelator h`, not a finite-target resolver or a lookalike discrete word. -/
theorem modTwoHThreeExact_DSq_of_injectiveFoxBoundary
    (h : ℕ)
    {R X : Type}
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) R]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.SqCore.DSq h : Type) R X)
    (comparison : ContinuousModTwoBarFoxComparison R X fox)
    (hinjective : Function.Injective fox.map) :
    ModTwoHThreeExact (GQ2.Dyadic.SqCore.DSq h : Type) :=
  modTwoHThreeExact_of_barFoxComparison fox comparison hinjective

/-- The completed-Fox non-power theorem stated on the definitional carrier `DSq h`.  This
specialized wrapper avoids asking typeclass search to unfold the noncomputable definition of
`DSq` while retaining exactly the same mathematical premise as
`NonSquareProTwoRelatorFoxInjectivity`. -/
structure NonSquareDSqFoxInjectivity
    (h : ℕ)
    (R X : Type)
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) R]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.SqCore.DSq h : Type) R X) : Prop where
  injective : IsNonSquareInFreeProTwo (GQ2.Dyadic.SqCore.sqRelator h) →
    Function.Injective fox.map

/-- Nonsquare/completed-Fox constructor for the actual improved square relator.  A finite
2-group witness can discharge `hnonsquare`; the two structural arguments are exactly the
continuous completed Fox theorem which remains to be formalized. -/
theorem modTwoHThreeExact_DSq_of_nonSquare
    (h : ℕ)
    {R X : Type}
    [AddCommGroup R] [Module (ZMod 2) R]
    [AddCommGroup X] [Module (ZMod 2) X]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) R]
    [DistribMulAction (GQ2.Dyadic.SqCore.DSq h : Type) X]
    (fox : ModTwoFoxBoundary (GQ2.Dyadic.SqCore.DSq h : Type) R X)
    (comparison : ContinuousModTwoBarFoxComparison R X fox)
    (foxInjectivity : NonSquareDSqFoxInjectivity h R X fox)
    (hnonsquare : IsNonSquareInFreeProTwo (GQ2.Dyadic.SqCore.sqRelator h)) :
    ModTwoHThreeExact (GQ2.Dyadic.SqCore.DSq h : Type) :=
  modTwoHThreeExact_of_barFoxComparison fox comparison
    (foxInjectivity.injective hnonsquare)

end

end GQ2.ContCoh
