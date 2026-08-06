/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.SqModelCupForm
import GQ2.Dyadic.Instances.GammaLOddDegreePresentingFrame

/-!
# The presenting frame is cup-adapted, unconditionally

`GammaLOddDegreePresentingFrame` builds, with no hypothesis at odd degree, a Frattini frame
`frameOfOrientedEquiv f horient` of `G_K(2)` out of the unconditional oriented equivalence
`f : D_sq(h) ≃ₜ* G_K(2)`, and shows it carries the improved relator.  Its docstring records
what it could *not* do:

> `frameOfOrientedEquiv` is **not** shown to be cup-adapted. … The missing step is the converse
> Labute direction — that the cup form of `G_K(2)` in the basis dual to a *presenting* tuple is
> the relator's quadratic initial Gram. … the repo has no `H²(D_sq(h))` cup computation to land
> it on.

`SqModelCupForm` supplies that computation, and this file closes the loop:
`isCupAdapted_frameOfOrientedEquiv`.  So at every odd degree there is a Frattini frame which is
cup-adapted **and** presenting, with no binder (`exists_cupAdapted_presentingFrame_oddDegree`).

## The mechanism, and why no transport lemma was needed

The naive route is to transport the cup form along `f` — pull `H²(G_K(2))` back to
`H²(D_sq h)`, check that the pullback commutes with `⌣`, and match the two identifications of
`H²` with `𝔽₂`.  That route needs a cup-functoriality lemma and a comparison of two `H² ≃ 𝔽₂`
identifications.

The route taken here skips the transport entirely.  `SqModelCupForm`'s
`obsH2_sqNatWord_characterCup` is stated for an *arbitrary* group carrying a marking that kills
the improved word, so it can be read **directly at `G_K(2)`** with the marking `f ∘ sqGen h`.
That gives a second functional on `H²(G_K(2), 𝔽₂)`, the frame obstruction `frameObs`, which
computes the Gram on the nose.  What remains is only to identify `frameObs` with the field's own
functional `b_K = inv_K ∘ ⌣`, and that is where "`H²` is one-dimensional, so its identification
with `𝔽₂` is unique" enters — in the sharp form

  *two injective additive maps `A →+ 𝔽₂` are equal* (`addMonoidHom_zmodTwo_eq_of_injective`),

which needs no cardinality input at all.  Injectivity of `frameObs` is
`WordCoh.obsH2_injective` at the transported presentation `presentedByOfEquiv`; injectivity of
`inv_K ∘ inf²` is `h2InflationGalK_injective` plus the invariant map being an equivalence.

## What the cup statement does *not* need

`cupFormK_eq_quadraticInitialGram_of_equiv` takes no orientation clause: the cup form only sees
the marking, so cup-adaptation of a presenting tuple is independent of the cyclotomic
constructor table.  `isCupAdapted_frameOfOrientedEquiv` is that theorem applied at the
generators of `frameOfOrientedEquiv`, and the orientation only enters through the frame
structure itself.

## Axioms

`cupFormK_eq_quadraticInitialGram_of_equiv` prints std-3 together with **B6** (`tateDualityAt`,
through `FieldData.invGalK` and `card_H2_zmodTwo_galK`) and nothing else.
`isCupAdapted_frameOfOrientedEquiv` adds **B1** (`absGalQ2_isTopologicallyFinitelyGenerated`),
carried by the frame's `levelTwoGen` field; the unconditional existence statements add the
census axioms already carried by `orientedEquiv_of_oddDegree` (**B5**, **B5-K**, **B7**,
**B11a**).  Nothing new is introduced.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic ContCoh SqCore GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Two injective functionals to `𝔽₂` agree -/

/-- **The identification of a group with `𝔽₂` is unique.**  Any two injective additive maps
into `ZMod 2` coincide: each sends `0` to `0` and everything else to the unique nonzero scalar.

This is the sharp form of "`H²` is one-dimensional, so its identification with `𝔽₂` is unique",
and unlike the cardinality formulation it takes no hypothesis on the source. -/
theorem addMonoidHom_zmodTwo_eq_of_injective {A : Type*} [AddCommGroup A]
    (α β : A →+ ZMod 2) (hα : Function.Injective α) (hβ : Function.Injective β) : α = β := by
  have hne : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  ext a
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  · have h1 : α a ≠ 0 := fun hz => ha (hα (hz.trans (map_zero α).symm))
    have h2 : β a ≠ 0 := fun hz => ha (hβ (hz.trans (map_zero β).symm))
    rw [hne _ h1, hne _ h2]

/-! ## §2 The field-side identification `H²(G_K(2), 𝔽₂) ≃ 𝔽₂` -/

section FieldSide

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The invariant map of `G_K(2)`**: local Tate duality's `inv_K` pulled back along
degree-two inflation.  It is the functional through which `FieldData.cupFormK` is defined, once
both slots are inflated from `G_K(2)`. -/
def maxProTwoInv (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) →+ ZMod 2 :=
  (FieldData.invGalK K).toAddMonoidHom.comp (h2InflationGalK (K := K))

/-- `maxProTwoInv` is injective: degree-two inflation `H²(G_K(2)) → H²(G_K)` is injective and
the invariant map is an equivalence. -/
theorem maxProTwoInv_injective : Function.Injective (maxProTwoInv K) :=
  (FieldData.invGalK K).injective.comp (h2InflationGalK_injective (K := K))

/-- **The field cup form is `maxProTwoInv` of the cup product on `G_K(2)`.**  Degree-one
inflation is the equivalence `h1MaxProTwoEquivGalK` and it respects cup products, so the two
descriptions of `b_K` on inflated classes agree. -/
theorem cupFormK_eq_maxProTwoInv (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    FieldData.cupFormK K (h1MaxProTwoEquivGalK (K := K) x) (h1MaxProTwoEquivGalK (K := K) y) =
      maxProTwoInv K
        (trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) (fun _ _ => rfl) x y) :=
  congrArg (FieldData.invGalK K) (inf2_trivialCupPairing_maxProPMk_galK (K := K) x y).symm

end FieldSide

/-! ## §3 The presenting marking is a presentation of `G_K(2)` -/

section Presenting

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The image marking is a marked relator.**  `IsFrattini` is a property of the word alone,
and the relation holds because `f` is a homomorphism killing `dsq_relation`.  Note that no
orientation clause is involved: the improved word dies at the image of *any* equivalence. -/
theorem markedRelatorOfEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    WordCoh.MarkedRelator (maxProPQuotient 2 (GalK K)) (MarkedCore.sqNatWord h)
      (fun i => f (sqGen h i)) :=
  ⟨sqNatWord_isFrattini h, by
    show sqRelWord (fun i => f (sqGen h i)) = 1
    rw [← map_sqRelWord f (sqGen h), dsq_relation h, map_one]⟩

/-- **The image marking presents `G_K(2)`.**  Transport of `presentedBy_DSq` along the
equivalence: lifts are composed with `f⁻¹`, and homs out of `G_K(2)` are determined on the image
marking because `f` is surjective. -/
def presentedByOfEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    WordCoh.PresentedBy (maxProPQuotient 2 (GalK K)) (MarkedCore.sqNatWord h)
      (fun i => f (sqGen h i)) where
  liftHom hP ν hν :=
    ((presentedBy_DSq h).liftHom hP ν hν).comp ⟨f.symm.toMonoidHom, f.symm.continuous_toFun⟩
  liftHom_mark hP ν hν k := by
    show (presentedBy_DSq h).liftHom hP ν hν (f.symm (f (sqGen h k))) = ν k
    rw [f.symm_apply_apply]
    exact (presentedBy_DSq h).liftHom_mark hP ν hν k
  hom_ext φ ψ hgen := by
    have hcomp : φ.comp ⟨f.toMonoidHom, f.continuous_toFun⟩ =
        ψ.comp ⟨f.toMonoidHom, f.continuous_toFun⟩ :=
      (presentedBy_DSq h).hom_ext _ _ hgen
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun hcomp (f.symm x)
    show φ x = ψ x
    rw [← f.apply_symm_apply x]
    exact hx

/-- **The frame obstruction**: the one-relator obstruction functional on `H²(G_K(2), 𝔽₂)`
attached to the improved word at the marking `f ∘ sqGen h`. -/
def frameObs {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h) (fun i => f (sqGen h i))
    (markedRelatorOfEquiv f)

omit [FiniteDimensional ℚ_[2] K] in
/-- The frame obstruction is injective: `WordCoh.obsH2_injective` at the transported
presentation. -/
theorem frameObs_injective {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    Function.Injective (frameObs f) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (MarkedCore.sqNatWord h) (fun i => f (sqGen h i))
    (markedRelatorOfEquiv f) (presentedByOfEquiv f) isProP_maxProPQuotient

/-- **The two identifications of `H²(G_K(2), 𝔽₂)` with `𝔽₂` coincide.**  The arithmetic one is
`inv_K` after inflation; the presentation one is the improved relator's obstruction at the
image marking.  Both are injective, hence equal. -/
theorem maxProTwoInv_eq_frameObs {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    maxProTwoInv K = frameObs f :=
  addMonoidHom_zmodTwo_eq_of_injective _ _ (maxProTwoInv_injective (K := K))
    (frameObs_injective f)

/-- **The converse Labute direction, in the odd-degree square case.**  The mod-two cup form of
`G_K(2)`, read in the basis dual to the image of the canonical generating tuple of `D_sq(h)`
under *any* topological isomorphism `f`, is the improved relator's quadratic initial Gram.

No orientation clause appears: the cup form only sees the marking, so cup-adaptation of a
presenting tuple is free of the cyclotomic constructor table.  The proof composes §2's
description of `b_K`, §3's identification of the two `𝔽₂`-valued functionals on
`H²(G_K(2), 𝔽₂)`, and `SqModelCupForm.obsH2_sqNatWord_characterCup` read at `G_K(2)`. -/
theorem cupFormK_eq_quadraticInitialGram_of_equiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) =
      GQ2.ContCoh.sqRelatorQuadraticInitialGram h
        (fun i j => Multiplicative.toAdd (c (f (sqGen h i))) *
          Multiplicative.toAdd (d (f (sqGen h j)))) := by
  rw [cupFormK_eq_maxProTwoInv, maxProTwoInv_eq_frameObs f]
  exact obsH2_sqNatWord_characterCup (fun _ _ => rfl) h (fun i => f (sqGen h i))
    (markedRelatorOfEquiv f) c d

/-- **The presenting frame is cup-adapted.**  `IsCupAdapted` is exactly
`cupFormK_eq_quadraticInitialGram_of_equiv` at the frame's generators. -/
theorem isCupAdapted_frameOfOrientedEquiv {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) :
    (frameOfOrientedEquiv f horient).IsCupAdapted :=
  fun c d => cupFormK_eq_quadraticInitialGram_of_equiv f c d

/-- **A cup-adapted presenting Frattini frame exists at every odd degree, with no hypothesis.**
This is `exists_presentingFrame_oddDegree` with cup-adaptation added: one frame carrying the
improved relator, the cyclotomic constructor table, topological generation, the level-three
relation, *and* the field cup form in the relator's quadratic initial Gram. -/
theorem exists_cupAdapted_presentingFrame_oddDegree {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
      (Subgroup.closure (Set.range F.generators)).topologicalClosure = ⊤ ∧
        F.LevelThreeRelation := by
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree (K := K) hdeg
  exact ⟨frameOfOrientedEquiv f horient, isCupAdapted_frameOfOrientedEquiv f horient,
    sqRelWord_frameOfOrientedEquiv f horient,
    topologicalClosure_frameOfOrientedEquiv f horient,
    levelThreeRelation_frameOfOrientedEquiv f horient⟩

end Presenting

/-! ## §4 The frame supply, unconditionally -/

/-- **`OddDegreeSqCyclotomicFrattiniFrameSupply`, from the presentation side.**  The
cup-adapted frame supply of `GammaLSylowPreimageFieldLabuteLevelThreeSeed` is discharged by the
presenting frame, with no arithmetic Witt-adaptation input. -/
theorem oddDegreeSqCyclotomicFrattiniFrameSupply_of_presentingFrame :
    OddDegreeSqCyclotomicFrattiniFrameSupply := by
  intro K _ _ _ _ hodd
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨f, horient⟩ :=
    orientedEquiv_of_oddDegree (K := K) (h := (Module.finrank ℚ_[2] K - 1) / 2) (by omega)
  exact ⟨frameOfOrientedEquiv f horient, isCupAdapted_frameOfOrientedEquiv f horient⟩

#print axioms addMonoidHom_zmodTwo_eq_of_injective
#print axioms maxProTwoInv
#print axioms maxProTwoInv_injective
#print axioms cupFormK_eq_maxProTwoInv
#print axioms markedRelatorOfEquiv
#print axioms presentedByOfEquiv
#print axioms frameObs
#print axioms frameObs_injective
#print axioms maxProTwoInv_eq_frameObs
#print axioms isCupAdapted_frameOfOrientedEquiv
#print axioms cupFormK_eq_quadraticInitialGram_of_equiv
#print axioms exists_cupAdapted_presentingFrame_oddDegree
#print axioms oddDegreeSqCyclotomicFrattiniFrameSupply_of_presentingFrame

end

end GQ2.Dyadic.LSquare
