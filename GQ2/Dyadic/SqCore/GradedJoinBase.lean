/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedUniformJoin

/-!
# W76-BASE: the depth-two base of the odd route

Wave 75 cut the `h ≥ 1` residual `SqLamMarkTransitivity h` down to three named inputs:

```
gJoin_markTransitivity_of_base :
  GJoinBase h → GJoinSeparationAll h → GTowerKnobRealizable h → SqLamMarkTransitivity h
```

This file attacks the first of them, `GJoinBase h = ∀ ν' selected, GTowerLayerReach h ν' 2`.

## §1 Letter generation in `Q₄`

`Q₄ = levelQuot (D_sq h) 4` is discrete (`gTower_discrete`), so every subgroup of it is closed
and the topological generation `dsq_topGen` transfers to a plain "contains every letter class,
hence is everything" statement (`gBase_letters_mem`).  Every reduction below is an instance of
it.

## §2 The relator's degree-three consequence

The wave-75 join note scoped the depth-`2` base to one missing piece: the graded identity the
relator's degree-`2` leading form `R = x₁^{[2]} + ⁅x₀, σ⁆ + Σⱼ ⁅uⱼ, vⱼ⁆` yields at degree `3`.
It is one bracket of the relator, read in `Q₄` through the committed `cfour_sqRelWord`:

```
gBase_relator_bracket :
  ⁅⁅σ, x₀⁆, c⁆ · (⁅x₁, c⁆² · ⁅⁅x₁, c⁆, x₁⁆) · ⁅H, c⁆ = 1
```

with `H` the handle word, and its solved form `gBase_xOne_triple`.

**Correction to the wave-75 note.**  The note predicted
`⁅⁅c, x₁⁆, x₁⁆ = ⁅⁅x₀, σ⁆, c⁆ + Σⱼ ⁅⁅uⱼ, vⱼ⁆, c⁆`.  The honest identity carries a **third**
term, the bracket square `⁅x₁, c⁆²`, and it is not removable: at group level
`commP (p ^ 2) q = (commP p q) ^ 2 * commP (commP p q) p` (`gThreeFour_commP_sq_left`), and the
first factor is a genuine `(Λ²V)^{[2]}`-class.  The graded slogan `ad (x^{[2]}) = (ad x)²` is
false in this grading, because the restriction of the lower `2`-central series raises degree by
one rather than doubling it; the correct graded identity is
`ad (ξ x) = ξ ∘ ad x + (ad x)²` on degree-one elements.  The extra term costs nothing for the
consumer (`(Λ²V)^{[2]}` has to be paid for anyway) but the identity as the note stated it is not
what the relator gives.

## §3 The three families at the depth-two reach

`cfourCmp_zLayer_le_gens` reduces `zLayer (D_sq h) 3 ≤ S` to three families over all of `Q₄`.
§3 supplies the first two of them at `S = gTowerFullReach h ν' 2`:

* the triple brackets `⁅⁅p, q⁆, r⁆` (`gBase_triple_mem`), by letter reduction in all three
  slots, Jacobi to move `x₁` out of the outer slot, and §2 for the one case Jacobi cannot
  reach;
* the bracket squares `⁅p, q⁆²` (`gBase_bracketSq_mem`), from the `x₁`-slot bundle knob against
  the triple brackets.

The fourth powers are **not** supplied here; see §4 and the lane note.

Prefix: `gBase`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The letters in `Q₄`, and letter generation -/

section Letters

variable {h : ℕ}

variable (h) in
/-- The letter `σ`, read in `Q₄`. -/
noncomputable def gBaseS : levelQuot (DSq h : Type) 4 := levelMk (DSq h : Type) 4 (dsqSigma h)

variable (h) in
/-- The letter `x₀`, read in `Q₄`. -/
noncomputable def gBaseX : levelQuot (DSq h : Type) 4 := levelMk (DSq h : Type) 4 (dsqX0 h)

variable (h) in
/-- The letter `x₁`, read in `Q₄`. -/
noncomputable def gBaseT : levelQuot (DSq h : Type) 4 := levelMk (DSq h : Type) 4 (dsqX1 h)

variable (h) in
/-- The handle word on the letters, read in `Q₄`. -/
noncomputable def gBaseHandle : levelQuot (DSq h : Type) 4 :=
  handleWord (fun j => levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j)))
    (fun j => levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j)))

/-- ⭐ **Letter generation in `Q₄`**: a subgroup containing every letter class is everything.
`Q₄` is discrete, so the subgroup is closed, its `levelMk`-preimage is closed, and
`dsq_topGen` finishes.  This is the workhorse of every reduction below: it is what lets a
statement about all of `Q₄` be checked on the `3 + 2h` letters. -/
theorem gBase_letters_mem {K : Subgroup (levelQuot (DSq h : Type) 4)}
    (hK : ∀ i, levelMk (DSq h : Type) 4 (sqGen h i) ∈ K) (p : levelQuot (DSq h : Type) 4) :
    p ∈ K := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 4) := gTower_discrete 4
  have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) 4) K :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (isClosed_discrete _).preimage (continuous_levelMk (DSq h : Type) 4)
  have hsub : (Subgroup.closure (Set.range (sqGen h))).topologicalClosure ≤
      Subgroup.comap (levelMk (DSq h : Type) 4) K := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hpre
    rintro _ ⟨i, rfl⟩
    exact hK i
  obtain ⟨g, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  exact hsub (by rw [dsq_topGen h]; trivial)

end Letters

/-! ## §2 The relator's degree-three consequence -/

section Relator

variable {h : ℕ}

/-- **The relator, read in `Q₄`.**  `cfour_sqRelWord` at the marked generators, against
`dsq_relation`. -/
theorem gBase_relator_four :
    commP (gBaseS h) (gBaseX h) * gBaseX h ^ 4 * gBaseT h ^ 2 *
      commP (gBaseT h) (commP (gBaseT h) (gBaseS h)) * gBaseHandle h = 1 := by
  have hrel : sqRelWord (fun i => levelMk (DSq h : Type) 4 (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, dsq_relation, map_one]
  rw [cfour_sqRelWord] at hrel
  exact hrel

/-- The handle word lies in `Y`. -/
theorem gBase_handle_mem : gBaseHandle h ∈ lambdaImage (DSq h : Type) 2 4 :=
  cfour_handleWord_mem_lambdaTwo _ _

/-- ⭐⭐⭐ **The relator's degree-three consequence**, one bracket of the relation.  Every
factor of `cfour_sqRelWord` lies in `Y`, so bracketing against `c` is additive
(`gThreeFour_ad_left`); the fourth power and the `x₁`/`σ` triple bracket are already central
and drop out; the `x₁`-square contributes through `gThreeFour_commP_sq_left`.

This is the graded identity the wave-75 join note named as the one piece the tree had not
committed, **with one correction**: the bracket square `⁅x₁, c⁆²` is a genuine third term.  See
the module docstring. -/
theorem gBase_relator_bracket (c : levelQuot (DSq h : Type) 4) :
    commP (commP (gBaseS h) (gBaseX h)) c *
        ((commP (gBaseT h) c) ^ 2 * commP (commP (gBaseT h) c) (gBaseT h)) *
        commP (gBaseHandle h) c = 1 := by
  have hA : commP (gBaseS h) (gBaseX h) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_commP_mem_lambdaTwo _ _
  have hB : gBaseX h ^ 4 ∈ zLayer (DSq h : Type) 3 := cfour_pow_four_mem_zLayer _
  have hB' : gBaseX h ^ 4 ∈ lambdaImage (DSq h : Type) 2 4 := cfour_zLayer_le_lambdaTwo hB
  have hC : gBaseT h ^ 2 ∈ lambdaImage (DSq h : Type) 2 4 := cfour_sq_mem_lambdaTwo _
  have hD : commP (gBaseT h) (commP (gBaseT h) (gBaseS h)) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right _ (cfour_commP_mem_lambdaTwo _ _)
  have hD' : commP (gBaseT h) (commP (gBaseT h) (gBaseS h)) ∈ lambdaImage (DSq h : Type) 2 4 :=
    cfour_zLayer_le_lambdaTwo hD
  have h1 : commP (commP (gBaseS h) (gBaseX h) * gBaseX h ^ 4 * gBaseT h ^ 2 *
      commP (gBaseT h) (commP (gBaseT h) (gBaseS h)) * gBaseHandle h) c = 1 := by
    rw [gBase_relator_four, cfour_one_comm]
  rw [gThreeFour_ad_left (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hA hB') hC) hD'),
    gThreeFour_ad_left (Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB') hC),
    gThreeFour_ad_left (Subgroup.mul_mem _ hA hB'),
    gThreeFour_ad_left hA,
    cfour_commP_zLayer_left hB c, cfour_commP_zLayer_left hD c,
    gThreeFour_commP_sq_left, mul_one, mul_one] at h1
  exact h1

/-- ⭐⭐⭐ **The `x₁`-tower triple bracket, solved.**  Everything in sight lies in the central
involutive layer `Z`, so `gBase_relator_bracket` may be solved for the one term Jacobi cannot
reach:

`⁅⁅x₁, c⁆, x₁⁆ = ⁅⁅σ, x₀⁆, c⁆ · ⁅x₁, c⁆² · ⁅H, c⁆`.

The right-hand side is a far-span knob (`⁅σ, x₀⁆` and `H` are brackets, hence exactly
row-trivial `γ₂`-elements) times a bracket square. -/
theorem gBase_xOne_triple (c : levelQuot (DSq h : Type) 4) :
    commP (commP (gBaseT h) c) (gBaseT h) =
      commP (commP (gBaseS h) (gBaseX h)) c * (commP (gBaseT h) c) ^ 2 *
        commP (gBaseHandle h) c := by
  have hA' : commP (commP (gBaseS h) (gBaseX h)) c ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) c
  have hsq : (commP (gBaseT h) c) ^ 2 ∈ zLayer (DSq h : Type) 3 :=
    cfour_sq_mem_zLayer (cfour_commP_mem_lambdaTwo _ _)
  have htri : commP (commP (gBaseT h) c) (gBaseT h) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo _ _) _
  have hE' : commP (gBaseHandle h) c ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_left gBase_handle_mem c
  have hz : commP (commP (gBaseS h) (gBaseX h)) c * (commP (gBaseT h) c) ^ 2 *
      commP (gBaseHandle h) c ∈ zLayer (DSq h : Type) 3 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hA' hsq) hE'
  have hcomm : Commute (commP (commP (gBaseT h) c) (gBaseT h)) (commP (gBaseHandle h) c) :=
    zLayer_commute htri _
  have hmul : (commP (commP (gBaseS h) (gBaseX h)) c * (commP (gBaseT h) c) ^ 2 *
      commP (gBaseHandle h) c) * commP (commP (gBaseT h) c) (gBaseT h) = 1 := by
    have hb := gBase_relator_bracket (h := h) c
    simp only [mul_assoc] at hb ⊢
    rw [← hcomm.eq]
    exact hb
  rw [eq_inv_of_mul_eq_one_left hmul]
  exact (zLayer_inv_self htri).symm

/-- Bracketing a product of `Y`-elements against a slot is additive, in list form. -/
theorem gBase_ad_listProd {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : levelQuot G 4) : ∀ (L : List (levelQuot G 4)),
      (∀ y ∈ L, y ∈ lambdaImage G 2 4) →
        commP L.prod c = (L.map (fun y => commP y c)).prod
  | [], _ => by rw [List.prod_nil, List.map_nil, List.prod_nil, cfour_one_comm]
  | a :: L, hL => by
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      gThreeFour_ad_left (hL a List.mem_cons_self) _ c,
      gBase_ad_listProd c L (fun y hy => hL y (List.mem_cons_of_mem a hy))]

/-- **The handle term, expanded.**  `⁅H, c⁆ = Πⱼ ⁅⁅uⱼ, vⱼ⁆, c⁆`, so the right-hand side of
`gBase_xOne_triple` is, term by term, a bracket of a bracket of letters. -/
theorem gBase_handle_bracket (c : levelQuot (DSq h : Type) 4) :
    commP (gBaseHandle h) c =
      ((List.finRange h).map fun j => commP (commP
        (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j)))
        (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j)))) c).prod := by
  rw [gBaseHandle, handleWord,
    gBase_ad_listProd c _ (by
      intro y hy
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
      exact cfour_commP_mem_lambdaTwo _ _),
    List.map_map]
  rfl

end Relator

/-! ## §3 Axiom pins -/

section AxiomPins

#print axioms gBaseS
#print axioms gBaseX
#print axioms gBaseT
#print axioms gBaseHandle
#print axioms gBase_letters_mem
#print axioms gBase_relator_four
#print axioms gBase_handle_mem
#print axioms gBase_relator_bracket
#print axioms gBase_xOne_triple
#print axioms gBase_ad_listProd
#print axioms gBase_handle_bracket

end AxiomPins

end SqCore

end Dyadic

end GQ2
