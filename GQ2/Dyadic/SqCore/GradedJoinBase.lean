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

/-! ## §3 The triple brackets and the bracket squares at the depth-two reach -/

section Triples

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The bracket is antisymmetric on the nose. -/
theorem gBase_commP_swap (p q : levelQuot G 4) : commP p q = (commP q p)⁻¹ := by
  simp only [commP]; group

/-- ⭐ **The triple bracket is additive in its inner-left slot.**  The correction term of
`cfour_commP_mul_left` is already central, so the outer bracket kills it. -/
theorem gBase_triple_mul_left (p p' q r : levelQuot G 4) :
    commP (commP (p * p') q) r = commP (commP p q) r * commP (commP p' q) r := by
  have hX : commP p q ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p q
  have hY : commP (commP p q) p' ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hX p'
  rw [cfour_commP_mul_left p p' q,
    gThreeFour_ad_left (Subgroup.mul_mem _ hX (cfour_zLayer_le_lambdaTwo hY)),
    gThreeFour_ad_left hX, cfour_commP_zLayer_left hY r, mul_one]

/-- ⭐ **The triple bracket is additive in its inner-right slot.** -/
theorem gBase_triple_mul_right (p q q' r : levelQuot G 4) :
    commP (commP p (q * q')) r = commP (commP p q') r * commP (commP p q) r := by
  have hX : commP p q' ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p q'
  have hY : commP p q ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p q
  have hZ : commP (commP p q) q' ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hY q'
  rw [cfour_commP_mul_right p q q',
    gThreeFour_ad_left (Subgroup.mul_mem _ hX hY),
    gThreeFour_ad_left hX, cfour_commP_zLayer_left hZ r, mul_one]

/-- The inner-left slot of a triple bracket, at an inverse. -/
theorem gBase_triple_inv_left (p q r : levelQuot G 4) :
    commP (commP p⁻¹ q) r = (commP (commP p q) r)⁻¹ := by
  have hh := gBase_triple_mul_left p p⁻¹ q r
  rw [mul_inv_cancel, cfour_one_comm, cfour_one_comm] at hh
  exact eq_inv_of_mul_eq_one_right hh.symm

/-- The inner-right slot of a triple bracket, at an inverse. -/
theorem gBase_triple_inv_right (p q r : levelQuot G 4) :
    commP (commP p q⁻¹) r = (commP (commP p q) r)⁻¹ := by
  have hh := gBase_triple_mul_right p q q⁻¹ r
  rw [mul_inv_cancel, cfour_comm_one, cfour_one_comm] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

variable (G) in
/-- The inner-left test subgroup of a triple-bracket family. -/
def gBaseTripleLeft (S : Subgroup (levelQuot G 4)) (r : levelQuot G 4) :
    Subgroup (levelQuot G 4) where
  carrier := {p | ∀ q, commP (commP p q) r ∈ S}
  one_mem' := fun q => by rw [cfour_one_comm, cfour_one_comm]; exact Subgroup.one_mem _
  mul_mem' := fun {_ _} hp hp' q => by
    rw [gBase_triple_mul_left]; exact Subgroup.mul_mem _ (hp q) (hp' q)
  inv_mem' := fun {_} hp q => by
    rw [gBase_triple_inv_left]; exact Subgroup.inv_mem _ (hp q)

variable (G) in
/-- The inner-right test subgroup of a triple-bracket family. -/
def gBaseTripleRight (S : Subgroup (levelQuot G 4)) (p r : levelQuot G 4) :
    Subgroup (levelQuot G 4) where
  carrier := {q | commP (commP p q) r ∈ S}
  one_mem' := by
    show commP (commP p 1) r ∈ S
    rw [cfour_comm_one, cfour_one_comm]; exact Subgroup.one_mem _
  mul_mem' := fun {_ _} hq hq' => by
    show commP (commP p (_ * _)) r ∈ S
    rw [gBase_triple_mul_right]; exact Subgroup.mul_mem _ hq' hq
  inv_mem' := fun {_} hq => by
    show commP (commP p _⁻¹) r ∈ S
    rw [gBase_triple_inv_right]; exact Subgroup.inv_mem _ hq

end Triples

section Base

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐ **Every bracket is an admissible depth-`2` correction.**  Both rows are characters into
an abelian group, so they kill every commutator outright; this is what makes the whole
`L₃(V)`-half of the base a knob question rather than a row question. -/
theorem gBase_adm_commP (a b : (DSq h : Type)) : GTowerAdm h nu' 2 (commP a b) :=
  ⟨cfour_commP_mem_two a b, gTower_row_commP _ a b, gTower_row_commP nu' a b⟩

/-- A bracket knob at depth `2`: `⁅⁅a, b⁆, q⁆` for `q` in the far span. -/
theorem gBase_knob_mem {a b q : (DSq h : Type)} (hq : q ∈ gTowerFar h) :
    levelMk (DSq h : Type) 4 (commP (commP a b) q) ∈ gTowerReach h nu' 2 :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨commP a b, q, gBase_adm_commP a b, hq, rfl⟩))

/-- The `x₁`-slot bundle knob at depth `2`, at a bracket correction. -/
theorem gBase_bundle_mem (a b : (DSq h : Type)) :
    levelMk (DSq h : Type) 4 (commP a b ^ 2 * commP (commP a b) (dsqX1 h))
      ∈ gTowerReach h nu' 2 :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨commP a b, gBase_adm_commP a b, rfl⟩))

/-- The `levelMk`-image of a triple bracket, in `Q₄` vocabulary. -/
theorem gBase_levelMk_triple (a b g : (DSq h : Type)) :
    levelMk (DSq h : Type) 4 (commP (commP a b) g) =
      commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
        (levelMk (DSq h : Type) 4 g) := by
  simp only [commP, map_mul, map_inv]

/-- ⭐ **Triple brackets with a non-`x₁` letter in the outer slot reach**: they are bracket
knobs of the admissible correction `⁅a, b⁆`. -/
theorem gBase_triple_far (p q : levelQuot (DSq h : Type) 4) {i : Fin (sqRank h)} (hi : i ≠ 2) :
    commP (commP p q) (levelMk (DSq h : Type) 4 (sqGen h i)) ∈ gTowerReach h nu' 2 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  rw [← gBase_levelMk_triple]
  exact gBase_knob_mem (gTower_letters_mem_far i hi)

variable (h nu') in
/-- ⭐⭐⭐ **The residual of the depth-two base**, isolated: the `x₁`-slot triple brackets
`⁅⁅x₁, letter⁆, x₁⁆`.  These are the only triple brackets Jacobi cannot move out of the `x₁`
outer slot, and by `gBase_xOne_triple` they are interchangeable with the bracket squares
`⁅x₁, letter⁆²`, the `(Λ²V)^{[2]}`-classes at the `x₁` slot. -/
def GBaseXOneTriple : Prop :=
  ∀ i : Fin (sqRank h),
    commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqGen h i))) (gBaseT h)
      ∈ gTowerReach h nu' 2

/-- ⭐⭐ **The `x₁` outer slot, at letter pairs.**  Jacobi moves `x₁` out of the outer slot
whenever neither inner slot is `x₁`; when one of them is, the bracket is the residual; when
both are, the bracket is trivial. -/
theorem gBase_triple_xOne_letters (H : GBaseXOneTriple h nu') (i i' : Fin (sqRank h)) :
    commP (commP (levelMk (DSq h : Type) 4 (sqGen h i))
      (levelMk (DSq h : Type) 4 (sqGen h i'))) (gBaseT h) ∈ gTowerReach h nu' 2 := by
  by_cases hi : i = 2
  · subst hi
    by_cases hi' : i' = 2
    · subst hi'
      rw [show levelMk (DSq h : Type) 4 (sqGen h 2) = gBaseT h from rfl, cfour_comm_self,
        cfour_one_comm]
      exact Subgroup.one_mem _
    · exact H i'
  · by_cases hi' : i' = 2
    · subst hi'
      rw [gBase_commP_swap (levelMk (DSq h : Type) 4 (sqGen h i)),
        gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo _ _)]
      exact H i
    · have hjac := gThreeFour_jacobi (levelMk (DSq h : Type) 4 (sqGen h i))
        (levelMk (DSq h : Type) 4 (sqGen h i')) (gBaseT h)
      have hsol : commP (commP (levelMk (DSq h : Type) 4 (sqGen h i))
          (levelMk (DSq h : Type) 4 (sqGen h i'))) (gBaseT h) =
          (commP (commP (levelMk (DSq h : Type) 4 (sqGen h i')) (gBaseT h))
              (levelMk (DSq h : Type) 4 (sqGen h i)) *
            commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqGen h i)))
              (levelMk (DSq h : Type) 4 (sqGen h i')))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hjac)
      rw [hsol]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (gBase_triple_far _ _ hi)
        (gBase_triple_far _ _ hi'))

/-- ⭐⭐ **The `x₁` outer slot, in general.**  Both inner slots reduce to letters, the triple
bracket being additive in each of them. -/
theorem gBase_triple_xOne (H : GBaseXOneTriple h nu') (p q : levelQuot (DSq h : Type) 4) :
    commP (commP p q) (gBaseT h) ∈ gTowerReach h nu' 2 := by
  have hleft : p ∈ gBaseTripleLeft (DSq h : Type) (gTowerReach h nu' 2) (gBaseT h) := by
    refine gBase_letters_mem (fun i => ?_) p
    intro q
    exact gBase_letters_mem (K := gBaseTripleRight (DSq h : Type)
      (gTowerReach h nu' 2) (levelMk (DSq h : Type) 4 (sqGen h i)) (gBaseT h))
      (fun i' => gBase_triple_xOne_letters H i i') q
  exact hleft q

/-- A triple bracket of letters against the outer letter slot, packaged for the closure
induction of `gBase_triple`. -/
theorem gBase_letter_triple_mem (H : GBaseXOneTriple h nu') (a b : (DSq h : Type))
    (i : Fin (sqRank h)) :
    levelMk (DSq h : Type) 4 (commP (commP a b) (sqGen h i)) ∈ gTowerReach h nu' 2 := by
  by_cases hi : i = 2
  · subst hi
    rw [gBase_levelMk_triple]
    exact gBase_triple_xOne H _ _
  · exact gBase_knob_mem (gTower_letters_mem_far i hi)

/-- ⭐⭐⭐ **Every triple bracket reaches**, granted the residual.  The outer slot reduces to
the letters by the committed `gTower_commHom_span`; the non-`x₁` letters are far-span knobs and
the `x₁` letter is the previous theorem. -/
theorem gBase_triple (H : GBaseXOneTriple h nu') (p q r : levelQuot (DSq h : Type) 4) :
    commP (commP p q) r ∈ gTowerReach h nu' 2 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  obtain ⟨g, rfl⟩ := levelMk_surjective (DSq h : Type) 4 r
  rw [← gBase_levelMk_triple]
  have hspan := gTower_commHom_span (h := h) (k := 2) (cfour_commP_mem_two a b) g
  refine Subgroup.closure_le (K := gTowerReach h nu' 2) |>.2 ?_ hspan
  rintro _ ⟨i, rfl⟩
  exact gBase_letter_triple_mem H a b i

/-- ⭐⭐ **Every bracket square reaches**, granted the residual: the `x₁`-slot bundle knob is
the square times the `x₁`-outer triple bracket, and the latter reaches by `gBase_triple`. -/
theorem gBase_bracketSq (H : GBaseXOneTriple h nu') (p q : levelQuot (DSq h : Type) 4) :
    commP p q ^ 2 ∈ gTowerReach h nu' 2 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  have hbundle := gBase_bundle_mem (nu' := nu') a b
  rw [map_mul, map_pow, gBase_levelMk_triple] at hbundle
  have hsplit : commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b) ^ 2 =
      (levelMk (DSq h : Type) 4 (commP a b) ^ 2 *
        commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
          (levelMk (DSq h : Type) 4 (dsqX1 h))) *
      (commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
          (levelMk (DSq h : Type) 4 (dsqX1 h)))⁻¹ := by
    rw [mul_inv_cancel_right]
    simp only [commP, map_mul, map_inv]
  rw [hsplit]
  exact Subgroup.mul_mem _ hbundle (Subgroup.inv_mem _ (gBase_triple H _ _ _))

end Base

/-! ## §5 Axiom pins -/

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
#print axioms gBase_commP_swap
#print axioms gBase_triple_mul_left
#print axioms gBase_triple_mul_right
#print axioms gBase_triple_inv_left
#print axioms gBase_triple_inv_right
#print axioms gBaseTripleLeft
#print axioms gBaseTripleRight
#print axioms gBase_adm_commP
#print axioms gBase_knob_mem
#print axioms gBase_bundle_mem
#print axioms gBase_levelMk_triple
#print axioms gBase_triple_far
#print axioms GQ2.Dyadic.SqCore.GBaseXOneTriple
#print axioms gBase_triple_xOne_letters
#print axioms gBase_triple_xOne
#print axioms gBase_letter_triple_mem
#print axioms gBase_triple
#print axioms gBase_bracketSq

end AxiomPins

end SqCore

end Dyadic

end GQ2
