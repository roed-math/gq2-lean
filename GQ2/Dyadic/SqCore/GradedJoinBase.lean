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

## §3 and §4: the base, reduced to one atomic family

`cfourCmp_zLayer_le_gens` reduces `zLayer (D_sq h) 3 ≤ S` to three families over all of `Q₄`,
and §§3-4 supply all three at `S = gTowerFullReach h ν' 2`, from **one** hypothesis:

```
GBaseXOneTriple h ν' :  ∀ i, ⁅⁅x₁, letter i⁆, x₁⁆ ∈ gTowerReach h ν' 2
```

* the triple brackets `⁅⁅p, q⁆, r⁆` (`gBase_triple`): the outer slot reduces to the letters by
  `gTower_commHom_span`, the non-`x₁` letters are far-span knobs, and for the `x₁` letter both
  inner slots reduce to letters (the triple bracket being additive in each) where Jacobi
  discharges every pair except the ones with an `x₁`, which is the hypothesis;
* the bracket squares `⁅p, q⁆²` (`gBase_bracketSq`): the `x₁`-slot bundle knob divided by a
  triple bracket;
* the fourth powers `p⁴` (`gBase_pow_four`): `p⁴ = (p²)²` with `p²` a `γ₂`-class, and the row
  grading splits a `γ₂`-square into a bundle knob (divided by `gBase_comm_xOne`) and a
  complement tower.  No letter-by-letter identification of the towers is needed.

The conclusion is `gBase_joinBase_of_residual : GBaseResidual h → GJoinBase h`, and with it
`gBase_markTransitivity_of_residual`.  So wave 75's first named input is **discharged by** the
`2 + 2h` brackets `⁅⁅x₁, letter⁆, x₁⁆`, and by nothing else in this file.

⚠ **`2 + 2h`, not `3 + 2h`.**  `GBaseXOneTriple` is *indexed* by all `sqRank h = 3 + 2h`
letters, but one of them is `x₁` itself and `⁅⁅x₁, x₁⁆, x₁⁆` is trivial on the nose, so it is in
the reach for free at every `h` and carries no content.  Proved downstream as
`gDecide_triple_self` (`SqCore/GradedBaseDecide.lean`, wave 77), by `cfour_comm_self` and
`cfour_one_comm`.

⚠ **One direction only.**  What is proved here is `GBaseResidual h → GJoinBase h`.  The converse
is *not* in this file, so "wave 75's first named input **is** the brackets" would be an
over-reading: supplying the brackets suffices for `GJoinBase h`, and refuting `GJoinBase h`
refutes them, but refuting the brackets does not by itself refute `GJoinBase h`.
`gBase_residual_iff` is an equivalence between two *spellings of one class* at a fixed `c`, not a
converse to `gBase_joinBase_of_residual`.

**Whether they hold is open, and the lane note argues they do not.**  Nothing in this file is
evidence either way: every statement here is a reduction, and `GBaseXOneTriple` is a
hypothesis.  See `docs/dyadic/w76-base-note.md`.

⚠⚠ **[W78-HOUSE, as of `e6bbd2b9`: no longer open.  They do not hold.**  `gDecide_not_baseResidual`
and `gDecide_not_joinBase` (`SqCore/GradedBaseDecide.lean`, wave 77) refute `GBaseResidual h`
and `GJoinBase h` at every `h`, from a group of order sixteen and with no structure theorem.
So `gBase_markTransitivity_of_residual` and `gBase_supply_of_residual` below are **vacuous**,
and the sentence "whether they hold is open" is superseded.  The reductions in this file are
unaffected and remain correct; what has gone is their input.  `SqClassClearingSupply h k` is
untouched by that refutation.]**

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

/-- The `levelMk`-image of a bracket, in `Q₄` vocabulary. -/
theorem gBase_levelMk_commP (a b : (DSq h : Type)) :
    levelMk (DSq h : Type) 4 (commP a b) =
      commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b) := by
  simp only [commP, map_mul, map_inv]

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

/-- The four far letters, as members of the far span. -/
theorem gBase_sigma_far : dsqSigma h ∈ gTowerFar h :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inl (Or.inl (Or.inl rfl))))

theorem gBase_x0_far : dsqX0 h ∈ gTowerFar h :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr rfl))))

theorem gBase_handleU_far (j : Fin h) : sqGen h (sqHandleIdxU j) ∈ gTowerFar h :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inl (Or.inr ⟨j, rfl⟩)))

theorem gBase_handleV_far (j : Fin h) : sqGen h (sqHandleIdxV j) ∈ gTowerFar h :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inr ⟨j, rfl⟩))

/-- ⭐⭐ **Jacobi discharges the `x₁` outer slot for far inner slots**, unconditionally: the two
rotations put a far element in the outer slot, where both are bracket knobs. -/
theorem gBase_jacobi_xOne {a b : (DSq h : Type)} (ha : a ∈ gTowerFar h) (hb : b ∈ gTowerFar h) :
    commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b)) (gBaseT h)
      ∈ gTowerReach h nu' 2 := by
  have hjac := gThreeFour_jacobi (levelMk (DSq h : Type) 4 a)
    (levelMk (DSq h : Type) 4 b) (gBaseT h)
  have hsol : commP (commP (levelMk (DSq h : Type) 4 a)
      (levelMk (DSq h : Type) 4 b)) (gBaseT h) =
      (commP (commP (levelMk (DSq h : Type) 4 b) (gBaseT h)) (levelMk (DSq h : Type) 4 a) *
        commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 a)) (levelMk (DSq h : Type) 4 b))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hjac)
  rw [hsol]
  refine Subgroup.inv_mem _ (Subgroup.mul_mem _ ?_ ?_)
  · have hk := gBase_knob_mem (a := b) (b := dsqX1 h) (q := a) (nu' := nu') ha
    rwa [gBase_levelMk_triple] at hk
  · have hk := gBase_knob_mem (a := dsqX1 h) (b := a) (q := b) (nu' := nu') hb
    rwa [gBase_levelMk_triple] at hk

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
    · exact gBase_jacobi_xOne (gTower_letters_mem_far i hi) (gTower_letters_mem_far i' hi')

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

/-! ## §4 The fourth powers, and the base -/

section FourthPowers

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

variable (h nu') in
/-- The `Y`-elements whose bracket against `x₁` reaches. -/
def gBaseXOneTest : Subgroup (levelQuot (DSq h : Type) 4) where
  carrier := {y | y ∈ lambdaImage (DSq h : Type) 2 4 ∧
    commP y (gBaseT h) ∈ gTowerReach h nu' 2}
  one_mem' := ⟨Subgroup.one_mem _, by rw [cfour_one_comm]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {_ _} hy hy' => ⟨Subgroup.mul_mem _ hy.1 hy'.1, by
    rw [gThreeFour_ad_left hy.1]; exact Subgroup.mul_mem _ hy.2 hy'.2⟩
  inv_mem' := fun {_} hy => ⟨Subgroup.inv_mem _ hy.1, by
    rw [gThreeFour_ad_inv_left hy.1]; exact hy.2⟩

/-- ⭐⭐ **The `x₁`-bracket of any `γ₂`-element reaches**, granted the residual.  `γ₂` is
generated by squares and commutators; a square contributes a bracket square and a triple
bracket through `gThreeFour_commP_sq_left`, a commutator contributes a triple bracket. -/
theorem gBase_comm_xOne (H : GBaseXOneTriple h nu') {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 4 (commP v (dsqX1 h)) ∈ gTowerReach h nu' 2 := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 4) := gTower_discrete 4
  have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) 4) (gBaseXOneTest h nu') :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (isClosed_discrete _).preimage (continuous_levelMk (DSq h : Type) 4)
  have hsub : twoCentralSeries (DSq h : Type) 2 ≤
      Subgroup.comap (levelMk (DSq h : Type) 4) (gBaseXOneTest h nu') := by
    rw [cfour_lambda_two, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, -, rfl⟩
      refine ⟨?_, ?_⟩
      · show levelMk (DSq h : Type) 4 (g ^ 2) ∈ lambdaImage (DSq h : Type) 2 4
        rw [map_pow]
        exact cfour_sq_mem_lambdaTwo _
      · show commP (levelMk (DSq h : Type) 4 (g ^ 2)) (gBaseT h) ∈ gTowerReach h nu' 2
        rw [map_pow, gThreeFour_commP_sq_left]
        exact Subgroup.mul_mem _ (gBase_bracketSq H _ _) (gBase_triple H _ _ _)
    · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · show levelMk (DSq h : Type) 4 (a * b * a⁻¹ * b⁻¹) ∈ lambdaImage (DSq h : Type) 2 4
        rw [gThreeFour_levelMk_commutator]
        exact cfour_commP_mem_lambdaTwo _ _
      · show commP (levelMk (DSq h : Type) 4 (a * b * a⁻¹ * b⁻¹)) (gBaseT h)
          ∈ gTowerReach h nu' 2
        rw [gThreeFour_levelMk_commutator]
        exact gBase_triple H _ _ _
  rw [gBase_levelMk_commP]
  exact (hsub hv).2

/-- ⭐⭐ **The square of any `γ₂`-element lands in the full reach**, granted the residual.  The
row grading splits the element into an admissible part, whose square is the `x₁`-slot bundle
divided by the previous theorem, and a two-tower part, whose square is a complement tower. -/
theorem gBase_sq_gammaTwo (H : GBaseXOneTriple h nu')
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 4 (v ^ 2) ∈ gTowerFullReach h nu' 2 := by
  obtain ⟨d, hdmem, hdl, hdn, hdec⟩ := gTower_decomp nu' hsigma hx0 (by omega) hv
  set a := toAdd (nuLam h v) with ha
  set b := toAdd (nu' v) with hb
  have hda : (2 ^ (2 - 1) : ℤ_[2]) ∣ a := gTower_row_dvd (nuLam h) hv
  have hdb : (2 ^ (2 - 1) : ℤ_[2]) ∣ b := gTower_row_dvd nu' hv
  have hxa : zpowZtwo (isProP_DSq h) (dsqX0 h) a ∈ twoCentralSeries (DSq h : Type) 2 :=
    gTower_zpow_dvd_mem (by omega) hda _
  have hwb : zpowZtwo (isProP_DSq h) (sqPivot h) b ∈ twoCentralSeries (DSq h : Type) 2 :=
    gTower_zpow_dvd_mem (by omega) hdb _
  have htow : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) 2 :=
    Subgroup.mul_mem _ hxa hwb
  rw [hdec, gTower_sq_congr (le_refl 2) hdmem htow]
  refine Subgroup.mul_mem _ ?_ ?_
  · -- the admissible part: the bundle knob divided by the `x₁`-bracket
    have hbundle : levelMk (DSq h : Type) 4 (d ^ 2 * commP d (dsqX1 h))
        ∈ gTowerReach h nu' 2 :=
      Subgroup.subset_closure (Or.inl (Or.inr ⟨d, ⟨hdmem, hdl, hdn⟩, rfl⟩))
    have hsplit : levelMk (DSq h : Type) 4 (d ^ 2)
        = levelMk (DSq h : Type) 4 (d ^ 2 * commP d (dsqX1 h)) *
          (levelMk (DSq h : Type) 4 (commP d (dsqX1 h)))⁻¹ := by
      rw [map_mul, mul_inv_cancel_right]
    rw [hsplit]
    exact gTower_reach_le_fullReach (Subgroup.mul_mem _ hbundle
      (Subgroup.inv_mem _ (gBase_comm_xOne H hdmem)))
  · -- the tower part squares into the complement towers
    rw [gTowerTower, gTower_sq_congr (le_refl 2) hxa hwb, gTower_zpow_sq, gTower_zpow_sq,
      ← map_mul]
    refine le_sup_right (α := Subgroup _) ?_
    refine Subgroup.subset_closure ⟨2 * a, 2 * b, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hda
      exact ⟨c, by rw [hc]; ring⟩
    · obtain ⟨c, hc⟩ := hdb
      exact ⟨c, by rw [hc]; ring⟩
    · rw [gTowerTower]

/-- ⭐⭐ **Every fourth power lands in the full reach**, granted the residual: `p⁴ = (p²)²` and
`p²` is a `γ₂`-class.  No letter-by-letter identification of the towers is needed, which is
what makes this the cheap family after all. -/
theorem gBase_pow_four (H : GBaseXOneTriple h nu')
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p : levelQuot (DSq h : Type) 4) :
    p ^ 4 ∈ gTowerFullReach h nu' 2 := by
  obtain ⟨v, hv, hveq⟩ := cfour_sq_mem_lambdaTwo p
  have hfour : p ^ 4 = (p ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hfour, ← hveq, ← map_pow]
  exact gBase_sq_gammaTwo H hsigma hx0 hv

/-- ⭐⭐⭐ **The depth-two base, granted the residual.**  The three families of
`cfourCmp_zLayer_le_gens` are §3's two plus §4's, so the whole layer `Z = γ₃/γ₄` lands in the
full reach; `gTower_cut` then pulls the exactly row-trivial part back into the admissible
reach. -/
theorem gBase_layerReach_of_xOneTriple (H : GBaseXOneTriple h nu')
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : GTowerLayerReach h nu' 2 := by
  intro g hg hgl hgn
  refine gTower_cut hsigma hx0 hgl hgn ?_
  exact cfourCmp_zLayer_le_gens (gBase_pow_four H hsigma hx0)
    (fun p q => gTower_reach_le_fullReach (gBase_bracketSq H p q))
    (fun p q r => gTower_reach_le_fullReach (gBase_triple H p q r)) ⟨g, hg, rfl⟩

variable (h) in
/-- **The residual of the depth-two base, at every selected marking.**

⚠⚠ **FALSE at every `h`**, as of `e6bbd2b9`: `gDecide_not_baseResidual`
(`SqCore/GradedBaseDecide.lean`).  The two composites below are vacuous. -/
def GBaseResidual : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      GBaseXOneTriple h nu'

/-- ⭐⭐⭐ **`GJoinBase h` from the residual.**  Wave 75's first named input is discharged by the
`2 + 2h` brackets `⁅⁅x₁, letter⁆, x₁⁆` with content, at every selected marking.  (The family is
indexed by all `3 + 2h` letters; the `x₁` one is trivial on the nose, `gDecide_triple_self`.)

⚠ This is the implication `GBaseResidual h → GJoinBase h`, not an equivalence; no converse is
proved in this file.  See the module docstring. -/
theorem gBase_joinBase_of_residual (H : GBaseResidual h) : GJoinBase h :=
  fun nu' hsigma hx0 => gBase_layerReach_of_xOneTriple (H nu' hsigma hx0) hsigma hx0

/-- ⭐⭐⭐ **The `h ≥ 1` residual from three inputs, one of them now atomic.**  Wave 75's
composite with `GJoinBase` replaced by the `x₁`-slot triple brackets. -/
theorem gBase_markTransitivity_of_residual (H : GBaseResidual h)
    (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  gJoin_markTransitivity_of_base (gBase_joinBase_of_residual H) hsep HR

/-- ⭐⭐⭐ **The per-class supply from the same three inputs.** -/
theorem gBase_supply_of_residual (H : GBaseResidual h)
    (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
    ∀ k, SqClassClearingSupply h k :=
  gJoin_supply_of_base (gBase_joinBase_of_residual H) hsep HR

end FourthPowers


/-! ## §5 The residual is exactly the `x₁`-slot bracket squares

Both knob terms of the relator identity `gBase_xOne_triple` reach unconditionally, so the
residual triple bracket and the bracket square `⁅x₁, c⁆²` stand or fall together.  This is the
sharpest reading of what the depth-two base is missing: the `(Λ²V)^{[2]}`-classes at the `x₁`
slot, and nothing else. -/

section Residual

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **A triple bracket with two far elements inside reaches unconditionally.**  The outer
slot reduces to the letters; a far letter there is a bracket knob, and `x₁` there is Jacobi. -/
theorem gBase_triple_far_inner {a b : (DSq h : Type)} (ha : a ∈ gTowerFar h)
    (hb : b ∈ gTowerFar h) (r : levelQuot (DSq h : Type) 4) :
    commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b)) r
      ∈ gTowerReach h nu' 2 := by
  obtain ⟨g, rfl⟩ := levelMk_surjective (DSq h : Type) 4 r
  rw [← gBase_levelMk_triple]
  have hspan := gTower_commHom_span (h := h) (k := 2) (cfour_commP_mem_two a b) g
  refine Subgroup.closure_le (K := gTowerReach h nu' 2) |>.2 ?_ hspan
  rintro _ ⟨i'', rfl⟩
  by_cases hi'' : i'' = 2
  · subst hi''
    have hgoal : levelMk (DSq h : Type) 4 (commP (commP a b) (sqGen h 2))
        ∈ gTowerReach h nu' 2 := by
      rw [gBase_levelMk_triple]
      exact gBase_jacobi_xOne ha hb
    exact hgoal
  · exact gBase_knob_mem (gTower_letters_mem_far i'' hi'')

/-- The `⁅σ, x₀⁆`-term of the relator identity reaches, at every slot. -/
theorem gBase_sigmaX0_mem (c : levelQuot (DSq h : Type) 4) :
    commP (commP (gBaseS h) (gBaseX h)) c ∈ gTowerReach h nu' 2 :=
  gBase_triple_far_inner gBase_sigma_far gBase_x0_far c

/-- The handle term of the relator identity reaches, at every slot. -/
theorem gBase_handleTerm_mem (c : levelQuot (DSq h : Type) 4) :
    commP (gBaseHandle h) c ∈ gTowerReach h nu' 2 := by
  rw [gBase_handle_bracket]
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
  exact gBase_triple_far_inner (gBase_handleU_far j) (gBase_handleV_far j) c

/-- ⭐⭐⭐ **The residual, in its two equivalent forms.**  By the relator identity of §2 the
`x₁`-slot triple bracket and the `x₁`-slot bracket square differ by two terms that always
reach, so the depth-two base is missing exactly the `(Λ²V)^{[2]}`-classes at the `x₁` slot. -/
theorem gBase_residual_iff (c : levelQuot (DSq h : Type) 4) :
    commP (commP (gBaseT h) c) (gBaseT h) ∈ gTowerReach h nu' 2 ↔
      (commP (gBaseT h) c) ^ 2 ∈ gTowerReach h nu' 2 := by
  have hA := gBase_sigmaX0_mem (nu' := nu') c
  have hH := gBase_handleTerm_mem (nu' := nu') c
  rw [gBase_xOne_triple c]
  constructor
  · intro hmem
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hmem)
      (Subgroup.inv_mem _ hH)
    rwa [show (commP (commP (gBaseS h) (gBaseX h)) c)⁻¹ *
        (commP (commP (gBaseS h) (gBaseX h)) c * commP (gBaseT h) c ^ 2 *
          commP (gBaseHandle h) c) * (commP (gBaseHandle h) c)⁻¹
        = commP (gBaseT h) c ^ 2 from by group] at this
  · intro hmem
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hmem) hH

end Residual

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms gBaseS
#print axioms gBaseX
#print axioms gBaseT
#print axioms gBaseHandle
#print axioms gBase_letters_mem
#print axioms gBase_levelMk_commP
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
#print axioms gBase_jacobi_xOne
#print axioms GQ2.Dyadic.SqCore.GBaseXOneTriple
#print axioms gBase_triple_xOne_letters
#print axioms gBase_triple_xOne
#print axioms gBase_letter_triple_mem
#print axioms gBase_triple
#print axioms gBase_bracketSq
#print axioms gBaseXOneTest
#print axioms gBase_comm_xOne
#print axioms gBase_sq_gammaTwo
#print axioms gBase_pow_four
#print axioms gBase_layerReach_of_xOneTriple
#print axioms GQ2.Dyadic.SqCore.GBaseResidual
#print axioms gBase_joinBase_of_residual
#print axioms gBase_markTransitivity_of_residual
#print axioms gBase_supply_of_residual
#print axioms gBase_sigma_far
#print axioms gBase_x0_far
#print axioms gBase_handleU_far
#print axioms gBase_handleV_far
#print axioms gBase_triple_far_inner
#print axioms gBase_sigmaX0_mem
#print axioms gBase_handleTerm_mem
#print axioms gBase_residual_iff

end AxiomPins

end SqCore

end Dyadic

end GQ2
