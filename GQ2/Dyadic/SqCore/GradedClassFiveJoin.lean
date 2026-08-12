/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFiveKnob

/-!
# W73-FIVE: joining the class-five knob inventory to the six families

Wave 72 proved the **relations** half of the graded decomposition of `γ₄/γ₅`
(`cfiveSpan_zLayer_le_gens`, six families indexed by `Q₅`) and recorded that it says nothing
about whether the knob subgroup contains any of those families.  This file is that join.

Throughout `Q₅ = levelQuot G 5`, `Y = lambdaImage G 2 5`, `T = lambdaImage G 3 5` and
`Z = zLayer G 4` is the top layer, central in `Q₅` and of exponent two.

## The inventory, read as a subgroup

Wave 71's table (`GradedGammaFourFive` §4) gives, for a `γ₃`-valued correction `c ∈ T`, five
knobs.  Four of them are **pure brackets** `commP c w` against a fixed frame letter `w`, and the
fifth, at the `x₁`-slot, is `c ^ 2 * commP c x` where `x` is the letter `m 2`.  So the data is a
set `X` of x₁-free far slots together with the one distinguished slot `x`, and the knob subgroup
is `cfiveJoinKnobSub X x`.

## The headline: the join is one equivalence with one open input

⭐⭐⭐ `cfiveJoin_zLayer_le_iff`: if `S` is a closed subgroup holding every bracket knob and every
`x₁`-slot knob, and `insert x X` topologically generates `Q₅`, then

```text
  zLayer G 4 ≤ S   ↔   ∀ c ∈ T, commP c x ∈ S .
```

It is an **equivalence**, so the join has no slack: the knob subgroup contains the whole layer
exactly when it contains the one x₁-free defect.  ⭐ `cfiveJoin_defect_iff` gives the second form
of that defect: `∀ c ∈ T, commP c x ∈ S` iff `∀ c ∈ T, c ^ 2 ∈ S`, since the `x₁`-slot knob is
their product.  This is the same defect wave 71 diagnosed when it refuted wave 70's `L₃(V)`
argument, now proved to be the **only** obstruction one class up.

## The six families, one at a time (§5)

Every one of wave 72's six families reduces to a member of the last two, with the free far slots
put at `x`:

| family | status |
| --- | --- |
| `g ^ 8` | equivalent to `commP (commP (g ^ 2) x) x` (`cfiveJoin_family_one_iff`) |
| `commP a b ^ 4` | equivalent to `commP (commP (commP a b) x) x` (`cfiveJoin_family_two_iff`) |
| `(commP (g ^ 2) r) ^ 2` | equivalent to `commP (commP (g ^ 2) r) x` (`cfiveJoin_family_three_iff`) |
| `(commP (commP a b) r) ^ 2` | equivalent to `commP (commP (commP a b) r) x` (`..._four_iff`) |
| `commP (commP (g ^ 2) r) q` | **unconditional** for `q` in the closed span of `X ∪ Y`; open at `q = x` |
| `commP (commP (commP a b) r) q` | the same |

So the four square families are not reached by the bracket knobs at all, and the two bracket
families are reached at every far slot except the `x₁`-direction.  The reduction of the first four
to the last two runs through the pairing: ⭐ `cfiveJoin_pow_four_iff` is
`cfiveSpan_pair_correction` read at `q = x`, and it is where wave 72's pairing is consumed.

## Two simplifications of the pairing (§6)

`commP (commP y q) y = 1` for `y ∈ Y`, because `commP y q ∈ T` and `⁅T, Y⁆` is trivial.  Hence
⭐ `cfiveJoin_commP_sq_lambdaTwo`: `commP (y ^ 2) q = (commP y q) ^ 2` for `y ∈ Y`, with no
trailing bracket, and the pairing itself loses one of its two factors
(`cfiveJoin_pair_correction`).

## What is **not** established

`∀ c ∈ T, commP c x ∈ S` is **open**.  Nothing here says it holds and nothing here says it fails;
`cfiveJoin_zLayer_le_iff` is an equivalence, so a failure of the join at these knobs would be a
statement about this route and not about `SqClassClearingSupply h 5`, which
`cfiveKnob_supply_of_reach` reaches through an existentially quantified base frame and which is
conditional on class four in any case.  §7 reduces the defect as far as this wave takes it: to
two families over `Y` (`cfiveJoin_defect_of_two_families`), and, on the bracket generators of
`T`, to brackets of two `Y`-elements by Jacobi (`cfiveJoin_defect_jacobi`).

Lane W73-FIVE.  New file; no edits to existing files.  Prefix `cfiveJoin`.
-/

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The far slot of a knob is blind to `Y`

For `t ∈ T` the map `q ↦ commP t q` is a homomorphism into the exponent-two layer `Z`, so it
kills `Y`.  Hence the far slot of a bracket knob matters only modulo `Y`, and a check against a
set `X` extends to the closed span of `X ∪ Y`. -/

section FarSlot

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A `Y`-valued right factor in the far slot of a knob is invisible.**  This is
`gFourFive_commP_vanish` fed through the far-slot homomorphism law, and it is why the far slots a
knob reaches form the preimage of a subspace of `Q₅ / Y`. -/
theorem cfiveJoin_far_lambdaTwo_mul {t : levelQuot G 5} (ht : t ∈ lambdaImage G 3 5)
    (q : levelQuot G 5) {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    commP t (q * y) = commP t q := by
  rw [cfive_commP_right_hom_five ht, gFourFive_commP_vanish ht hy, one_mul]

/-- **A knob check against `X` extends to the closed span of `X`.**  This is
`cfiveSpan_ad_far_of_gens` with the conclusion kept at the span instead of being pushed to `⊤`,
which is the form the partial results of §5 need. -/
theorem cfiveJoin_ad_far_mem {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {t : levelQuot G 5} (ht : t ∈ lambdaImage G 3 5) {X : Set (levelQuot G 5)}
    (hgen : ∀ g ∈ X, commP t g ∈ S) {q : levelQuot G 5}
    (hq : q ∈ (Subgroup.closure X).topologicalClosure) : commP t q ∈ S := by
  have hcont : Continuous fun r : levelQuot G 5 => commP t r := by
    simp only [commP]
    fun_prop
  have hle : (Subgroup.closure X).topologicalClosure ≤ cfiveSpanFarSub S ht :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 fun g hg => hgen g hg)
      (hS.preimage hcont)
  exact hle hq

/-- ⭐ **The far slots a knob reaches are a subgroup containing `Y`.**  Adding `Y` to the check
set costs nothing by `cfiveJoin_far_lambdaTwo_mul`, so the reached far slots are the closed span
of `X ∪ Y`, i.e. the preimage in `Q₅` of the span of `X` in `Q₅ / Y`. -/
theorem cfiveJoin_ad_far_lambdaTwo {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {t : levelQuot G 5} (ht : t ∈ lambdaImage G 3 5) {X : Set (levelQuot G 5)}
    (hgen : ∀ g ∈ X, commP t g ∈ S) {q : levelQuot G 5}
    (hq : q ∈ Subgroup.topologicalClosure (Subgroup.closure
      (X ∪ ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))))) :
    commP t q ∈ S := by
  refine cfiveJoin_ad_far_mem hS ht (fun g hg => ?_) hq
  rcases hg with hg | hg
  · exact hgen g hg
  · rw [gFourFive_commP_vanish ht hg]
    exact S.one_mem

end FarSlot

/-! ## §2 The knob subgroup

Wave 71's inventory is five knobs at a `γ₃`-valued correction `c`.  Four of them are pure
brackets against a fixed frame letter, and the fifth carries the square:

| slot | knob | far slot |
| --- | --- | --- |
| `σ` | `commP c (m 1)` | `m 1` |
| `x₀` | `commP (m 0) c` | `m 0` |
| `x₁` | `c ^ 2 * commP c (m 2)` | `m 2` |
| `u_{j'}` | `commP c (m (sqHandleIdxV j'))` | `m (sqHandleIdxV j')` |
| `v_{j'}` | `commP (m (sqHandleIdxU j')) c` | `m (sqHandleIdxU j')` |

The two knobs written with `c` on the right are the inverses of the corresponding left forms
(`commP p c = (commP c p)⁻¹`), so a subgroup holds one exactly when it holds the other.  The data
is therefore a set `X` of x₁-free far slots and one distinguished far slot `x`. -/

section KnobSub

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The set of knobs**: the bracket knobs at the far slots `X`, and the `x₁`-slot knob. -/
def cfiveJoinKnobSet (X : Set (levelQuot G 5)) (x : levelQuot G 5) : Set (levelQuot G 5) :=
  {z | ∃ c ∈ lambdaImage G 3 5, (∃ w ∈ X, z = commP c w) ∨ z = c ^ 2 * commP c x}

/-- **The knob subgroup** generated by the inventory of wave 71 at every `γ₃`-valued correction,
with x₁-free far slots `X` and distinguished far slot `x`. -/
def cfiveJoinKnobSub (X : Set (levelQuot G 5)) (x : levelQuot G 5) : Subgroup (levelQuot G 5) :=
  Subgroup.closure (cfiveJoinKnobSet X x)

/-- **The knob subgroup lies inside the layer.**  Every knob is a bracket with a `T`-slot or a
square of a `T`-element, and both are in `Z`.  With `cfiveJoin_zLayer_le_iff` this is what turns
the join into an equality `cfiveJoinKnobSub X x = zLayer G 4`. -/
theorem cfiveJoin_knobSub_le (X : Set (levelQuot G 5)) (x : levelQuot G 5) :
    cfiveJoinKnobSub X x ≤ zLayer G 4 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z ⟨c, hc, ⟨w, -, rfl⟩ | rfl⟩
  · exact cfive_commP_mem_zLayer_left hc w
  · exact Subgroup.mul_mem _ (gFourFive_sq_mem_zLayer hc) (cfive_commP_mem_zLayer_left hc x)

/-- **The bracket knobs are in the knob subgroup.**  This is the satisfiability check for the
first hypothesis of §4: the hypothesis is not vacuous, and the subgroup meeting it is the one the
inventory actually generates. -/
theorem cfiveJoin_knobSub_bracket {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    {c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) {w : levelQuot G 5} (hw : w ∈ X) :
    commP c w ∈ cfiveJoinKnobSub X x :=
  Subgroup.subset_closure ⟨c, hc, Or.inl ⟨w, hw, rfl⟩⟩

/-- **The `x₁`-slot knob is in the knob subgroup.**  The satisfiability check for the second
hypothesis of §4. -/
theorem cfiveJoin_knobSub_sq {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    {c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) :
    c ^ 2 * commP c x ∈ cfiveJoinKnobSub X x :=
  Subgroup.subset_closure ⟨c, hc, Or.inr rfl⟩

end KnobSub

/-! ## §3 The two forms of the defect

The `x₁`-slot knob is the product of the two things the join is missing, so holding either one is
holding the other.  Wave 71 refuted wave 70's `L₃(V)` argument for reading the bracket alone off
this knob; the content of §3 is that the two readings stand or fall together, and nothing more. -/

section Defect

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **The bracket defect and the square defect are the same defect.**  Given the `x₁`-slot
knob `c ^ 2 * commP c x`, the subgroup holds `commP c x` for every `γ₃`-valued `c` exactly when
it holds `c ^ 2` for every such `c`.  No closedness and no generation are used: this is the
single knob relation, read both ways. -/
theorem cfiveJoin_defect_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) :
    (∀ c ∈ lambdaImage G 3 5, commP c x ∈ S) ↔ ∀ c ∈ lambdaImage G 3 5, c ^ 2 ∈ S := by
  constructor
  · intro hd c hc
    have h : c ^ 2 = (c ^ 2 * commP c x) * (commP c x)⁻¹ := by group
    rw [h]
    exact S.mul_mem (hsq c hc) (S.inv_mem (hd c hc))
  · intro hd c hc
    have h : commP c x = (c ^ 2)⁻¹ * (c ^ 2 * commP c x) := by group
    rw [h]
    exact S.mul_mem (S.inv_mem (hd c hc)) (hsq c hc)

end Defect

/-! ## §4 The join

The generation half `gFourFive_zLayer_le` asks for exactly two things: the squares of `T` and the
brackets of `T` against every `q`.  The inventory delivers the brackets at every far slot in the
span of `X`, and delivers the squares only bundled with the bracket at `x`.  So the whole join
turns on the single family `commP c x`, `c ∈ T`. -/

section Join

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Every knob bracket, at every far slot, once the defect is granted.** -/
theorem cfiveJoin_ad_far_all {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    (hgen : (Subgroup.closure (insert x X)).topologicalClosure = ⊤)
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S)
    (hdef : ∀ c ∈ lambdaImage G 3 5, commP c x ∈ S)
    {c : levelQuot G 5} (hc : c ∈ lambdaImage G 3 5) (q : levelQuot G 5) : commP c q ∈ S := by
  refine cfiveJoin_ad_far_mem hS hc (X := insert x X) (fun g hg => ?_) ?_
  · rcases hg with rfl | hg
    · exact hdef c hc
    · exact hbr c hc g hg
  · rw [hgen]
    exact Subgroup.mem_top q

/-- ⭐⭐⭐ **The join.**  For a closed subgroup `S` holding every bracket knob and every
`x₁`-slot knob, with `insert x X` topologically generating `Q₅`,

```text
  zLayer G 4 ≤ S   ↔   ∀ c ∈ T, commP c x ∈ S .
```

The forward direction is free, since a bracket with a `T`-slot lies in `Z`.  The backward
direction is `gFourFive_zLayer_le`: the defect unbundles the square from the `x₁`-slot knob
(`cfiveJoin_defect_iff`) and fills in the one missing far-slot direction
(`cfiveJoin_ad_far_all`), which is exactly the generation half's two inputs.

Being an equivalence, this settles the join in the sense the ticket asked for: the knob subgroup
contains the whole layer `γ₄/γ₅` **iff** it contains the x₁-free defect, and no rearrangement of
the five knobs can do better. -/
theorem cfiveJoin_zLayer_le_iff {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    (hgen : (Subgroup.closure (insert x X)).topologicalClosure = ⊤)
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S)
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) :
    zLayer G 4 ≤ S ↔ ∀ c ∈ lambdaImage G 3 5, commP c x ∈ S := by
  constructor
  · exact fun hle c hc => hle (cfive_commP_mem_zLayer_left hc x)
  · intro hdef
    exact gFourFive_zLayer_le hS ((cfiveJoin_defect_iff hsq).1 hdef)
      (fun c hc q => cfiveJoin_ad_far_all hS hgen hbr hdef hc q)

/-- ⭐⭐ **The join with the square form of the defect.** -/
theorem cfiveJoin_zLayer_le_iff_sq {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    (hgen : (Subgroup.closure (insert x X)).topologicalClosure = ⊤)
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S)
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) :
    zLayer G 4 ≤ S ↔ ∀ c ∈ lambdaImage G 3 5, c ^ 2 ∈ S :=
  (cfiveJoin_zLayer_le_iff hS hgen hbr hsq).trans (cfiveJoin_defect_iff hsq)

/-- ⭐⭐ **The containment, as an equality of subgroups.**  The knob subgroup sits inside the
layer (`cfiveJoin_knobSub_le`), so once the defect is granted the join is an equality
`cfiveJoinKnobSub X x = zLayer G 4`, and the class-five analogue of `K ⊇ L₄(V)` holds in the
strongest available form: `K` is the whole graded piece `γ₄/γ₅`, not merely its Lie part. -/
theorem cfiveJoin_knobSub_eq_of_defect {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    (hS : IsClosed ((cfiveJoinKnobSub X x : Subgroup (levelQuot G 5)) :
      Set (levelQuot G 5)))
    (hgen : (Subgroup.closure (insert x X)).topologicalClosure = ⊤)
    (hdef : ∀ c ∈ lambdaImage G 3 5, commP c x ∈ cfiveJoinKnobSub X x) :
    cfiveJoinKnobSub X x = zLayer G 4 :=
  le_antisymm (cfiveJoin_knobSub_le X x)
    ((cfiveJoin_zLayer_le_iff hS hgen (fun _ hc _ hw => cfiveJoin_knobSub_bracket hc hw)
      (fun _ hc => cfiveJoin_knobSub_sq hc)).2 hdef)

end Join

end SqCore

end Dyadic

end GQ2
