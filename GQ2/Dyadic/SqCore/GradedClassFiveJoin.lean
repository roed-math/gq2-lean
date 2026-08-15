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

## The six families, one at a time (§6)

Every one of wave 72's six families reduces to a member of the last two, with the free far slots
put at `x`:

| family | status |
| --- | --- |
| `g ^ 8` | equivalent to `commP (commP (g ^ 2) x) x` (`cfiveJoin_family_one_iff`) |
| `commP a b ^ 4` | equivalent to `commP (commP (commP a b) x) x` (`cfiveJoin_family_two_iff`) |
| `(commP (g ^ 2) r) ^ 2` | equivalent to `commP (commP (g ^ 2) r) x` (`..._three_iff`) |
| `(commP (commP a b) r) ^ 2` | equivalent to `commP (commP (commP a b) r) x` (`..._four_iff`) |
| `commP (commP (g ^ 2) r) q` | **unconditional** for `q` in the span of `X ∪ Y`; open at `x` |
| `commP (commP (commP a b) r) q` | the same |

So the four square families are not reached by the bracket knobs at all, and the two bracket
families are reached at every far slot except the `x₁`-direction.  The reduction of the first four
to the last two splits: families **three and four** are the `x₁`-slot knob read at a single
correction, with no pairing (`cfiveJoin_defect_pt_iff`), and only families **one and two**, the
fourth powers, run through the pairing.  ⭐ `cfiveJoin_pow_four_iff` is `cfiveJoin_pair_correction`
(§5's form, with the second bracket already evaluated away) read at `q = x`, and it is where wave
72's pairing is consumed.

## Two simplifications of the pairing (§5)

`commP (commP y q) y = 1` for `y ∈ Y`, because `commP y q ∈ T` and `⁅T, Y⁆` is trivial.  Hence
⭐ `cfiveJoin_commP_sq_lambdaTwo`: `commP (y ^ 2) q = (commP y q) ^ 2` for `y ∈ Y`, with no
trailing bracket, and the pairing itself loses one of its two factors
(`cfiveJoin_pair_correction`).  Wave 72's statements are true as written; these are the same
statements with a factor evaluated.

## At the real inventory (§8)

⭐⭐⭐ `cfiveJoin_zLayer_le_iff_frame` runs the whole join at a mod-2 independent frame of
`D_sq h`: every closedness condition is free because `Q₅` is discrete, the generation condition
**follows from** mod-2 independence (`cfiveJoin_topGen_of_modTwoIndep`, which proves that
direction and only that direction), and the far slots of the four bracket knobs are exactly the
frame letters other than `m 2` (`cfiveJoin_farSlot_cases`).

## What is **not** established

`∀ c ∈ T, commP c x ∈ S` is **open**.  Nothing here says it holds and nothing here says it fails;
`cfiveJoin_zLayer_le_iff` is an equivalence, so a failure of the join at these knobs would be a
statement about this route and not about `SqClassClearingSupply h 5`, which
`cfiveKnob_supply_of_reach` reaches through an existentially quantified base frame, presupposing
no class-four witness, and which enters `limFinal_markTransitivity_iff` only alongside every other
class, class four included.

**[W75-HOUSE, wave-74 update, and read the qualifier.**  One class down, the analogous span
hypothesis is now **refuted** as a theorem (`gDelta_cfourCmp_span_hyp_false`,
`GradedDeltaFunctionals.lean:1575`): the committed route's corrections cannot reach the Frobenius
towers, which the twisted functionals detect and the moves do not move.  At class five the same
mechanism is argued in `docs/dyadic/w74-func-note.md` §4.2 -- `zLayer 4` contains the tower class
`σ^{2^3}` while class-five knob readings sit in `2^4 ℤ₂` -- so `zLayer G 4 ≤ S` is expected to
fail at the committed knob subgroup, and with it, by this file's own equivalence read
contrapositively, the defect clause.  **That class-five half is analysis, not a theorem**: it
needs the mod-16 congruence kit, which wave 74 did **not** commit (it committed mod-8, which class
four consumes).  So the defect above is still open *in the tree*, and the honest reading is that
the route is expected dead rather than known dead.  Everything in this file stands as stated: the
theorems are about arbitrary subgroups `S`, and only the instantiation at the knob subgroup is in
question.]**  §7 reduces the defect as far as this wave takes it: to
two families over `Y` (`cfiveJoin_defect_of_two_families`), and, on the bracket generators of
`T`, to brackets of two `Y`-elements by Jacobi (`cfiveJoin_defect_jacobi`).  Neither reduction
is a discharge, and no `SqClassClearingSupply` instance is proved or refuted at any class.

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
`cfiveSpan_ad_far_of_gens` with the conclusion kept at the span instead of being pushed to `⊤`.
Its direct consumers are `cfiveJoin_ad_far_lambdaTwo` just below and §4's `cfiveJoin_ad_far_all`;
through the former it is what §6's `cfiveJoin_family_five_of_span` and `..._six_of_span` need. -/
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
set costs nothing by `cfiveJoin_far_lambdaTwo_mul`, so the reached far slots **include** the
closed span of `X ∪ Y`, i.e. the preimage in `Q₅` of the span of `X` in `Q₅ / Y`.  Only that
direction is proved: nothing here shows a far slot outside the span is unreached. -/
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

/-- ⭐ **The bracket defect and the square defect are the same defect, at one correction.**  The
`x₁`-slot knob is their product, so a subgroup holding it holds either one exactly when it holds
the other.  Stated pointwise in the correction, since that is the form §5 consumes. -/
theorem cfiveJoin_defect_pt_iff {S : Subgroup (levelQuot G 5)} {c x : levelQuot G 5}
    (hk : c ^ 2 * commP c x ∈ S) : c ^ 2 ∈ S ↔ commP c x ∈ S := by
  constructor
  · intro hd
    have h : commP c x = (c ^ 2)⁻¹ * (c ^ 2 * commP c x) := by group
    rw [h]
    exact S.mul_mem (S.inv_mem hd) hk
  · intro hd
    have h : c ^ 2 = (c ^ 2 * commP c x) * (commP c x)⁻¹ := by group
    rw [h]
    exact S.mul_mem hk (S.inv_mem hd)

/-- ⭐ **The bracket defect and the square defect are the same defect.**  Given the `x₁`-slot
knob `c ^ 2 * commP c x`, the subgroup holds `commP c x` for every `γ₃`-valued `c` exactly when
it holds `c ^ 2` for every such `c`.  No closedness and no generation are used: this is the
single knob relation, read both ways. -/
theorem cfiveJoin_defect_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) :
    (∀ c ∈ lambdaImage G 3 5, commP c x ∈ S) ↔ ∀ c ∈ lambdaImage G 3 5, c ^ 2 ∈ S :=
  ⟨fun hd c hc => (cfiveJoin_defect_pt_iff (hsq c hc)).2 (hd c hc),
    fun hd c hc => (cfiveJoin_defect_pt_iff (hsq c hc)).1 (hd c hc)⟩

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

/-! ## §5 The pairing, with one factor removed

For `y ∈ Y` the bracket `commP y q` lies in `T`, and `⁅T, Y⁆` is trivial, so
`commP (commP y q) y = 1` outright.  That kills one of the two factors wave 72's pairing carries
and turns its Hall-Petrescu step into a bare squaring law.  Nothing is corrected here: wave 72's
statements are true as written; these are the same statements with a factor evaluated. -/

section Pairing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A `Y`-element commutes with its own brackets.**  `commP y q` lies in `T` and
`gFourFive_commP_vanish` kills `⁅T, Y⁆`. -/
theorem cfiveJoin_commP_self_lambdaTwo {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) : commP (commP y q) y = 1 :=
  gFourFive_commP_vanish (cfive_commP_lambdaTwo_mem_lambdaThree hy q) hy

/-- ⭐ **Hall-Petrescu at `γ₄/γ₅`, with no trailing bracket**: `commP (y ^ 2) q = (commP y q) ^ 2`
for `y ∈ Y` and every `q`.  This is `cfiveSpan_commP_sq_left` with its correction term evaluated
by `cfiveJoin_commP_self_lambdaTwo`. -/
theorem cfiveJoin_commP_sq_lambdaTwo {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) : commP (y ^ 2) q = (commP y q) ^ 2 := by
  rw [cfiveSpan_commP_sq_left hy q, cfiveJoin_commP_self_lambdaTwo hy q, mul_one]

/-- ⭐ **The pairing, with one factor removed**: the `x₁`-slot knob of the single `T`-correction
`y ^ 2 * commP y q` is `y ^ 4 * commP (commP y q) q`, a fourth power times **one** pure iterated
bracket.  Wave 72's `cfiveSpan_pair_correction` carries a second bracket
`commP (commP y q) y`, which is trivial. -/
theorem cfiveJoin_pair_correction {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) :
    (y ^ 2 * commP y q) ^ 2 * commP (y ^ 2 * commP y q) q = y ^ 4 * commP (commP y q) q := by
  rw [cfiveSpan_pair_correction hy q, cfiveJoin_commP_self_lambdaTwo hy q, one_mul]

/-- The `T`-correction the pairing runs at. -/
theorem cfiveJoin_pair_mem {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) : y ^ 2 * commP y q ∈ lambdaImage G 3 5 :=
  (lambdaImage G 3 5).mul_mem (cfiveSpan_sq_mem_lambdaThree hy)
    (cfive_commP_lambdaTwo_mem_lambdaThree hy q)

end Pairing

/-! ## §6 The six families, one at a time

Every family of `cfiveSpan_zLayer_le_gens` is either the square of a `T`-element (families one to
four) or a bracket of a `T`-element against a free far slot (families five and six).  The bracket
knobs reach the second kind at every far slot in the closed span of `X ∪ Y`, unconditionally; the
first kind is reached only through the `x₁`-slot knob, and there each family turns out to be
**equivalent** to a specific member of families five and six with the free far slots put at `x`.

The two square families that are fourth powers of `Y`-elements are where the pairing is
consumed. -/

section Families

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A fourth power written as an iterated square, the shape the six families use. -/
theorem cfiveJoin_pow_four_eq (y : levelQuot G 5) : (y ^ 2) ^ 2 = y ^ 4 := by
  rw [← pow_mul]

/-- ⭐⭐ **The fourth power of a `Y`-element is a knob exactly when the double-`x` bracket is.**
This is where wave 72's pairing enters the join: run the `x₁`-slot knob at the single
`T`-correction `y ^ 2 * commP y x` and it evaluates, by `cfiveJoin_pair_correction`, to
`y ^ 4 * commP (commP y x) x`.  So the fourth power and the iterated bracket differ by a knob,
and neither is reached without the other. -/
theorem cfiveJoin_pow_four_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S)
    {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    y ^ 4 ∈ S ↔ commP (commP y x) x ∈ S := by
  have hk := hsq _ (cfiveJoin_pair_mem hy x)
  rw [cfiveJoin_pair_correction hy x] at hk
  constructor
  · intro h4
    have h : commP (commP y x) x = (y ^ 4)⁻¹ * (y ^ 4 * commP (commP y x) x) := by group
    rw [h]
    exact S.mul_mem (S.inv_mem h4) hk
  · intro hb
    have h : y ^ 4 = (y ^ 4 * commP (commP y x) x) * (commP (commP y x) x)⁻¹ := by group
    rw [h]
    exact S.mul_mem hk (S.inv_mem hb)

/-- **Family one, `g ^ 8`**: equivalent to the member `commP (commP (g ^ 2) x) x` of family
five. -/
theorem cfiveJoin_family_one_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) (g : levelQuot G 5) :
    ((g ^ 2) ^ 2) ^ 2 ∈ S ↔ commP (commP (g ^ 2) x) x ∈ S := by
  rw [cfiveJoin_pow_four_eq (g ^ 2)]
  exact cfiveJoin_pow_four_iff hsq (cfiveSpan_sq_mem_lambdaTwo g)

/-- **Family two, `⁅a, b⁆ ^ 4`**: equivalent to the member `commP (commP (commP a b) x) x` of
family six. -/
theorem cfiveJoin_family_two_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) (a b : levelQuot G 5) :
    ((commP a b) ^ 2) ^ 2 ∈ S ↔ commP (commP (commP a b) x) x ∈ S := by
  rw [cfiveJoin_pow_four_eq (commP a b)]
  exact cfiveJoin_pow_four_iff hsq (gFourFive_commP_mem_lambdaTwo a b)

/-- **Family three, `⁅g², r⁆ ^ 2`**: equivalent to the member `commP (commP (g ^ 2) r) x` of
family five.  This one is the `x₁`-slot knob read at a single correction, with no pairing. -/
theorem cfiveJoin_family_three_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) (g r : levelQuot G 5) :
    (commP (g ^ 2) r) ^ 2 ∈ S ↔ commP (commP (g ^ 2) r) x ∈ S :=
  cfiveJoin_defect_pt_iff
    (hsq _ (cfive_commP_lambdaTwo_mem_lambdaThree (cfiveSpan_sq_mem_lambdaTwo g) r))

/-- **Family four, `⁅⁅a, b⁆, r⁆ ^ 2`**: equivalent to the member `commP (commP (commP a b) r) x`
of family six. -/
theorem cfiveJoin_family_four_iff {S : Subgroup (levelQuot G 5)} {x : levelQuot G 5}
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S) (a b r : levelQuot G 5) :
    (commP (commP a b) r) ^ 2 ∈ S ↔ commP (commP (commP a b) r) x ∈ S :=
  cfiveJoin_defect_pt_iff
    (hsq _ (cfive_commP_lambdaTwo_mem_lambdaThree (gFourFive_commP_mem_lambdaTwo a b) r))

/-- ⭐ **Family five is reached unconditionally away from the `x₁`-direction**: the bracket knobs
give `commP (commP (g ^ 2) r) q` for every far slot `q` in the closed span of `X ∪ Y`, with no
hypothesis on the defect.  This is the part of the join that closes outright. -/
theorem cfiveJoin_family_five_of_span {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)}
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S) (g r : levelQuot G 5)
    {q : levelQuot G 5}
    (hq : q ∈ Subgroup.topologicalClosure (Subgroup.closure
      (X ∪ ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))))) :
    commP (commP (g ^ 2) r) q ∈ S :=
  cfiveJoin_ad_far_lambdaTwo hS
    (cfive_commP_lambdaTwo_mem_lambdaThree (cfiveSpan_sq_mem_lambdaTwo g) r)
    (fun w hw => hbr _ (cfive_commP_lambdaTwo_mem_lambdaThree
      (cfiveSpan_sq_mem_lambdaTwo g) r) w hw) hq

/-- ⭐ **Family six is reached unconditionally away from the `x₁`-direction.**  The fourfold
bracket `commP (commP (commP a b) r) q` is a knob at every far slot in the closed span of
`X ∪ Y`. -/
theorem cfiveJoin_family_six_of_span {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)}
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S) (a b r : levelQuot G 5)
    {q : levelQuot G 5}
    (hq : q ∈ Subgroup.topologicalClosure (Subgroup.closure
      (X ∪ ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))))) :
    commP (commP (commP a b) r) q ∈ S :=
  cfiveJoin_ad_far_lambdaTwo hS
    (cfive_commP_lambdaTwo_mem_lambdaThree (gFourFive_commP_mem_lambdaTwo a b) r)
    (fun w hw => hbr _ (cfive_commP_lambdaTwo_mem_lambdaThree
      (gFourFive_commP_mem_lambdaTwo a b) r) w hw) hq

/-- ⭐⭐ **The join run through the six families.**  Granted the defect, all six families of
`cfiveSpan_zLayer_le_gens` land in `S`, so the relations half closes the containment.  This is
the literal join the ticket asked for; `cfiveJoin_zLayer_le_iff` reaches the same conclusion
through the generation half with two fewer closedness hypotheses, and the agreement of the two
routes is the check that no family was mislaid. -/
theorem cfiveJoin_zLayer_le_via_gens {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hT : IsClosed ((lambdaImage G 3 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hY : IsClosed ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {X : Set (levelQuot G 5)} {x : levelQuot G 5}
    (hgen : (Subgroup.closure (insert x X)).topologicalClosure = ⊤)
    (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S)
    (hsq : ∀ c ∈ lambdaImage G 3 5, c ^ 2 * commP c x ∈ S)
    (hdef : ∀ c ∈ lambdaImage G 3 5, commP c x ∈ S) :
    zLayer G 4 ≤ S := by
  have hall : ∀ c ∈ lambdaImage G 3 5, ∀ q, commP c q ∈ S :=
    fun c hc q => cfiveJoin_ad_far_all hS hgen hbr hdef hc q
  refine cfiveSpan_zLayer_le_gens hS hT hY (fun g => ?_) (fun a b => ?_) (fun g r => ?_)
    (fun a b r => ?_) (fun g r q => hall _ (cfive_commP_lambdaTwo_mem_lambdaThree
      (cfiveSpan_sq_mem_lambdaTwo g) r) q)
    (fun a b r q => hall _ (cfive_commP_lambdaTwo_mem_lambdaThree
      (gFourFive_commP_mem_lambdaTwo a b) r) q)
  · exact (cfiveJoin_family_one_iff hsq g).2
      (hall _ (cfive_commP_lambdaTwo_mem_lambdaThree (cfiveSpan_sq_mem_lambdaTwo g) x) x)
  · exact (cfiveJoin_family_two_iff hsq a b).2
      (hall _ (cfive_commP_lambdaTwo_mem_lambdaThree (gFourFive_commP_mem_lambdaTwo a b) x) x)
  · exact (cfiveJoin_family_three_iff hsq g r).2
      (hall _ (cfive_commP_lambdaTwo_mem_lambdaThree (cfiveSpan_sq_mem_lambdaTwo g) r) x)
  · exact (cfiveJoin_family_four_iff hsq a b r).2
      (hall _ (cfive_commP_lambdaTwo_mem_lambdaThree (gFourFive_commP_mem_lambdaTwo a b) r) x)

end Families

/-! ## §7 The defect, reduced as far as this wave takes it

Two reductions, neither of them a discharge.

* `t ↦ commP t x` is a homomorphism on `T`, so the defect need only be checked on generators of
  `T`, which are the squares and the brackets of `Y` (`cfiveJoin_defect_of_two_families`).
* On a bracket generator `commP y w` with `w` an x₁-free far slot, Jacobi trades the defect for
  a bracket of two `Y`-elements (`cfiveJoin_defect_jacobi`).  Nothing here says that bracket is a
  knob; the reduction moves the question, it does not answer it. -/

section Reduction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **Jacobi trades the defect at a bracket generator for a bracket of two `Y`-elements.**
For `y ∈ Y` and `w` an x₁-free far slot, `cfiveSpan_jacobi_rewrite` gives
`commP (commP y w) x = commP (commP w x) y * commP (commP x y) w`, and the second factor is a
bracket knob because `commP x y ∈ T`.  So the defect at the correction `commP y w` costs exactly
`commP (commP w x) y`, whose two slots are both in `Y`.

This is not a discharge: the `⁅Y, Y⁆` term is not supplied by the inventory, and no claim is made
here that it is or is not a knob. -/
theorem cfiveJoin_defect_jacobi {S : Subgroup (levelQuot G 5)} {X : Set (levelQuot G 5)}
    {x : levelQuot G 5} (hbr : ∀ c ∈ lambdaImage G 3 5, ∀ w ∈ X, commP c w ∈ S)
    {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) {w : levelQuot G 5} (hw : w ∈ X)
    (hpair : commP (commP w x) y ∈ S) : commP (commP y w) x ∈ S := by
  rw [cfiveSpan_jacobi_rewrite hy w x]
  exact S.mul_mem hpair (hbr _ (gFourFive_commP_mem_lambdaThree_right x hy) w hw)

/-- ⭐⭐ **The defect on generators of `T`.**  Since `t ↦ commP t x` is a homomorphism on `T` and
`T` is topologically generated by the squares and the brackets of `Y`, the whole defect follows
from two families indexed by `Y`: the squares `(commP y x) ^ 2` and the brackets
`commP (commP y r) x`.  The first family is `commP (y ^ 2) x` evaluated by
`cfiveJoin_commP_sq_lambdaTwo`. -/
theorem cfiveJoin_defect_of_two_families {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hT : IsClosed ((lambdaImage G 3 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    {x : levelQuot G 5}
    (h1 : ∀ y ∈ lambdaImage G 2 5, (commP y x) ^ 2 ∈ S)
    (h2 : ∀ y ∈ lambdaImage G 2 5, ∀ r, commP (commP y r) x ∈ S) :
    ∀ c ∈ lambdaImage G 3 5, commP c x ∈ S := by
  intro c hc
  have hcont : Continuous fun t : levelQuot G 5 => commP t x := by
    simp only [commP]
    fun_prop
  have hadSub : IsClosed
      ((cfiveSpanAdSub S x : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)) :=
    hT.inter (hS.preimage hcont)
  refine (cfiveSpan_lambdaImage_le (k := 2) (n := 5) (by norm_num) hadSub ?_ ?_ hc).2
  · intro w hw
    refine ⟨cfiveSpan_sq_mem_lambdaThree hw, ?_⟩
    rw [cfiveJoin_commP_sq_lambdaTwo hw x]
    exact h1 w hw
  · intro w hw r
    exact ⟨cfive_commP_lambdaTwo_mem_lambdaThree hw r, h2 w hw r⟩

end Reduction

/-! ## §8 At `D_sq h`, and at a mod-2 independent frame

At `D_sq h` the level-five quotient is discrete, so every closedness side condition is free, and
the generation hypothesis follows from the mod-2 independence clause that
`cfiveKnob_supply_of_reach` already carries. -/

section Dsq

variable {h : ℕ}

/-- **The four bracket knobs supply exactly the far slots other than `m 2`.**  The `σ`-slot knob
supplies `m 1`, the `x₀`-slot knob `m 0`, the `u_j`-slot knob `m (sqHandleIdxV j)` and the
`v_j`-slot knob `m (sqHandleIdxU j)`; by `sqIdx_cases` these exhaust the frame. -/
theorem cfiveJoin_farSlot_cases {i : Fin (sqRank h)} (hi : i ≠ 2) :
    i = 0 ∨ i = 1 ∨ (∃ j : Fin h, i = sqHandleIdxU j) ∨ ∃ j : Fin h, i = sqHandleIdxV j := by
  rcases sqIdx_cases i with h0 | h1 | h2 | hU | hV
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact absurd h2 hi
  · exact Or.inr (Or.inr (Or.inl hU))
  · exact Or.inr (Or.inr (Or.inr hV))

/-- ⭐ **A mod-2 independent frame topologically generates the level-five quotient.**  The
pro-2 Frattini criterion gives it in `D_sq h`, and the level map is a continuous surjection, so
the preimage of the closed span swallows everything. -/
theorem cfiveJoin_topGen_of_modTwoIndep {m : Fin (sqRank h) → (DSq h : Type)}
    (hm : SqModTwoIndep m) :
    (Subgroup.closure (Set.range fun i => levelMk (DSq h : Type) 5 (m i))).topologicalClosure
      = ⊤ := by
  set H := Subgroup.topologicalClosure
    (Subgroup.closure (Set.range fun i => levelMk (DSq h : Type) 5 (m i)))
  have hHclosed : IsClosed ((H : Subgroup (levelQuot (DSq h : Type) 5)) :
      Set (levelQuot (DSq h : Type) 5)) := Subgroup.isClosed_topologicalClosure _
  have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) 5) H :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact hHclosed.preimage (continuous_levelMk (DSq h : Type) 5)
  have hmem : ∀ i, m i ∈ Subgroup.comap (levelMk (DSq h : Type) 5) H := fun i =>
    Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨i, rfl⟩)
  have htop : Subgroup.comap (levelMk (DSq h : Type) 5) H = ⊤ := by
    refine eq_top_of_forall_not_le_index_p (p := 2) (isProP_DSq h) hpre ?_
    intro M hM hle
    obtain ⟨i, hi⟩ := hm M hM
    exact hi (hle (hmem i))
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨v, rfl⟩ := levelMk_surjective (DSq h : Type) 5 q
  have hv : v ∈ Subgroup.comap (levelMk (DSq h : Type) 5) H := by
    rw [htop]
    exact Subgroup.mem_top v
  exact hv

/-- **Generation passes to any superset of the frame's image.** -/
theorem cfiveJoin_topGen_of_subset {m : Fin (sqRank h) → (DSq h : Type)}
    (hm : SqModTwoIndep m) {Z : Set (levelQuot (DSq h : Type) 5)}
    (hsub : (Set.range fun i => levelMk (DSq h : Type) 5 (m i)) ⊆ Z) :
    (Subgroup.closure Z).topologicalClosure = ⊤ :=
  eq_top_iff.2 (le_trans (le_of_eq (cfiveJoin_topGen_of_modTwoIndep hm).symm)
    (Subgroup.topologicalClosure_mono (Subgroup.closure_mono hsub)))

/-- ⭐⭐⭐ **The join at a mod-2 independent frame of `D_sq h`.**  The far slots of the four
bracket knobs are the frame letters other than `m 2` (`cfiveJoin_farSlot_cases`), the `x₁`-slot
knob's far slot is `m 2`, every closedness condition is free because `Q₅` is discrete, and the
generation condition follows from mod-2 independence.  So the whole join at the real inventory is

```text
  zLayer 4 ≤ S   ↔   ∀ c ∈ T, commP c (levelMk 5 (m 2)) ∈ S ,
```

the `x₁`-free defect and nothing else. -/
theorem cfiveJoin_zLayer_le_iff_frame {m : Fin (sqRank h) → (DSq h : Type)}
    (hm : SqModTwoIndep m) {S : Subgroup (levelQuot (DSq h : Type) 5)}
    (hbr : ∀ c ∈ lambdaImage (DSq h : Type) 3 5, ∀ i : Fin (sqRank h), i ≠ 2 →
      commP c (levelMk (DSq h : Type) 5 (m i)) ∈ S)
    (hsq : ∀ c ∈ lambdaImage (DSq h : Type) 3 5,
      c ^ 2 * commP c (levelMk (DSq h : Type) 5 (m 2)) ∈ S) :
    zLayer (DSq h : Type) 4 ≤ S ↔ ∀ c ∈ lambdaImage (DSq h : Type) 3 5,
      commP c (levelMk (DSq h : Type) 5 (m 2)) ∈ S := by
  refine cfiveJoin_zLayer_le_iff (cfiveSpan_isClosed S)
    (X := {z | ∃ i : Fin (sqRank h), i ≠ 2 ∧ z = levelMk (DSq h : Type) 5 (m i)})
    (cfiveJoin_topGen_of_subset hm ?_) (fun c hc w hw => ?_) hsq
  · rintro _ ⟨i, rfl⟩
    by_cases hi : i = 2
    · rw [hi]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := hw
    exact hbr c hc i hi

end Dsq

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms cfiveJoin_far_lambdaTwo_mul
#print axioms cfiveJoin_ad_far_mem
#print axioms cfiveJoin_ad_far_lambdaTwo
#print axioms cfiveJoinKnobSet
#print axioms cfiveJoinKnobSub
#print axioms cfiveJoin_knobSub_le
#print axioms cfiveJoin_knobSub_bracket
#print axioms cfiveJoin_knobSub_sq
#print axioms cfiveJoin_defect_pt_iff
#print axioms cfiveJoin_defect_iff
#print axioms cfiveJoin_ad_far_all
#print axioms cfiveJoin_zLayer_le_iff
#print axioms cfiveJoin_zLayer_le_iff_sq
#print axioms cfiveJoin_knobSub_eq_of_defect
#print axioms cfiveJoin_commP_self_lambdaTwo
#print axioms cfiveJoin_commP_sq_lambdaTwo
#print axioms cfiveJoin_pair_correction
#print axioms cfiveJoin_pair_mem
#print axioms cfiveJoin_pow_four_eq
#print axioms cfiveJoin_pow_four_iff
#print axioms cfiveJoin_family_one_iff
#print axioms cfiveJoin_family_two_iff
#print axioms cfiveJoin_family_three_iff
#print axioms cfiveJoin_family_four_iff
#print axioms cfiveJoin_family_five_of_span
#print axioms cfiveJoin_family_six_of_span
#print axioms cfiveJoin_zLayer_le_via_gens
#print axioms cfiveJoin_defect_jacobi
#print axioms cfiveJoin_defect_of_two_families
#print axioms cfiveJoin_farSlot_cases
#print axioms cfiveJoin_topGen_of_modTwoIndep
#print axioms cfiveJoin_topGen_of_subset
#print axioms cfiveJoin_zLayer_le_iff_frame

end AxiomPins

end SqCore

end Dyadic

end GQ2
