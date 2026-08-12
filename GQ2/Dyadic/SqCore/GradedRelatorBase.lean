/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFour

/-!
# W70-FIVE: the relator base at every class

Wave 69 (`SqCore/GradedClassFour.lean`) reduced the class-four instance of the residual to a
single `Q₄`-identity, by way of ⭐⭐ `cfour_relator_base`: with the **trivial** dressing the
class-four relator is exactly the class-four Eichler defect.  Its closing analysis observed that
the proof of that step "used no commutativity" and "should replay at every class".  This file
carries out the replay, and finds that the statement is stronger than the class-four reading
suggests.

## The finding

`cfour_relator_base` is **not a class-four fact, and not a level-quotient fact**.  Stripped of
the `Q₄` packaging it is an identity in `D_sq h` itself, and it needs no hypothesis at all:

> ⭐⭐ `relBase_relator_base`: there is a `t` with
> `sqRelWord (sqArbBase h nu' j) = conjP (relBaseEichDefect nu' j) t`,

where `relBaseEichDefect` is the Eichler defect read **upstairs** (§3).  The conjugator is the
tail of the handle word past the twisted handle, and it is the only trace left of wave 68's
centrality hypothesis and wave 69's `Commute` hypothesis: those two hypotheses were never needed
for the *identity*, only for the cosmetic wish to have the defect land on the right-hand end of
the product rather than conjugated into it.

Since every `twoCentralSeries` layer is normal (`twoCentralSeries_normal`), conjugation is
invisible to every statement the residual actually consumes.  Hence, with **no** hypothesis and
at **every** class `k`:

* ⭐ `relBase_relator_base_mem_iff`: `sqRelWord (sqArbBase h nu' j) ∈ N ↔ relBaseEichDefect nu' j ∈ N`
  for every normal `N`;
* ⭐ `relBase_relator_base_levelMk`: the class-`k` relator of the undressed frame vanishes in
  `Q_k` iff the upstairs defect does;
* ⭐⭐ `relBase_supply_of_eichDefect`: if the upstairs Eichler defect lies in `γ_k` at every
  selected marking and handle, then `SqClassClearingSupply h k`.

So the class-four form was not the general form with a hypothesis attached; it was the general
form with an avoidable hypothesis attached.  §3 records the hypothesis anyway, as
`RelBaseCommuting`, because it is what buys the equality **on the nose** in a target group where
the layers are not normal, and because the `k = 4` instance of the general schema is re-derived
through it (`relBase_relator_base_four`) as an independent check against wave 69.

## Contents

* §1 `relBase_sqWord_free`: the core word expanded by the free-group calculus alone.  This is the
  `hid` step inside wave 69's `cfour_sqWord`, isolated: it holds in every group, and the two
  simplifications wave 69 applies to it afterwards (dropping the inverse on the fourth power,
  collapsing `conjP c a` to `commP c a`) are the class-four-only part.
* §2 The handle surgery with **no** hypothesis: `relBase_prod_map_update` and
  `relBase_handleWord_update` insert a factor at one entry of a product and pay for it with a
  conjugation instead of a commutation.  Wave 69's `cfour_prod_map_update` /
  `cfour_handleWord_update` are the `Commute` versions.  Of those two only
  `cfour_handleWord_update` is cited here, unchanged, inside §3's
  `relBase_relator_base_of_commuting`; `cfour_prod_map_update` is reached only through it.
* §3 The base identity, upstairs and at every class.
* §4 The schema: what the trivial dressing buys, class by class, and what the whole `h ≥ 1`
  residual would follow from.

## Scope

Nothing here discharges any instance of `SqClassClearingSupply`.  What is committed is a
reduction: the class-`k` obligation, **for the trivial dressing**, is the single upstairs
membership `relBaseEichDefect nu' j ∈ γ_k`.  `relBase_defectDies_iff_trivial` states that scope
as an equivalence, so the schema cannot be read as more than it is: a nontrivial dressing may
well discharge a class at which the base defect survives, and wave 68's class-three witness is
exactly such a dressing.

Lane W70-FIVE.  New file; no edits to existing files.  Prefix `relBase`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The core word, before any class is chosen

Wave 69's `cfour_sqWord` reads the core word in `Q₄` as
`commP a b · b⁴ · c² · commP c (commP c a)`.  Two of its three steps are class-four facts
(`cfour_pow_four_inv`, and the collapse of `conjP c a`); the first step is not, and it is the one
every class inherits. -/

section FreeWord

variable {Q : Type*} [Group Q]

/-- **The core word by the free-group calculus alone**: in every group,
`sqWord a b c = commP a b · ((b²)²)⁻¹ · c² · commP c (conjP c a)`.

This is the `hid` step of `cfour_sqWord`, isolated.  The two rewrites wave 69 applies to it
afterwards are the class-four content: `((b²)²)⁻¹ = b⁴` needs `b⁴` to be an involution
(`cfour_pow_four_inv`, which is `b⁸ ∈ γ₄`), and `commP c (conjP c a) = commP c (commP c a)` needs
the correction term of `cfour_commP_mul_right` to die.  Neither is available one class up, so it
is this statement, not `cfour_sqWord`, that a class-five run starts from. -/
theorem relBase_sqWord_free (a b c : Q) :
    sqWord a b c = commP a b * ((b ^ 2) ^ 2)⁻¹ * c ^ 2 * commP c (conjP c a) := by
  simp only [sqWord, conjP, commP]
  group

end FreeWord

/-- Naturality of the bracket.  `SqCore/GradedTwo.lean` has this as `map_commP`, but that module
is not in this file's import closure and is far too heavy to pull in for two rewrites. -/
theorem relBase_map_commP {A B : Type*} [Group A] [Group B] {F : Type*} [FunLike F A B]
    [MonoidHomClass F A B] (φ : F) (a b : A) : φ (commP a b) = commP (φ a) (φ b) := by
  simp only [commP, map_mul, map_inv]

/-! ## §2 Handle surgery with no hypothesis

Wave 68's surgery required the inserted factor to be **central**; wave 69 weakened that to
`Commute` with every entry, which is what its §3 supplied at class four.  Neither is needed: a
factor inserted at entry `j` reaches the end of the product by being **conjugated** by the tail
past `j`.  The conjugator is not named in the statements below, because nothing downstream uses
it: §3 only ever consumes it through a normal subgroup, where it is invisible. -/

section Surgery

variable {Q : Type*} [Group Q]

/-- **One entry of a product over `Fin n` picking up a right factor**, with no hypothesis on that
factor: it emerges at the end of the product conjugated by the entries past `j`.  Wave 69's
`cfour_prod_map_update` is the special case in which the factor commutes with every entry, so
that the conjugation may be discarded. -/
theorem relBase_prod_map_update (n : ℕ) :
    ∀ (F : Fin n → Q) (j : Fin n) (z : Q), ∃ t : Q,
      ((List.finRange n).map fun k => if k = j then F k * z else F k).prod
        = ((List.finRange n).map F).prod * conjP z t := by
  induction n with
  | zero => exact fun F j z => j.elim0
  | succ n ih =>
    intro F j z
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    cases j using Fin.cases with
    | zero =>
      refine ⟨((List.finRange n).map (F ∘ Fin.succ)).prod, ?_⟩
      rw [if_pos rfl]
      have htail : (List.finRange n).map ((fun k => if k = 0 then F k * z else F k)
            ∘ Fin.succ) = (List.finRange n).map (F ∘ Fin.succ) := by
        refine List.map_congr_left fun k _ => ?_
        simp [Fin.succ_ne_zero]
      rw [htail]
      simp only [conjP]
      group
    | succ j' =>
      obtain ⟨t, ht⟩ := ih (F ∘ Fin.succ) j' z
      refine ⟨t, ?_⟩
      rw [if_neg (Fin.succ_ne_zero j').symm]
      have htail : (List.finRange n).map ((fun k => if k = Fin.succ j' then F k * z else F k)
            ∘ Fin.succ)
          = (List.finRange n).map fun k => if k = j' then (F ∘ Fin.succ) k * z
              else (F ∘ Fin.succ) k := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, Fin.succ_inj]
      rw [htail, ht, ← mul_assoc]

/-- **A handle word with one bracket changed by an arbitrary factor**: the factor emerges at the
end conjugated.  Compare `cfour_handleWord_update`, which asks the factor to commute with every
bracket and gets it out unconjugated. -/
theorem relBase_handleWord_update {n : ℕ} (u v u' v' : Fin n → Q) (j : Fin n) (z : Q)
    (hne : ∀ i, i ≠ j → commP (u i) (v i) = commP (u' i) (v' i))
    (hj : commP (u j) (v j) = commP (u' j) (v' j) * z) :
    ∃ t : Q, handleWord u v = handleWord u' v' * conjP z t := by
  obtain ⟨t, ht⟩ := relBase_prod_map_update n (fun i => commP (u' i) (v' i)) j z
  refine ⟨t, ?_⟩
  have hmap : ((List.finRange n).map fun i => commP (u i) (v i))
      = ((List.finRange n).map fun i => if i = j then commP (u' i) (v' i) * z
          else commP (u' i) (v' i)) := by
    refine List.map_congr_left fun i _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij]
      subst hij
      exact hj
    · rw [if_neg hij]
      exact hne i hij
  rw [handleWord, hmap, ht, handleWord]

end Surgery

/-! ## §3 The base identity, upstairs and at every class

The Eichler defect is defined **in `D_sq h`**, not in a level quotient: nothing about it needed
one.  `relBase_relator_base` is then the whole of wave 69's §4 with the class-four packaging
removed, and it carries no hypothesis. -/

section BaseAtEveryClass

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The Eichler defect upstairs**: the amount by which the two cleared handle letters miss the
plain handle bracket, in `D_sq h` itself.  Its image under `levelMk _ 4` is wave 69's
`cfourEichDefect` (`relBase_eichDefect_four`). -/
noncomputable def relBaseEichDefect : (DSq h : Type) :=
  (commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)))⁻¹ *
    commP (sqEichU h nu' j) (sqEichV h nu' j)

/-- The handle brackets of the undressed frame agree with the generator frame's away from the
twisted handle. -/
theorem relBase_handle_ne {i : Fin h} (hi : i ≠ j) :
    commP (sqArbBase h nu' j (sqHandleIdxU i)) (sqArbBase h nu' j (sqHandleIdxV i))
      = commP (sqGen h (sqHandleIdxU i)) (sqGen h (sqHandleIdxV i)) := by
  simp only [sqArbBase_handleU_ne hi, sqArbBase_handleV_ne hi]

/-- At the twisted handle the two differ by the Eichler defect, by construction. -/
theorem relBase_handle_eq :
    commP (sqArbBase h nu' j (sqHandleIdxU j)) (sqArbBase h nu' j (sqHandleIdxV j))
      = commP (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) *
        relBaseEichDefect nu' j := by
  simp only [sqArbBase_handleU, sqArbBase_handleV, relBaseEichDefect]
  rw [mul_inv_cancel_left]

/-- ⭐⭐ **The undressed frame's relator is the Eichler defect, up to conjugation, in `D_sq h`.**

This is wave 69's `cfour_relator_base` with the class-four packaging removed: no level quotient,
no class, and **no hypothesis**.  The generator relation `dsq_relation` absorbs the entire core
word and every untwisted handle bracket, exactly as it does at class four, and the twisted handle
contributes the defect conjugated by the tail of the handle word past `j`.

The conjugator is existentially quantified because nothing downstream needs its value: every
consumer of this statement reads it through a normal subgroup, where conjugation is invisible
(`relBase_relator_base_mem_iff`). -/
theorem relBase_relator_base :
    ∃ t : (DSq h : Type),
      sqRelWord (sqArbBase h nu' j) = conjP (relBaseEichDefect nu' j) t := by
  obtain ⟨t, ht⟩ := relBase_handleWord_update
    (fun i => sqArbBase h nu' j (sqHandleIdxU i)) (fun i => sqArbBase h nu' j (sqHandleIdxV i))
    (fun i => sqGen h (sqHandleIdxU i)) (fun i => sqGen h (sqHandleIdxV i)) j
    (relBaseEichDefect nu' j) (fun i hi => relBase_handle_ne nu' j hi) (relBase_handle_eq nu' j)
  refine ⟨t, ?_⟩
  have hgen : sqRelWord (sqGen h) = 1 := dsq_relation h
  have h0 : sqArbBase h nu' j 0 = sqGen h 0 := cfour_base_eq_gen nu' j
    (by rw [sqVal_zero, sqHandleIdxU_val]; omega) (by rw [sqVal_zero, sqHandleIdxV_val]; omega)
  have h1 : sqArbBase h nu' j 1 = sqGen h 1 := cfour_base_eq_gen nu' j
    (by rw [sqVal_one, sqHandleIdxU_val]; omega) (by rw [sqVal_one, sqHandleIdxV_val]; omega)
  have h2 : sqArbBase h nu' j 2 = sqGen h 2 := cfour_base_eq_gen nu' j
    (by rw [sqVal_two, sqHandleIdxU_val]; omega) (by rw [sqVal_two, sqHandleIdxV_val]; omega)
  rw [sqRelWord] at hgen
  rw [sqRelWord, h0, h1, h2, ht, ← mul_assoc, hgen, one_mul]

/-- ⭐ **The base relator and the base defect are interchangeable inside any normal subgroup.**
This is the form in which every class consumes `relBase_relator_base`: the conjugator of that
statement is invisible to `N`, so no hypothesis survives into the statement at all. -/
theorem relBase_relator_base_mem_iff (N : Subgroup (DSq h : Type)) [hN : N.Normal] :
    sqRelWord (sqArbBase h nu' j) ∈ N ↔ relBaseEichDefect nu' j ∈ N := by
  have key : ∀ (z g : (DSq h : Type)), z ∈ N → conjP z g ∈ N := by
    intro z g hz
    simpa only [conjP, inv_inv] using hN.conj_mem z hz g⁻¹
  obtain ⟨t, ht⟩ := relBase_relator_base nu' j
  rw [ht]
  refine ⟨fun hm => ?_, fun hm => key _ t hm⟩
  have hback := key _ t⁻¹ hm
  have hcancel : conjP (conjP (relBaseEichDefect nu' j) t) t⁻¹ = relBaseEichDefect nu' j := by
    simp only [conjP]
    group
  rwa [hcancel] at hback

/-- ⭐ **The undressed frame clears class `k` exactly when the upstairs defect has died to class
`k`**, at every `k`.  At `k = 4` this is wave 69's reduction; the point is that the class plays no
role in it. -/
theorem relBase_relator_base_levelMk (k : ℕ) :
    sqRelWord (fun i => levelMk (DSq h : Type) k (sqArbBase h nu' j i)) = 1 ↔
      levelMk (DSq h : Type) k (relBaseEichDefect nu' j) = 1 := by
  rw [← map_sqRelWord, ← lim_mem_twoCentralSeries_iff_levelMk,
    ← lim_mem_twoCentralSeries_iff_levelMk]
  exact relBase_relator_base_mem_iff nu' j (twoCentralSeries (DSq h : Type) k)

end BaseAtEveryClass

/-! ### The hypothesis that buys the equality on the nose

Nothing above needs it, but it is worth naming, because it is what wave 69 actually verified at
class four and it is the exact shape that fails at class five: at class four the handle brackets
and the defect both lie in `Y = lambdaImage G 2 4`, which is abelian (`cfour_commP_lambdaTwo`),
whereas in `Q₅` the layer `Y = lambdaImage G 2 5` is only class-two nilpotent, so the commutation
is not available and only the conjugated form survives. -/

section OnTheNose

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The named hypothesis**: in the target of `φ`, every generator handle bracket commutes with
the image of the Eichler defect.  Verified at `k = 4` in `relBase_relator_base_four`. -/
def RelBaseCommuting {Q : Type*} [Group Q] (φ : (DSq h : Type) →* Q) : Prop :=
  ∀ i : Fin h,
    Commute (commP (φ (sqGen h (sqHandleIdxU i))) (φ (sqGen h (sqHandleIdxV i))))
      (φ (relBaseEichDefect nu' j))

/-- ⭐ **The base identity on the nose**, in any target group satisfying `RelBaseCommuting`.  The
proof is wave 69's, with `cfour_handleWord_update` reused verbatim: that lemma was already stated
for an arbitrary group and is not a class-four statement. -/
theorem relBase_relator_base_of_commuting {Q : Type*} [Group Q] (φ : (DSq h : Type) →* Q)
    (H : RelBaseCommuting nu' j φ) :
    sqRelWord (fun i => φ (sqArbBase h nu' j i)) = φ (relBaseEichDefect nu' j) := by
  have hgen : sqRelWord (fun i => φ (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, dsq_relation, map_one]
  have h0 : sqArbBase h nu' j 0 = sqGen h 0 := cfour_base_eq_gen nu' j
    (by rw [sqVal_zero, sqHandleIdxU_val]; omega) (by rw [sqVal_zero, sqHandleIdxV_val]; omega)
  have h1 : sqArbBase h nu' j 1 = sqGen h 1 := cfour_base_eq_gen nu' j
    (by rw [sqVal_one, sqHandleIdxU_val]; omega) (by rw [sqVal_one, sqHandleIdxV_val]; omega)
  have h2 : sqArbBase h nu' j 2 = sqGen h 2 := cfour_base_eq_gen nu' j
    (by rw [sqVal_two, sqHandleIdxU_val]; omega) (by rw [sqVal_two, sqHandleIdxV_val]; omega)
  have hne : ∀ i, i ≠ j →
      commP (φ (sqArbBase h nu' j (sqHandleIdxU i))) (φ (sqArbBase h nu' j (sqHandleIdxV i)))
        = commP (φ (sqGen h (sqHandleIdxU i))) (φ (sqGen h (sqHandleIdxV i))) := by
    intro i hi
    rw [← relBase_map_commP, ← relBase_map_commP, relBase_handle_ne nu' j hi]
  have hj : commP (φ (sqArbBase h nu' j (sqHandleIdxU j))) (φ (sqArbBase h nu' j (sqHandleIdxV j)))
      = commP (φ (sqGen h (sqHandleIdxU j))) (φ (sqGen h (sqHandleIdxV j))) *
        φ (relBaseEichDefect nu' j) := by
    rw [← relBase_map_commP, ← relBase_map_commP, relBase_handle_eq nu' j, map_mul]
  rw [sqRelWord] at hgen
  rw [sqRelWord, h0, h1, h2, cfour_handleWord_update _ _ _ _ j _ H hne hj, ← mul_assoc, hgen,
    one_mul]

/-- The upstairs defect maps onto wave 69's class-four defect. -/
theorem relBase_eichDefect_four :
    levelMk (DSq h : Type) 4 (relBaseEichDefect nu' j) = cfourEichDefect nu' j := by
  rw [relBaseEichDefect, cfourEichDefect, map_mul, map_inv, relBase_map_commP, relBase_map_commP]

/-- ⭐ **Wave 69's `cfour_relator_base`, re-derived from the general schema.**  The `k = 4`
instance of `RelBaseCommuting` is discharged from the committed class-four material: both the
handle brackets and the defect lie in `Y`, and `Y` is abelian in `Q₄`.  This is the independent
check that the generalisation did not drop anything. -/
theorem relBase_relator_base_four :
    sqRelWord (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j i))
      = cfourEichDefect nu' j := by
  rw [← relBase_eichDefect_four]
  refine relBase_relator_base_of_commuting nu' j (levelMk (DSq h : Type) 4) fun i => ?_
  rw [relBase_eichDefect_four]
  exact cfour_commute_lambdaTwo (cfour_commP_mem_lambdaTwo _ _) (cfour_eichDefect_mem nu' j)

end OnTheNose

/-! ## §4 The schema

The payoff of §3: every class inherits the reduction, so a class-`k` run no longer begins with a
fresh relator analysis.  It begins with a single upstairs membership.

The scope is stated exactly.  `RelBaseDefectDies h k` is **equivalent** to "the trivial dressing
clears class `k`" (`relBase_defectDies_iff_trivial`), and it is only **sufficient** for
`SqClassClearingSupply h k`, since that predicate quantifies over all admissible dressings.  Wave
68's class-three witness is a nontrivial dressing, so the gap is real and is not an artefact of
the statement. -/

section Schema

variable {h : ℕ}

/-- ⭐⭐ **The class-`k` supply from the upstairs Eichler defect, at every `k`.**  Wherever the
defect has died to class `k`, the trivial dressing discharges the class-`k` clearing problem:
rows on the nose, mod-2 independence by wave 67's `lim_sqArbBase_modTwoIndep`, and the relator by
`relBase_relator_base_mem_iff`.  Wave 69's `cfour_supply_of_eichDefect` is the case `k = 4`. -/
theorem relBase_supply_of_eichDefect (k : ℕ)
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        relBaseEichDefect nu' j ∈ twoCentralSeries (DSq h : Type) k) :
    SqClassClearingSupply h k := by
  intro nu' j hs hx
  have hfr : sqArbFrame h nu' j (fun _ => 1) = sqArbBase h nu' j := funext fun i => mul_one _
  refine ⟨fun _ => 1, fun _ => map_one _, fun _ => map_one _, ?_, ?_⟩
  · rw [hfr]
    exact lim_sqArbBase_modTwoIndep
  · rw [hfr]
    exact (relBase_relator_base_mem_iff nu' j _).mpr (H nu' j hs hx)

/-- **The class-`k` clause of the schema**: the upstairs Eichler defect has died to class `k` at
every selected marking and every handle. -/
def RelBaseDefectDies (h k : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      relBaseEichDefect nu' j ∈ twoCentralSeries (DSq h : Type) k

/-- ⭐ **The scope of the schema, exactly**: the clause is neither more nor less than the
statement that the *trivial* dressing clears class `k`.  Stated so that
`relBase_supply_of_defectDies` cannot be misread as an equivalence with the supply, which
quantifies over every admissible dressing. -/
theorem relBase_defectDies_iff_trivial (h k : ℕ) :
    RelBaseDefectDies h k ↔
      ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          sqRelWord (sqArbFrame h nu' j (fun _ => 1)) ∈ twoCentralSeries (DSq h : Type) k := by
  have hfr : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      sqArbFrame h nu' j (fun _ => 1) = sqArbBase h nu' j :=
    fun nu' j => funext fun i => mul_one _
  refine ⟨fun H nu' j hs hx => ?_, fun H nu' j hs hx => ?_⟩
  · rw [hfr nu' j]
    exact (relBase_relator_base_mem_iff nu' j _).mpr (H nu' j hs hx)
  · have hm := H nu' j hs hx
    rw [hfr nu' j] at hm
    exact (relBase_relator_base_mem_iff nu' j _).mp hm

/-- The class-`k` clause supplies class `k`. -/
theorem relBase_supply_of_defectDies {k : ℕ} (H : RelBaseDefectDies h k) :
    SqClassClearingSupply h k :=
  relBase_supply_of_eichDefect k H

/-- The clause is inherited downwards, since the tower is antitone. -/
theorem relBase_defectDies_of_le {k k' : ℕ} (hkk : k' ≤ k) (H : RelBaseDefectDies h k) :
    RelBaseDefectDies h k' :=
  fun nu' j hs hx =>
    twoCentralSeries_antitone (G := (DSq h : Type)) hkk (H nu' j hs hx)

/-- ⭐⭐ **The schema, as the residual reads it**: if the upstairs Eichler defect dies at every
class from four on, wave 68's `BridgeFinalResidual` follows, and with it the whole `h ≥ 1`
residual.  This is a *sufficient* condition, being the trivial-dressing route only. -/
theorem relBase_residual_of_defectDies (H : ∀ k, 4 ≤ k → RelBaseDefectDies h k) :
    BridgeFinalResidual h :=
  fun k hk => relBase_supply_of_defectDies (H k hk)

/-- ⭐⭐ The same condition, carried to the campaign's endgame statement through wave 68's
`bridgeFinal_residual_iff`. -/
theorem relBase_transitivity_of_defectDies (H : ∀ k, 4 ≤ k → RelBaseDefectDies h k) :
    SqLamMarkTransitivity h :=
  bridgeFinal_residual_iff.mpr (relBase_residual_of_defectDies H)

end Schema

/-! ## §5 Axiom pins -/

section AxiomPins

#print axioms relBase_sqWord_free
#print axioms relBase_map_commP
#print axioms relBase_prod_map_update
#print axioms relBase_handleWord_update
#print axioms relBaseEichDefect
#print axioms relBase_handle_ne
#print axioms relBase_handle_eq
#print axioms relBase_relator_base
#print axioms relBase_relator_base_mem_iff
#print axioms relBase_relator_base_levelMk
#print axioms RelBaseCommuting
#print axioms relBase_relator_base_of_commuting
#print axioms relBase_eichDefect_four
#print axioms relBase_relator_base_four
#print axioms relBase_supply_of_eichDefect
#print axioms RelBaseDefectDies
#print axioms relBase_defectDies_iff_trivial
#print axioms relBase_supply_of_defectDies
#print axioms relBase_defectDies_of_le
#print axioms relBase_residual_of_defectDies
#print axioms relBase_transitivity_of_defectDies

end AxiomPins

end SqCore

end Dyadic

end GQ2
