/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.CommFrames
import GQ2.Roe.Labute.TwoCentralTower

/-!
# W67-LIMIT: the compactness assembly - the `h ≥ 1` residual, one class at a time

The residual `SqLamMarkTransitivity h` is committed-equivalent to the arbitrary-dressing word
identity `SqArbRelWord h` (`SqCore/CommFrames.lean` §1).  Wave after wave of instrumentation
measured the CLASS-`k` shadow of that identity - solvability of the clearing system in the
finite quotients of the lower 2-central tower - without ever attempting the assembly: "if the
class-`k` clearing problem is solvable for every `k`, the pro-2 clearing dressing exists".
This file commits the assembly.  After it, the limit step is mathematics and what remains of
the residual is a per-class graded statement.

## §1 The compatibility analysis

The assembly needs the per-class solution sets to form an inverse system.  Verdict: they
**project by construction, in the strongest possible form - the sets are nested.**

* The class-`k` solution set is stated *upstairs*: `limClearingSet h nu' j k` is the set of
  dressings `a : Fin (sqRank h) → DSq h` whose rows are exactly `λ`-trivial and `ν'`-trivial,
  whose frame is mod-2 independent, and whose relator value lies in
  `twoCentralSeries (DSq h) k`.  Only the relator clause mentions `k`, so the ambient space is
  the same for every class and `twoCentralSeries_antitone` makes the family **antitone**
  (`limClearingSet_antitone`): a class-`(k+1)` solution *is* a class-`k` solution.  No
  inverse-system functor, no compatible-subsystem repair, no solutions-with-memory variant.
* The committed template's assembly (`Instances/StageAbstractionEvenFinite.lean`,
  `exists_globalMarking`: a König section selection by
  `nonempty_sections_of_finite_cofiltered_system`, then a coordinate realization by
  `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) collapses accordingly
  into the finite-intersection property of a nested family of closed subsets of the compact
  space `(DSq h)^(sqRank h)` - the same compactness, run one functor earlier, by the mathlib
  lemma the template's realization step uses.  The
  template's `OpenTuple` interface itself does not fit verbatim: it carries one `ℤ₂ˣ`-valued
  row functional where the clearing problem carries two `ℤ₂`-valued rows plus the independence
  clause, so this file re-instantiates the committed pattern rather than invoking the template.
* **Measured vs provable.**  The sweeps' solution sets live in the finite level quotients;
  this file's sets live upstairs with exact rows.  Upstairs nonemptiness projects to
  finite-level solvability trivially; the converse per class is a row-lifting question (lift a
  finite-level dressing to an exactly-row-trivial one) that is *not* settled here and belongs
  to the class-`k` attack surface.  The reduction does not consume it: `SqArbRelWord h` is
  **equivalent** to all-`k` upstairs solvability (`limFinal_arbRelWord_iff`), because a global
  solution restricts to every class.  The sweep's affine-coset picture (w50 §6.2) remains
  measured, and is not needed by the assembly.

## §2 The per-class statement

`SqClassClearingSupply h k` is *literally* `SqArbRelWord h` with the relator identity
`sqRelWord (sqArbFrame h nu' j a) = 1` weakened to membership in `twoCentralSeries (DSq h) k`.
At `k` fixed it is the statement the sweeps measured, stated upstairs; the family is antitone
in `k` (`sqClassClearingSupply_of_le`) and follows from `SqArbRelWord h` at every `k`
(`sqClassClearingSupply_of_arbRelWord`).

## §3 The assembly

⭐⭐⭐ `limFinal_arbRelWord`: if `SqClassClearingSupply h k` holds for every `k`, then
`SqArbRelWord h`.  Compactness of `(DSq h)^(sqRank h)`, closedness of every clause, the nested
family, and the committed separation `⨅ k, twoCentralSeries (DSq h) k = ⊥`
(`iInf_twoCentralSeries`, through `dsq_topGen` and `isProP_DSq`) are the whole proof.  With the
committed equivalences this yields `SqClearingStep h` and `SqLamMarkTransitivity h`
(`limFinal_clearingStep`, `limFinal_markTransitivity`), and the reduction is exact:
⭐⭐⭐ `limFinal_markTransitivity_iff`:
`SqLamMarkTransitivity h ↔ ∀ k, SqClassClearingSupply h k`.

## §4 The committed classes

`sqRelWord` lands in `twoCentralSeries G 2` at *every* tuple of *every* topological group
(`lim_sqRelWord_mem_twoCentralSeries_two`: the core word is a product of two commutators and
two squares, the handles are commutators), and the undressed frame is mod-2 independent
(`lim_sqArbBase_modTwoIndep`), so `SqClassClearingSupply h k` is a theorem for `k ≤ 2`
(`sqClassClearingSupply_two`, `sqClassClearingSupply_of_le_two`) - the trivial dressing
witnesses it.  No class `k ≥ 3` instance is committed today: the class-3 slice statement of
`GradedContain` and the census kills of `GradedCensusAchieve` are proved on the graded slices
over the marking binder (`SqU4 gr3R` and `SqU6 gr3R` respectively), not on the tower, and the
binder-to-tower bridge is part of the attack surface.

## §5 The residual, restated

`LimFinalResidual h`: `SqClassClearingSupply h k` for every `k ≥ 3` - the honest remainder
after §4, and equivalent to the full residual (⭐⭐⭐ `limFinal_residual_iff`).  What a proof of
the general class-`k` step has to produce, per the measurements: a dressing solving a linear
system of uniform corank `sqRank h + 1` over the class-`k` layer (w50 §6.3), with the mod-2
parity dependence of w51 §2.4 (confirmed at class 6 in §5.3) and the graded Fox form δ of w52
as the structure; the mechanism is w52 §7's containment target, that the defect of any
`K`-dressed frame of the relator lies in `im δ` at every level.  ⚠ At class four ON THE SLICE
that is already a theorem (`GradedContainFour.sqRelWord_conFourDress_of_rel`, whose docstring
is the "pure dressing artefact" phrasing often quoted for it); on the tower it is conjectural,
and the tower form is what this residual needs.

Lane W67-LIMIT.  New file; no edits to existing files.  Prefixes `lim` / `sqClassClearing` /
`limFinal`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The per-class solution sets, nested -/

section ClearingSets

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

variable (h nu' j) in
/-- **The class-`k` solution set** of the clearing problem at a marking `nu'` and handle `j`
(selectedness of `nu'` is *not* required here; it enters through `SqClassClearingSupply`):
dressings with exactly trivial `λ`- and `ν'`-rows and a mod-2 independent frame, whose
relator value has died to class `k`.  Only the last clause depends on `k`. -/
def limClearingSet (k : ℕ) : Set (Fin (sqRank h) → (DSq h : Type)) :=
  {a | (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
    SqModTwoIndep (sqArbFrame h nu' j a) ∧
      sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) k}

theorem mem_limClearingSet {k : ℕ} {a : Fin (sqRank h) → (DSq h : Type)} :
    a ∈ limClearingSet h nu' j k ↔
      (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
        SqModTwoIndep (sqArbFrame h nu' j a) ∧
          sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) k :=
  Iff.rfl

/-- **The compatibility verdict, in one line**: the class-`(k+1)` solutions do not merely
project into the class-`k` solutions - the sets are nested, because only the relator clause
sees `k` and the tower is antitone. -/
theorem limClearingSet_antitone {k k' : ℕ} (hkk : k' ≤ k) :
    limClearingSet h nu' j k ⊆ limClearingSet h nu' j k' :=
  fun _ ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2, h3, twoCentralSeries_antitone (G := (DSq h : Type)) hkk h4⟩

/-- The relator clause of `limClearingSet`, read in the tower's own language: membership in
`twoCentralSeries G k` is vanishing at level `k`, i.e. under `levelMk G k`. -/
theorem lim_mem_twoCentralSeries_iff_levelMk {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (k : ℕ) (r : G) :
    r ∈ twoCentralSeries G k ↔ levelMk G k r = 1 :=
  (QuotientGroup.eq_one_iff r).symm

/-- `D_sq h` is topologically finitely generated, in the `Finset` form the tower's profinite
section consumes (`dsq_topGen`, with the range of `sqGen` as the finite set). -/
theorem lim_dsq_finsetGen (h : ℕ) :
    ∃ s : Finset (DSq h : Type),
      (Subgroup.closure (s : Set (DSq h : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (sqGen h), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact dsq_topGen h

/-- **The tower of `D_sq h` separates points**: the committed neighborhood-basis argument
(`iInf_twoCentralSeries`), instantiated through `lim_dsq_finsetGen` and `isProP_DSq`. -/
theorem lim_iInf_twoCentralSeries (h : ℕ) :
    ⨅ k, twoCentralSeries (DSq h : Type) k = ⊥ :=
  iInf_twoCentralSeries (G := (DSq h : Type)) (lim_dsq_finsetGen h) (isProP_DSq h)

end ClearingSets

/-! ## §2 Closedness of every clause -/

section Closedness

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- Each frame slot varies continuously in the dressing: the slot is a fixed base element
times the dressing's own coordinate. -/
theorem limContinuous_arbFrame_apply (i : Fin (sqRank h)) :
    Continuous fun a : Fin (sqRank h) → (DSq h : Type) => sqArbFrame h nu' j a i :=
  continuous_const.mul (continuous_apply i)

/-- The relator value of the dressed frame varies continuously in the dressing: the relator
shape is a group word in the slots. -/
theorem limContinuous_sqRelWord_arbFrame :
    Continuous fun a : Fin (sqRank h) → (DSq h : Type) => sqRelWord (sqArbFrame h nu' j a) := by
  simp only [sqRelWord]
  refine Continuous.mul ?_ ?_
  · simp only [sqWord, conjP, commP, sqArbFrame]
    fun_prop
  · simp only [handleWord, sqArbFrame]
    refine continuous_list_prod _ fun j' _ => ?_
    simp only [commP]
    fun_prop

/-- The exact-row clauses are closed: point evaluation followed by a continuous character,
against a closed singleton. -/
theorem lim_isClosed_row (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    IsClosed {a : Fin (sqRank h) → (DSq h : Type) | ∀ i, f (a i) = 1} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i =>
    isClosed_eq (f.continuous_toFun.comp (continuous_apply i)) continuous_const

/-- The independence clause is closed: for each of the finitely many slots and each index-two
open normal subgroup, escape is a clopen condition. -/
theorem lim_isClosed_modTwoIndep :
    IsClosed {a : Fin (sqRank h) → (DSq h : Type) | SqModTwoIndep (sqArbFrame h nu' j a)} := by
  have hset : {a : Fin (sqRank h) → (DSq h : Type) | SqModTwoIndep (sqArbFrame h nu' j a)} =
      ⋂ (M : OpenNormalSubgroup (DSq h : Type)) (_ : M.toSubgroup.index = 2),
        ⋃ i : Fin (sqRank h),
          {a : Fin (sqRank h) → (DSq h : Type) |
            sqArbFrame h nu' j a i ∈ ((M.toSubgroup : Set (DSq h : Type)))ᶜ} := by
    ext a
    simp only [SqModTwoIndep, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_compl_iff, SetLike.mem_coe]
  rw [hset]
  refine isClosed_iInter fun M => isClosed_iInter fun _ => isClosed_iUnion_of_finite fun i => ?_
  exact IsClosed.preimage (limContinuous_arbFrame_apply i) M.isOpen'.isClosed_compl

/-- **The class-`k` solution set is closed** - all four clauses are. -/
theorem isClosed_limClearingSet (k : ℕ) : IsClosed (limClearingSet h nu' j k) :=
  (lim_isClosed_row (nuLam h)).inter ((lim_isClosed_row nu').inter
    (lim_isClosed_modTwoIndep.inter
      (IsClosed.preimage limContinuous_sqRelWord_arbFrame
        (isClosed_twoCentralSeries (G := (DSq h : Type)) k))))

end Closedness

/-! ## §3 The per-class supply -/

section Supply

variable {h : ℕ}

/-- **The class-`k` clearing supply**: `SqArbRelWord h` with the relator identity weakened to
"the relator value dies to class `k`".  At every selected marking and every handle there are
`λ`-trivial, `ν'`-trivial dressings whose frame spans `H₁` mod 2 and whose relator value lies
in `twoCentralSeries (DSq h) k`.  These are the depth sweeps' per-class statements, stated
upstairs (module docstring §1). -/
def SqClassClearingSupply (h k : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ a : Fin (sqRank h) → (DSq h : Type),
        (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
          SqModTwoIndep (sqArbFrame h nu' j a) ∧
            sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) k

/-- The supply is nonemptiness of the class-`k` solution sets, at every selected marking and
every handle. -/
theorem sqClassClearingSupply_iff {k : ℕ} :
    SqClassClearingSupply h k ↔
      ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          (limClearingSet h nu' j k).Nonempty :=
  Iff.rfl

/-- The family is antitone in the class: a deeper supply restricts to every shallower one.
This is the Prop-level face of `limClearingSet_antitone`. -/
theorem sqClassClearingSupply_of_le {k k' : ℕ} (hkk : k' ≤ k)
    (H : SqClassClearingSupply h k) : SqClassClearingSupply h k' := by
  intro nu' j hsigma hx0
  obtain ⟨a, h1, h2, h3, h4⟩ := H nu' j hsigma hx0
  exact ⟨a, h1, h2, h3, twoCentralSeries_antitone (G := (DSq h : Type)) hkk h4⟩

/-- The full relator identity supplies every class: `1` lies in every tower level. -/
theorem sqClassClearingSupply_of_arbRelWord (H : SqArbRelWord h) (k : ℕ) :
    SqClassClearingSupply h k := by
  intro nu' j hsigma hx0
  obtain ⟨a, h1, h2, h3, h4⟩ := H nu' j hsigma hx0
  exact ⟨a, h1, h2, h3, by rw [h4]; exact Subgroup.one_mem _⟩

end Supply

/-! ## §4 The assembly -/

section Assembly

variable {h : ℕ}

/-- **The compactness core**: the nested nonempty closed solution sets meet, by the
finite-intersection property in the compact space of dressings.  This is the same mathlib
lemma the committed König template runs
(`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`), applied one functor
earlier (module docstring §1). -/
theorem limClearingSet_iInter_nonempty
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
    (hne : ∀ k, (limClearingSet h nu' j k).Nonempty) :
    (⋂ k, limClearingSet h nu' j k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', limClearingSet_antitone (le_max_left k k'),
      limClearingSet_antitone (le_max_right k k')⟩
  · exact hne
  · exact fun k => (isClosed_limClearingSet k).isCompact
  · exact fun k => isClosed_limClearingSet k

/-- ⭐⭐⭐ **The compactness assembly**: if the class-`k` clearing problem is solvable for
every `k` - upstairs, in the sense of `SqClassClearingSupply` - then the arbitrary-dressing
relator identity holds outright.  Nestedness (§1), closedness (§2), compactness of the
dressing space, and the committed tower separation `lim_iInf_twoCentralSeries` are the whole
argument; no finite-quotient argument is asked to conclude on its own, so the discrete
obstruction (the amalgam's marking-transitivity failure, recorded at
`docs/dyadic/w67-limit-note.md` §2, which attributes it to wave 44) is not in the way. -/
theorem limFinal_arbRelWord (H : ∀ k, SqClassClearingSupply h k) : SqArbRelWord h := by
  intro nu' j hsigma hx0
  have hne : ∀ k, (limClearingSet h nu' j k).Nonempty := fun k => H k nu' j hsigma hx0
  obtain ⟨a, ha⟩ := limClearingSet_iInter_nonempty hne
  have hmem : ∀ k, a ∈ limClearingSet h nu' j k := Set.mem_iInter.mp ha
  obtain ⟨h1, h2, h3, -⟩ := hmem 0
  refine ⟨a, h1, h2, h3, ?_⟩
  have hall : sqRelWord (sqArbFrame h nu' j a) ∈ ⨅ k, twoCentralSeries (DSq h : Type) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2
  rwa [lim_iInf_twoCentralSeries h, Subgroup.mem_bot] at hall

/-- ⭐⭐⭐ **The reduction is exact**: the residual's word form is precisely the conjunction
of its class instances. -/
theorem limFinal_arbRelWord_iff : SqArbRelWord h ↔ ∀ k, SqClassClearingSupply h k :=
  ⟨sqClassClearingSupply_of_arbRelWord, limFinal_arbRelWord⟩

/-- The clearing scheme, from the class instances. -/
theorem limFinal_clearingStep (H : ∀ k, SqClassClearingSupply h k) : SqClearingStep h :=
  sqClearingStep_of_arbRelWord (limFinal_arbRelWord H)

/-- **The `h ≥ 1` residual, from the class instances.** -/
theorem limFinal_markTransitivity (H : ∀ k, SqClassClearingSupply h k) :
    SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_arbRelWord (limFinal_arbRelWord H)

/-- ⭐⭐⭐ **The residual is its class instances**: `SqLamMarkTransitivity h` holds iff the
class-`k` clearing problem is solvable for every `k`.  The limit step is committed
mathematics; what remains is graded, class by class. -/
theorem limFinal_markTransitivity_iff :
    SqLamMarkTransitivity h ↔ ∀ k, SqClassClearingSupply h k :=
  sqArbRelWord_iff_lamMarkTransitivity.symm.trans limFinal_arbRelWord_iff

end Assembly

/-! ## §5 The committed classes: `k ≤ 2` -/

section CommittedClasses

/-- **The relator dies to class 2 at every tuple of every topological group**: the core word
is two commutators and two squares, the handle word is a product of commutators, and
`twoCentralSeries G 2` is the closed span of all squares and commutators of `G`. -/
theorem lim_sqRelWord_mem_twoCentralSeries_two {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {hh : ℕ} (m : Fin (sqRank hh) → G) :
    sqRelWord m ∈ twoCentralSeries G 2 := by
  have h2 : twoCentralSeries G 2 = twoCentralSucc (⊤ : Subgroup G) := by
    rw [twoCentralSeries_succ (G := G) (le_refl 1), twoCentralSeries_one]
  rw [h2, sqRelWord]
  refine Subgroup.mul_mem _ ?_ ?_
  · have hid : sqWord (m 0) (m 1) (m 2) =
        commP (m 0) (m 1) * (((m 1) ^ 2) ^ 2)⁻¹ * (m 2) ^ 2 *
          commP (m 2) (conjP (m 2) (m 0)) := by
      simp only [sqWord, conjP, commP]
      group
    rw [hid]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (commP_mem_twoCentralSucc (Subgroup.mem_top _) _)
      (Subgroup.inv_mem _ (sq_mem_twoCentralSucc (Subgroup.mem_top _))))
      (sq_mem_twoCentralSucc (Subgroup.mem_top _)))
      (commP_mem_twoCentralSucc (Subgroup.mem_top _) _)
  · simp only [handleWord]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j', -, rfl⟩ := List.mem_map.mp hx
    exact commP_mem_twoCentralSucc (Subgroup.mem_top _) _

/-- **The undressed frame is mod-2 independent** at every marking and every handle: an
index-two open normal subgroup swallowing every slot swallows `σ`, `x₀` and hence the pivot,
hence both cleared letters' pivot dressings, hence every standard generator - against
`exists_sqGen_notMem`. -/
theorem lim_sqArbBase_modTwoIndep {h : ℕ}
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h} :
    SqModTwoIndep (sqArbBase h nu' j) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, sqArbBase h nu' j i ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hs : dsqSigma h ∈ M.toSubgroup := by
    have h0 := hmem 0
    rwa [sqArbBase_zero] at h0
  have hx : dsqX0 h ∈ M.toSubgroup := by
    have h1 := hmem 1
    rwa [sqArbBase_one] at h1
  have hpiv : sqPivot h ∈ M.toSubgroup := sqPivot_mem_of_index_two hM hs hx
  have hgen : ∀ i, sqGen h i ∈ M.toSubgroup := by
    intro i
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · exact hs
    · exact hx
    · have h2 := hmem 2
      rwa [sqArbBase_two] at h2
    · by_cases hjj : j' = j
      · subst hjj
        have hU := hmem (sqHandleIdxU j')
        rw [sqArbBase_handleU] at hU
        have hz := zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv
          (toAdd (nu' (sqGen h (sqHandleIdxU j'))))
        have hprod := M.toSubgroup.mul_mem hz hU
        rwa [sqEichU, mul_inv_cancel_left] at hprod
      · have hU := hmem (sqHandleIdxU j')
        rwa [sqArbBase_handleU_ne hjj] at hU
    · by_cases hjj : j' = j
      · subst hjj
        have hV := hmem (sqHandleIdxV j')
        rw [sqArbBase_handleV] at hV
        have hz := zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv
          (toAdd (nu' (sqGen h (sqHandleIdxV j'))))
        have hprod := M.toSubgroup.mul_mem hV hz
        rwa [sqEichV, inv_mul_cancel_right] at hprod
      · have hV := hmem (sqHandleIdxV j')
        rwa [sqArbBase_handleV_ne hjj] at hV
  obtain ⟨i, hi⟩ := exists_sqGen_notMem M hM
  exact hi (hgen i)

/-- **Class 2 is a theorem**: the trivial dressing has exactly trivial rows, its frame is the
undressed frame, and the relator value dies to class 2 wherever it is evaluated. -/
theorem sqClassClearingSupply_two (h : ℕ) : SqClassClearingSupply h 2 := by
  intro nu' j _ _
  refine ⟨fun _ => 1, fun _ => map_one (nuLam h), fun _ => map_one nu', ?_, ?_⟩
  · have hfr : sqArbFrame h nu' j (fun _ => 1) = sqArbBase h nu' j :=
      funext fun i => mul_one _
    rw [hfr]
    exact lim_sqArbBase_modTwoIndep
  · exact lim_sqRelWord_mem_twoCentralSeries_two _

/-- **The committed classes**: `SqClassClearingSupply h k` for every `k ≤ 2`.  No class
`k ≥ 3` instance is committed today - the class-3 material of `GradedContain` and the census
kills live on the binder, not the tower (module docstring §4). -/
theorem sqClassClearingSupply_of_le_two {h k : ℕ} (hk : k ≤ 2) : SqClassClearingSupply h k :=
  sqClassClearingSupply_of_le hk (sqClassClearingSupply_two h)

end CommittedClasses

/-! ## §6 The residual, restated -/

section Residual

/-- **The honest remainder**: the class-`k` clearing supply at every class `k ≥ 3`.  Classes
`k ≤ 2` are theorems (§5), so the residual now begins exactly where the depth sweeps began
measuring. -/
def LimFinalResidual (h : ℕ) : Prop :=
  ∀ k, 3 ≤ k → SqClassClearingSupply h k

/-- The remainder supplies every class, the committed ones filling `k ≤ 2`. -/
theorem limFinal_supply_of_residual {h : ℕ} (H : LimFinalResidual h) (k : ℕ) :
    SqClassClearingSupply h k := by
  by_cases hk : k ≤ 2
  · exact sqClassClearingSupply_of_le_two hk
  · exact H k (by omega)

/-- **The `h ≥ 1` residual, from the classes not yet committed.** -/
theorem limFinal_markTransitivity_of_residual {h : ℕ} (H : LimFinalResidual h) :
    SqLamMarkTransitivity h :=
  limFinal_markTransitivity (limFinal_supply_of_residual H)

/-- ⭐⭐⭐ **The wave's landing**: the residual *equals* its class-`k ≥ 3` instances. -/
theorem limFinal_residual_iff {h : ℕ} : SqLamMarkTransitivity h ↔ LimFinalResidual h :=
  ⟨fun H k _ => sqClassClearingSupply_of_arbRelWord
      (sqArbRelWord_iff_lamMarkTransitivity.mpr H) k,
    limFinal_markTransitivity_of_residual⟩

end Residual

/-! ## §7 Axiom pins -/

section AxiomPins

#print axioms limClearingSet
#print axioms mem_limClearingSet
#print axioms limClearingSet_antitone
#print axioms lim_mem_twoCentralSeries_iff_levelMk
#print axioms lim_dsq_finsetGen
#print axioms lim_iInf_twoCentralSeries
#print axioms limContinuous_arbFrame_apply
#print axioms limContinuous_sqRelWord_arbFrame
#print axioms lim_isClosed_row
#print axioms lim_isClosed_modTwoIndep
#print axioms isClosed_limClearingSet
#print axioms SqClassClearingSupply
#print axioms sqClassClearingSupply_iff
#print axioms sqClassClearingSupply_of_le
#print axioms sqClassClearingSupply_of_arbRelWord
#print axioms limClearingSet_iInter_nonempty
#print axioms limFinal_arbRelWord
#print axioms limFinal_arbRelWord_iff
#print axioms limFinal_clearingStep
#print axioms limFinal_markTransitivity
#print axioms limFinal_markTransitivity_iff
#print axioms lim_sqRelWord_mem_twoCentralSeries_two
#print axioms lim_sqArbBase_modTwoIndep
#print axioms sqClassClearingSupply_two
#print axioms sqClassClearingSupply_of_le_two
#print axioms LimFinalResidual
#print axioms limFinal_supply_of_residual
#print axioms limFinal_markTransitivity_of_residual
#print axioms limFinal_residual_iff

end AxiomPins

end SqCore

end Dyadic

end GQ2
