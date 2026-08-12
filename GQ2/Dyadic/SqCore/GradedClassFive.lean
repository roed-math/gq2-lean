/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedRelatorBase

/-!
# W70-FIVE: the class-five map

Class five loses the property which made class four tractable: `⁅γ₂, γ₂⁆ ≤ γ₄`
is exactly a class-four fact, so the class-four proof that `γ₂` is abelian delivers nothing in
`Q₅`, the "reorder at will" step of `GradedClassFour` §3 is no longer justified (the phrase is
that file's, verbatim), and the relator can no longer be treated as a product in an abelian
group.  (That is a statement about the available proof, not about `Y`; see the scope note
below.)  Two things the class-five analogue therefore needs are `⁅γ₂, γ₃⁆ ≤ γ₅` and a
non-abelian bookkeeping layer.  This file supplies both, and locates the degradation of the rest
of the class-four calculus precisely.

**Attribution.**  This reading is **this file's own**, not wave 69's.  Wave 69 is
`GradedClassFour.lean` together with `docs/dyadic/w69-class4-note.md`; the module mentions class
five on exactly one line ("the residual would start at class five") and says nothing about
`⁅γ₂, γ₃⁆ ≤ γ₅` or about a bookkeeping layer, and the note does not mention class five at all.

## The three answers

**(a) `⁅γ₂, γ₃⁆ ≤ γ₅` is true, and the wave-69 closed-annihilator argument proves it after an
index shift only.**  §3 carries the argument out once, at every layer at once:

> ⭐⭐ `cfive_commutator_lambdaTwo`: for every `k`, `v ∈ γ_k` and `w ∈ γ₂` give `commP v w ∈ γ_{k+2}`,

that is `⁅γ_k, γ₂⁆ ≤ γ_{k+2}`.  Nothing in wave 69's proof was about the number two: the
annihilator `{g | commP v g ∈ γ_{k+2}}` of a `γ_k`-element is closed for the same reason, is a
subgroup because the correction term of `cfour_commP_mul_right` is a **double** bracket against
`γ_k` and so is already two layers down, contains every square because `commP v g ∈ γ_{k+1}` and
`γ_{k+1}² ≤ γ_{k+2}`, and contains every commutator because `cfiveCommHom` is a homomorphism into
the central layer `Z_{k+1}`.  Hence it contains `twoCentralSucc ⊤ = γ₂`.

`⁅γ₂, γ₃⁆ ≤ γ₅` is the instance `k = 3` (`cfive_commutator_two_three`), and wave 69's
`cfour_commutator_lambdaTwo` is the instance `k = 2`, re-derived here as
`cfive_commutator_four_of_two`.

**(b) What replaces `γ₂`-abelianness is a nilpotency-class-at-most-two layer, and it is linear.**
In `Q₅` the layer `Y = lambdaImage G 2 5` is no longer *known* to be abelian, but by (a) at
`k = 2` its commutators land in `zLayer G 4`, which is **central** in `Q₅` and of **exponent
two**.  So (§4):

* `cfive_swap_free`: `y · y' = y' · y · commP y y'` in any group at all;
* ⭐ `cfive_commP_lambdaTwo_central` and `cfive_commP_lambdaTwo_sq`: the correction is central and
  squares to `1`;
* ⭐ `cfive_commP_lambdaTwo_hom_left` / `_right`: `commP` restricted to `Y × Y` is
  **bimultiplicative** into that central exponent-two layer.

So the class-five reordering device is: reorder freely, and collect an `F₂`-bilinear correction.
That is strictly more bookkeeping than class four, but it is a linear amount, not a bracket
jungle, and it is the honest replacement for `cfour_commP_lambdaTwo`.

**(c) Which of wave 69's lemmas survive, and in what form.**  There is no table anywhere in this
file; what follows is the inventory of the lemmas §1 to §5 restate or replace, in three groups.
It is not the complete list of wave-69 lemmas without a class-five reading: the scope note below
names `cfour_pow_four_inv` as a further one, and `cfour_commP_lambdaTwo` (`Y` abelian) is the
lemma whose replacement (b) is about.

*Surviving verbatim once restated uniformly*: the bracket step (§1 `cfive_commP_mem_succ`, which
subsumes `cfour_commP_mem_three` and `cfour_commP_mem_four`) and the annihilator argument (§3,
which subsumes `cfour_commutator_lambdaTwo` as `cfive_commutator_four_of_two`).

*Surviving with a side condition*: bimultiplicativity.  §2 is the general statement: in
`Q_{k+2}`, a bracket whose slot is a `γ_k`-image lands in the central layer, so bimultiplicativity
survives **against a slot `k` layers down**.  Wave 69's `cfour_commP_left_hom` is the case
`k = 2`; the class-five statement is the case `k = 3` (`cfive_commP_left_hom_five`), and that is
exactly the `λ`-image side condition.

*Not surviving*: two class-four lemmas, both replaced in §5.  `cfour_pow_four_mem_zLayer` stops,
because fourth powers are only three layers down at class five
(`cfive_pow_four_mem_lambdaThree`) and it is **eighth** powers that are central
(`cfive_pow_eight_mem_zLayer`); and `cfour_commP_mem_zLayer_left` stops, because a bracket with a
`Y`-slot is likewise only three layers down (`cfive_commP_lambdaTwo_mem_lambdaThree`).  Nothing
in this third group is asserted to be **false** one class up.  What is committed is only that the
wave-69 proof delivers nothing there; see the scope note below.

## Scope

No class-five instance of `SqClassClearingSupply` is discharged here, and nothing is refuted.  In
particular this file does **not** claim that `Y` fails to be abelian in `Q₅`: that would need a
witness in `D_sq h`, and none is committed.  What is committed is that the class-four *proof* of
abelianness is unavailable one class up, since it delivers `⁅γ₂, γ₂⁆ ≤ γ₄` and `γ₄`-membership
does not imply `γ₅`-membership, together
with the weaker statement that does survive (`cfive_commP_lambdaTwo_mem_zLayer`).  (`γ₄ ⊄ γ₅` as
a *strictness* claim is not committed and over these binders is false: for the trivial group all
layers coincide, `twoCentralSeries` being antitone and nothing making it strict.)  Likewise
`cfour_pow_four_inv` (`p⁴` an involution) is not restated at class five in any form: it is `p⁸ ∈ γ₄`,
which says nothing about `γ₅`.

Lane W70-FIVE.  New file; no edits to existing files.  Prefix `cfive`.
-/

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The bracket step, at every layer

Wave 69 needed `cfour_commP_mem_three` and `cfour_commP_mem_four` separately, one per index.  The
statement is uniform, including at the junk index `k = 0` where `γ₁ = ⊤`. -/

section BracketStep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A bracket against `γ_k` sinks to `γ_{k+1}`**, at every `k`.  Wave 69's
`cfour_commP_mem_three` and `cfour_commP_mem_four` are the cases `k = 2` and `k = 3`. -/
theorem cfive_commP_mem_succ {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) (g : G) :
    commP v g ∈ twoCentralSeries G (k + 1) := by
  match k with
  | 0 => exact Subgroup.mem_top _
  | (k + 1) =>
    rw [twoCentralSeries_succ (G := G) (by omega)]
    exact commP_mem_twoCentralSucc hv g

end BracketStep

/-! ## §2 The layer calculus in `Q_{k+2}`, and the `λ`-image side condition

Wave 69's ⭐ `cfour_commP_left_hom` says that bimultiplicativity survives in `Q₄` against a
`Y`-slot, and reads that as "the class-four degradation of wave 68's calculus".  The uniform
statement shows what is really going on: what a slot must be is **two layers above the bottom of
the quotient**, and at `Q₄` that happens to be `γ₂`.  At `Q₅` it is `γ₃`, so the class-five form of
`cfour_commP_left_hom` carries a `λ`-image side condition and the argument no longer runs on a
`γ₂`-slot.  Whether a `γ₂`-slot would in fact do at `Q₅` is not decided here. -/

section LayerCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- A bracket whose left slot is a `γ_k`-image lands in the central layer of `Q_{k+2}`.  The case
`k = 2` is `cfour_commP_mem_zLayer_left`. -/
theorem cfive_commP_mem_zLayer_left {y : levelQuot G (k + 2)} (hy : y ∈ lambdaImage G k (k + 2))
    (q : levelQuot G (k + 2)) : commP y q ∈ zLayer G (k + 1) := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := levelMk_surjective G (k + 2) q
  exact ⟨commP v b, cfive_commP_mem_succ hv b, by simp only [commP, map_mul, map_inv]⟩

/-- The right-slot version. -/
theorem cfive_commP_mem_zLayer_right (q : levelQuot G (k + 2)) {y : levelQuot G (k + 2)}
    (hy : y ∈ lambdaImage G k (k + 2)) : commP q y ∈ zLayer G (k + 1) := by
  have h : commP q y = (commP y q)⁻¹ := by simp only [commP]; group
  rw [h]
  exact (zLayer G (k + 1)).inv_mem (cfive_commP_mem_zLayer_left hy q)

/-- A central-layer element kills a bracket from the left. -/
theorem cfive_commP_zLayer_left {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (q : levelQuot G (k + 2)) : commP z q = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq

/-- ⭐ **Bimultiplicativity against a slot `k` layers down**, in `Q_{k+2}`: the correction term of
`cfour_commP_mul_left` is then a bracket with a central element.  Wave 69's
`cfour_commP_left_hom` is the case `k = 2`. -/
theorem cfive_commP_left_hom (p q : levelQuot G (k + 2)) {y : levelQuot G (k + 2)}
    (hy : y ∈ lambdaImage G k (k + 2)) : commP (p * q) y = commP p y * commP q y := by
  rw [cfour_commP_mul_left,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_right p hy) q, mul_one]

/-- ⭐ **Bimultiplicativity against a slot `k` layers down**, right-hand version. -/
theorem cfive_commP_right_hom {y : levelQuot G (k + 2)} (hy : y ∈ lambdaImage G k (k + 2))
    (q r : levelQuot G (k + 2)) : commP y (q * r) = commP y r * commP y q := by
  rw [cfour_commP_mul_right,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hy q) r, mul_one]

end LayerCalculus

/-! ## §3 `⁅γ_k, γ₂⁆ ≤ γ_{k+2}`

The one place in the file where the topology is used, and it is wave 69's argument with `2`
replaced by `k` throughout.  The point of doing it uniformly is that `⁅γ₂, γ₃⁆ ≤ γ₅` then costs
nothing beyond naming it. -/

section AnnihilatorGeneral

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The set of `g` whose bracket against a fixed `γ_k`-element `v` has already died two layers
down.  It is a subgroup because the correction term of `cfour_commP_mul_right` is a double bracket
against `γ_k`, and closed as a preimage of the closed `γ_{k+2}`. -/
def cfiveAnnih {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) : Subgroup G where
  carrier := {g : G | commP v g ∈ twoCentralSeries G (k + 2)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, cfour_comm_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [cfour_commP_mul_right]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb ha)
      (cfive_commP_mem_succ (cfive_commP_mem_succ hv a) b)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hid := cfour_commP_mul_right v a a⁻¹
    rw [mul_inv_cancel, cfour_comm_one] at hid
    have hsplit : commP v a⁻¹ = (commP v a * commP (commP v a) a⁻¹)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, ← hid])
    rw [hsplit]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ha
      (cfive_commP_mem_succ (cfive_commP_mem_succ hv a) a⁻¹))

theorem cfive_mem_annih {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) {g : G} :
    g ∈ cfiveAnnih hv ↔ commP v g ∈ twoCentralSeries G (k + 2) := Iff.rfl

/-- The annihilator is closed, being the preimage of the closed `γ_{k+2}` under the continuous
map `g ↦ commP v g`. -/
theorem cfive_isClosed_annih {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) :
    IsClosed ((cfiveAnnih hv : Subgroup G) : Set G) := by
  have hset : ((cfiveAnnih hv : Subgroup G) : Set G)
      = (fun g : G => commP v g) ⁻¹' ((twoCentralSeries G (k + 2) : Subgroup G) : Set G) := rfl
  rw [hset]
  refine IsClosed.preimage ?_ (isClosed_twoCentralSeries G (k + 2))
  simp only [commP]
  fun_prop

/-- The bracket against a fixed `γ_k`-element, as a homomorphism `G →* Q_{k+2}`.  Its values lie
in the central layer, which is what makes it multiplicative and what makes it kill commutators. -/
def cfiveCommHom {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) : G →* levelQuot G (k + 2) :=
  MonoidHom.mk' (fun g => levelMk G (k + 2) (commP v g)) (by
    intro a b
    have hz : levelMk G (k + 2) (commP v a) ∈ zLayer G (k + 1) :=
      ⟨commP v a, cfive_commP_mem_succ hv a, rfl⟩
    have h1 : levelMk G (k + 2) (commP (commP v a) b) = 1 :=
      (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp
        (cfive_commP_mem_succ (cfive_commP_mem_succ hv a) b)
    rw [cfour_commP_mul_right, map_mul, map_mul, h1, mul_one]
    exact (zLayer_commute hz (levelMk G (k + 2) (commP v b))).symm.eq)

theorem cfive_commHom_apply {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) (g : G) :
    cfiveCommHom hv g = levelMk G (k + 2) (commP v g) := rfl

theorem cfive_commHom_mem {k : ℕ} {v : G} (hv : v ∈ twoCentralSeries G k) (g : G) :
    cfiveCommHom hv g ∈ zLayer G (k + 1) :=
  ⟨commP v g, cfive_commP_mem_succ hv g, rfl⟩

/-- ⭐⭐ **`⁅γ_k, γ₂⁆ ≤ γ_{k+2}`**, at every `k`.  The annihilator of a `γ_k`-element is a closed
subgroup containing every square and every commutator, hence contains `twoCentralSucc ⊤ = γ₂`. -/
theorem cfive_commutator_lambdaTwo {k : ℕ} {v w : G} (hv : v ∈ twoCentralSeries G k)
    (hw : w ∈ twoCentralSeries G 2) : commP v w ∈ twoCentralSeries G (k + 2) := by
  have hsub : twoCentralSeries G 2 ≤ cfiveAnnih hv := by
    rw [cfour_lambda_two, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (cfive_isClosed_annih hv)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, -, rfl⟩
      show commP v (g ^ 2) ∈ twoCentralSeries G (k + 2)
      rw [pow_two, cfour_commP_mul_right]
      have h3 := cfive_commP_mem_succ hv g
      have hsq : commP v g * commP v g ∈ twoCentralSeries G (k + 2) := by
        rw [← pow_two]
        exact sq_mem_twoCentralSeries_succ (G := G) h3
      exact Subgroup.mul_mem _ hsq (cfive_commP_mem_succ h3 g)
    · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [commutatorElement_def, cfive_mem_annih,
        lim_mem_twoCentralSeries_iff_levelMk (k + 2) (commP v (a * b * a⁻¹ * b⁻¹))]
      have hval : levelMk G (k + 2) (commP v (a * b * a⁻¹ * b⁻¹))
          = cfiveCommHom hv (a * b * a⁻¹ * b⁻¹) := rfl
      rw [hval, map_mul, map_mul, map_mul, map_inv, map_inv,
        (zLayer_commute (cfive_commHom_mem hv a) (cfiveCommHom hv b)).eq]
      group
  exact hsub hw

/-- The same with the two slots exchanged. -/
theorem cfive_commutator_lambdaTwo_swap {k : ℕ} {v w : G} (hv : v ∈ twoCentralSeries G k)
    (hw : w ∈ twoCentralSeries G 2) : commP w v ∈ twoCentralSeries G (k + 2) := by
  have h : commP w v = (commP v w)⁻¹ := by simp only [commP]; group
  rw [h]
  exact Subgroup.inv_mem _ (cfive_commutator_lambdaTwo hv hw)

/-- ⭐⭐ **`⁅γ₂, γ₃⁆ ≤ γ₅`**: the class-five prerequisite named in this file's header, as the
instance `k = 3` of `cfive_commutator_lambdaTwo`.  (Not wave 69's; see the attribution note in
the header.) -/
theorem cfive_commutator_two_three {v w : G} (hv : v ∈ twoCentralSeries G 3)
    (hw : w ∈ twoCentralSeries G 2) : commP v w ∈ twoCentralSeries G 5 :=
  cfive_commutator_lambdaTwo hv hw

/-- Wave 69's ⭐ `cfour_commutator_lambdaTwo` as the instance `k = 2`, re-derived: the check that
the uniform argument did not lose the class-four case. -/
theorem cfive_commutator_four_of_two {v w : G} (hv : v ∈ twoCentralSeries G 2)
    (hw : w ∈ twoCentralSeries G 2) : commP v w ∈ twoCentralSeries G 4 :=
  cfive_commutator_lambdaTwo hv hw

end AnnihilatorGeneral

/-! ## §4 The class-five bookkeeping layer

`Y = lambdaImage G 2 5` is not *known* to be abelian in `Q₅` (the scope note in the module header
records that no witness is committed either way), so wave 69's §3 ("the relator may be reordered
at will") has no class-five analogue available.  What does survive is one step weaker and still
linear: `⁅Y, Y⁆` lands in `zLayer G 4`, which is central in `Q₅` and of exponent two, and the
bracket is bimultiplicative on `Y × Y`.  A class-five run reorders freely and collects an
`F₂`-bilinear correction. -/

section BookkeepingFive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **`⁅Y, Y⁆` lands in the central layer of `Q₅`**: the class-five residue of
`cfour_commutator_lambdaTwo`, which upstairs delivers `γ₄` and so says nothing modulo `γ₅` on its
own.  Read in `Q₅` it says the commutator subgroup of `Y` sits inside `Z₄`. -/
theorem cfive_commP_lambdaTwo_mem_zLayer {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) : commP y y' ∈ zLayer G 4 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  exact ⟨commP v v', cfive_commutator_lambdaTwo hv hv', by simp only [commP, map_mul, map_inv]⟩

/-- ⭐ **`Y` is nilpotent of class at most two in `Q₅`**: its commutators are central.  This is
the statement that replaces `cfour_commP_lambdaTwo`.  The bound is not claimed to be sharp:
nothing here rules out `Y` being abelian, which would be class one. -/
theorem cfive_commP_lambdaTwo_central {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) (p : levelQuot G 5) : Commute (commP y y') p :=
  zLayer_commute (cfive_commP_lambdaTwo_mem_zLayer hy hy') p

/-- ⭐ The commutators of `Y` have order dividing two, so the corrections collected while
reordering are `F₂`-valued. -/
theorem cfive_commP_lambdaTwo_sq {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) : commP y y' ^ 2 = 1 :=
  zLayer_sq G (cfive_commP_lambdaTwo_mem_zLayer hy hy')

/-- **The reordering identity itself**, which is free: swapping two factors costs exactly their
bracket.  All the class-five content is in what that bracket is, which is the three statements
above and the two below. -/
theorem cfive_swap_free {Q : Type*} [Group Q] (y y' : Q) : y * y' = y' * y * commP y y' := by
  simp only [commP]
  group

/-- ⭐ **The bracket is bimultiplicative on `Y × Y` in `Q₅`**, left slot: the correction term of
`cfour_commP_mul_left` is a bracket with the central element `commP y y''`. -/
theorem cfive_commP_lambdaTwo_hom_left {y y'' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy'' : y'' ∈ lambdaImage G 2 5) (q : levelQuot G 5) :
    commP (y * q) y'' = commP y y'' * commP q y'' := by
  rw [cfour_commP_mul_left,
    bridge_comm_of_commute (cfive_commP_lambdaTwo_central hy hy'' q).eq, mul_one]

/-- ⭐ **The bracket is bimultiplicative on `Y × Y` in `Q₅`**, right slot. -/
theorem cfive_commP_lambdaTwo_hom_right {y y'' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy'' : y'' ∈ lambdaImage G 2 5) (r : levelQuot G 5) :
    commP y (y'' * r) = commP y r * commP y y'' := by
  rw [cfour_commP_mul_right,
    bridge_comm_of_commute (cfive_commP_lambdaTwo_central hy hy'' r).eq, mul_one]

end BookkeepingFive

/-! ## §5 Where class four had a collapse and class five does not

Two entries of wave 69's calculus have no class-five reading by the wave-69 argument, and it is
worth having their replacements committed rather than described, because both are easy to
misremember.  The two are `cfour_pow_four_mem_zLayer` and `cfour_commP_mem_zLayer_left`; this
section carries three replacement statements, two for the first and one for the second.  Neither
class-four lemma is asserted to be false in `Q₅`; each is simply about `Q₄`.

The fourth power is the important one.  `cfour_pow_four_mem_zLayer` puts `p⁴` in the central layer
of `Q₄`; one class up `p⁴` is only three layers down, and it is `p⁸` that is central.  In
particular `cfour_pow_four_inv` (`p⁴` an involution, which is `p⁸ ∈ γ₄`) has no class-five reading
at all, so the `((b²)²)⁻¹` factor of `relBase_sqWord_free` may **not** be simplified to `b⁴` in
`Q₅`.  That is the precise sense in which the class-five relator is larger than the class-four
one. -/

section Degradation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Fourth powers in `Q₅` lie three layers down**, where at class four they were central.  This
is where `cfour_pow_four_mem_zLayer` stops. -/
theorem cfive_pow_four_mem_lambdaThree (p : levelQuot G 5) : p ^ 4 ∈ lambdaImage G 3 5 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 5 p
  refine ⟨a ^ 4, ?_, by rw [map_pow]⟩
  have h := pow_two_pow_mem_twoCentralSeries_succ (G := G) a 2
  rwa [show (2 : ℕ) ^ 2 = 4 from by norm_num] at h

/-- **Eighth powers are what is central at class five.** -/
theorem cfive_pow_eight_mem_zLayer (p : levelQuot G 5) : p ^ 8 ∈ zLayer G 4 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 5 p
  refine ⟨a ^ 8, ?_, by rw [map_pow]⟩
  have h := pow_two_pow_mem_twoCentralSeries_succ (G := G) a 3
  rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at h

/-- **A bracket with a `Y`-slot in `Q₅` lies three layers down**, where at class four it was
central.  This is where `cfour_commP_mem_zLayer_left` stops, and it is why the class-five
bimultiplicativity statement asks for a `γ₃`-slot instead. -/
theorem cfive_commP_lambdaTwo_mem_lambdaThree {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) : commP y q ∈ lambdaImage G 3 5 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := levelMk_surjective G 5 q
  exact ⟨commP v b, cfive_commP_mem_succ hv b, by simp only [commP, map_mul, map_inv]⟩

/-- ⭐ **The class-five form of `cfour_commP_left_hom`**: bimultiplicativity survives against a
`γ₃`-image slot.  This is the `λ`-image side condition, and it is the case `k = 3` of
`cfive_commP_left_hom`.  The class-four form's `γ₂`-slot is not available to this argument one
class up; it is not shown to fail. -/
theorem cfive_commP_left_hom_five (p q : levelQuot G 5) {y : levelQuot G 5}
    (hy : y ∈ lambdaImage G 3 5) : commP (p * q) y = commP p y * commP q y :=
  cfive_commP_left_hom p q hy

/-- ⭐ The right-hand version of the same. -/
theorem cfive_commP_right_hom_five {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5)
    (q r : levelQuot G 5) : commP y (q * r) = commP y r * commP y q :=
  cfive_commP_right_hom hy q r

end Degradation

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms cfive_commP_mem_succ
#print axioms cfive_commP_mem_zLayer_left
#print axioms cfive_commP_mem_zLayer_right
#print axioms cfive_commP_zLayer_left
#print axioms cfive_commP_left_hom
#print axioms cfive_commP_right_hom
#print axioms cfiveAnnih
#print axioms cfive_mem_annih
#print axioms cfive_isClosed_annih
#print axioms cfiveCommHom
#print axioms cfive_commHom_apply
#print axioms cfive_commHom_mem
#print axioms cfive_commutator_lambdaTwo
#print axioms cfive_commutator_lambdaTwo_swap
#print axioms cfive_commutator_two_three
#print axioms cfive_commutator_four_of_two
#print axioms cfive_commP_lambdaTwo_mem_zLayer
#print axioms cfive_commP_lambdaTwo_central
#print axioms cfive_commP_lambdaTwo_sq
#print axioms cfive_swap_free
#print axioms cfive_commP_lambdaTwo_hom_left
#print axioms cfive_commP_lambdaTwo_hom_right
#print axioms cfive_pow_four_mem_lambdaThree
#print axioms cfive_pow_eight_mem_zLayer
#print axioms cfive_commP_lambdaTwo_mem_lambdaThree
#print axioms cfive_commP_left_hom_five
#print axioms cfive_commP_right_hom_five

end AxiomPins

end SqCore

end Dyadic

end GQ2
