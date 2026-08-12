/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFourKnob
import GQ2.Dyadic.SqCore.GradedGammaFourFive

/-!
# W72-FIVE: the row repair at `γ₃`, and the relations half of `γ₄/γ₅`

Wave 71 left the class-five layer with its knob inventory complete and its obligation stated
(`cfiveKnob_supply_of_reach`), and named two next steps.  This file is those two steps.

Throughout `Q₅ = levelQuot G 5`, `Y = lambdaImage G 2 5`, `T = lambdaImage G 3 5` and
`Z = zLayer G 4` is the top layer, central in `Q₅` and of exponent two.

## §1-§4 The row repair at `γ₃`

`bridge_row_image` is stated at a **free** index `m`: it produces a `γ_{m+1}`-element with any
prescribed rows in `2^m ℤ₂ × 2^m ℤ₂`.  Wave 70 used it at `m = 2`, where the repair factor is
central in `Q₄`.  One class up the correction itself lives in `γ₃`, and the repair factor must be
central in `Q₅`, that is it must come from `γ₄`; so the index moves to `m = 3` and the repairable
rows are `8ℤ₂`.

⭐⭐ `cfiveRow_repair` is the repair, in the sharp form "differs by a `Z`-factor";
`cfiveRow_repair_knob` is wave 70's knob form.  The step that fails at `m = 2` is invisibility,
and `cfiveRow_comm_lambdaThree_dress` writes the failure out: a `γ₃`-valued repair factor `t`
moves the knob by `commP t q`, which lies in `Z` and is supplied with no reason to vanish.

⭐⭐ `cfiveRow_relator_blind`: the class-five relator does not see a `Z`-valued correction of any
slot, so the repair is free at the level of the relator and not only of the knob.  Hence
⭐⭐ `cfiveRow_supply_of_reachable`: `cfiveKnob_supply_of_reach`'s "exactly row-trivial
correction" may be weakened to "correction with rows in `8ℤ₂`" (`CfiveRowReachable`).

§3 records that the corrections that actually arise need no repair at all: a square of an exactly
row-trivial `γ₂`-element and a bracket with a `γ₂`-slot are exactly row-trivial `γ₃`-corrections
on the nose (`cfiveRow_sq_admissible`, `cfiveRow_comm_admissible`).

## §5 The pairing, with both ingredients re-established

Wave 71 removed a square from the `x₁`-slot knob by pairing two knobs
(`cfourKnob_sq_knob_pair`), and recorded that the pairing needs a Hall-Petrescu step and "a
`Y`-element has trivial fourth power" per class.  Both change here.

* ⭐ `cfiveSpan_commP_sq_left` carries a hypothesis `y ∈ Y` that wave 70's
  `gThreeFour_commP_sq_left` does not: the reordering needs `commP (commP y q) y` central, and at
  `Q₅` an iterated bracket is central only when its innermost slot is a `Y`-element.
* ⭐ the fourth-power cancellation is carried by `T`, not by `Y`
  (`cfiveSpan_pow_four_lambdaThree`).  A `Y`-element's square only reaches `T` here, so what a
  `Y`-element has is a trivial **eighth** power (`cfiveSpan_pow_eight_lambdaTwo`), its fourth
  power lying in `Z` (`cfiveSpan_pow_four_lambdaTwo_mem`).  Nothing here says that fourth power
  is nontrivial.

⭐⭐ `cfiveSpan_sq_knob_pair` is the pairing, and `cfiveSpan_pair_correction` exhibits it as the
single `T`-correction `y ^ 2 * commP y q`, by `cfiveSpan_dress_two_mul`.

## §6-§7 The relations half of the graded decomposition

`gFourFive_zLayer_le_gen` gives generation only, and its two families are indexed by the opaque
`T`.  Both maps `t ↦ t ^ 2` and `t ↦ commP t q` are **homomorphisms** on `T`, so each family need
only be checked on generators of `T`, which are the squares and brackets of `Y`; on a square
generator the check is §5's Hall-Petrescu step.  That is ⭐⭐⭐ `cfiveSpan_zLayer_le_rel`, three
families indexed by `Y` with free `Q₅`-slots.  Running the same reduction once more, from `Y` to
its generators, gives ⭐⭐⭐ `cfiveSpan_zLayer_le_gens`: six families indexed by `Q₅` alone, the
last of them the fourfold bracket, which is exactly what `gFourFive_jacobi_iter` is a relation on
(`cfiveSpan_jacobi_iter_rewrite` solves that relation for one member).  `cfiveSpan_lambdaImage_le`
is `gFourFive_zLayer_le_gen` with the target level freed, which is what lets the reduction be run
at `T` inside `Q₅`.

`cfiveSpan_zLayer_le_dsq` and `cfiveSpan_zLayer_le_gens_dsq` are the two forms at `D_sq h`, where
`Q₅` is discrete and the closedness side conditions are free.

## Scope

No instance of `SqClassClearingSupply` is discharged here, at any class, and nothing is refuted.
The relations half is a statement about what a subgroup must contain to contain the layer; it is
not a claim that the knob subgroup contains any of the six families.

Lane W72-FIVE.  New file; no edits to existing files.  Prefixes `cfiveRow` / `cfiveSpan`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 A `Z`-valued correction is invisible

The three facts a repair factor has to satisfy to cost nothing: it is invisible to a bracket,
to a square, and hence to the whole relator. -/

section Blind

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A central right factor in the near slot of a bracket is invisible.**  The class-four
statement is `cfourId_comm_zLayer_dress`; the class-five proof is the same two cancellations,
taken from the class-five calculus. -/
theorem cfiveRow_comm_zLayer_dress {z : levelQuot G 5} (hz : z ∈ zLayer G 4)
    (p q : levelQuot G 5) : commP (p * z) q = commP p q := by
  rw [cfour_commP_mul_left, gFourFive_commP_zLayer_right hz (commP p q),
    cfive_commP_zLayer_left hz q, mul_one, mul_one]

/-- **A `T`-valued right factor in the near slot costs exactly one bracket.**  This is the
class-five statement of what a `γ₃`-valued repair factor does, and the contrast with
`cfiveRow_comm_zLayer_dress` is the whole content of §2's arithmetic: at `Q₅` a `γ₃`-element is
not central, so its bracket against the far slot survives. -/
theorem cfiveRow_comm_lambdaThree_dress {t : levelQuot G 5} (ht : t ∈ lambdaImage G 3 5)
    (p q : levelQuot G 5) : commP (p * t) q = commP p q * commP t q := by
  rw [cfour_commP_mul_left,
    gFourFive_commP_vanish' (gFourFive_commP_mem_lambdaTwo p q) ht, mul_one]

/-- **A pointwise congruence for the handle word**, in any group: the word depends on its two
tuples only through the `h` brackets `⁅u j, v j⁆`.  Stated with the hypothesis pointwise, per
wave 71's standing correction. -/
theorem cfiveRow_handleWord_congr {Q : Type*} [Group Q] {n : ℕ} (u v u' v' : Fin n → Q)
    (hb : ∀ i, commP (u' i) (v' i) = commP (u i) (v i)) :
    handleWord u' v' = handleWord u v := by
  simp only [handleWord]
  congr 1
  exact List.map_congr_left fun i _ => hb i

/-- ⭐⭐ **The class-five relator is blind to a `Z`-valued correction of every slot.**  Each of
the five factors of `gFourFive_sqRelWord` is a bracket, a square, a fourth power or a
conjugation, and a central factor of exponent two survives none of them.  This is what makes the
row repair of §2 free: the repaired correction has the same relator, not merely the same knob. -/
theorem cfiveRow_relator_blind {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 5)
    {z : Fin (sqRank n) → levelQuot G 5} (hz : ∀ i, z i ∈ zLayer G 4)
    (hm : ∀ i, m' i = m i * z i) : sqRelWord m' = sqRelWord m := by
  have hA : commP (m' 0) (m' 1) = commP (m 0) (m 1) := by
    rw [hm 0, hm 1, cfiveRow_comm_zLayer_dress (hz 0), gFourFive_drop_right _ _ (hz 1)]
  have hB : ((m' 1 ^ 2) ^ 2)⁻¹ = ((m 1 ^ 2) ^ 2)⁻¹ := by
    rw [hm 1, gFourFive_sq_zLayer_dress (hz 1)]
  have hC : m' 2 ^ 2 = m 2 ^ 2 := by rw [hm 2, gFourFive_sq_zLayer_dress (hz 2)]
  have hconj : conjP (m' 2) (m' 0) = conjP (m 2) (m 0) * z 2 := by
    rw [gFourFive_conj_eq (m' 2) (m' 0), hm 2, hm 0, cfiveRow_comm_zLayer_dress (hz 2),
      gFourFive_drop_right _ _ (hz 0), gFourFive_conj_eq (m 2) (m 0), mul_assoc,
      gFourFive_zLayer_comm (hz 2) (commP (m 2) (m 0)), ← mul_assoc]
  have hD : commP (m' 2) (conjP (m' 2) (m' 0)) = commP (m 2) (conjP (m 2) (m 0)) := by
    rw [hconj, hm 2, cfiveRow_comm_zLayer_dress (hz 2), gFourFive_drop_right _ _ (hz 2)]
  have hE : handleWord (fun i => m' (sqHandleIdxU i)) (fun i => m' (sqHandleIdxV i))
      = handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) := by
    refine cfiveRow_handleWord_congr _ _ _ _ fun i => ?_
    rw [hm (sqHandleIdxU i), hm (sqHandleIdxV i),
      cfiveRow_comm_zLayer_dress (hz (sqHandleIdxU i)),
      gFourFive_drop_right _ _ (hz (sqHandleIdxV i))]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hA, hB, hC, hD, hE]

end Blind

/-! ## §2 The row repair at `γ₃`

Wave 68's `bridge_row_image` is stated at a free index `m`: it produces a `γ_{m+1}`-element with
any prescribed rows in `2^m ℤ₂ × 2^m ℤ₂`.  Wave 70 used it at `m = 2`, where the repair factor
lands in `γ₃` and is therefore central in `Q₄`.  One class up the correction itself lives in
`γ₃`, and the repair factor must be central in `Q₅`, that is it must come from `γ₄`, so the index
moves to `m = 3` and the repairable rows are `8ℤ₂` rather than `4ℤ₂`.

The step that fails at `m = 2` is invisibility, and `cfiveRow_comm_lambdaThree_dress` is the
failure written out: a `γ₃`-valued repair factor `t` changes the knob of a correction `c` by the
bracket `commP t q`, which lies in `Z` and is not supplied with any reason to vanish. -/

section RowRepair

variable {h : ℕ}

/-- ⭐⭐ **Rows in `8ℤ₂` are repairable inside `γ₃`, by a factor that is central in `Q₅`.**
`bridge_row_image` at `m = 3` supplies a `γ₄`-element with any prescribed rows in
`8ℤ₂ × 8ℤ₂`, and `γ₄ ≤ γ₃`, so a `γ₃`-correction whose two rows already lie in `8ℤ₂` may be
replaced by one with **exactly** trivial rows differing from it by a `Z`-factor.  This is wave
70's `cfourId_row_repair` one class up, with `4ℤ₂` replaced by `8ℤ₂` for the reason recorded in
the section docstring. -/
theorem cfiveRow_repair (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    {c : (DSq h : Type)} (hc : c ∈ twoCentralSeries (DSq h : Type) 3) {a b : ℤ_[2]}
    (hla : toAdd (nuLam h c) = 8 * a) (hnb : toAdd (nu' c) = 8 * b) :
    ∃ c' ∈ twoCentralSeries (DSq h : Type) 3, nuLam h c' = 1 ∧ nu' c' = 1 ∧
      ∃ z ∈ zLayer (DSq h : Type) 4,
        levelMk (DSq h : Type) 5 c' = levelMk (DSq h : Type) 5 c * z := by
  obtain ⟨v, hv, hvl, hvn⟩ := bridge_row_image nu' hsigma hx0 3 (-a) (-b)
  have height : ((2 : ℤ_[2]) ^ 3) = 8 := by norm_num
  refine ⟨c * v, (twoCentralSeries (DSq h : Type) 3).mul_mem hc
      (twoCentralSeries_antitone (G := (DSq h : Type)) (by norm_num) hv), ?_, ?_,
    levelMk (DSq h : Type) 5 v, ⟨v, hv, rfl⟩, by rw [map_mul]⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, toAdd_mul, hla, hvl, height, toAdd_one]
    ring
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, toAdd_mul, hnb, hvn, height, toAdd_one]
    ring

/-- **The row repair in the knob form of `cfourId_row_repair`**: the repaired correction has the
same bracket against every slot of `Q₅` and the same square.  Both are read off the `Z`-factor
by §1. -/
theorem cfiveRow_repair_knob (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    {c : (DSq h : Type)} (hc : c ∈ twoCentralSeries (DSq h : Type) 3) {a b : ℤ_[2]}
    (hla : toAdd (nuLam h c) = 8 * a) (hnb : toAdd (nu' c) = 8 * b) :
    ∃ c' ∈ twoCentralSeries (DSq h : Type) 3, nuLam h c' = 1 ∧ nu' c' = 1 ∧
      (∀ q : levelQuot (DSq h : Type) 5,
          commP (levelMk (DSq h : Type) 5 c') q = commP (levelMk (DSq h : Type) 5 c) q) ∧
        levelMk (DSq h : Type) 5 c' ^ 2 = levelMk (DSq h : Type) 5 c ^ 2 := by
  obtain ⟨c', hc', hl, hn, z, hz, hzq⟩ := cfiveRow_repair nu' hsigma hx0 hc hla hnb
  exact ⟨c', hc', hl, hn, fun q => by rw [hzq, cfiveRow_comm_zLayer_dress hz],
    by rw [hzq, gFourFive_sq_zLayer_dress hz]⟩

end RowRepair

/-! ## §3 Corrections that need no repair at all

Wave 71's class-four lane recorded that the codimension condition of a row repair is not the
binding constraint on the corrections that actually arise, because those are exactly row-trivial
on the nose.  The same holds one class up, and here are the two families, at `γ₃`. -/

section Admissible

variable {h : ℕ}

/-- A square of a `γ₂`-element is a `γ₃`-element. -/
theorem cfiveRow_sq_mem {d : (DSq h : Type)} (hd : d ∈ twoCentralSeries (DSq h : Type) 2) :
    d ^ 2 ∈ twoCentralSeries (DSq h : Type) 3 :=
  sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) hd

/-- ⭐ **The square of an exactly row-trivial `γ₂`-element is an admissible `γ₃`-correction**,
with no repair.  This is `cfourKnob_sq_admissible` one layer down in the tower. -/
theorem cfiveRow_sq_admissible (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {d : (DSq h : Type)} (hd : d ∈ twoCentralSeries (DSq h : Type) 2) (hl : nuLam h d = 1)
    (hn : nu' d = 1) :
    d ^ 2 ∈ twoCentralSeries (DSq h : Type) 3 ∧ nuLam h (d ^ 2) = 1 ∧ nu' (d ^ 2) = 1 :=
  ⟨cfiveRow_sq_mem hd, cfourKnob_sq_nuLam hl, cfourKnob_sq_nu nu' hn⟩

/-- A bracket with a `γ₂`-slot is a `γ₃`-element: this is `⁅G, γ₂⁆ ≤ γ₃`. -/
theorem cfiveRow_comm_mem (a : (DSq h : Type)) {b : (DSq h : Type)}
    (hb : b ∈ twoCentralSeries (DSq h : Type) 2) : commP a b ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfive_commutator_lambdaTwo (Subgroup.mem_top a) hb

/-- ⭐ **A bracket with a `γ₂`-slot is an admissible `γ₃`-correction**, with no repair: it lies in
`γ₃` and both rows kill every commutator (`cfourKnob_comm_row`).  This is the class-five analogue
of `cfourKnob_comm_admissible`, and it is what makes `cfiveKnob_supply_of_reach` consumable
without any row arithmetic at all. -/
theorem cfiveRow_comm_admissible (nu' : ContinuousMonoidHom (DSq h : Type)
    (Multiplicative ℤ_[2])) (a : (DSq h : Type)) {b : (DSq h : Type)}
    (hb : b ∈ twoCentralSeries (DSq h : Type) 2) :
    commP a b ∈ twoCentralSeries (DSq h : Type) 3 ∧ nuLam h (commP a b) = 1 ∧
      nu' (commP a b) = 1 :=
  ⟨cfiveRow_comm_mem a hb, cfourKnob_comm_row _ a b, cfourKnob_comm_row nu' a b⟩

/-- A product of two exactly row-trivial `γ₃`-elements is again one. -/
theorem cfiveRow_mul_admissible (nu' : ContinuousMonoidHom (DSq h : Type)
    (Multiplicative ℤ_[2])) {c₁ c₂ : (DSq h : Type)}
    (h₁ : c₁ ∈ twoCentralSeries (DSq h : Type) 3) (h₂ : c₂ ∈ twoCentralSeries (DSq h : Type) 3)
    (hl₁ : nuLam h c₁ = 1) (hl₂ : nuLam h c₂ = 1) (hn₁ : nu' c₁ = 1) (hn₂ : nu' c₂ = 1) :
    c₁ * c₂ ∈ twoCentralSeries (DSq h : Type) 3 ∧ nuLam h (c₁ * c₂) = 1 ∧ nu' (c₁ * c₂) = 1 :=
  ⟨Subgroup.mul_mem _ h₁ h₂, by rw [map_mul, hl₁, hl₂, one_mul],
    by rw [map_mul, hn₁, hn₂, one_mul]⟩

end Admissible

/-! ## §4 The weakened obligation

`cfiveKnob_supply_of_reach` asks its correction to be **exactly** row-trivial.  With §2 and §1
that clause can be weakened to rows in `8ℤ₂`: the repair moves each slot by a `Z`-element, and
by `cfiveRow_relator_blind` the relator does not see it. -/

section Weakened

variable {h : ℕ}

/-- **The class-five reachability target with `8ℤ₂` rows.**  This is
`cfiveKnob_supply_of_reach`'s hypothesis with "exactly row-trivial correction" weakened to
"correction whose two rows lie in `8ℤ₂`".  It is the weakest replacement the row repair of §2
supports, and `cfiveRow_supply_of_reachable` commits the implication. -/
def CfiveRowReachable (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ a d : Fin (sqRank h) → (DSq h : Type),
        (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
          SqModTwoIndep (sqArbFrame h nu' j a) ∧
            (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 3) ∧
              (∀ i, ∃ α : ℤ_[2], toAdd (nuLam h (d i)) = 8 * α) ∧
                (∀ i, ∃ β : ℤ_[2], toAdd (nu' (d i)) = 8 * β) ∧
                  sqRelWord (fun i => levelMk (DSq h : Type) 5
                      (sqArbFrame h nu' j a i * d i)) = 1

/-- ⭐⭐ **The weakened obligation still supplies class five.**  Repair each slot's correction by
§2; the repair multiplies the slot by a `Z`-element, which the relator does not see
(`cfiveRow_relator_blind`), so the repaired tuple satisfies `cfiveKnob_supply_of_reach`
verbatim. -/
theorem cfiveRow_supply_of_reachable (H : CfiveRowReachable h) : SqClassClearingSupply h 5 := by
  refine cfiveKnob_supply_of_reach ?_
  intro nu' j hs hx
  obtain ⟨a, d, hal, han, hai, hd3, hrl, hrn, hrel⟩ := H nu' j hs hx
  choose α hα using hrl
  choose β hβ using hrn
  choose c' hc'3 hc'l hc'n z hz hzq using
    fun i => cfiveRow_repair nu' hs hx (hd3 i) (hα i) (hβ i)
  refine ⟨a, c', hal, han, hai, hc'3, hc'l, hc'n, ?_⟩
  rw [cfiveRow_relator_blind
    (fun i => levelMk (DSq h : Type) 5 (sqArbFrame h nu' j a i * d i)) _ hz
    (fun i => by rw [map_mul, map_mul, hzq i, mul_assoc])]
  exact hrel

end Weakened

/-! ## §5 The two ingredients of the pairing, re-established at `γ₄/γ₅`

Wave 71 removed a square from the `x₁`-slot knob by pairing two knobs
(`cfourKnob_sq_knob_pair`) rather than by reading one, and recorded that the pairing needs
exactly two inputs per class: a Hall-Petrescu step in the shape of `gThreeFour_commP_sq_left`,
and "a `Y`-element has trivial fourth power".  Both change one class up, and the second changes
in a way that wave 70's §5 warning predicted. -/

section Pair

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A square of a `Y`-element lies in `T`. -/
theorem cfiveSpan_sq_mem_lambdaThree {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    y ^ 2 ∈ lambdaImage G 3 5 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ (G := G) hv, by rw [map_pow]⟩

/-- ⭐ **Hall-Petrescu at `γ₄/γ₅`**: `commP (y ^ 2) q = (commP y q) ^ 2 * commP (commP y q) y`
for `y ∈ Y`.  Wave 70's `gThreeFour_commP_sq_left` holds at **arbitrary** near slot; here the
hypothesis `y ∈ Y` is doing real work, because the step that reorders the three factors needs
`commP (commP y q) y` central, and at `Q₅` an iterated bracket is central only when the innermost
slot is a `Y`-element (`cfive_commP_lambdaTwo_mem_lambdaThree` puts `commP y q` in `T`, and a
bracket with a `T`-slot lands in `Z`).  The restriction costs nothing where the statement is
used: the class-five knob corrections range over `T ≤ Y`. -/
theorem cfiveSpan_commP_sq_left {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) : commP (y ^ 2) q = (commP y q) ^ 2 * commP (commP y q) y := by
  have hz : commP (commP y q) y ∈ zLayer G 4 :=
    cfive_commP_mem_zLayer_left (cfive_commP_lambdaTwo_mem_lambdaThree hy q) y
  conv_lhs => rw [pow_two, cfour_commP_mul_left]
  rw [mul_assoc, gFourFive_zLayer_comm hz, ← mul_assoc, ← pow_two]

/-- ⭐ **A `T`-element has trivial fourth power**: its square is already a `Z`-element, and `Z`
has exponent two.  This is the cancellation the pairing runs on, and it is `T` and not `Y` that
carries it. -/
theorem cfiveSpan_pow_four_lambdaThree {t : levelQuot G 5} (ht : t ∈ lambdaImage G 3 5) :
    t ^ 2 * t ^ 2 = 1 := by
  rw [← pow_two]
  exact zLayer_sq G (gFourFive_sq_mem_zLayer ht)

/-- ⭐ **What a `Y`-element has at class five is a trivial *eighth* power.**  This is where wave
70's §5 warning bites and why the fact had to be re-established rather than transported: the
class-four proof of `cfourKnob_pow_four_lambdaTwo` puts the square of a `Y`-element in the top
layer, and one class up that square only reaches `T`.  Nothing here says a `Y`-element's fourth
power is nontrivial at class five; what is proved is that it lies in `Z`
(`cfiveSpan_pow_four_lambdaTwo_mem`), one layer short of where the class-four argument needs
it. -/
theorem cfiveSpan_pow_four_lambdaTwo_mem {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    y ^ 2 * y ^ 2 ∈ zLayer G 4 := by
  rw [← pow_two]
  exact gFourFive_sq_mem_zLayer (cfiveSpan_sq_mem_lambdaThree hy)

/-- The eighth power of a `Y`-element is trivial in `Q₅`, in the shape the pairing would need. -/
theorem cfiveSpan_pow_eight_lambdaTwo {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    (y ^ 2) ^ 2 * (y ^ 2) ^ 2 = 1 :=
  cfiveSpan_pow_four_lambdaThree (cfiveSpan_sq_mem_lambdaThree hy)

/-- ⭐⭐ **The two `x₁`-slot knobs whose squares cancel, at class five.**  The class-five
`x₁`-slot knob is `c ↦ c ^ 2 * commP c (m 2)` (`cfiveKnob_dress_two`, whose square part is the
only square in the inventory), with the correction `c` ranging over `T`.  Run it at `c = y ^ 2`
and at `c = commP y q` for `y ∈ Y` (both are `T`-elements, so both are legal corrections) and
multiply: each contributes `(commP y q) ^ 2`, and the two cancel because `commP y q` is a
`T`-element and `T`-elements have trivial fourth power.  What is left is

```text
  y⁴ · ⁅⁅y, q⁆, y⁆ · ⁅⁅y, q⁆, q⁆ ,
```

a fourth power times two pure iterated brackets, with no square attached.  This is wave 71's
`cfourKnob_sq_knob_pair` one class up; the difference is that the near slot must now come from
`Y`, which is exactly the regime where both ingredients hold. -/
theorem cfiveSpan_sq_knob_pair {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) :
    ((y ^ 2) ^ 2 * commP (y ^ 2) q) * ((commP y q) ^ 2 * commP (commP y q) q)
      = y ^ 4 * (commP (commP y q) y * commP (commP y q) q) := by
  have ht : commP y q ∈ lambdaImage G 3 5 := cfive_commP_lambdaTwo_mem_lambdaThree hy q
  have hz1 : (commP y q) ^ 2 ∈ zLayer G 4 := gFourFive_sq_mem_zLayer ht
  have hz2 : commP (commP y q) y ∈ zLayer G 4 := cfive_commP_mem_zLayer_left ht y
  have hsq : (y ^ 2 : levelQuot G 5) ^ 2 = y ^ 4 := by rw [← pow_mul]
  have hmid : commP (commP y q) y * ((commP y q) ^ 2 * commP (commP y q) q)
      = (commP y q) ^ 2 * (commP (commP y q) y * commP (commP y q) q) := by
    rw [← mul_assoc, ← gFourFive_zLayer_comm hz1 (commP (commP y q) y), mul_assoc]
  rw [hsq, cfiveSpan_commP_sq_left hy]
  simp only [mul_assoc]
  rw [hmid, ← mul_assoc ((commP y q) ^ 2), cfiveSpan_pow_four_lambdaThree ht, one_mul]

/-- A square of a product of two `T`-elements splits: the correction of `gFourFive_sq_dress` is
a bracket of a `T`-element against a `T ≤ Y`-element, and `⁅T, Y⁆` is trivial. -/
theorem cfiveSpan_sq_mul_lambdaThree {c₁ c₂ : levelQuot G 5} (hc₁ : c₁ ∈ lambdaImage G 3 5)
    (hc₂ : c₂ ∈ lambdaImage G 3 5) : (c₁ * c₂) ^ 2 = c₁ ^ 2 * c₂ ^ 2 := by
  rw [gFourFive_sq_dress hc₂, gFourFive_commP_vanish hc₂ (gFourFive_lambdaThree_le hc₁), mul_one]

/-- ⭐ **The `x₁`-slot knob is multiplicative in its correction**, so the pairing above is the
knob of the **single** `T`-element `y ^ 2 * commP y q` and costs no extra slot.  This is
`cfourKnob_dress_two_mul` one class up, run on `T` rather than on `Y`. -/
theorem cfiveSpan_dress_two_mul {c₁ c₂ : levelQuot G 5} (hc₁ : c₁ ∈ lambdaImage G 3 5)
    (hc₂ : c₂ ∈ lambdaImage G 3 5) (q : levelQuot G 5) :
    (c₁ * c₂) ^ 2 * commP (c₁ * c₂) q = c₁ ^ 2 * commP c₁ q * (c₂ ^ 2 * commP c₂ q) := by
  have hz2 : c₂ ^ 2 ∈ zLayer G 4 := gFourFive_sq_mem_zLayer hc₂
  have key : c₂ ^ 2 * (commP c₁ q * commP c₂ q) = commP c₁ q * (c₂ ^ 2 * commP c₂ q) := by
    rw [← mul_assoc, gFourFive_zLayer_comm hz2 (commP c₁ q), mul_assoc]
  rw [cfiveSpan_sq_mul_lambdaThree hc₁ hc₂, gFourFive_ad_left hc₁ c₂ q]
  simp only [mul_assoc]
  rw [key]

/-- ⭐⭐ **The pairing as a single correction.**  For `y ∈ Y` the `T`-element
`c = y ^ 2 * commP y q` has `x₁`-slot knob `y⁴ · ⁅⁅y, q⁆, y⁆ · ⁅⁅y, q⁆, q⁆`, with no square
attached.  This is the class-five form of wave 71's `cfourKnob_pair_correction`, stated at the
layer rather than at `D_sq h`. -/
theorem cfiveSpan_pair_correction {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (q : levelQuot G 5) :
    (y ^ 2 * commP y q) ^ 2 * commP (y ^ 2 * commP y q) q
      = y ^ 4 * (commP (commP y q) y * commP (commP y q) q) := by
  rw [cfiveSpan_dress_two_mul (cfiveSpan_sq_mem_lambdaThree hy)
    (cfive_commP_lambdaTwo_mem_lambdaThree hy q) q]
  exact cfiveSpan_sq_knob_pair hy q

end Pair

/-! ## §6 Jacobi as a rewriting, and the relations half of the graded decomposition

`gFourFive_zLayer_le_gen` gives the "generated by" half: `Z` is reached from the squares and the
brackets of `T`.  That is not consumable on its own, because `T` is opaque: it is the image of
`γ₃`, not a family indexed by `Q₅`.  The relations half turns the two `T`-indexed families into
three families indexed by `Y × Q₅ × Q₅`, and what pays for it is that both maps
`t ↦ t ^ 2` and `t ↦ commP t q` are **homomorphisms** on `T` (`cfiveSpan_sq_mul_lambdaThree`,
`gFourFive_ad_left`), so a check on generators of `T` suffices.  The generators of `T` are the
squares and the brackets of `Y`, and on each the check is evaluated by §5's Hall-Petrescu step
and by Jacobi. -/

section Relations

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **Jacobi as a rewriting inside `Z`.**  All three rotations lie in the top layer, which is
central of exponent two, so `gFourFive_jacobi` can be solved for its first factor with no signs
and no ordering.  This is the relation that lets a fourfold bracket's two outer slots be
exchanged at the cost of one bracket of `Y`-elements. -/
theorem cfiveSpan_jacobi_rewrite {p : levelQuot G 5} (hp : p ∈ lambdaImage G 2 5)
    (q r : levelQuot G 5) :
    commP (commP p q) r = commP (commP q r) p * commP (commP r p) q := by
  have hB : commP (commP q r) p ∈ zLayer G 4 :=
    cfive_commP_lambdaTwo_mem_zLayer (gFourFive_commP_mem_lambdaTwo q r) hp
  have hC : commP (commP r p) q ∈ zLayer G 4 :=
    cfive_commP_mem_zLayer_left (gFourFive_commP_mem_lambdaThree_right r hp) q
  have h1 : commP (commP p q) r = (commP (commP q r) p * commP (commP r p) q)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact gFourFive_jacobi hp q r)
  rw [h1, mul_inv_rev, zLayer_inv_self hC, zLayer_inv_self hB, gFourFive_zLayer_comm hC]

/-- **The fourfold form of the rewriting**, with no hypothesis at all, since a bracket of two
`Q₅`-elements lies in `Y`.  This is `gFourFive_jacobi_iter` solved for its first factor. -/
theorem cfiveSpan_jacobi_iter_rewrite (a b q r : levelQuot G 5) :
    commP (commP (commP a b) q) r
      = commP (commP q r) (commP a b) * commP (commP r (commP a b)) q :=
  cfiveSpan_jacobi_rewrite (gFourFive_commP_mem_lambdaTwo a b) q r

/-- **The `T`-elements whose square lies in `S`.**  A subgroup, because squaring is a
homomorphism on `T` (`cfiveSpan_sq_mul_lambdaThree`). -/
def cfiveSpanSqSub (S : Subgroup (levelQuot G 5)) : Subgroup (levelQuot G 5) where
  carrier := {y | y ∈ lambdaImage G 3 5 ∧ y ^ 2 ∈ S}
  mul_mem' := fun {a b} ha hb =>
    ⟨(lambdaImage G 3 5).mul_mem ha.1 hb.1, by
      rw [cfiveSpan_sq_mul_lambdaThree ha.1 hb.1]; exact S.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨(lambdaImage G 3 5).one_mem, by rw [one_pow]; exact S.one_mem⟩
  inv_mem' := fun {a} ha =>
    ⟨(lambdaImage G 3 5).inv_mem ha.1, by rw [inv_pow]; exact S.inv_mem ha.2⟩

/-- **The `T`-elements whose bracket against `q` lies in `S`.**  A subgroup, because
`t ↦ commP t q` is a homomorphism on `T` (`gFourFive_ad_left`, `gFourFive_ad_inv_left`). -/
def cfiveSpanAdSub (S : Subgroup (levelQuot G 5)) (q : levelQuot G 5) :
    Subgroup (levelQuot G 5) where
  carrier := {y | y ∈ lambdaImage G 3 5 ∧ commP y q ∈ S}
  mul_mem' := fun {a b} ha hb =>
    ⟨(lambdaImage G 3 5).mul_mem ha.1 hb.1, by
      rw [gFourFive_ad_left ha.1 b q]; exact S.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨(lambdaImage G 3 5).one_mem, by rw [cfour_one_comm]; exact S.one_mem⟩
  inv_mem' := fun {a} ha =>
    ⟨(lambdaImage G 3 5).inv_mem ha.1, by rw [gFourFive_ad_inv_left ha.1 q]; exact ha.2⟩

/-- **The layer `γ_{k+1}` seen inside `Q_n`**, generated by the squares and the brackets of the
layer below.  `gFourFive_zLayer_le_gen` is the case `n = k + 2`; the level is free here because
nothing in the proof is about the level, and the relations half needs `k = 2` with `n = 5`, where
the target is `T` and not the top layer. -/
theorem cfiveSpan_lambdaImage_le {k n : ℕ} (hk : 1 ≤ k) {S : Subgroup (levelQuot G n)}
    (hS : IsClosed ((S : Subgroup (levelQuot G n)) : Set (levelQuot G n)))
    (hsq : ∀ y ∈ lambdaImage G k n, y ^ 2 ∈ S)
    (hcomm : ∀ y ∈ lambdaImage G k n, ∀ q, commP y q ∈ S) :
    lambdaImage G (k + 1) n ≤ S := by
  rintro _ ⟨v, hv, rfl⟩
  have hpre : IsClosed ((Subgroup.comap (levelMk G n) S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_comap]
    exact hS.preimage (continuous_levelMk G n)
  have hsub : twoCentralSeries G (k + 1) ≤ Subgroup.comap (levelMk G n) S := by
    rw [twoCentralSeries_succ (G := G) hk, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      show levelMk G n (g ^ 2) ∈ S
      rw [map_pow]
      exact hsq _ ⟨g, hg, rfl⟩
    · refine Subgroup.commutator_le.2 fun a ha b _ => ?_
      rw [commutatorElement_def]
      show levelMk G n (a * b * a⁻¹ * b⁻¹) ∈ S
      rw [gFourFive_levelMk_commutator]
      exact hcomm _ ⟨a⁻¹, (twoCentralSeries G k).inv_mem ha, rfl⟩ _
  exact hsub hv

/-- ⭐⭐⭐ **The relations half of the graded decomposition of `γ₄/γ₅`.**  A closed subgroup of
`Q₅` containing the three families

* `(y ^ 2) ^ 2` for `y ∈ Y`,
* `(commP y r) ^ 2` for `y ∈ Y` and `r ∈ Q₅`,
* `commP (commP y r) q` for `y ∈ Y` and `r, q ∈ Q₅`,

contains the whole of `Z = γ₄/γ₅`.  Compared with the generation half `gFourFive_zLayer_le`,
whose two families are indexed by the opaque `T`, every family here is indexed by `Y` with one or
two free slots of `Q₅`, and in graded language the three are the restricted summands of
`γ₄/γ₅` together with `L₄(V)`.

Two relations pay for the reduction.  Squaring and `ad(·)(q)` are homomorphisms on `T`, so both
`T`-indexed families of the generation half need only be checked on generators of `T`; and the
generators of `T` are the squares and the brackets of `Y` (`cfiveSpan_lambdaImage_le` at
`k = 2`, `n = 5`).  On a square generator the check is §5's Hall-Petrescu step, which is where
the third family is consumed with `q` in its innermost slot. -/
theorem cfiveSpan_zLayer_le_rel {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hT : IsClosed ((lambdaImage G 3 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hfour : ∀ y ∈ lambdaImage G 2 5, (y ^ 2) ^ 2 ∈ S)
    (hsqbr : ∀ y ∈ lambdaImage G 2 5, ∀ r, (commP y r) ^ 2 ∈ S)
    (hJ : ∀ y ∈ lambdaImage G 2 5, ∀ r q, commP (commP y r) q ∈ S) :
    zLayer G 4 ≤ S := by
  have hsqSub : IsClosed
      ((cfiveSpanSqSub S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)) :=
    hT.inter (hS.preimage (continuous_pow 2))
  have hsq : ∀ y ∈ lambdaImage G 3 5, y ^ 2 ∈ S := by
    intro y hy
    exact (cfiveSpan_lambdaImage_le (k := 2) (n := 5) (by norm_num) hsqSub
      (fun w hw => ⟨cfiveSpan_sq_mem_lambdaThree hw, hfour w hw⟩)
      (fun w hw r => ⟨cfive_commP_lambdaTwo_mem_lambdaThree hw r, hsqbr w hw r⟩) hy).2
  have hcomm : ∀ y ∈ lambdaImage G 3 5, ∀ q, commP y q ∈ S := by
    intro y hy q
    have hcont : Continuous fun t : levelQuot G 5 => commP t q := by
      simp only [commP]
      fun_prop
    have hadSub : IsClosed
        ((cfiveSpanAdSub S q : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)) :=
      hT.inter (hS.preimage hcont)
    refine (cfiveSpan_lambdaImage_le (k := 2) (n := 5) (by norm_num) hadSub ?_ ?_ hy).2
    · intro w hw
      refine ⟨cfiveSpan_sq_mem_lambdaThree hw, ?_⟩
      rw [cfiveSpan_commP_sq_left hw q]
      exact S.mul_mem (hsqbr w hw q) (hJ w hw q w)
    · intro w hw r
      exact ⟨cfive_commP_lambdaTwo_mem_lambdaThree hw r, hJ w hw r q⟩
  exact gFourFive_zLayer_le hS hsq hcomm

/-! ### The same reduction once more, from `Y` down to `Q₅`

`Y` is generated by the squares and the brackets of `Q₅`, and the three families of
`cfiveSpan_zLayer_le_rel` are again homomorphic in their `Y`-slot.  So the reduction can be run a
second time, and it lands on six families indexed by `Q₅` alone. -/

/-- A square of a `Q₅`-element lies in `Y`. -/
theorem cfiveSpan_sq_mem_lambdaTwo (g : levelQuot G 5) : g ^ 2 ∈ lambdaImage G 2 5 := by
  obtain ⟨v, rfl⟩ := levelMk_surjective G 5 g
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ (G := G) (Subgroup.mem_top _), by rw [map_pow]⟩

/-- ⭐ **`ad(·)(r)` is a homomorphism on `Y`**, valued in `T`.  The correction term of
`cfour_commP_mul_left` is a bracket of a `T`-element against a `Y`-element, so §1's vanishing
kills it.  Compare `gFourFive_ad_left`, which is the same statement with the near slot in `T` and
the other slot free. -/
theorem cfiveSpan_ad_lambdaTwo_left {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) (r : levelQuot G 5) :
    commP (y * y') r = commP y r * commP y' r := by
  rw [cfour_commP_mul_left,
    gFourFive_commP_vanish (cfive_commP_lambdaTwo_mem_lambdaThree hy r) hy', mul_one]

/-- **An inverse in the `Y`-slot inverts the bracket.**  Unlike at `T`, the value lies in `T` and
not in `Z`, so it is not its own inverse and the inversion survives. -/
theorem cfiveSpan_ad_lambdaTwo_inv {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (r : levelQuot G 5) : commP y⁻¹ r = (commP y r)⁻¹ := by
  have h := cfiveSpan_ad_lambdaTwo_left hy ((lambdaImage G 2 5).inv_mem hy) r
  rw [mul_inv_cancel, cfour_one_comm] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- ⭐ **The fourth power is a homomorphism on `Y`.**  The square alone is not: `cfour_sq_mul`
leaves the `Z`-defect `commP y' y`, which one class down would have been killed by `Y` being
abelian.  The outer square kills it instead, and the two inner squares then add because they lie
in `T` (`cfiveSpan_sq_mul_lambdaThree`). -/
theorem cfiveSpan_pow_four_lambdaTwo_mul {y y' : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hy' : y' ∈ lambdaImage G 2 5) : ((y * y') ^ 2) ^ 2 = (y ^ 2) ^ 2 * (y' ^ 2) ^ 2 := by
  have hz : commP y' y ∈ zLayer G 4 := cfive_commP_lambdaTwo_mem_zLayer hy' hy
  have hmul : (y * y') ^ 2 = y ^ 2 * y' ^ 2 * commP y' y := by
    rw [cfour_sq_mul, cfive_commP_zLayer_left hz y', mul_one]
  rw [hmul, gFourFive_sq_zLayer_dress hz,
    cfiveSpan_sq_mul_lambdaThree (cfiveSpan_sq_mem_lambdaThree hy)
      (cfiveSpan_sq_mem_lambdaThree hy')]

/-- **The `Y`-elements carrying all three families of `cfiveSpan_zLayer_le_rel` into `S`.**  A
subgroup, by the three homomorphism statements above. -/
def cfiveSpanGenSub (S : Subgroup (levelQuot G 5)) : Subgroup (levelQuot G 5) where
  carrier := {y | y ∈ lambdaImage G 2 5 ∧ (y ^ 2) ^ 2 ∈ S ∧ (∀ r, (commP y r) ^ 2 ∈ S) ∧
    ∀ r q, commP (commP y r) q ∈ S}
  mul_mem' := fun {a b} ha hb =>
    ⟨(lambdaImage G 2 5).mul_mem ha.1 hb.1, by
      rw [cfiveSpan_pow_four_lambdaTwo_mul ha.1 hb.1]; exact S.mul_mem ha.2.1 hb.2.1,
      fun r => by
        rw [cfiveSpan_ad_lambdaTwo_left ha.1 hb.1 r,
          cfiveSpan_sq_mul_lambdaThree (cfive_commP_lambdaTwo_mem_lambdaThree ha.1 r)
            (cfive_commP_lambdaTwo_mem_lambdaThree hb.1 r)]
        exact S.mul_mem (ha.2.2.1 r) (hb.2.2.1 r),
      fun r q => by
        rw [cfiveSpan_ad_lambdaTwo_left ha.1 hb.1 r,
          gFourFive_ad_left (cfive_commP_lambdaTwo_mem_lambdaThree ha.1 r) _ q]
        exact S.mul_mem (ha.2.2.2 r q) (hb.2.2.2 r q)⟩
  one_mem' := ⟨(lambdaImage G 2 5).one_mem, by simp only [one_pow]; exact S.one_mem,
    fun r => by rw [cfour_one_comm, one_pow]; exact S.one_mem,
    fun r q => by rw [cfour_one_comm, cfour_one_comm]; exact S.one_mem⟩
  inv_mem' := fun {a} ha =>
    ⟨(lambdaImage G 2 5).inv_mem ha.1, by
      rw [inv_pow, inv_pow]; exact S.inv_mem ha.2.1,
      fun r => by
        rw [cfiveSpan_ad_lambdaTwo_inv ha.1 r, inv_pow]; exact S.inv_mem (ha.2.2.1 r),
      fun r q => by
        rw [cfiveSpan_ad_lambdaTwo_inv ha.1 r,
          gFourFive_ad_inv_left (cfive_commP_lambdaTwo_mem_lambdaThree ha.1 r) q]
        exact ha.2.2.2 r q⟩

/-- The carrier of `cfiveSpanGenSub` is closed whenever `S` and `Y` are. -/
theorem cfiveSpan_isClosed_genSub {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hY : IsClosed ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))) :
    IsClosed ((cfiveSpanGenSub S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)) := by
  have hc1 : Continuous fun y : levelQuot G 5 => (y ^ 2) ^ 2 := by fun_prop
  have hc2 : ∀ r : levelQuot G 5, Continuous fun y : levelQuot G 5 => (commP y r) ^ 2 := by
    intro r; simp only [commP]; fun_prop
  have hc3 : ∀ r q : levelQuot G 5,
      Continuous fun y : levelQuot G 5 => commP (commP y r) q := by
    intro r q; simp only [commP]; fun_prop
  have hset : ((cfiveSpanGenSub S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))
      = ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5))
          ∩ ((fun y => (y ^ 2) ^ 2) ⁻¹' (S : Set (levelQuot G 5)))
          ∩ (⋂ r : levelQuot G 5, (fun y => (commP y r) ^ 2) ⁻¹' (S : Set (levelQuot G 5)))
          ∩ (⋂ r : levelQuot G 5, ⋂ q : levelQuot G 5,
              (fun y => commP (commP y r) q) ⁻¹' (S : Set (levelQuot G 5))) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun hh => ⟨⟨⟨hh.1, hh.2.1⟩, hh.2.2.1⟩, hh.2.2.2⟩,
      fun hh => ⟨hh.1.1.1, hh.1.1.2, hh.1.2, hh.2⟩⟩
  rw [hset]
  exact ((hY.inter (hS.preimage hc1)).inter
      (isClosed_iInter fun r => hS.preimage (hc2 r))).inter
    (isClosed_iInter fun r => isClosed_iInter fun q => hS.preimage (hc3 r q))

/-- ⭐⭐⭐ **The graded decomposition of `γ₄/γ₅`, in six families indexed by `Q₅` alone.**  A
closed subgroup of `Q₅` containing

* `((g ^ 2) ^ 2) ^ 2` and `((commP a b) ^ 2) ^ 2` (the two restricted eighth/fourth powers),
* `(commP (g ^ 2) r) ^ 2` and `(commP (commP a b) r) ^ 2` (the squares of the weight-three
  brackets),
* `commP (commP (g ^ 2) r) q` and `commP (commP (commP a b) r) q` (the weight-four brackets, the
  second being the fourfold bracket `L₄(V)`),

for all `g, a, b, r, q ∈ Q₅`, contains the whole of `Z = γ₄/γ₅`.

This is `cfiveSpan_zLayer_le_rel` with its reduction run a second time, from `Y` down to the
generators of `Y`.  Its last family is exactly the one `gFourFive_jacobi_iter` is a relation on,
and `cfiveSpan_jacobi_iter_rewrite` is that relation solved for one member. -/
theorem cfiveSpan_zLayer_le_gens {S : Subgroup (levelQuot G 5)}
    (hS : IsClosed ((S : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hT : IsClosed ((lambdaImage G 3 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (hY : IsClosed ((lambdaImage G 2 5 : Subgroup (levelQuot G 5)) : Set (levelQuot G 5)))
    (h8 : ∀ g : levelQuot G 5, ((g ^ 2) ^ 2) ^ 2 ∈ S)
    (hbr4 : ∀ a b : levelQuot G 5, ((commP a b) ^ 2) ^ 2 ∈ S)
    (hsq2 : ∀ g r : levelQuot G 5, (commP (g ^ 2) r) ^ 2 ∈ S)
    (hsq3 : ∀ a b r : levelQuot G 5, (commP (commP a b) r) ^ 2 ∈ S)
    (hJ2 : ∀ g r q : levelQuot G 5, commP (commP (g ^ 2) r) q ∈ S)
    (hJ4 : ∀ a b r q : levelQuot G 5, commP (commP (commP a b) r) q ∈ S) :
    zLayer G 4 ≤ S := by
  have hgen : lambdaImage G 2 5 ≤ cfiveSpanGenSub S :=
    cfiveSpan_lambdaImage_le (k := 1) (n := 5) le_rfl (cfiveSpan_isClosed_genSub hS hY)
      (fun g _ => ⟨cfiveSpan_sq_mem_lambdaTwo g, h8 g, fun r => hsq2 g r,
        fun r q => hJ2 g r q⟩)
      (fun g _ q => ⟨gFourFive_commP_mem_lambdaTwo g q, hbr4 g q, fun r => hsq3 g q r,
        fun r q' => hJ4 g q r q'⟩)
  exact cfiveSpan_zLayer_le_rel hS hT (fun y hy => (hgen hy).2.1)
    (fun y hy r => (hgen hy).2.2.1 r) (fun y hy r q => (hgen hy).2.2.2 r q)

end Relations

/-! ## §7 The relations half at `D_sq h`, with no closedness side conditions -/

section RelationsDsq

variable {h : ℕ}

/-- Every level of the tower of `D_sq h` is discrete, at level five as at level four. -/
theorem cfiveSpan_discreteTopology : DiscreteTopology (levelQuot (DSq h : Type) 5) :=
  discreteTopology_levelQuot (DSq h : Type) (lim_dsq_finsetGen h) (isProP_DSq h) 5

/-- Every subgroup of `Q₅` is closed, `Q₅` being discrete. -/
theorem cfiveSpan_isClosed (S : Subgroup (levelQuot (DSq h : Type) 5)) :
    IsClosed ((S : Subgroup (levelQuot (DSq h : Type) 5)) : Set (levelQuot (DSq h : Type) 5)) := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 5) := cfiveSpan_discreteTopology
  exact isClosed_discrete _

/-- ⭐⭐⭐ **The relations half at `D_sq h`, with no side condition**: this is the form a
class-five witness search consumes.  To reach the whole leftover it is enough to reach the fourth
powers of `Y`, the squares of the brackets of `Y`, and the fourfold brackets. -/
theorem cfiveSpan_zLayer_le_dsq {S : Subgroup (levelQuot (DSq h : Type) 5)}
    (hfour : ∀ y ∈ lambdaImage (DSq h : Type) 2 5, (y ^ 2) ^ 2 ∈ S)
    (hsqbr : ∀ y ∈ lambdaImage (DSq h : Type) 2 5, ∀ r, (commP y r) ^ 2 ∈ S)
    (hJ : ∀ y ∈ lambdaImage (DSq h : Type) 2 5, ∀ r q, commP (commP y r) q ∈ S) :
    zLayer (DSq h : Type) 4 ≤ S :=
  cfiveSpan_zLayer_le_rel (cfiveSpan_isClosed S) (cfiveSpan_isClosed _) hfour hsqbr hJ

/-- ⭐⭐⭐ **The graded decomposition at `D_sq h`, with no side condition.**  Six families indexed
by `Q₅`, and reaching all six reaches the whole class-five leftover. -/
theorem cfiveSpan_zLayer_le_gens_dsq {S : Subgroup (levelQuot (DSq h : Type) 5)}
    (h8 : ∀ g : levelQuot (DSq h : Type) 5, ((g ^ 2) ^ 2) ^ 2 ∈ S)
    (hbr4 : ∀ a b : levelQuot (DSq h : Type) 5, ((commP a b) ^ 2) ^ 2 ∈ S)
    (hsq2 : ∀ g r : levelQuot (DSq h : Type) 5, (commP (g ^ 2) r) ^ 2 ∈ S)
    (hsq3 : ∀ a b r : levelQuot (DSq h : Type) 5, (commP (commP a b) r) ^ 2 ∈ S)
    (hJ2 : ∀ g r q : levelQuot (DSq h : Type) 5, commP (commP (g ^ 2) r) q ∈ S)
    (hJ4 : ∀ a b r q : levelQuot (DSq h : Type) 5, commP (commP (commP a b) r) q ∈ S) :
    zLayer (DSq h : Type) 4 ≤ S :=
  cfiveSpan_zLayer_le_gens (cfiveSpan_isClosed S) (cfiveSpan_isClosed _) (cfiveSpan_isClosed _)
    h8 hbr4 hsq2 hsq3 hJ2 hJ4

end RelationsDsq

/-! ## §8 Axiom pins -/

section AxiomPins

#print axioms cfiveRow_comm_zLayer_dress
#print axioms cfiveRow_comm_lambdaThree_dress
#print axioms cfiveRow_handleWord_congr
#print axioms cfiveRow_relator_blind
#print axioms cfiveRow_repair
#print axioms cfiveRow_repair_knob
#print axioms cfiveRow_sq_mem
#print axioms cfiveRow_sq_admissible
#print axioms cfiveRow_comm_mem
#print axioms cfiveRow_comm_admissible
#print axioms cfiveRow_mul_admissible
#print axioms CfiveRowReachable
#print axioms cfiveRow_supply_of_reachable
#print axioms cfiveSpan_sq_mem_lambdaThree
#print axioms cfiveSpan_commP_sq_left
#print axioms cfiveSpan_pow_four_lambdaThree
#print axioms cfiveSpan_pow_four_lambdaTwo_mem
#print axioms cfiveSpan_pow_eight_lambdaTwo
#print axioms cfiveSpan_sq_knob_pair
#print axioms cfiveSpan_sq_mul_lambdaThree
#print axioms cfiveSpan_dress_two_mul
#print axioms cfiveSpan_pair_correction
#print axioms cfiveSpan_jacobi_rewrite
#print axioms cfiveSpan_jacobi_iter_rewrite
#print axioms cfiveSpanSqSub
#print axioms cfiveSpanAdSub
#print axioms cfiveSpan_lambdaImage_le
#print axioms cfiveSpan_zLayer_le_rel
#print axioms cfiveSpan_sq_mem_lambdaTwo
#print axioms cfiveSpan_ad_lambdaTwo_left
#print axioms cfiveSpan_ad_lambdaTwo_inv
#print axioms cfiveSpan_pow_four_lambdaTwo_mul
#print axioms cfiveSpanGenSub
#print axioms cfiveSpan_isClosed_genSub
#print axioms cfiveSpan_zLayer_le_gens
#print axioms cfiveSpan_discreteTopology
#print axioms cfiveSpan_isClosed
#print axioms cfiveSpan_zLayer_le_dsq
#print axioms cfiveSpan_zLayer_le_gens_dsq

end AxiomPins

end SqCore

end Dyadic

end GQ2
