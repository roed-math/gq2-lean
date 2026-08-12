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

/-! ## §5 Axiom pins -/

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

end AxiomPins

end SqCore

end Dyadic

end GQ2
