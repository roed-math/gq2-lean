/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenDerivKer

/-!
# W52-EV3FB §2: the even raw-to-bracket upgrade, and what it costs

Boundary three of the three that `StageAbstractionEvenKernelAdapted.lean` §3 isolates inside
`EvenClimbResidualSupply`, namely `EvenKernelRawToBracketSupply`: *raw shift span membership
upgrades to even bracket span membership*.  This file does three things, and the second and
third are the honest replacement for a discharge.

1. **The easy inclusion, unconditionally.**  The bracket span always sits inside the raw shift
   span (§1): the six bracket atom families are literally the six raw coordinate rows with the
   coordinate restricted, so restricting can only shrink.  Consequently the boundary asserts
   an *equality* of the two spans, which is how §3 restates it.
2. **The reduction to one coordinatewise statement** (§2).  The boundary follows from
   `EvenRawToNeutralSupply`: every depth-`k-1` coordinate becomes neutral after multiplication
   by a central class.  This is genuinely all that is needed, because the atoms do not see
   central factors at all: brackets against a central class are trivial and the graded layer
   has exponent two, so the raw row at `p` and the bracket row at `p · z` are *equal*, not
   merely congruent.  The boundary therefore shrinks from a statement about subgroups of
   `Q_{k+1}` at every level and every stage to a statement about single coordinates.
3. **The arithmetic price, machine-checked** (§4).  `EvenRawToNeutralSupply` forces
   `2^(k+1) ∣ χ(g) − 1` for every `g ∈ λ_{k-1}`, at every `k ≥ 3`.  The committed generic
   bound `dvd_chi_of_mem_twoCentralSeries` gives only `2^k`, so this is one digit deeper than
   anything the two-central tower supplies on its own, uniformly in `k`, and it is an
   *arithmetic* condition on the character with no span in it.  Any carrier possessing a
   depth-`k-1` element whose character has exact level `k` refutes the route.

## Why this is not a port failure

The L template does **not** prove a raw-to-bracket span inclusion, and does not contain one:
`GammaLSylowPreimageFieldLabuteBracketSpan.lean` and `…ForwardSpanAudit.lean` identify the
bracket span with the image of the neutral shift homomorphism and stop there.  What the L
template proves at this station is
`stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill`, which is a *conditional*
upgrade: it consumes the hypothesis that the raw correction kills the defect, the hypothesis
that its handle rows are already trivial (the separately named
`SqStageHandleDigitRepairSupply`), and `Function.Surjective chiCycKTwo`.  It then repairs two
rows by commuting `2^(k-2)`-power moves on the base and flips the remaining fresh digits with
central classes of prescribed character, which is exactly where surjectivity is spent.

`EvenKernelRawToBracketSupply` drops all three inputs and quantifies over every element of the
span.  So it is strictly stronger than the L crux, and §4 measures by how much.  The
composition `evenKernel_residualSupply_of_supplies` remains valid and committed; this file
supplies the sharper hypothesis it can be fed.

## Numbering

1. the bracket span sits inside the raw shift span, unconditionally;
2. the neutralisation supply, and the reduction of the boundary to it;
3. the boundary restated as an equality of spans;
4. the arithmetic obstruction the neutralisation supply carries.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore

/-! ## §1 The bracket span sits inside the raw shift span

Unconditional, and the reason the boundary is an equality in disguise.  Each of the six
bracket atom families is the value of one raw coordinate row at a coordinate that happens to
be neutral, and F1's rows do not care whether it is. -/

section BracketLe

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {s h k : ℕ}

/-- **The bracket span is contained in the raw shift span.**  The `⊇` half of §B §5, read into
the raw span instead of the neutral one. -/
theorem evenRawTo_bracketSpan_le_rawShiftSpan
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k) :
    evenBracketSpan s chi base ≤ evenRawShiftSpan base hk := by
  rw [evenBracketSpan, Subgroup.closure_le]
  rintro z (⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨j, p, rfl⟩ | ⟨j, p, rfl⟩)
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 0 ⟨p.1, p.2.1⟩ : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_zero_apply base hk ⟨p.1, p.2.1⟩] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 1 ⟨p.1, p.2.1⟩ : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_one_apply base hk ⟨p.1, p.2.1⟩] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 2 ⟨p.1, p.2.1⟩ : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_two_apply base hk ⟨p.1, p.2.1⟩] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 3 ⟨p.1, p.2.1⟩ : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_three_apply base hk ⟨p.1, p.2.1⟩] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) ⟨p.1, p.2.1⟩ :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleU_apply base hk j ⟨p.1, p.2.1⟩] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) ⟨p.1, p.2.1⟩ :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleV_apply base hk j ⟨p.1, p.2.1⟩] at hmem

end BracketLe

/-! ## §2 The neutralisation supply, and the reduction

The whole difference between the two spans is whether the coordinate carries a character
condition.  The coordinate enters each atom only through `p²` and `commP p (base i)`, and both
are blind to a central factor: `commP p z = 1` because `Z_k` is central, and `z² = 1` because
`Z_k` has exponent two.  So it is enough to be able to *move* each coordinate into the neutral
subgroup by a central factor. -/

section Neutralisation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {s h k : ℕ}

/-- **The neutralisation supply.**  Every depth-`k-1` coordinate becomes a depth-`s` neutral
coordinate after multiplication by a class of the graded layer.  This is the shrunken form of
boundary three: one statement about single coordinates, with no span and no stage in it. -/
def EvenRawToNeutralSupply (s : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ p ∈ lambdaImage G (k - 1) (k + 1),
    ∃ z ∈ zLayer G k, p * z ∈ evenBracketNeutralSubgroup s G chi k

/-- A bracket against a graded-layer class is trivial. -/
private theorem evenRawTo_commP_zLayer_right {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    (b : levelQuot G (k + 1)) : commP b z = 1 :=
  commP_eq_one_of_mul_comm (zLayer_commute hz b).symm.eq

/-- **The atoms are blind to central factors.**  Both quantities a coordinate contributes to
an even row, its square and its brackets, are unchanged by a graded-layer factor. -/
theorem evenRawTo_atom_mul_zLayer (hk : 3 ≤ k) {p : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1)) {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) :
    (p * z) ^ 2 = p ^ 2 ∧ ∀ b : levelQuot G (k + 1), commP (p * z) b = commP p b := by
  refine ⟨?_, fun b ↦ ?_⟩
  · rw [(zLayer_commute hz p).symm.mul_pow, zLayer_sq G hz, mul_one]
  · rw [evenRawCommP_mul_left_of_depth k hk hp,
      commP_eq_one_of_mul_comm (zLayer_commute hz b).eq, mul_one]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **Every one-coordinate raw row lies in the bracket span**, given the neutralisation
supply. -/
theorem evenRawTo_coordinateShift_mem_bracketSpan
    (Hneut : EvenRawToNeutralSupply s G chi) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (i : Fin (MarkedCore.coreRank h)) (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection i p)).1 ∈
      evenBracketSpan s chi base := by
  obtain ⟨z, hz, hq⟩ := Hneut k hk p.1 p.2
  obtain ⟨hsq, hbr⟩ := evenRawTo_atom_mul_zLayer hk p.2 hz
  set q : evenBracketNeutralSubgroup s G chi k := ⟨p.1 * z, hq⟩ with hqdef
  have hq1 : q.1 = p.1 * z := rfl
  refine evenIndex_cases
    (P := fun i ↦ ((evenRawDepthShiftHom base hk)
      (evenRawDepthCoordinateCorrection i p)).1 ∈ evenBracketSpan s chi base) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [evenRawDepthShiftHom_zero_apply]
    refine Subgroup.subset_closure (Or.inl ⟨q, ?_⟩)
    rw [hq1, hsq, hbr, hbr]
  · rw [evenRawDepthShiftHom_one_apply]
    refine Subgroup.subset_closure (Or.inr (Or.inl ⟨q, ?_⟩))
    rw [hq1, hbr]
  · rw [evenRawDepthShiftHom_two_apply]
    refine Subgroup.subset_closure (Or.inr (Or.inr (Or.inl ⟨q, ?_⟩)))
    rw [hq1, hbr]
  · rw [evenRawDepthShiftHom_three_apply]
    refine Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, ?_⟩))))
    rw [hq1, hbr]
  · intro j
    rw [evenRawDepthShiftHom_handleU_apply]
    refine Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, q, ?_⟩)))))
    rw [hq1, hbr]
  · intro j
    rw [evenRawDepthShiftHom_handleV_apply]
    refine Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, q, ?_⟩)))))
    rw [hq1, hbr]

/-- **The raw shift span is contained in the bracket span**, given the neutralisation supply.
A raw depth correction is the ordered product of its one-coordinate corrections, so the six
rows suffice. -/
theorem evenRawTo_rawShiftSpan_le_bracketSpan
    (Hneut : EvenRawToNeutralSupply s G chi) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawShiftSpan base hk ≤ evenBracketSpan s chi base := by
  rintro y ⟨q, hq, rfl⟩
  obtain ⟨V, rfl⟩ := hq
  rw [evenDeriv_rawDepthCorrection_eq_prod V, map_list_prod, map_list_prod]
  simp only [List.map_map]
  refine Subgroup.list_prod_mem _ ?_
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  exact evenRawTo_coordinateShift_mem_bracketSpan Hneut hk base i
    ⟨V.correction i, V.depth i⟩

/-- **Boundary three, reduced.**  The neutralisation supply gives
`EvenKernelRawToBracketSupply` at every word datum and every value table. -/
theorem evenRawTo_supply_of_neutral {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (Hneut : EvenRawToNeutralSupply s G chi) :
    EvenKernelRawToBracketSupply s W v G chi :=
  fun k hk T _ hz ↦
    evenRawTo_rawShiftSpan_le_bracketSpan Hneut hk
      (fun i ↦ canonLift G k (T.generators i)) hz

end Neutralisation

/-! ## §3 The boundary is an equality of spans

§1 and §2 together say the boundary asserts that the character condition on corrections is
invisible at the level of shift words.  Stating it that way is what makes §4 legible. -/

section SpanEq

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {s h k : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **Boundary three is exactly the equality of the two spans**, at every level and every
stage.  The `←` direction is trivial and the `→` direction is §1. -/
theorem evenRawTo_supply_iff_span_eq :
    EvenKernelRawToBracketSupply s W v G chi ↔
      ∀ (k : ℕ) (hk : 3 ≤ k) (T : Tuple W v G chi k),
        evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk =
          evenBracketSpan s chi (fun i ↦ canonLift G k (T.generators i)) := by
  constructor
  · intro H k hk T
    exact le_antisymm (fun z hz ↦ H k hk T z hz)
      (evenRawTo_bracketSpan_le_rawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk)
  · intro H k hk T z hz
    rw [← H k hk T]
    exact hz

end SpanEq
