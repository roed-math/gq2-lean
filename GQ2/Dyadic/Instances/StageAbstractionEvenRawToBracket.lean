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

/-! ## §4 The arithmetic price of the neutralisation supply

This is the finding of the lane.  §2 shrank boundary three to `EvenRawToNeutralSupply`, which
is a statement about single coordinates; unfolding it turns it into a statement about the
character alone, with no group theory left.  The two bounds below bracket it:

* **sufficient** (`evenRawTo_neutral_of_chi_deep`): `χ` trivial to `k+1+s` digits on
  `λ_{k-1}`, at every `k ≥ 3`;
* **necessary** (`evenRawTo_chi_dvd_of_neutral`): `2^(k+1) ∣ χ(g) − 1` for every
  `g ∈ λ_{k-1}`, at every `k ≥ 3`.

The committed generic bound is `dvd_chi_of_mem_twoCentralSeries`, which at `j = k-1` gives
only `2^k ∣ χ(g) − 1`.  So the necessary condition is **one digit deeper than the two-central
tower supplies**, uniformly in `k`, and it is not available from anything this lane has: it is
neither implied by the image identification `Hrange` (which constrains `χ(G)`, not the
filtration `χ(λ_m)`) nor by `EvenRowDeepFibreLiftSupply` (which lifts representatives to exact
fibres and says nothing about how deep `χ` is on a layer).

`evenRawTo_neutralSupply_false_of_chi_exact` is the refutation in usable form: exhibit one
`g ∈ λ_{k-1}` whose character has exact level `k`, and the route is dead.  This is why the
L template does not attempt a span inclusion here, and instead proves a kill-conditional
upgrade whose digit repairs are paid for by `Function.Surjective chiCycKTwo`. -/

section Obstruction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {s k : ℕ}

/-- **Sufficiency.**  If the character is already trivial to `k+1+s` digits on every
depth-`k-1` element, the neutralisation supply holds with the trivial central factor. -/
theorem evenRawTo_neutral_of_chi_deep
    (H : ∀ (m : ℕ), 3 ≤ m → ∀ g ∈ twoCentralSeries G (m - 1),
      Units.map (PadicInt.toZModPow (m + 1 + s)).toMonoidHom (chi g) = 1) :
    EvenRawToNeutralSupply s G chi := by
  intro m hm p hp
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  obtain ⟨g, hg, rfl⟩ := hp
  rw [mul_one]
  exact ⟨⟨g, hg, rfl⟩, g, rfl, H m hm g hg⟩

/-- **Unfolding the neutralisation supply at a single element.**  A depth-`k-1` element can be
multiplied by a depth-`k` element so that the character of the product is trivial to `k+1+s`
digits.  All the group theory of §2 is spent here; what remains is arithmetic. -/
theorem evenRawTo_exists_lambda_mul_of_neutral (Hneut : EvenRawToNeutralSupply s G chi)
    (hk : 3 ≤ k) {g : G} (hg : g ∈ twoCentralSeries G (k - 1)) :
    ∃ w ∈ twoCentralSeries G k,
      Units.map (PadicInt.toZModPow (k + 1 + s)).toMonoidHom (chi (g * w)) = 1 := by
  obtain ⟨z, hz, _, g'', hg'', hchi''⟩ :=
    Hneut k hk (levelMk G (k + 1) g) ⟨g, hg, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hz
  have hprod : levelMk G (k + 1) (g * y) = levelMk G (k + 1) g'' := by
    rw [map_mul]; exact hg''
  have hr : (g * y)⁻¹ * g'' ∈ twoCentralSeries G (k + 1) := QuotientGroup.eq.mp hprod
  refine ⟨y * ((g * y)⁻¹ * g''), Subgroup.mul_mem _ hy
    (twoCentralSeries_antitone G (by omega : k ≤ k + 1) hr), ?_⟩
  rw [show g * (y * ((g * y)⁻¹ * g'')) = g'' by group]
  exact hchi''

/-- **Necessity, and the obstruction.**  The neutralisation supply forces the character to
vanish to `k+1` digits on every depth-`k-1` element, at every level `k ≥ 3`.  The committed
`dvd_chi_of_mem_twoCentralSeries` gives only `k` digits there. -/
theorem evenRawTo_chi_dvd_of_neutral (Hneut : EvenRawToNeutralSupply s G chi)
    (hk : 3 ≤ k) {g : G} (hg : g ∈ twoCentralSeries G (k - 1)) :
    ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨w, hw, hchiw⟩ := evenRawTo_exists_lambda_mul_of_neutral Hneut hk hg
  have hgw : ((2 : ℕ) : ℤ_[2]) ^ (k + 1 + s) ∣ ((chi (g * w) : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    mem_ker_units_toZModPow_iff.mp hchiw
  have hgw' : ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣
      ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    refine dvd_trans (pow_dvd_pow _ (by omega : k + 1 ≤ k + 1 + s)) ?_
    rw [show ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * ((chi w : ℤ_[2]ˣ) : ℤ_[2]) =
      ((chi (g * w) : ℤ_[2]ˣ) : ℤ_[2]) by rw [map_mul]; push_cast; ring]
    exact hgw
  have hwdvd : ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hd := dvd_chi_of_mem_twoCentralSeries chi (by omega : 2 ≤ k) hw
    simpa using hd
  rw [show ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 =
      (((chi g : ℤ_[2]ˣ) : ℤ_[2]) * ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1) -
        ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * (((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1) by ring]
  exact dvd_sub hgw' (hwdvd.mul_left _)

/-- **The refutation in usable form.**  One depth-`k-1` element whose character has exact
level `k` kills the neutralisation route, hence the natural route to boundary three. -/
theorem evenRawTo_neutralSupply_false_of_chi_exact (hk : 3 ≤ k) {g : G}
    (hg : g ∈ twoCentralSeries G (k - 1))
    (hex : ¬ ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    ¬ EvenRawToNeutralSupply s G chi :=
  fun Hneut ↦ hex (evenRawTo_chi_dvd_of_neutral Hneut hk hg)

end Obstruction

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`, matching the nine pins of the L template's
`BracketSpan.lean` and the four of `ForwardSpanAudit.lean`, the two files this station sits
against.  Nothing here is arithmetic about `ℚ_[2]`, so nothing may exceed std-3. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the easy inclusion
#print axioms evenRawTo_bracketSpan_le_rawShiftSpan

-- §2 the neutralisation supply and the reduction
#print axioms EvenRawToNeutralSupply
#print axioms evenRawTo_atom_mul_zLayer
#print axioms evenRawTo_coordinateShift_mem_bracketSpan
#print axioms evenRawTo_rawShiftSpan_le_bracketSpan
#print axioms evenRawTo_supply_of_neutral

-- §3 the boundary as an equality of spans
#print axioms evenRawTo_supply_iff_span_eq

-- §4 the arithmetic price
#print axioms evenRawTo_neutral_of_chi_deep
#print axioms evenRawTo_exists_lambda_mul_of_neutral
#print axioms evenRawTo_chi_dvd_of_neutral
#print axioms evenRawTo_neutralSupply_false_of_chi_exact

end AxiomPins
