/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.RowClauses
import GQ2.Dyadic.Instances.MpcRamifiedRow
import GQ2.Dyadic.Instances.MpcSelectedScalar

/-!
# The blocks the record still carries  (dyadic campaign, lane W85-BLOCKS)

W84-CLAUSES measured the `ℚ₂(√5)` row down to four things: two open analytic clauses at the
candidate carrier (`stokes`, `determinant`), one coefficient `Prop` (`askCStageVanishing`)
carried once at each of the row's two carriers, and, on the `Mpc` row only, a missing
unconditional corrected bundle.  This module works those four blocks.

Sections are added as the lane lands them; the axiom pins at the end carry the honest split.
-/

namespace GQ2.Dyadic.Instances.RecordBlocks

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances

/-! ## §1 The `Mpc` corrected bundle (ticket T4)

W84-CLAUSES §2 narrowed "the residue is uniform across the four rows" to **three**: the two `M0`
rows and the `N0` row get the identical treatment, and `Mpc 2 1 false 1 0` (`ℚ₂(√10)`) does not,
because `MProcyclicExact` has no `exactLiftingRN_unconditional` and its corrected bundle still
carries an `Hsimp`-family hypothesis.

That gap is now closable, and the reason is a file the note did not consult.
`MpcPairings.lean:72` records `MProcyclicExact.RamifiedNormalPairingSeparates` as **not** proved
there, with a precise obstruction (on the ramified reading neither commutator base is trivial,
so `heisCommR_of_trivial_right` does not apply and a fully general commutator law is needed).
That obstruction was subsequently removed: `MpcRamifiedRow.lean:988` proves
`MProcyclicExact.ramifiedNormalPairingSeparates` at `1 ≤ α` for **every** display, and
`MpcSelectedScalar.lean:206` reduces `UniformPushedHsimp` to exactly that one input.  Composing
the two is the whole ticket.

⚠ **"Unconditional" is not the same word here as on the `M` side.**  `MCompact` quantifies over
`(α, h, q)` and nothing else, so its bundle is unconditional in the literal sense.  The `Mpc`
carrier is indexed by a *display* of the field unit `η`, and the reduction needs that display to
be well formed and to represent `η`.  Both are fields of `MpcDisplayFor η`, which is what the
field seam presents, so the honest statement is **unconditional given the display package**, and
that is how §1 states it.  `1 ≤ r` is likewise carried, and it is not free: it is supplied at the
seam by `FieldBranchSelection.valid`, which gives `2 ≤ α ∧ 1 ≤ r` on the `Mpc` branch. -/

section MpcBundle

open GQ2.Dyadic.MProcyclicExact GQ2.Dyadic.Words.Mpc

/-- **The procyclic-`M` uniform pushed residue, for every display package.**  The `Mpc` twin of
`MCompact.uniformPushedHsimp`.  Three second-order inputs feed
`uniformPushedHsimp_of_pairings`; two were already theorems for every display the seam can
present, and the third is `MpcRamifiedRow`'s separation, which needs only `1 ≤ α`. -/
theorem recBl_mpc_uniformPushedHsimp {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ}
    (hα : 2 ≤ alpha) (hqe : Even q) (d : MpcDisplayFor eta) :
    UniformPushedHsimp alpha r pp h q d.display :=
  uniformPushedHsimp_of_ramified_display hα hqe d (ramifiedNormalPairingSeparates (by omega))

/-- **Corrected exact lifting at the procyclic-`M` presentation, for every display package.**
The `Mpc` twin of `MCompact.exactLiftingRN_unconditional`, and the theorem whose absence made
W84-CLAUSES narrow its uniformity claim from four rows to three.  With it the `Mpc` row joins
the other three: its `exactLifting` clause is `askCStageVanishing` at its own candidate carrier
and nothing else. -/
theorem recBl_mpc_exactLiftingRN {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (hα : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma alpha r (p epsilon r) h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_uniformPushed d (recBl_mpc_uniformPushedHsimp hα hqe d) (by omega) hr hqe nuP

end MpcBundle

/-! ## §2 The coefficient frame (ticket T1)

W84-CLAUSES §3 named this the sharpest item: `rowCl_mCand_isEmpty_boundaryLifts` says that if the
row's frozen `exactLifting` clause holds then `BoundaryLiftsK b F T` is **empty** for every
boundary-framed marked target with `1 < #Φ(K)`, so one frame with a nonempty `BoundaryLiftsK`
refutes the clause, and with it `askCStageVanishing` at the candidate carrier.  The note's
recommended starting point was `MCompact.datumRho`, "a handle-uniform surjection onto a
nontrivial finite 2-group".

**That starting point does not work, and the reason generalises.**  A frame needs a
`SectionSeven.MinimalBlock`, whose `nontrivial_action` field demands a `y` and a `p ∈ P` with
`y p y⁻¹ p⁻¹ ∉ S`: the chief factor `P/S` must be a *nontrivial* `Y`-module.  §2 proves that no
**nilpotent** `Y` admits one, for any marked kernel `L`.  Finite 2-groups are nilpotent, so the
whole "surject onto a nontrivial finite 2-group" strategy is dead, and `datumRho` in particular
is dead twice over: its target `Base ⧸ datum.M` has exponent 2 (`datumQuot_sq`), hence is
abelian.

So the refutation handle is real but its input is not a 2-group quotient: **any refuting frame
must have a target `Y` that is not nilpotent**, i.e. one whose odd part acts nontrivially on a
2-group chief factor.  The smallest shape that can work is `Y` with `L_Y = Q₈`, `S = Z(Q₈)`,
`P = Q₈`, `K = Q₈` and `H = Y/Q₈` of order 3, where `Φ(K) = Z(Q₈)` has order 2; nothing in the
`M`-row's resolver package produces a surjection of the candidate group onto such a `Y` with the
boundary equation satisfied, and this lane did not build one.

This is a **narrowing, not a discharge**: `askCStageVanishing` at the candidate carrier is still
open, and the honest statement of what changed is that the cheap route to refuting it is closed
and the owner call still rests on W81-ASK's recommendation to restate the records against
`ExactLiftingSemanticsRN` (which `rowCl_rn_both_carriers_sqrtFive` already supports at both
carriers). -/

section CoefficientFrame

open GQ2.SectionSeven

variable {Y : Type} [Group Y] [Finite Y]

/-- The centraliser of `S` "one layer up": the elements whose class in `Y ⧸ S` is central.  It is
the largest subgroup on which the `Y`-action mod `S` is trivial, and it is what lets §2 conclude
from a *generator-wise* triviality statement to the whole of `P`, with no decomposition of the
join `S ⊔ X` into a product. -/
private def centralMod (S : Subgroup Y) [S.Normal] : Subgroup Y :=
  (Subgroup.center (Y ⧸ S)).comap (QuotientGroup.mk' S)

omit [Finite Y] in
private theorem mem_centralMod {S : Subgroup Y} [S.Normal] {p : Y} :
    p ∈ centralMod S ↔ ∀ y : Y, y * p * y⁻¹ * p⁻¹ ∈ S := by
  constructor
  · intro hp y
    have hz : (QuotientGroup.mk y : Y ⧸ S) * QuotientGroup.mk p
        = QuotientGroup.mk p * QuotientGroup.mk y :=
      Subgroup.mem_center_iff.mp hp _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hz
    have h3 := (‹S.Normal›).conj_mem _
      (S.inv_mem ((‹S.Normal›).conj_mem _ hz y)) p
    have heq : p * (y * ((y * p)⁻¹ * (p * y)) * y⁻¹)⁻¹ * p⁻¹ = y * p * y⁻¹ * p⁻¹ := by group
    rwa [heq] at h3
  · intro hp
    rw [centralMod, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    show (QuotientGroup.mk y : Y ⧸ S) * QuotientGroup.mk p
      = QuotientGroup.mk p * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := (‹S.Normal›).conj_mem _ (hp y⁻¹) p⁻¹
    have heq : p⁻¹ * (y⁻¹ * p * y⁻¹⁻¹ * p⁻¹) * p⁻¹⁻¹ = (y * p)⁻¹ * (p * y) := by group
    rwa [heq] at h

omit [Finite Y] in
private theorem le_centralMod_self (S : Subgroup Y) [S.Normal] : S ≤ centralMod S := fun s hs =>
  mem_centralMod.mpr fun y => S.mul_mem ((‹S.Normal›).conj_mem _ hs y) (S.inv_mem hs)

/-- The `Y`-lower central series of a normal subgroup: `P₀ = P`, `Pₙ₊₁ = ⁅Y, Pₙ⁆`.  Mathlib's
`Subgroup.lowerCentralSeries P` is the lower central series of `P` **as a group in its own
right** (`⁅Pₙ, P⁆`), which is not the same thing and does not see the `Y`-action; the whole point
here is that the outer group acts. -/
private def yLower (P : Subgroup Y) : ℕ → Subgroup Y
  | 0 => P
  | n + 1 => ⁅(⊤ : Subgroup Y), yLower P n⁆

omit [Finite Y] in
private theorem yLower_normal {P : Subgroup Y} (hP : P.Normal) : ∀ n, (yLower P n).Normal
  | 0 => hP
  | n + 1 => @Subgroup.commutator_normal _ _ ⊤ (yLower P n) inferInstance (yLower_normal hP n)

omit [Finite Y] in
private theorem yLower_le {P : Subgroup Y} (hP : P.Normal) : ∀ n, yLower P n ≤ P
  | 0 => le_rfl
  | n + 1 => le_trans (@Subgroup.commutator_le_right _ _ ⊤ _ (yLower_normal hP n)) (yLower_le hP n)

omit [Finite Y] in
private theorem yLower_le_lcs (P : Subgroup Y) :
    ∀ n, yLower P n ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup Y) n
  | 0 => le_top
  | n + 1 => by
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl (yLower_le_lcs P n)

/-- **No nilpotent group carries a §7 minimal block.**

The block asks for a chief factor `P/S` of `Y` inside the marked kernel on which `Y` acts
nontrivially.  In a nilpotent group there is no such factor: the `Y`-lower central series of `P`
reaches `⊥`, and at every step the chief dichotomy forces `S ⊔ ⁅Y, …⁆ = P`, because the only
alternative makes the whole of `P` central mod `S` and so contradicts `nontrivial_action`.  At
the last step `S ⊔ ⊥ = P` reads `S = P`, against `S < P`.

This is what closes the cheap route to ticket T1: every finite 2-group is nilpotent, so no
surjection of the candidate carrier onto a finite 2-group can carry a refuting frame, whatever
`H`, `E`, `b` and `F` are chosen alongside it. -/
theorem recBl_minimalBlock_isEmpty_of_nilpotent [Group.IsNilpotent Y] (L : Subgroup Y) :
    IsEmpty (MinimalBlock L) := by
  refine ⟨fun B => ?_⟩
  haveI hSn : B.S.Normal := B.hS
  haveI hPn : B.P.Normal := B.hP
  -- If the whole of `P` is central mod `S`, the block's `nontrivial_action` fails.
  have hcentral : ¬ B.P ≤ centralMod B.S := by
    intro hle
    obtain ⟨y, p, hp, hnot⟩ := B.nontrivial_action
    exact hnot (mem_centralMod.mp (hle hp) y)
  -- The chief dichotomy propagates `S ⊔ yLower P n = P` down the whole series.
  have key : ∀ n, B.S ⊔ yLower B.P n = B.P := by
    intro n
    induction n with
    | zero => exact sup_eq_right.mpr B.hSP.le
    | succ n ih =>
        haveI := yLower_normal hPn n
        haveI := yLower_normal hPn (n + 1)
        have hle : B.S ⊔ yLower B.P (n + 1) ≤ B.P :=
          sup_le (le_trans B.hSP.le le_rfl) (yLower_le hPn (n + 1))
        rcases B.chief _ (Subgroup.sup_normal _ _) le_sup_left hle with hS | hP
        · exfalso
          refine hcentral ?_
          rw [← ih]
          refine sup_le (le_centralMod_self B.S) fun x hx => mem_centralMod.mpr fun y => ?_
          have : y * x * y⁻¹ * x⁻¹ ∈ yLower B.P (n + 1) :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top y) hx
          exact hS ▸ (le_sup_right.trans_eq hS) this
        · exact hP
  -- Nilpotency drives the series to `⊥`, so the last instance of `key` says `S = P`.
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent Y›
  have hbot : yLower B.P n = ⊥ := le_bot_iff.mp (hn ▸ yLower_le_lcs B.P n)
  have := key n
  rw [hbot, sup_bot_eq] at this
  exact absurd this B.hSP.ne

/-- **No finite `p`-group carries a §7 minimal block.**  Finite `p`-groups are nilpotent. -/
theorem recBl_minimalBlock_isEmpty_of_isPGroup {p : ℕ} [Fact (Nat.Prime p)] (hY : IsPGroup p Y)
    (L : Subgroup Y) : IsEmpty (MinimalBlock L) :=
  haveI := hY.isNilpotent
  recBl_minimalBlock_isEmpty_of_nilpotent L

/-- **No exponent-2 group carries a §7 minimal block.**  Exponent 2 forces commutativity, and a
commutative group is nilpotent of class at most one.  This is the form that applies to
`Base ⧸ datum.M`, the target of every `datumRho`. -/
theorem recBl_minimalBlock_isEmpty_of_sq (h2 : ∀ y : Y, y * y = 1) (L : Subgroup Y) :
    IsEmpty (MinimalBlock L) := by
  have hinv : ∀ y : Y, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (h2 y)
  have hcomm : ∀ a b : Y, a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  haveI : Group.IsNilpotent Y := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Subgroup.upperCentralSeries_one]
    exact eq_top_iff.2 fun y _ => Subgroup.mem_center_iff.mpr fun g => hcomm g y
  exact recBl_minimalBlock_isEmpty_of_nilpotent L

end CoefficientFrame

/-! ## Axiom audit -/

section AxiomPins

#print axioms recBl_mpc_uniformPushedHsimp
#print axioms recBl_mpc_exactLiftingRN
#print axioms recBl_minimalBlock_isEmpty_of_nilpotent
#print axioms recBl_minimalBlock_isEmpty_of_isPGroup
#print axioms recBl_minimalBlock_isEmpty_of_sq

end AxiomPins

end GQ2.Dyadic.Instances.RecordBlocks
