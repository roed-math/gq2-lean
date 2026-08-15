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

/-! ## Axiom audit -/

section AxiomPins

#print axioms recBl_mpc_uniformPushedHsimp
#print axioms recBl_mpc_exactLiftingRN

end AxiomPins

end GQ2.Dyadic.Instances.RecordBlocks
