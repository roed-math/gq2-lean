/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcBuild

/-!
# W86-LADDER5: the `M6` ladder at class five and above

Wave 85 (`GQ2/Dyadic/Instances/MpcBuild.lean`) climbed the class-four rung of the `M6` ansatz and
built the increment engine that prices every correction slot exactly.  It left the engine as a
pair of *sufficient* conditions with a caution attached: the hypothesis of
`mpcBld_shift_of_full_supply` quantifies over **every** class-`(j+1)` solution, and wave 85 §9.2
recorded as open whether a class-`(j+2)` solution has to be a `λ_j`-move away from a
class-`(j+1)` one, calling that "what would turn the engine into a decision procedure".

This module answers that question and takes the consequences.

Declaration prefix `mpcLad` (namespace `GQ2.Dyadic.Instances.MpcLad`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcLad

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-! ## §0 Orientation

The wave-85 class-four witness, named once so the class-five work has a starting point, and the
core word as a function of the four corrections. -/

/-- The wave-85 class-four witness, as a four-tuple in the shape the solution sets take:
`s = t = ⁅D̄, B̄⁆`, `m = n = 1`. -/
def mpcLadW4 : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) :=
  (mpcBldW, mpcBldW, 1, 1)

theorem mpcLad_w4_mem : mpcLadW4 ∈ mpcWordSet 4 := by
  refine ⟨⟨mpcBld_w_mem, ?_⟩, ⟨mpcBld_w_mem, ?_⟩, one_mem _, one_mem _,
    mpcBld_mem_four_witness⟩ <;>
  exact mpcBld_chi_commP _ _

/-- **The defect of a correction quadruple**: the `M6` core word evaluated at the four letters.
`mpcWordSet k` is exactly the set of legal quadruples whose defect lies in `λ_k`. -/
def mpcLadDefect (p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)) :
    (DM 2 0 : Type) :=
  mWord 2 (mpcWordLetA p.1) (mpcWordLetB p.2.1) (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2)

theorem mpcLad_mem_wordSet_iff {k : ℕ}
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)} :
    p ∈ mpcWordSet k ↔ p.1 ∈ mpcWordCorr ∧ p.2.1 ∈ mpcWordCorr ∧ p.2.2.1 ∈ mpcWordCorrC ∧
      p.2.2.2 ∈ mpcWordCorr ∧ mpcLadDefect p ∈ twoCentralSeries (DM 2 0 : Type) k :=
  Iff.rfl

/-! ## §1 Reachable moves

A `λ_j`-move multiplies the four corrections by elements of their own carriers that additionally
lie `j` layers down.  Wave 85's `mpcBldIncr` is the whole effect of such a move on the defect,
and §1 records the two facts that were left implicit there: the identity is a move, and its
increment is trivial. -/

section Move

/-- **A reachable `λ_j`-move of the four corrections.**  Each factor stays inside the carrier its
slot demands (`mpcWordCorr` for the `Ā`-, `B̄`- and `D̄`-slots, the row-invisible `mpcWordCorrC`
for the pivot) and lies in `λ_j`.  These are exactly the eight side conditions of
`mpcBld_step`. -/
def MpcLadMove (j : ℕ) (us ut um un : (DM 2 0 : Type)) : Prop :=
  (us ∈ mpcWordCorr ∧ us ∈ twoCentralSeries (DM 2 0 : Type) j) ∧
  (ut ∈ mpcWordCorr ∧ ut ∈ twoCentralSeries (DM 2 0 : Type) j) ∧
  (um ∈ mpcWordCorrC ∧ um ∈ twoCentralSeries (DM 2 0 : Type) j) ∧
  (un ∈ mpcWordCorr ∧ un ∈ twoCentralSeries (DM 2 0 : Type) j)

/-- The identity is a reachable move at every class. -/
theorem mpcLad_move_one (j : ℕ) : MpcLadMove j 1 1 1 1 :=
  ⟨⟨one_mem _, one_mem _⟩, ⟨one_mem _, one_mem _⟩, ⟨one_mem _, one_mem _⟩,
    ⟨one_mem _, one_mem _⟩⟩

/-- Reachable moves compose: the carriers are subgroups and `λ_j` is one too. -/
theorem mpcLad_move_mul {j : ℕ} {us ut um un us' ut' um' un' : (DM 2 0 : Type)}
    (h : MpcLadMove j us ut um un) (h' : MpcLadMove j us' ut' um' un') :
    MpcLadMove j (us * us') (ut * ut') (um * um') (un * un') :=
  ⟨⟨Subgroup.mul_mem _ h.1.1 h'.1.1, Subgroup.mul_mem _ h.1.2 h'.1.2⟩,
    ⟨Subgroup.mul_mem _ h.2.1.1 h'.2.1.1, Subgroup.mul_mem _ h.2.1.2 h'.2.1.2⟩,
    ⟨Subgroup.mul_mem _ h.2.2.1.1 h'.2.2.1.1, Subgroup.mul_mem _ h.2.2.1.2 h'.2.2.1.2⟩,
    ⟨Subgroup.mul_mem _ h.2.2.2.1 h'.2.2.2.1, Subgroup.mul_mem _ h.2.2.2.2 h'.2.2.2.2⟩⟩

/-- **The identity move has trivial increment.**  Small, and load bearing: it is the whole
content of the converse in §2. -/
theorem mpcLad_incr_one (t n : (DM 2 0 : Type)) : mpcBldIncr t n 1 1 1 1 = 1 := by
  simp only [mpcBldIncr, one_pow, cfour_one_comm, cfour_comm_one, mul_one]

/-- ⭐⭐ **THE DEFECT IS AFFINE ALONG A `λ_j`-MOVE.**  Wave 85's `mpcBld_step` proves a
membership; this is the equation behind it.  Modulo `λ_{j+2}` the defect of the moved quadruple
is the defect of the base quadruple times the move's increment, exactly.  Nothing is assumed
about the base beyond its two `λ₂`-side conditions, in particular it need not be a solution at
any class. -/
theorem mpcLad_defect_move {j : ℕ}
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)}
    (hp1 : p.1 ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hp3 : p.2.2.1 ∈ twoCentralSeries (DM 2 0 : Type) 2)
    {us ut um un : (DM 2 0 : Type)}
    (hus : us ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (husj : us ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hutj : ut ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hum : um ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (humj : um ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hunj : un ∈ twoCentralSeries (DM 2 0 : Type) j) :
    levelMk (DM 2 0 : Type) (j + 2)
        (mpcLadDefect (p.1 * us, p.2.1 * ut, p.2.2.1 * um, p.2.2.2 * un))
      = levelMk (DM 2 0 : Type) (j + 2)
        (mpcLadDefect p * mpcBldIncr p.2.1 p.2.2.2 us ut um un) := by
  have hsu : p.1 * us ∈ twoCentralSeries (DM 2 0 : Type) 2 := Subgroup.mul_mem _ hp1 hus
  have hmu : p.2.2.1 * um ∈ twoCentralSeries (DM 2 0 : Type) 2 := Subgroup.mul_mem _ hp3 hum
  have hassoc : mpcLadDefect p * mpcBldIncr p.2.1 p.2.2.2 us ut um un
      = mpcLadDefect p * (us ^ 2 * commP us (dmA 2 0) * commP us (mpcWordLetB p.2.1)) *
        commP um (mpcWordLetD p.2.2.2) * commP (dmA 2 0) ut * commP (dmC 2 0) un := by
    simp only [mpcBldIncr]; group
  simp only [mpcLadDefect] at hassoc ⊢
  rw [mpcBld_incr_n (p.1 * us) (p.2.1 * ut) (p.2.2.1 * um) p.2.2.2 un hmu hunj, map_mul,
    mpcBld_incr_t (p.1 * us) p.2.1 (p.2.2.1 * um) p.2.2.2 ut hsu hutj, map_mul,
    mpcBld_incr_m (p.1 * us) p.2.1 p.2.2.1 p.2.2.2 um humj, map_mul,
    mpcBld_incr_s p.1 p.2.1 p.2.2.1 p.2.2.2 us hp1 husj, map_mul,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← hassoc]

end Move

/-! ## §2 The connectivity converse, and the engine as a decision procedure

Wave 85 §9.2 asked whether a class-`(j+2)` solution must be a `λ_j`-move away from a
class-`(j+1)` one.  **It must, and the reason is that it already is one**: the solution sets are
nested (`mpcWordSet_antitone`), so a class-`(j+2)` solution *is* a class-`(j+1)` solution, and
the identity is a reachable move with trivial increment (`mpcLad_incr_one`).  Connectivity
therefore holds, at every class, with no hypothesis.

That settles the question, and the settlement is worth stating carefully, because the trivial
proof does **not** make the answer vacuous.  What it buys is exactly one thing, and it is the
thing wave 85 wanted: the one-step supply criterion becomes an **iff**, so the engine decides
each rung rather than only certifying it.  Three consequences follow, in §2.2, §2.3, §2.4:
the sufficient condition weakens from `∀ p` to `∃ p`; a per-class *failure* over all `p` becomes
a proof of emptiness; and, through wave 84's per-class criterion, that emptiness refutes the
ansatz outright. -/

section Converse

/-- **The one-step supply condition at a single quadruple**: some reachable `λ_j`-move kills the
defect down to `λ_{j+2}`. -/
def MpcLadSupply (j : ℕ)
    (p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)) : Prop :=
  ∃ us ut um un, MpcLadMove j us ut um un ∧
    mpcLadDefect p * mpcBldIncr p.2.1 p.2.2.2 us ut um un
      ∈ twoCentralSeries (DM 2 0 : Type) (j + 2)

/-- ⭐ **THE CONVERSE.**  A class-`(j+2)` solution has one-step supply at class `j`, witnessed by
the identity move.  This is wave 85 §9.2's open question, and the answer is yes. -/
theorem mpcLad_supply_of_mem {j : ℕ}
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)}
    (hp : p ∈ mpcWordSet (j + 2)) : MpcLadSupply j p := by
  refine ⟨1, 1, 1, 1, mpcLad_move_one j, ?_⟩
  rw [mpcLad_incr_one, mul_one]
  exact hp.2.2.2.2

/-- One reachable move that kills the defect produces a class-`(j+2)` solution: wave 85's
`mpcBld_step`, restated against `MpcLadMove`. -/
theorem mpcLad_mem_of_supply {j : ℕ}
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)}
    (hp : p ∈ mpcWordSet (j + 1)) (hs : MpcLadSupply j p) :
    ∃ q ∈ mpcWordSet (j + 2), True := by
  obtain ⟨us, ut, um, un, ⟨⟨hus, husj⟩, ⟨hut, hutj⟩, ⟨hum, humj⟩, ⟨hun, hunj⟩⟩, hkill⟩ := hs
  exact ⟨_, mpcBld_step hp us ut um un hus husj hut hutj hum humj hun hunj hkill, trivial⟩

/-- ⭐⭐⭐ **THE RUNG, AS AN IFF.**  A class-`(j+2)` solution exists exactly when *some*
class-`(j+1)` solution has one-step supply.  The forward direction is the converse
(`mpcLad_supply_of_mem`, the identity move) together with `mpcWordSet_antitone`; the backward
direction is wave 85's `mpcBld_step`.

This is the statement wave 85 §9.2 named as the missing piece, and with it the increment engine
is a **decision procedure** for the ladder: at each class the question "is there a solution one
class further?" is the linear-algebra question "does some class-`(j+1)` solution's defect lie in
the reachable `𝔽₂`-subspace?", with no gap in either direction. -/
theorem mpcLad_nonempty_iff (j : ℕ) :
    (mpcWordSet (j + 2)).Nonempty ↔ ∃ p ∈ mpcWordSet (j + 1), MpcLadSupply j p := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, mpcWordSet_antitone (by omega) hp, mpcLad_supply_of_mem hp⟩
  · rintro ⟨p, hp, hs⟩
    obtain ⟨q, hq, -⟩ := mpcLad_mem_of_supply hp hs
    exact ⟨q, hq⟩

/-- ⭐⭐⭐ **THE RESIDUE, WITH THE QUANTIFIER CORRECTED.**  Wave 85's
`mpcBld_shift_of_full_supply` asked for supply at *every* class-`(j+1)` solution; by the converse
it is enough to have it at *one*.  This is strictly weaker, and it is the weakest hypothesis the
one-step engine admits.

The induction hypothesis is not used: one supplied quadruple per class is enough on its own, and
the class-four rung is already a theorem (`mpcBld_nonempty_four`). -/
theorem mpcLad_shift_of_exists_supply
    (H : ∀ j, 3 ≤ j → ∃ p ∈ mpcWordSet (j + 1), MpcLadSupply j p) : MpcPivShift 2 := by
  refine mpcWord_shift_of_forall_class_four fun k hk => ?_
  rcases eq_or_lt_of_le hk with h | h
  · exact h ▸ mpcBld_nonempty_four
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact (mpcLad_nonempty_iff j).mpr (H j (by omega))

/-- ⭐⭐ **THE REFUTATION ROUTE, NOW REACHABLE BY THE ENGINE.**  Wave 85 recorded that a failed
one-step supply is not a refutation, and that is right *at a single quadruple*.  By the converse
it becomes one as soon as the failure is proved over the whole class-`(j+1)` solution set: then
`mpcWordSet (j+2)` is empty, which is the shape wave 84 named as the only admissible negative
claim. -/
theorem mpcLad_eq_empty_of_no_supply {j : ℕ}
    (H : ∀ p ∈ mpcWordSet (j + 1), ¬ MpcLadSupply j p) : mpcWordSet (j + 2) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  exact H p (mpcWordSet_antitone (by omega) hp) (mpcLad_supply_of_mem hp)

/-- The same failure, stated at the level the ladder consumes: no class-`(j+2)` solution. -/
theorem mpcLad_not_nonempty_of_no_supply {j : ℕ}
    (H : ∀ p ∈ mpcWordSet (j + 1), ¬ MpcLadSupply j p) : ¬ (mpcWordSet (j + 2)).Nonempty := by
  rw [mpcLad_eq_empty_of_no_supply H]
  exact Set.not_nonempty_empty

end Converse

/-! ## §3 Axiom pins

One line per public declaration, in declaration order, measured against the mirror. -/

section AxiomPins

#print axioms mpcLadW4
#print axioms mpcLad_w4_mem
#print axioms mpcLadDefect
#print axioms mpcLad_mem_wordSet_iff
#print axioms MpcLadMove
#print axioms mpcLad_move_one
#print axioms mpcLad_move_mul
#print axioms mpcLad_incr_one
#print axioms mpcLad_defect_move
#print axioms MpcLadSupply
#print axioms mpcLad_supply_of_mem
#print axioms mpcLad_mem_of_supply
#print axioms mpcLad_nonempty_iff
#print axioms mpcLad_shift_of_exists_supply
#print axioms mpcLad_eq_empty_of_no_supply
#print axioms mpcLad_not_nonempty_of_no_supply

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcLad
