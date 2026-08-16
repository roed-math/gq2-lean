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

## What lands

1. **The converse holds** (§2).  A class-`(j+2)` solution *is* a class-`(j+1)` solution, and the
   identity is a reachable move with trivial increment, so `mpcLad_supply_of_mem` needs no
   hypothesis.  Hence `mpcLad_nonempty_iff`: a rung is an **iff**, and the engine decides it.
   Three consequences: the sufficient condition weakens from `∀ p` to `∃ p`
   (`mpcLad_shift_of_exists_supply`); a supply failure proved over the whole class-`(j+1)`
   solution set proves `mpcWordSet (j+2) = ∅` (`mpcLad_eq_empty_of_no_supply`); and that
   emptiness is exactly the negative claim wave 84 named as the only admissible one
   [W86-HOUSE scope: a negative claim about the ANSATZ; see the
   `mpcLad_eq_empty_of_no_supply` docstring's block].

2. **A rung's exact shape** (§3).  The increment map is a homomorphism (`mpcLad_incr_hom`) into
   the central involutive layer (`mpcLad_incr_mem_zLayer`), so the reachable increments are an
   `𝔽₂`-subspace (`mpcLadReachSub`) that does not move along the orbit
   (`mpcLad_reach_base_indep`), and the defects of a `λ_j`-orbit are one coset of it
   (`mpcLad_defect_orbit`).

3. **The first exact class-five term** (§4).  `mpcLad_pow_letC_five`: the pivot letter's fourth
   power, blind to everything at class four, carries four central corrections at class five, two
   of them independent of the correction slot and so present in the class-four witness itself.

## What does not land

**The decision.**  `MpcPivShift 2` is neither proved nor refuted here.  The class-five defect of
the class-four witness is not computed in full: §4 computes one of the four factors of `mWord`
exactly, and the other three are open.  No class-five claim is made in either direction, and
wave 84 §5's control (the greedy ladder kills `M5`, a theorem of the tree) still forbids reading
a stall as evidence.

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
each rung rather than only certifying it.  Three consequences follow below: the sufficient
condition weakens from `∀ p` to `∃ p`; a per-class *failure* proved over all `p` becomes a proof
of emptiness; and that emptiness is the shape wave 84 named as the only admissible negative
claim. -/

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
claim.

[W86-HOUSE scope, as of `0a479c6e`: "refutation" throughout this docstring means refuting the
ANSATZ.  An empty `mpcWordSet` refutes `MpcPivShift 2` itself only if the ansatz is exhaustive
among the markings `mpcOrb_shift_iff_marking` quantifies over, which is not proved; wave 84's
"only admissible negative claim" carried the same inversion.  The statement below is exact as
written.  See `mpcBld_shift_of_bracket_supply`'s W86-HOUSE block.

W87-HOUSE, as of `1541635f`: the hash above read `f0de6ad5` and is corrected here.  This file
does not exist at `f0de6ad5` (`git cat-file -e f0de6ad5:GQ2/Dyadic/Instances/MpcLadder.lean`
fails); it is created at `d18f840e` and this block was written by `1d286428`, after the house
lane closed, which carried the lane's own base hash onto a file the lane never saw.
`MpcBuild.lean`'s block stamps this same site `0a479c6e`, correctly, so the tree carried two
hashes for one finding and one of them could not be checked out.] -/
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

/-! ## §3 The exact structure of a rung

§2 makes the rung an iff, but leaves the search space as a set.  This section says what shape it
has.  Every factor of `mpcBldIncr` lands in the central involutive layer `Z_{j+1} = λ_{j+1}/λ_{j+2}`
of `Q_{j+2}` (`mpcLad_incr_mem_zLayer`), and the increment map is a **homomorphism** in the four
correction factors (`mpcLad_incr_hom`).  Hence the reachable increments are a subgroup - an
`𝔽₂`-subspace, since `Z_{j+1}` has exponent two - and the defects reachable from a quadruple by
`λ_j`-moves are exactly one **coset** of it (`mpcLad_defect_orbit`).

The `λ₂`-side conditions that make this work come free from the carriers: `mpcWordCorr` and
`mpcWordCorrC` both sit inside `λ₂`, so no lower bound on `j` is needed anywhere below. -/

section LayerFive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

/-- A `λ₂`-image and a `λ_j`-image commute in `Q_{j+2}`: wave 85's private `mpcBld_vanish`,
re-proved because the structure theorems need it in public. -/
theorem mpcLad_vanish {y ε : levelQuot G (j + 2)}
    (hy : y ∈ lambdaImage G 2 (j + 2)) (hε : ε ∈ lambdaImage G j (j + 2)) : commP y ε = 1 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hε
  have h : commP (levelMk G (j + 2) v) (levelMk G (j + 2) w)
      = levelMk G (j + 2) (commP v w) := by simp only [commP, map_mul, map_inv]
  rw [h]
  exact (lim_mem_twoCentralSeries_iff_levelMk (j + 2) _).mp
    (cfive_commutator_lambdaTwo_swap hw hv)

/-- The square of a `λ_j`-image is in the central layer of `Q_{j+2}`. -/
theorem mpcLad_sq_mem_zLayer {ε : levelQuot G (j + 2)} (hε : ε ∈ lambdaImage G j (j + 2)) :
    ε ^ 2 ∈ zLayer G (j + 1) := by
  obtain ⟨v, hv, rfl⟩ := hε
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G hv, by rw [map_pow]⟩

/-- **Left-slot additivity against a `λ_j`-image**: the correction term of
`cfour_commP_mul_left` is a bracket with a central element.  The right slot is unrestricted;
this is the mirror image of `cfive_commP_left_hom`, which restricts the right slot instead. -/
theorem mpcLad_commP_left_add {α α' : levelQuot G (j + 2)}
    (hα : α ∈ lambdaImage G j (j + 2)) (ξ : levelQuot G (j + 2)) :
    commP (α * α') ξ = commP α ξ * commP α' ξ := by
  rw [cfour_commP_mul_left,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hα ξ) α', mul_one]

/-- **Right-slot additivity against `λ_j`-images**, in the unreversed order: the two factors are
central, so they may be written either way round. -/
theorem mpcLad_commP_right_add (ξ : levelQuot G (j + 2)) {α α' : levelQuot G (j + 2)}
    (hα : α ∈ lambdaImage G j (j + 2)) (hα' : α' ∈ lambdaImage G j (j + 2)) :
    commP ξ (α * α') = commP ξ α * commP ξ α' := by
  rw [cfour_commP_mul_right,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_right ξ hα) α', mul_one]
  exact (zLayer_commute (cfive_commP_mem_zLayer_right ξ hα') _).eq

/-- **The square of a product of `λ`-images splits**: the correction of `cfour_sq_mul` is a
bracket of a `λ₂`-image against a `λ_j`-image, which dies in `Q_{j+2}`. -/
theorem mpcLad_sq_add {α α' : levelQuot G (j + 2)} (hα : α ∈ lambdaImage G j (j + 2))
    (hα' : α' ∈ lambdaImage G 2 (j + 2)) : (α * α') ^ 2 = α ^ 2 * α' ^ 2 := by
  rw [cfour_sq_mul, mpcLad_vanish hα' hα, cfour_one_comm, mul_one, mul_one]

/-- Every bracket of `Q_{j+2}` is a `λ₂`-image. -/
theorem mpcLad_commP_mem_two (p q : levelQuot G (j + 2)) :
    commP p q ∈ lambdaImage G 2 (j + 2) := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G (j + 2) p
  obtain ⟨b, rfl⟩ := levelMk_surjective G (j + 2) q
  exact ⟨commP a b, cfour_commP_mem_two a b, by simp only [commP, map_mul, map_inv]⟩

/-- **A trailing `λ_j`-factor in the far slot of a bracket is invisible** when the near slot is a
`λ₂`-image: this is why the reachable set does not depend on where in a `λ_j`-orbit it is read
(`mpcLad_reach_base_indep`). -/
theorem mpcLad_commP_drop (ξ : levelQuot G (j + 2)) {α : levelQuot G (j + 2)}
    (hα : α ∈ lambdaImage G 2 (j + 2)) {ε : levelQuot G (j + 2)}
    (hε : ε ∈ lambdaImage G j (j + 2)) : commP α (ξ * ε) = commP α ξ := by
  rw [cfour_commP_mul_right, mpcLad_vanish hα hε,
    mpcLad_vanish (mpcLad_commP_mem_two α ξ) hε, one_mul, mul_one]

/-- Six central factors may be paired off two by two. -/
private theorem mpcLad_shuffle6 {Q : Type*} [Group Q]
    {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : Q}
    (h₁ : ∀ x : Q, b₁ * x = x * b₁) (h₂ : ∀ x : Q, b₂ * x = x * b₂)
    (h₃ : ∀ x : Q, b₃ * x = x * b₃) (h₄ : ∀ x : Q, b₄ * x = x * b₄)
    (h₅ : ∀ x : Q, b₅ * x = x * b₅) :
    a₁ * b₁ * (a₂ * b₂) * (a₃ * b₃) * (a₄ * b₄) * (a₅ * b₅) * (a₆ * b₆)
      = a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * (b₁ * b₂ * b₃ * b₄ * b₅ * b₆) := by
  have hc : ∀ {u v : Q}, (∀ x : Q, u * x = x * u) → (∀ x : Q, v * x = x * v) →
      ∀ x : Q, u * v * x = x * (u * v) := by
    intro u v hu hv x
    rw [mul_assoc, hv x, ← mul_assoc, hu x, mul_assoc]
  have p : ∀ {a b c d : Q}, (∀ x : Q, b * x = x * b) → a * b * (c * d) = a * c * (b * d) := by
    intro a b c d hb
    calc a * b * (c * d) = a * (b * c * d) := by group
      _ = a * (c * b * d) := by rw [hb c]
      _ = a * c * (b * d) := by group
  rw [p h₁, p (hc h₁ h₂), p (hc (hc h₁ h₂) h₃), p (hc (hc (hc h₁ h₂) h₃) h₄),
    p (hc (hc (hc (hc h₁ h₂) h₃) h₄) h₅)]

end LayerFive

section Reach

/-- Every factor of a reachable increment, and so the increment itself, lies in the central
involutive layer `Z_{j+1}` of `Q_{j+2}`.  This is what makes the reachable set an
`𝔽₂`-subspace rather than merely a subgroup. -/
theorem mpcLad_incr_mem_zLayer {j : ℕ} (t n : (DM 2 0 : Type)) {us ut um un : (DM 2 0 : Type)}
    (husj : us ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hutj : ut ∈ twoCentralSeries (DM 2 0 : Type) j)
    (humj : um ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hunj : un ∈ twoCentralSeries (DM 2 0 : Type) j) :
    levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n us ut um un)
      ∈ zLayer (DM 2 0 : Type) (j + 1) := by
  simp only [mpcBldIncr, map_mul, map_pow, mpcBld_map_commP]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (mpcLad_sq_mem_zLayer ⟨us, husj, rfl⟩)
      (cfive_commP_mem_zLayer_left ⟨us, husj, rfl⟩ _))
    (cfive_commP_mem_zLayer_left ⟨us, husj, rfl⟩ _))
    (cfive_commP_mem_zLayer_left ⟨um, humj, rfl⟩ _))
    (cfive_commP_mem_zLayer_right _ ⟨ut, hutj, rfl⟩))
    (cfive_commP_mem_zLayer_right _ ⟨un, hunj, rfl⟩)

/-- ⭐⭐⭐ **THE INCREMENT MAP IS A HOMOMORPHISM.**  Composing two reachable `λ_j`-moves adds
their increments, exactly, in `λ_{j+1}/λ_{j+2}`.  The four slots contribute a square and four
brackets, and each is additive because its correction term is a bracket against a central
element or a bracket of two `λ`-images that dies two layers down.

With `mpcLad_incr_mem_zLayer` this says the reachable increments form an `𝔽₂`-subspace of
`λ_{j+1}/λ_{j+2}`, which is `mpcLadReach` below. -/
theorem mpcLad_incr_hom {j : ℕ} (t n : (DM 2 0 : Type))
    {us ut um un us' ut' um' un' : (DM 2 0 : Type)}
    (h : MpcLadMove j us ut um un) (h' : MpcLadMove j us' ut' um' un') :
    levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n (us * us') (ut * ut') (um * um') (un * un'))
      = levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n us ut um un) *
        levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n us' ut' um' un') := by
  obtain ⟨⟨-, husj⟩, ⟨-, hutj⟩, ⟨-, humj⟩, ⟨-, hunj⟩⟩ := h
  obtain ⟨⟨hus', husj'⟩, ⟨-, hutj'⟩, ⟨hum', humj'⟩, ⟨-, hunj'⟩⟩ := h'
  have mσ : levelMk (DM 2 0 : Type) (j + 2) us ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨us, husj, rfl⟩
  have mμ : levelMk (DM 2 0 : Type) (j + 2) um ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨um, humj, rfl⟩
  have mτ : levelMk (DM 2 0 : Type) (j + 2) ut ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨ut, hutj, rfl⟩
  have mν : levelMk (DM 2 0 : Type) (j + 2) un ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨un, hunj, rfl⟩
  have mσ' : levelMk (DM 2 0 : Type) (j + 2) us' ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨us', husj', rfl⟩
  have mμ' : levelMk (DM 2 0 : Type) (j + 2) um' ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨um', humj', rfl⟩
  have mτ' : levelMk (DM 2 0 : Type) (j + 2) ut' ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨ut', hutj', rfl⟩
  have mν' : levelMk (DM 2 0 : Type) (j + 2) un' ∈ lambdaImage (DM 2 0 : Type) j (j + 2) :=
    ⟨un', hunj', rfl⟩
  have mσ'2 : levelMk (DM 2 0 : Type) (j + 2) us' ∈ lambdaImage (DM 2 0 : Type) 2 (j + 2) :=
    ⟨us', hus'.1, rfl⟩
  simp only [mpcBldIncr, map_mul, map_pow, mpcBld_map_commP]
  rw [mpcLad_sq_add mσ mσ'2, mpcLad_commP_left_add mσ, mpcLad_commP_left_add mσ,
    mpcLad_commP_left_add mμ, mpcLad_commP_right_add _ mτ mτ',
    mpcLad_commP_right_add _ mν mν']
  exact mpcLad_shuffle6
    (fun x => (zLayer_commute (mpcLad_sq_mem_zLayer mσ') x).eq)
    (fun x => (zLayer_commute (cfive_commP_mem_zLayer_left mσ' _) x).eq)
    (fun x => (zLayer_commute (cfive_commP_mem_zLayer_left mσ' _) x).eq)
    (fun x => (zLayer_commute (cfive_commP_mem_zLayer_left mμ' _) x).eq)
    (fun x => (zLayer_commute (cfive_commP_mem_zLayer_right _ mτ') x).eq)

/-- **The reachable increment set at class `j`**, read in `Q_{j+2}`: the values `mpcBldIncr`
takes on reachable `λ_j`-moves of the four corrections. -/
def mpcLadReach (j : ℕ) (t n : (DM 2 0 : Type)) : Set (levelQuot (DM 2 0 : Type) (j + 2)) :=
  {x | ∃ us ut um un, MpcLadMove j us ut um un ∧
    x = levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n us ut um un)}

theorem mpcLad_reach_subset_zLayer (j : ℕ) (t n : (DM 2 0 : Type)) :
    mpcLadReach j t n ⊆ (zLayer (DM 2 0 : Type) (j + 1) : Set (levelQuot (DM 2 0 : Type) (j + 2)))
    := by
  rintro x ⟨us, ut, um, un, ⟨⟨-, husj⟩, ⟨-, hutj⟩, ⟨-, humj⟩, ⟨-, hunj⟩⟩, rfl⟩
  exact mpcLad_incr_mem_zLayer t n husj hutj humj hunj

/-- ⭐⭐ **THE REACHABLE INCREMENTS ARE A SUBGROUP.**  Closed under products by
`mpcLad_incr_hom`, containing `1` by `mpcLad_incr_one`, and closed under inverses because it sits
inside the exponent-two layer, where every element is its own inverse.  So the reachable set is
an `𝔽₂`-subspace of `λ_{j+1}/λ_{j+2}` and each rung is honest linear algebra. -/
theorem mpcLad_reach_one_mem (j : ℕ) (t n : (DM 2 0 : Type)) :
    (1 : levelQuot (DM 2 0 : Type) (j + 2)) ∈ mpcLadReach j t n :=
  ⟨1, 1, 1, 1, mpcLad_move_one j, by rw [mpcLad_incr_one, map_one]⟩

theorem mpcLad_reach_mul_mem {j : ℕ} {t n : (DM 2 0 : Type)}
    {x y : levelQuot (DM 2 0 : Type) (j + 2)} (hx : x ∈ mpcLadReach j t n)
    (hy : y ∈ mpcLadReach j t n) : x * y ∈ mpcLadReach j t n := by
  obtain ⟨us, ut, um, un, hm, rfl⟩ := hx
  obtain ⟨us', ut', um', un', hm', rfl⟩ := hy
  exact ⟨us * us', ut * ut', um * um', un * un', mpcLad_move_mul hm hm',
    (mpcLad_incr_hom t n hm hm').symm⟩

theorem mpcLad_reach_inv_mem {j : ℕ} {t n : (DM 2 0 : Type)}
    {x : levelQuot (DM 2 0 : Type) (j + 2)} (hx : x ∈ mpcLadReach j t n) :
    x⁻¹ ∈ mpcLadReach j t n := by
  obtain ⟨us, ut, um, un, hm, rfl⟩ := hx
  exact ⟨us, ut, um, un, hm, zLayer_inv_self
    (mpcLad_incr_mem_zLayer t n hm.1.2 hm.2.1.2 hm.2.2.1.2 hm.2.2.2.2)⟩

def mpcLadReachSub (j : ℕ) (t n : (DM 2 0 : Type)) :
    Subgroup (levelQuot (DM 2 0 : Type) (j + 2)) where
  carrier := mpcLadReach j t n
  mul_mem' := mpcLad_reach_mul_mem
  one_mem' := mpcLad_reach_one_mem j t n
  inv_mem' := mpcLad_reach_inv_mem

@[simp] theorem mpcLadReachSub_coe (j : ℕ) (t n : (DM 2 0 : Type)) :
    ((mpcLadReachSub j t n : Subgroup (levelQuot (DM 2 0 : Type) (j + 2))) :
      Set (levelQuot (DM 2 0 : Type) (j + 2))) = mpcLadReach j t n := rfl

/-- **Every reachable increment is an involution**: the subgroup is elementary abelian, so a rung
is an `𝔽₂`-linear question and not merely a group-theoretic one. -/
theorem mpcLad_reach_sq {j : ℕ} {t n : (DM 2 0 : Type)}
    {x : levelQuot (DM 2 0 : Type) (j + 2)} (hx : x ∈ mpcLadReach j t n) : x ^ 2 = 1 :=
  zLayer_sq (DM 2 0 : Type) (mpcLad_reach_subset_zLayer j t n hx)

/-- **The reachable set does not move along the orbit.**  Rebasing `t` and `n` by a `λ_j`-move
changes no increment: the two slots that see the base point see it through a bracket whose other
slot is a `λ₂`-image, and a trailing `λ_j`-factor there is invisible. -/
theorem mpcLad_reach_base_indep {j : ℕ} (t n : (DM 2 0 : Type))
    {ut un : (DM 2 0 : Type)}
    (hutj : ut ∈ twoCentralSeries (DM 2 0 : Type) j)
    (hunj : un ∈ twoCentralSeries (DM 2 0 : Type) j)
    {us' ut' um' un' : (DM 2 0 : Type)}
    (hus' : us' ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hum' : um' ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr (t * ut) (n * un) us' ut' um' un')
      = levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr t n us' ut' um' un') := by
  have hB : mpcWordLetB (t * ut) = mpcWordLetB t * ut := by
    rw [mpcWordLetB, mpcWordLetB, mul_assoc]
  have hD : mpcWordLetD (n * un) = mpcWordLetD n * un := by
    rw [mpcWordLetD, mpcWordLetD, mul_assoc]
  simp only [mpcBldIncr, hB, hD, map_mul, map_pow, mpcBld_map_commP]
  rw [mpcLad_commP_drop _ ⟨us', hus', rfl⟩ ⟨ut, hutj, rfl⟩,
    mpcLad_commP_drop _ ⟨um', hum', rfl⟩ ⟨un, hunj, rfl⟩]

/-- ⭐⭐⭐ **THE DEFECTS OF A `λ_j`-ORBIT ARE ONE COSET.**  Read in `Q_{j+2}`, the defects of the
quadruples reachable from `p` by a `λ_j`-move are exactly the coset of `mpcLadReach` through
`p`'s own defect.  Together with §2's iff this is the whole geometry of a rung:

* `mpcWordSet (j+2)` is nonempty **iff** some `λ_j`-orbit of `mpcWordSet (j+1)` has `1` in its
  coset, i.e. iff some class-`(j+1)` defect lies in the subgroup `mpcLadReach`;
* within one orbit the question is a single `𝔽₂`-linear membership test, decided by
  `mpcLadReach` alone (which by `mpcLad_reach_base_indep` does not move along the orbit);
* **between orbits nothing is claimed.**  This is where the search still lives: the orbit space
  of `mpcWordSet (j+1)` under `λ_j`-moves is not shown to be a single point, and two orbits can
  carry different cosets.  §2's `∃ p` quantifier cannot be reduced further by this argument. -/
theorem mpcLad_defect_orbit {j : ℕ}
    {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)}
    (hp1 : p.1 ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hp3 : p.2.2.1 ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    {x | ∃ us ut um un, MpcLadMove j us ut um un ∧
        x = levelMk (DM 2 0 : Type) (j + 2)
          (mpcLadDefect (p.1 * us, p.2.1 * ut, p.2.2.1 * um, p.2.2.2 * un))}
      = (fun v => levelMk (DM 2 0 : Type) (j + 2) (mpcLadDefect p) * v) ''
          mpcLadReach j p.2.1 p.2.2.2 := by
  ext x
  constructor
  · rintro ⟨us, ut, um, un, hm, rfl⟩
    refine ⟨levelMk (DM 2 0 : Type) (j + 2) (mpcBldIncr p.2.1 p.2.2.2 us ut um un),
      ⟨us, ut, um, un, hm, rfl⟩, ?_⟩
    exact (map_mul (levelMk (DM 2 0 : Type) (j + 2)) (mpcLadDefect p)
        (mpcBldIncr p.2.1 p.2.2.2 us ut um un)).symm.trans
      (mpcLad_defect_move hp1 hp3 hm.1.1.1 hm.1.2 hm.2.1.2 hm.2.2.1.1.1.1 hm.2.2.1.2
        hm.2.2.2.2).symm
  · rintro ⟨v, ⟨us, ut, um, un, hm, rfl⟩, rfl⟩
    refine ⟨us, ut, um, un, hm, ?_⟩
    exact (map_mul (levelMk (DM 2 0 : Type) (j + 2)) (mpcLadDefect p)
        (mpcBldIncr p.2.1 p.2.2.2 us ut um un)).symm.trans
      (mpcLad_defect_move hp1 hp3 hm.1.1.1 hm.1.2 hm.2.1.2 hm.2.2.1.1.1.1 hm.2.2.1.2
        hm.2.2.2.2).symm

end Reach

/-! ## §4 The class-five letters

§2 and §3 say what a rung is; this section starts computing the class-five one.  Wave 85's
class-four calculus rests on two collapses that are exactly class-four facts: `z = (B̄⁴)⁻¹` is
central in `Q₄`, and a fourth power is central there too.  In `Q₅` neither holds - `q⁴` is only a
`λ₃`-image and `q⁸` is what is central - so each of the four factors of `mWord` acquires
corrections.  This section computes the **pivot letter's fourth power**, which is the factor
wave 85 found completely blind at class four.

⭐⭐ It is **not** blind at class five.  `mpcBld_pow_letC` reads `(q²·r·μ)⁴ = r⁴` in `Q₄`; in `Q₅`

    (q²·r·μ)⁴ = r⁴ · (q⁸ · μ⁴ · ⁅μ,r⁆² · ⁅r,q²⁆²)

with all four extra factors central of order dividing two.  Two of them (`q⁸` and `⁅r,q²⁆²`) come
from the row shift `B̄²` alone and survive at `μ = 1`, so they are present in the class-four
witness itself.  That is the first exact class-five term of the `M6` defect. -/

section ClassFive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every square is a `λ₂`-image, in `Q₅`. -/
theorem mpcLad_five_sq_mem_two (p : levelQuot G 5) : p ^ 2 ∈ lambdaImage G 2 5 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 5 p
  exact ⟨a ^ 2, sq_mem_twoCentralSeries_succ G (Subgroup.mem_top a), by rw [map_pow]⟩

/-- The square of a `λ₂`-image is a `λ₃`-image, in `Q₅`. -/
theorem mpcLad_five_sq_mem_three {y : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5) :
    y ^ 2 ∈ lambdaImage G 3 5 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G hv, by rw [map_pow]⟩

theorem mpcLad_five_three_le_two {y : levelQuot G 5} (hy : y ∈ lambdaImage G 3 5) :
    y ∈ lambdaImage G 2 5 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v, twoCentralSeries_antitone (G := G) (by omega : (2 : ℕ) ≤ 3) hv, rfl⟩

/-- ⁅`λ₂`, `λ₃`⁆ dies in `Q₅`: `cfive_commutator_lambdaTwo` at `k = 3`, read downstairs.  This is
the single fact that replaces class four's "`λ₂` is abelian". -/
theorem mpcLad_five_vanish {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : commP y ε = 1 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hε
  have h : commP (levelMk G 5 v) (levelMk G 5 w) = levelMk G 5 (commP v w) := by
    simp only [commP, map_mul, map_inv]
  rw [h]
  exact (lim_mem_twoCentralSeries_iff_levelMk 5 _).mp (cfive_commutator_lambdaTwo_swap hw hv)

/-- The same with the slots exchanged. -/
theorem mpcLad_five_vanish' {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : commP ε y = 1 := by
  have h : commP ε y = (commP y ε)⁻¹ := by simp only [commP]; group
  rw [h, mpcLad_five_vanish hy hε, inv_one]

theorem mpcLad_five_commute {y ε : levelQuot G 5} (hy : y ∈ lambdaImage G 2 5)
    (hε : ε ∈ lambdaImage G 3 5) : Commute ε y :=
  cfour_commute_of_comm (mpcLad_five_vanish' hy hε)

/-- A `λ₂`-image in the right slot of a bracket produces a `λ₃`-image. -/
theorem mpcLad_five_commP_mem_three_right (x : levelQuot G 5) {y : levelQuot G 5}
    (hy : y ∈ lambdaImage G 2 5) : commP x y ∈ lambdaImage G 3 5 := by
  have h : commP x y = (commP y x)⁻¹ := by simp only [commP]; group
  rw [h]
  exact (lambdaImage G 3 5).inv_mem (cfive_commP_lambdaTwo_mem_lambdaThree hy x)

/-- **The square of a `λ₂`-image times a `λ₃`-image splits**, because the two commute in `Q₅`. -/
theorem mpcLad_five_sq_split {x y : levelQuot G 5} (hx : x ∈ lambdaImage G 2 5)
    (hy : y ∈ lambdaImage G 3 5) : (x * y) ^ 2 = x ^ 2 * y ^ 2 :=
  (mpcLad_five_commute hx hy).symm.mul_pow 2

/-- **A central factor drops out of a square** in `Q₅`, the layer being of exponent two. -/
theorem mpcLad_five_sq_drop {x z : levelQuot G 5} (hz : z ∈ zLayer G 4) :
    (x * z) ^ 2 = x ^ 2 := by
  rw [cfour_sq_mul, cfive_commP_zLayer_left hz x, cfour_one_comm, mul_one, mul_one,
    zLayer_sq G hz, mul_one]

/-- **The correction is invisible in the squared shift bracket**: the two brackets differ by
`⁅μ, q²⁆`, which is central of order dividing two, so it dies on squaring. -/
theorem mpcLad_five_commP_sq_drop {r μ v : levelQuot G 5} (hμ : μ ∈ lambdaImage G 2 5)
    (hv : v ∈ lambdaImage G 2 5) : commP (r * μ) v ^ 2 = commP r v ^ 2 := by
  have h1 : commP (r * μ) v = commP r v * commP μ v := by
    rw [cfour_commP_mul_left,
      mpcLad_five_vanish' hμ (mpcLad_five_commP_mem_three_right r hv), mul_one]
  have h2 : commP μ v ∈ zLayer G 4 := cfive_commP_lambdaTwo_mem_zLayer hμ hv
  rw [h1, (zLayer_commute h2 (commP r v)).symm.mul_pow 2, zLayer_sq G h2, mul_one]

/-- ⭐⭐ **THE PIVOT LETTER'S FOURTH POWER AT CLASS FIVE.**  Wave 85's `mpcBld_pow_letC` reads
`(q²·r·μ)⁴ = r⁴` in `Q₄`: the fourth power is blind to the whole row shift and to the
correction.  One class up it is not.  Four central factors survive, and two of them
(`q⁸` and `⁅r,q²⁆²`) do not involve the correction at all, so they are already present in the
class-four witness. -/
theorem mpcLad_pow_letC_five (q r : levelQuot G 5) {μ : levelQuot G 5}
    (hμ : μ ∈ lambdaImage G 2 5) :
    (q ^ 2 * r * μ) ^ 4
      = r ^ 4 * (q ^ 8 * (μ ^ 4 * (commP μ r ^ 2 * commP r (q ^ 2) ^ 2))) := by
  have e4 : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have e8 : (q ^ 4) ^ 2 = q ^ 8 := by rw [← pow_mul]
  have hv : q ^ 2 ∈ lambdaImage G 2 5 := mpcLad_five_sq_mem_two q
  have hq4 : q ^ 4 ∈ lambdaImage G 3 5 := cfive_pow_four_mem_lambdaThree q
  have hq8 : q ^ 8 ∈ zLayer G 4 := cfive_pow_eight_mem_zLayer q
  -- Step B: the fourth power of `r * μ`
  have hcm : commP μ r ∈ lambdaImage G 3 5 := cfive_commP_lambdaTwo_mem_lambdaThree hμ r
  have hμ2 : μ ^ 2 ∈ lambdaImage G 3 5 := mpcLad_five_sq_mem_three hμ
  have hT' : μ ^ 2 * commP μ r ∈ lambdaImage G 3 5 := Subgroup.mul_mem _ hμ2 hcm
  have hB2 : (r * μ) ^ 2 = r ^ 2 * (μ ^ 2 * commP μ r) := by
    rw [cfour_sq_mul, mpcLad_five_vanish' hμ hcm, mul_one, mul_assoc]
  have hB4 : (r * μ) ^ 4 = r ^ 4 * (μ ^ 4 * commP μ r ^ 2) := by
    have h : (r * μ) ^ 4 = ((r * μ) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h, hB2, mpcLad_five_sq_split (mpcLad_five_sq_mem_two r) hT',
      (mpcLad_five_commute (mpcLad_five_three_le_two hcm) hμ2).mul_pow 2,
      show ((r : levelQuot G 5) ^ 2) ^ 2 = r ^ 4 from by rw [← pow_mul],
      show ((μ : levelQuot G 5) ^ 2) ^ 2 = μ ^ 4 from by rw [← pow_mul]]
  -- Step A: the fourth power of the whole letter
  have hR2 : (r * μ) ^ 2 ∈ lambdaImage G 2 5 := mpcLad_five_sq_mem_two _
  have hT : commP (r * μ) (q ^ 2) ∈ lambdaImage G 3 5 :=
    mpcLad_five_commP_mem_three_right _ hv
  have hM : commP (commP (r * μ) (q ^ 2)) (r * μ) ∈ zLayer G 4 :=
    cfive_commP_mem_zLayer_left hT _
  have hS : q ^ 4 * (r * μ) ^ 2 ∈ lambdaImage G 2 5 :=
    Subgroup.mul_mem _ (mpcLad_five_three_le_two hq4) hR2
  have hA2 : (q ^ 2 * (r * μ)) ^ 2
      = q ^ 4 * (r * μ) ^ 2 * commP (r * μ) (q ^ 2) *
        commP (commP (r * μ) (q ^ 2)) (r * μ) := by
    rw [cfour_sq_mul, e4]
  have hA4 : (q ^ 2 * (r * μ)) ^ 4
      = q ^ 8 * (r * μ) ^ 4 * commP (r * μ) (q ^ 2) ^ 2 := by
    have h : (q ^ 2 * (r * μ)) ^ 4 = ((q ^ 2 * (r * μ)) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h, hA2, mpcLad_five_sq_drop hM, mpcLad_five_sq_split hS hT,
      (mpcLad_five_commute hR2 hq4).mul_pow 2, e8,
      show ((r * μ : levelQuot G 5) ^ 2) ^ 2 = (r * μ) ^ 4 from by rw [← pow_mul]]
  have hq8c : ∀ x : levelQuot G 5, q ^ 8 * x = x * q ^ 8 := fun x => (zLayer_commute hq8 x).eq
  calc (q ^ 2 * r * μ) ^ 4 = (q ^ 2 * (r * μ)) ^ 4 := by rw [mul_assoc]
    _ = q ^ 8 * (r * μ) ^ 4 * commP (r * μ) (q ^ 2) ^ 2 := hA4
    _ = q ^ 8 * (r ^ 4 * (μ ^ 4 * commP μ r ^ 2)) * commP r (q ^ 2) ^ 2 := by
        rw [hB4, mpcLad_five_commP_sq_drop hμ hv]
    _ = r ^ 4 * (q ^ 8 * (μ ^ 4 * (commP μ r ^ 2 * commP r (q ^ 2) ^ 2))) := by
        rw [← mul_assoc (q ^ 8) (r ^ 4), hq8c (r ^ 4)]
        group

/-- **The pivot letter itself, at class five.**  `mpcLad_pow_letC_five` transported to the `M6`
`C̄₀`-letter `B̄²·C̄₀·m` on `D_M 2 0`.  Wave 85's class-four reading of this factor is `C̄₀⁴`; the
class-five reading carries `B̄⁸`, `m⁴`, `⁅m, C̄₀⁆²` and `⁅C̄₀, B̄²⁆²` on top of it. -/
theorem mpcLad_letC_pow_five (m : (DM 2 0 : Type))
    (hm : m ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    levelMk (DM 2 0 : Type) 5 (mpcWordLetC m) ^ 4
      = levelMk (DM 2 0 : Type) 5 (dmC 2 0) ^ 4 *
        (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 8 *
          (levelMk (DM 2 0 : Type) 5 m ^ 4 *
            (commP (levelMk (DM 2 0 : Type) 5 m) (levelMk (DM 2 0 : Type) 5 (dmC 2 0)) ^ 2 *
              commP (levelMk (DM 2 0 : Type) 5 (dmC 2 0))
                (levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2) ^ 2))) := by
  have h : levelMk (DM 2 0 : Type) 5 (mpcWordLetC m)
      = levelMk (DM 2 0 : Type) 5 (dmB 2 0) ^ 2 * levelMk (DM 2 0 : Type) 5 (dmC 2 0) *
        levelMk (DM 2 0 : Type) 5 m := by
    rw [mpcWordLetC, map_mul, map_mul, map_pow]
  rw [h]
  exact mpcLad_pow_letC_five _ _ ⟨m, hm, rfl⟩

end ClassFive

/-! ## §5 The class-five rung, named

The residue of `MpcPivShift 2` starts at class five (`mpcBld_shift_of_forall_class_five`), and by
§2 the class-five rung is an iff against the class-four solution set, whose nonemptiness is a
theorem (`mpcBld_nonempty_four`, witness `mpcLadW4`).  So the next question in the campaign has a
name and a shape: **is there a class-four solution whose defect lies in the `𝔽₂`-subspace
`mpcLadReach 3`?**  Neither answer is claimed here.

[W87-FIVE: answered YES, inside `mpcLadW4`'s own orbit (`mpcFv_supply_witness`, move
`(1, B̄⁴, 1, B̄⁴·⁅B̄²,D̄⁆)`); hence `mpcFv_nonempty_five` via this section's iff, and the residue
starts at class SIX.  See `MpcFive.lean`.] -/

section RungFive

/-- ⭐ **THE CLASS-FIVE RUNG.**  `mpcLad_nonempty_iff` at `j = 3`, where the class-`(j+1)`
solution set is the class-four one and is known nonempty. -/
theorem mpcLad_nonempty_five_iff :
    (mpcWordSet 5).Nonempty ↔ ∃ p ∈ mpcWordSet 4, MpcLadSupply 3 p :=
  mpcLad_nonempty_iff 3

/-- **The class-five ANSATZ refutation, spelled out.**  If no class-four solution has one-step
supply at class three, the class-five solution set is empty, which refutes the `M6` ansatz.

[W87-HOUSE, as of `1541635f`: two corrections, neither touching the statement.

(1) **The headline said "the class-five refutation" unqualified.**  The scope block at
`mpcLad_eq_empty_of_no_supply` says "throughout this docstring", so it does not reach here, and
this was the fourth site of wave 86's inversion, 470 lines below the three that were scoped.
Emptying `mpcWordSet 5` refutes the ANSATZ; it refutes `MpcPivShift 2` only if the ansatz is
exhaustive among the markings `mpcOrb_shift_iff_marking` quantifies over, which is not proved.

(2) **The citation ran the wrong way and is dropped.**  This claim was attributed to
`mpcWord_shift_of_forall_class`, which is `(∀ k, (mpcWordSet k).Nonempty) → MpcPivShift 2`
(`MpcWord.lean`).  Its contrapositive gives `¬ MpcPivShift 2 → ∃ k, mpcWordSet k = ∅`, i.e.
emptiness FROM a refutation, never a refutation from emptiness, so it supports neither reading.
That an empty rung refutes the ansatz needs no citation at all: a quadruple of corrections
solving `mWord ... = 1` lies in every `mpcWordSet k`, since every `twoCentralSeries` term
contains `1`, so a single empty rung leaves no solution anywhere.  The separate
normative claim, that a PROVEN empty rung is the only admissible negative evidence and a stalled
walk is none, is wave 84 §5's control and is not a consequence of that theorem either.] -/
theorem mpcLad_five_empty_of_no_supply
    (H : ∀ p ∈ mpcWordSet 4, ¬ MpcLadSupply 3 p) : mpcWordSet 5 = ∅ :=
  mpcLad_eq_empty_of_no_supply H

end RungFive

/-! ## §6 Axiom pins

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
#print axioms mpcLad_vanish
#print axioms mpcLad_sq_mem_zLayer
#print axioms mpcLad_commP_left_add
#print axioms mpcLad_commP_right_add
#print axioms mpcLad_sq_add
#print axioms mpcLad_commP_mem_two
#print axioms mpcLad_commP_drop
#print axioms mpcLad_incr_mem_zLayer
#print axioms mpcLad_incr_hom
#print axioms mpcLadReach
#print axioms mpcLad_reach_subset_zLayer
#print axioms mpcLad_reach_one_mem
#print axioms mpcLad_reach_mul_mem
#print axioms mpcLad_reach_inv_mem
#print axioms mpcLadReachSub
#print axioms mpcLadReachSub_coe
#print axioms mpcLad_reach_sq
#print axioms mpcLad_reach_base_indep
#print axioms mpcLad_defect_orbit
#print axioms mpcLad_five_sq_mem_two
#print axioms mpcLad_five_sq_mem_three
#print axioms mpcLad_five_three_le_two
#print axioms mpcLad_five_vanish
#print axioms mpcLad_five_vanish'
#print axioms mpcLad_five_commute
#print axioms mpcLad_five_commP_mem_three_right
#print axioms mpcLad_five_sq_split
#print axioms mpcLad_five_sq_drop
#print axioms mpcLad_five_commP_sq_drop
#print axioms mpcLad_pow_letC_five
#print axioms mpcLad_letC_pow_five
#print axioms mpcLad_nonempty_five_iff
#print axioms mpcLad_five_empty_of_no_supply

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcLad
