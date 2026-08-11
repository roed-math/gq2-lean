/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedStageSeparate

/-!
# W63-FOUR: the achievable lattice at wave 61's FOUR gap markings, bounded with index-16 slack

Wave 61 proved `stageForces_iff_stageCentral` and recorded the strictness of the parity line
`StageOrth` as a **measurement**: four of 1650 admissible markings at which the parity line
FAILS and the stage-four forcing HOLDS.  Wave 62 could not prove the four and diagnosed why: at
each of them the forcing reads the achievable lattice **mod 4 or finer**, and no per-coordinate
congruence, no mod-`2` linear condition on the lattice image, and no letter-column chain
reaches it (`scripts/w62_separate/results/diagnose.txt`, `mod2_probe.txt`, `feasible3.txt`).

That diagnosis is correct, and this file does not contradict it.  What it does is stop
relaxing the lattice.

## ⭐⭐⭐ Headline 1: THE CHAIN NEVER HAD TO NAME A SUBGROUP CONTAINING THE IMAGE

Every earlier bound on `forceLcs H 2 = [[H, H], H]` in this tree runs `Subgroup.commutator_le`
twice, and that quantifies over ALL of `H`, so it needs a **named** subgroup `K0` containing the
image, and the arithmetic of the letters is then lost to whatever congruence defines `K0`.
Wave 62's three impossibility measurements are all measurements about that `K0`.

⭐⭐⭐ `le_of_gens_three` / `forceLcs_two_le_of_gens`: if `K` is **normalised by** `closure S`
and contains the weight-three bracket `[[s, t], u]` of every triple of GENERATORS, then
`[[closure S, closure S], closure S] <= K`.  No `K0` appears.  The proof is two reductions to
generators, `commutator_mem_of_gens_left` and `commutator_mem_of_gens_right`, each of which
works because `{g normalising K : [p, g] in K}` is a subgroup - the identities
`[p, u v] = [p, u] * (u [p, v] u⁻¹)` and `[p q, u] = (p [q, u] p⁻¹) * [p, u]` need exactly
the normalisation and nothing else - and the middle term of the chain is `commAll K H`,
itself normalised by `H`.

⚠ **The normalisation is load-bearing and it is normalisation by the IMAGE, not by the whole
carrier.**  Measured (`scripts/w63_four/results/normal_chain.txt`): at `gap-2` the smallest
subgroup normal in the whole carrier that contains the brackets is four times too big and NO
certificate survives on it; normalised by the image only, the bound is the lattice exactly.

## ⭐⭐⭐ Headline 2: THE FOUR MARKINGS, WITH THEIR LATTICES BOUNDED

⭐⭐⭐ `forceLcs_two_le_gapOneA`, `forceLcs_two_le_gapOneB`, `forceLcs_two_le_gapTwoA`,
`forceLcs_two_le_gapTwoB`: at each of wave 61's four gap markings, at every handle count and
every handle, every achievable stage-four dressing satisfies explicit `Z/8`-linear conditions:

* `gap-1` (`gapKOne`): `2 k + 4 m + 4 n = 0` and `2 l + 4 n = 0`, that is `k + 2m + 2n` and
  `l + 2n` vanish **mod 4**;
* `gap-2` (`gapKTwo`): `k + 4 n = 0`, `4 l = 0` and `2 m = 0`.

⚠ **For `gapKOne` neither condition is a per-coordinate congruence and neither is visible mod
`2`**: `gapKOne` forces `k` and `l` even but that is strictly weaker than either condition, and
wave 62 measured that the even-`k`, even-`l` relaxation does not repair the implication.

⚠ **For `gapKTwo` that is false of two of the three conditions.**  Over `ZMod 8`, `4 l = 0` is
exactly "`l` is even" and `2 m = 0` is exactly "`4 ∣ m`": both are per-coordinate congruences, so
only `k + 4 n = 0` is a genuine two-coordinate relation there.  And `4 l = 0` is the one
condition of the three that a mod-`2` reading of the coordinates DOES see; the other two it does
not.

The whole arithmetic input is the `216` weight-three brackets of the six slot values, one
`decide` on `ZMod 8` per marking.

The normalisation is supplied by a single column: every `gap-1` letter has an EVEN `(4,5)`-column
and every `gap-2` letter has one divisible by `4` (`gapEvenD`, `gapQuadD`), and by
`gaThree_conj_m`/`gaThree_conj_n` conjugation moves the class-four rows by `g.a * z.k - z.j * g.d`
and `g.b * z.l - z.k * g.e`, of which the target's own conditions kill three terms and the
column kills the fourth.

## ⭐⭐ Headline 3: WHAT REMAINS, STATED EXACTLY

⭐⭐ `stageForces_gapOneA_of_psi` and its three siblings: **given** that the certificate
functional `psiOne = l + 2 n + 4 o` (respectively `psiTwo = m + 4 o`) kills the stage-four shift
of every dressing whose slots lie in the target, the forcing HOLDS at that marking, at every
handle count and every handle.  The lattice half of the argument is discharged; the remaining
hypothesis is one `Z/8`-linear identity about `gaThreeShift`, and section 4 of the note says
what proving it needs.

## PROVED versus MEASURED

**PROVED**: the generator reduction, in any group; the `gamma_3` conjugation and inversion
calculus; the four markings and their relators (`SqU6.liftO 5` and `SqU6.liftO 1`, central with
ODD residues, by `sqRelWord_gapOneMark` and its three siblings); the two target subgroups,
their normalisation along the respective column, the `216 * 4` bracket memberships and hence the
four lattice bounds; and the reduction of the forcing to the certificate identity.

⚠ **NOT proved here**: that the four markings are ADMISSIBLE, and that the forcing's conclusion
`selPar (sqRelWord ...).o = 0` is FALSE at them.  Both are one-line consequences of the relator
values, but there is no admissibility predicate anywhere in the tree and no theorem in this file
states `selPar (sqRelWord ...).o = 1`, so neither is a statement this file owns.

**MEASURED**, and NOT proved: (i) the certificate identity itself, that
`psiOne (gaThreeShift h m z) = 0` for every `z` with slots in `gapKOne` (and the `psiTwo`
analogue); (ii) that no achievable dressing kills, that the parity line fails and that the sharp
line holds at all four.  `scripts/w63_four/results/certify.txt` runs **40** named checks with
**0** failures on wave 59's honest `6 x 6` matrices through wave 61's `sharp4lib`, including the
certificate identity on **all 16384** members of `gapKOne` at each of the five slots and on a
spanning family of five-slot tuples; `lean_match.txt` adds **24** more checking, coordinate by
coordinate, that this file's twelve letters, two targets and two certificates are exactly the
measured ones and not a transcription of them.

⚠ **The certificate is exactly the annihilator of the target.**  `gapKOne` is by construction
the joint kernel of the five slot pullbacks of `psiOne`, so the identity is not an extra
arithmetic accident: it is the linearity of `gaThreeShift` in the dressing tuple
(`gaThreeShift_mul`) applied to a subgroup that was chosen to make it hold.  What a Lean proof
still has to supply is the closed form of those five pullbacks, which means expanding
`gaThreeCore`, `gaThreeHandle` and the two block terms at the concrete letters.

⚠ **Slack.**  The targets are strictly bigger than the honest lattices - index `16` at `gap-1`
(1024 inside 16384) and `16` at `gap-2` (256 inside 4096).  That slack is deliberate: it makes
the conditions short enough to state and to conjugate, and the certificate survives all of it.

## Sweep against the tree's refutations

The four markings are wave 61's, re-derived by wave 62 and re-derived again here from the same
recorded letters; nothing here quotes the retracted wave-56 carried-input structures, nothing
here is a general criterion in the sense wave 60's three-covector line failed to be, and nothing
here widens the `gamma_2` route that wave 62 closed by a functional collision.  The bound is a
statement about ONE lattice at FOUR named markings, and the generator reduction of section 1 is
the only part offered for reuse.

## Contents

* **1** ⭐⭐⭐ the generator reduction; **2** ⭐ conjugation and inversion on `gamma_3`;
* **3** the four markings and their relators; **4** ⭐⭐ the two targets and their normalisation;
* **5** ⭐⭐⭐ the four lattice bounds; **6** ⭐⭐ the forcing, modulo one identity;
* **7** axiom pins.

## Merge notes

Reused: `forceLcs`, `isGaThree_of_mem_forceLcs`, `SqU6.IsGaThree`, `SqU6.isGaThree_one`,
`SqU6.IsGaThree.mul`, `SqU6.gaThree_mul_k/_l/_m/_n`, `gaThreeShift`, `sqRelWord_gaThreeDress`
(`GradedFiveStageFour`, `GradedFiveForce`, `GradedStageNecessity`); `StageForces`
(`GradedStageNecessity`); `fiveTuple`, `sqRelWord_fiveTuple`, `sqRank`, `SqU6.liftO`
(`GradedFive`, `Cores`); the `SqU6.mul_*` and `SqU6.inv_*` coordinate lemmas.  The private
`gapTuple_cases` is a third copy of the slot-case split that `GradedFiveStageFour`,
`GradedStageNecessity` and `GradedStageSeparate` each keep private.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `Fin 6` or tuples
over them.  All **75** committed prints are subsets of `[propext, Classical.choice, Quot.sound]`:
`31` std-3, `39` `propext` + `Quot.sound`, `5` `propext` alone.  No census axiom is consumed.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

/-! ## 1 The generator reduction -/

section GenReduce

variable {G : Type*} [Group G] {K H : Subgroup G} {S : Set G}

/-- Conjugation-stability upgrades to membership of the normaliser, because the inverse of a
normalising element normalises too. -/
theorem subset_normalizer_of_conj {N : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    (H : Set G) ⊆ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [SetLike.mem_coe] at hg ⊢
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  simpa [mul_assoc] using h g⁻¹ (inv_mem hg) _ hx

/-- `{g normalising K : [g, t] in K}`.  A subgroup, because
`[p * q, t] = (p * [q, t] * p⁻¹) * [p, t]` and `p` normalises `K`. -/
def commLeft (K : Subgroup G) (t : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅g, t⁆ ∈ K}
  mul_mem' := by
    rintro p q ⟨hp, hpt⟩ ⟨hq, hqt⟩
    refine ⟨mul_mem hp hq, ?_⟩
    have hid : ⁅p * q, t⁆ = p * ⁅q, t⁆ * p⁻¹ * ⁅p, t⁆ := by group
    exact hid ▸ mul_mem ((Subgroup.mem_normalizer_iff.mp hp _).mp hqt) hpt
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := by
    rintro p ⟨hp, hpt⟩
    refine ⟨inv_mem hp, ?_⟩
    have hid : ⁅p⁻¹, t⁆ = p⁻¹ * ⁅p, t⁆⁻¹ * p⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hp) _).mp (inv_mem hpt)

theorem mem_commLeft {t g : G} :
    g ∈ commLeft K t ↔ g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅g, t⁆ ∈ K := Iff.rfl

/-- `{g normalising K : [p, g] in K}`.  A subgroup, because
`[p, u * v] = [p, u] * (u * [p, v] * u⁻¹)` and `u` normalises `K`. -/
def commRight (K : Subgroup G) (p : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅p, g⁆ ∈ K}
  mul_mem' := by
    rintro u v ⟨hu, hpu⟩ ⟨hv, hpv⟩
    refine ⟨mul_mem hu hv, ?_⟩
    have hid : ⁅p, u * v⁆ = ⁅p, u⁆ * (u * ⁅p, v⁆ * u⁻¹) := by group
    exact hid ▸ mul_mem hpu ((Subgroup.mem_normalizer_iff.mp hu _).mp hpv)
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := by
    rintro u ⟨hu, hpu⟩
    refine ⟨inv_mem hu, ?_⟩
    have hid : ⁅p, u⁻¹⁆ = u⁻¹ * ⁅p, u⁆⁻¹ * u⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hu) _).mp (inv_mem hpu)

theorem mem_commRight {p g : G} :
    g ∈ commRight K p ↔ g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅p, g⁆ ∈ K := Iff.rfl

/-- ⭐ **Reduction on the right**: a commutator into a subgroup normalised by `closure S` need
only be tested against the generators `S`. -/
theorem commutator_mem_of_gens_right
    (hS : S ⊆ Subgroup.normalizer (K : Set G)) {p : G}
    (hp : ∀ t ∈ S, ⁅p, t⁆ ∈ K) {u : G} (hu : u ∈ Subgroup.closure S) :
    ⁅p, u⁆ ∈ K :=
  (mem_commRight.mp
    ((Subgroup.closure_le (commRight K p)).mpr
      (fun t ht => mem_commRight.mpr ⟨hS ht, hp t ht⟩) hu)).2

/-- ⭐ **Reduction on the left**: …and only against the generators on the left as well. -/
theorem commutator_mem_of_gens_left
    (hS : S ⊆ Subgroup.normalizer (K : Set G)) {t : G}
    (ht : ∀ s ∈ S, ⁅s, t⁆ ∈ K) {p : G} (hp : p ∈ Subgroup.closure S) :
    ⁅p, t⁆ ∈ K :=
  (mem_commLeft.mp
    ((Subgroup.closure_le (commLeft K t)).mpr
      (fun s hs => mem_commLeft.mpr ⟨hS hs, ht s hs⟩) hp)).2

/-- `{p normalising K : [p, u] in K for every u in H}`: where the middle term of the chain has
to land. -/
def commAll (K H : Subgroup G) : Subgroup G where
  carrier := {p | p ∈ Subgroup.normalizer (K : Set G) ∧ ∀ u ∈ H, ⁅p, u⁆ ∈ K}

  mul_mem' := by
    rintro p q ⟨hp, hpu⟩ ⟨hq, hqu⟩
    refine ⟨mul_mem hp hq, fun u hu => ?_⟩
    have hid : ⁅p * q, u⁆ = p * ⁅q, u⁆ * p⁻¹ * ⁅p, u⁆ := by group
    exact hid ▸ mul_mem ((Subgroup.mem_normalizer_iff.mp hp _).mp (hqu u hu)) (hpu u hu)
  one_mem' := ⟨one_mem _, fun u _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := by
    rintro p ⟨hp, hpu⟩
    refine ⟨inv_mem hp, fun u hu => ?_⟩
    have hid : ⁅p⁻¹, u⁆ = p⁻¹ * ⁅p, u⁆⁻¹ * p⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hp) _).mp (inv_mem (hpu u hu))

theorem mem_commAll {p : G} :
    p ∈ commAll K H ↔ p ∈ Subgroup.normalizer (K : Set G) ∧ ∀ u ∈ H, ⁅p, u⁆ ∈ K :=
  Iff.rfl

/-- `commAll K H` is normalised by `H` as soon as `K` is: the conjugation passes through both
arguments, `[r x r⁻¹, u] = r * [x, r⁻¹ u r] * r⁻¹`. -/
theorem le_normalizer_commAll
    (hH : (H : Set G) ⊆ Subgroup.normalizer (K : Set G)) :
    (H : Set G) ⊆ Subgroup.normalizer ((commAll K H : Subgroup G) : Set G) := by
  refine subset_normalizer_of_conj (H := H) fun r hr x hx => ?_
  obtain ⟨hxn, hxu⟩ := mem_commAll.mp hx
  refine mem_commAll.mpr ⟨mul_mem (mul_mem (hH hr) hxn) (inv_mem (hH hr)), fun u hu => ?_⟩
  have hid : ⁅r * x * r⁻¹, u⁆ = r * ⁅x, r⁻¹ * u * r⁆ * r⁻¹ := by group
  exact hid ▸ (Subgroup.mem_normalizer_iff.mp (hH hr) _).mp
    (hxu _ (mul_mem (mul_mem (inv_mem hr) hu) hr))

/-- ⭐⭐⭐ **THE GENERATOR REDUCTION FOR THE STAGE-FOUR LATTICE.**  If `K` is normalised by the
image `closure S` and contains the weight-three bracket `[[s, t], u]` of every triple of
GENERATORS, then it contains the whole achievable lattice `forceLcs (closure S) 2`.

This is what stops the argument from relaxing the achievable lattice: the bound is the
`closure S`-normal closure of finitely many explicit elements, so it reads the lattice mod `8`,
not mod `2` or mod `4`.  ⚠ It is a one-sided containment, and it does **not** by itself say that
the reduction loses nothing; that the bracket condition is not merely sufficient but EQUIVALENT
to containing the series term, among subgroups normalised by `S`, is the separate statement
`LcsGens.lcsSeries_le_iff_of_gens` of `GradedLcsGens`.  Both reductions are needed - the left one
by `commLeft`, the right one by `commRight` - and both need `K` to be normalised, which is why
the statement is about a normalised `K` rather than an arbitrary one. -/
theorem le_of_gens_three {K : Subgroup G} {S : Set G}
    (hS : S ⊆ Subgroup.normalizer (K : Set G))
    (hbr : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, ⁅⁅s, t⁆, u⁆ ∈ K) :
    ⁅⁅Subgroup.closure S, Subgroup.closure S⁆, Subgroup.closure S⁆ ≤ K := by
  set H := Subgroup.closure S with hH
  have hHn : (H : Set G) ⊆ Subgroup.normalizer (K : Set G) := by
    rw [hH]
    exact fun x hx => (Subgroup.closure_le _).mpr hS hx
  set D := commAll K H with hD
  have hDn : (H : Set G) ⊆ Subgroup.normalizer ((D : Subgroup G) : Set G) :=
    le_normalizer_commAll hHn
  have hSD : S ⊆ Subgroup.normalizer ((D : Subgroup G) : Set G) := fun s hs =>
    hDn (Subgroup.subset_closure hs)
  -- every basic commutator lands in `D`
  have hbase : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ D := by
    intro s hs t ht
    refine mem_commAll.mpr ⟨mul_mem (mul_mem (mul_mem (hS hs) (hS ht)) (inv_mem (hS hs)))
      (inv_mem (hS ht)), fun u hu => ?_⟩
    exact commutator_mem_of_gens_right hS (fun v hv => hbr s hs t ht v hv) hu
  -- …hence so does every commutator of the image, by the two reductions
  have hDD : ⁅H, H⁆ ≤ D := by
    refine Subgroup.commutator_le.mpr fun p hp q hq => ?_
    refine commutator_mem_of_gens_right hSD (p := p) (fun t ht => ?_) hq
    exact commutator_mem_of_gens_left hSD (fun s hs => hbase s hs t ht) hp
  refine Subgroup.commutator_le.mpr fun p hp u hu => ?_
  exact (mem_commAll.mp (hDD hp)).2 u hu

/-- …in the shape the tree states achievability. -/
theorem forceLcs_two_le_of_gens {S : Set (SqU6 gr3R)} {K : Subgroup (SqU6 gr3R)}
    (hS : S ⊆ Subgroup.normalizer (K : Set (SqU6 gr3R)))
    (hbr : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, ⁅⁅s, t⁆, u⁆ ∈ K) :
    forceLcs (Subgroup.closure S) 2 ≤ K :=
  le_of_gens_three hS hbr

end GenReduce


/-! ## 2 Conjugation on `gamma_3` -/

section Conj

variable {R : Type} [CommRing R] {z g : SqU6 R}

theorem gaThree_conj_j (hz : z.IsGaThree) : (g * z * g⁻¹).j = z.j := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.mul_j, SqU6.mul_a, SqU6.mul_f, SqU6.inv_j, SqU6.inv_g, SqU6.inv_c,
    za, zb, zc, zf, zg]
  ring

theorem gaThree_conj_k (hz : z.IsGaThree) : (g * z * g⁻¹).k = z.k := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.mul_k, SqU6.mul_b, SqU6.mul_g, SqU6.inv_k, SqU6.inv_h, SqU6.inv_d,
    zb, zc, zd, zg, zh]
  ring

theorem gaThree_conj_l (hz : z.IsGaThree) : (g * z * g⁻¹).l = z.l := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.mul_l, SqU6.mul_c, SqU6.mul_h, SqU6.inv_l, SqU6.inv_i, SqU6.inv_e,
    zc, zd, ze, zh, zi]
  ring

/-- ⭐ **The first class-four row moves by the `(a, d)`-pairing.**  Conjugating a
`gamma_3`-element leaves its class-three row alone and shifts the class-four row by
`g.a * z.k - z.j * g.d`. -/
theorem gaThree_conj_m (hz : z.IsGaThree) :
    (g * z * g⁻¹).m = z.m + g.a * z.k - z.j * g.d := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.mul_m, SqU6.mul_a, SqU6.mul_f, SqU6.mul_j, SqU6.inv_m, SqU6.inv_k,
    SqU6.inv_h, SqU6.inv_d, za, zb, zc, zd, zf, zg, zh]
  ring

/-- …and the second by the `(b, e)`-pairing. -/
theorem gaThree_conj_n (hz : z.IsGaThree) :
    (g * z * g⁻¹).n = z.n + g.b * z.l - z.k * g.e := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.mul_n, SqU6.mul_b, SqU6.mul_g, SqU6.mul_k, SqU6.inv_n, SqU6.inv_l,
    SqU6.inv_i, SqU6.inv_e, zb, zc, zd, ze, zg, zh, zi]
  ring

theorem gaThree_conj_isGaThree (hz : z.IsGaThree) :
    (g * z * g⁻¹).IsGaThree := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d,
      SqU6.inv_e, SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, za, zb, zc, zd, ze, zf, zg,
      zh, zi] <;>
    ring

theorem gaThree_inv_isGaThree (hz : z.IsGaThree) : (z⁻¹).IsGaThree := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, za, zb, zc, zd, ze, zf, zg, zh, zi] <;>
    ring

theorem gaThree_inv_k (hz : z.IsGaThree) : (z⁻¹).k = -z.k := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.inv_k, zb, zc, zd, zg, zh]
  ring

theorem gaThree_inv_l (hz : z.IsGaThree) : (z⁻¹).l = -z.l := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.inv_l, zc, zd, ze, zh, zi]
  ring

theorem gaThree_inv_m (hz : z.IsGaThree) : (z⁻¹).m = -z.m := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.inv_m, za, zb, zc, zd, zf, zg, zh]
  ring

theorem gaThree_inv_n (hz : z.IsGaThree) : (z⁻¹).n = -z.n := by
  obtain ⟨za, zb, zc, zd, ze, zf, zg, zh, zi⟩ := hz
  simp only [SqU6.inv_n, zb, zc, zd, ze, zg, zh, zi]
  ring

end Conj

/-! ## 3 The four gap markings and their exact lattice bound -/

section GapPoints

variable {h : ℕ} {j : Fin h}

/-- The `sigma`-slot of wave 61's first gap pair. -/
def gapOneS : SqU6 gr3R := ⟨5, 2, 3, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0⟩

/-- Its `x0`-slot. -/
def gapOneX : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 7, 0⟩

/-- Its `x1`-slot, in the `gap-1a` member of the pair. -/
def gapOneY : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0⟩

/-- …and in the `gap-1b` member: the two differ only in the `x1`-slot's class-four row. -/
def gapOneY' : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 4, 0⟩

/-- Its handle-`U` letter. -/
def gapOneU : SqU6 gr3R := ⟨0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0⟩

/-- Its handle-`V` letter. -/
def gapOneV : SqU6 gr3R := ⟨0, 3, 0, 6, 3, 2, 0, 1, 0, 0, 1, 1, 0, 0, 7⟩

/-- The `sigma`-slot of the second gap pair. -/
def gapTwoS : SqU6 gr3R := ⟨1, 7, 3, 0, 5, 1, 0, 0, 0, 0, 3, 7, 6, 0, 1⟩

/-- Its `x0`-slot. -/
def gapTwoX : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7⟩

/-- Its `x1`-slot, in `gap-2a`. -/
def gapTwoY : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0⟩

/-- …and in `gap-2b`. -/
def gapTwoY' : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0⟩

/-- Its handle-`U` letter. -/
def gapTwoU : SqU6 gr3R := ⟨6, 0, 0, 0, 0, 1, 0, 0, 2, 4, 0, 4, 4, 0, 4⟩

/-- Its handle-`V` letter. -/
def gapTwoV : SqU6 gr3R := ⟨0, 0, 0, 4, 0, 7, 0, 0, 7, 5, 0, 5, 0, 3, 0⟩

variable (h j) in
/-- **`gap-1a`**, at every handle count and every handle. -/
def gapOneMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j gapOneS gapOneX gapOneY gapOneU gapOneV

variable (h j) in
/-- **`gap-1b`**. -/
def gapOneMark' : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j gapOneS gapOneX gapOneY' gapOneU gapOneV

variable (h j) in
/-- **`gap-2a`**. -/
def gapTwoMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j gapTwoS gapTwoX gapTwoY gapTwoU gapTwoV

variable (h j) in
/-- **`gap-2b`**. -/
def gapTwoMark' : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j gapTwoS gapTwoX gapTwoY' gapTwoU gapTwoV

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial. -/
private theorem gapTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

/-- The relators: `gap-1` is `<o=5>`, `gap-2` is `<o=1>` - central translations with ODD
class-five residues, so both markings are ADMISSIBLE and the forcing's conclusion is false
there.  `StageForces` therefore says exactly that no achievable dressing kills. -/
theorem sqRelWord_gapOneMark :
    sqRelWord (gapOneMark h j) = SqU6.liftO 5 := by
  rw [gapOneMark, sqRelWord_fiveTuple]
  decide

theorem sqRelWord_gapOneMark' :
    sqRelWord (gapOneMark' h j) = SqU6.liftO 5 := by
  rw [gapOneMark', sqRelWord_fiveTuple]
  decide

theorem sqRelWord_gapTwoMark :
    sqRelWord (gapTwoMark h j) = SqU6.liftO 1 := by
  rw [gapTwoMark, sqRelWord_fiveTuple]
  decide

theorem sqRelWord_gapTwoMark' :
    sqRelWord (gapTwoMark' h j) = SqU6.liftO 1 := by
  rw [gapTwoMark', sqRelWord_fiveTuple]
  decide

end GapPoints

/-! ## 4 The exact lattice bound -/

section GapLattice

/-- Elements with an even `(4,5)`-column: the `gap-1` letters all lie here, and this is what
makes the `gap-1` target normal along the image. -/
def gapEvenD : Subgroup (SqU6 gr3R) where
  carrier := {z | (2 : gr3R) ∣ z.d}
  mul_mem' := by
    rintro p q hp hq
    rw [Set.mem_setOf_eq, SqU6.mul_d]
    exact dvd_add hp hq
  one_mem' := by rw [Set.mem_setOf_eq, SqU6.one_d]; exact dvd_zero _
  inv_mem' := by
    rintro p hp
    rw [Set.mem_setOf_eq, SqU6.inv_d]
    exact hp.neg_right

/-- …and with a `(4,5)`-column divisible by `4`: the `gap-2` letters. -/
def gapQuadD : Subgroup (SqU6 gr3R) where
  carrier := {z | (4 : gr3R) ∣ z.d}
  mul_mem' := by
    rintro p q hp hq
    rw [Set.mem_setOf_eq, SqU6.mul_d]
    exact dvd_add hp hq
  one_mem' := by rw [Set.mem_setOf_eq, SqU6.one_d]; exact dvd_zero _
  inv_mem' := by
    rintro p hp
    rw [Set.mem_setOf_eq, SqU6.inv_d]
    exact hp.neg_right

/-- ⭐⭐ **THE `gap-1` TARGET.**  A `gamma_3`-element with `2 k + 4 m + 4 n = 0` and
`2 l + 4 n = 0`.  These are two `Z/8`-linear conditions that are NOT congruences on single
coordinates and NOT visible mod `2`: they say `k + 2m + 2n` and `l + 2n` vanish mod `4`. -/
def gapKOne : Subgroup (SqU6 gr3R) where
  carrier := {z | z.IsGaThree ∧ 2 * z.k + 4 * z.m + 4 * z.n = 0 ∧ 2 * z.l + 4 * z.n = 0}
  mul_mem' := by
    rintro p q ⟨hp, hp1, hp2⟩ ⟨hq, hq1, hq2⟩
    refine ⟨hp.mul hq, ?_, ?_⟩
    · rw [SqU6.gaThree_mul_k hp, SqU6.gaThree_mul_m hp hq, SqU6.gaThree_mul_n hp hq]
      linear_combination hp1 + hq1
    · rw [SqU6.gaThree_mul_l hp, SqU6.gaThree_mul_n hp hq]
      linear_combination hp2 + hq2
  one_mem' := ⟨SqU6.isGaThree_one, by simp, by simp⟩
  inv_mem' := by
    rintro p ⟨hp, hp1, hp2⟩
    refine ⟨gaThree_inv_isGaThree hp, ?_, ?_⟩
    · rw [gaThree_inv_k hp, gaThree_inv_m hp, gaThree_inv_n hp]
      linear_combination -hp1
    · rw [gaThree_inv_l hp, gaThree_inv_n hp]
      linear_combination -hp2

/-- ⭐⭐ **THE `gap-2` TARGET.**  A `gamma_3`-element with `k + 4 n = 0`, `4 l = 0` and
`2 m = 0`.  ⚠ Only the first is a genuine two-coordinate relation: it forces `k` to be `0` or
`4`, and `n`'s parity decides which.  Over `ZMod 8` the other two are per-coordinate congruences:
`4 l = 0` says `l` is even, which a mod-`2` reading DOES see, and `2 m = 0` says `4 ∣ m`, which
it does not.  So `4 l = 0` is the one condition of the three visible mod `2`. -/
def gapKTwo : Subgroup (SqU6 gr3R) where
  carrier := {z | z.IsGaThree ∧ z.k + 4 * z.n = 0 ∧ 4 * z.l = 0 ∧ 2 * z.m = 0}
  mul_mem' := by
    rintro p q ⟨hp, hp1, hp2, hp3⟩ ⟨hq, hq1, hq2, hq3⟩
    refine ⟨hp.mul hq, ?_, ?_, ?_⟩
    · rw [SqU6.gaThree_mul_k hp, SqU6.gaThree_mul_n hp hq]
      linear_combination hp1 + hq1
    · rw [SqU6.gaThree_mul_l hp]
      linear_combination hp2 + hq2
    · rw [SqU6.gaThree_mul_m hp hq]
      linear_combination hp3 + hq3
  one_mem' := ⟨SqU6.isGaThree_one, by simp, by simp, by simp⟩
  inv_mem' := by
    rintro p ⟨hp, hp1, hp2, hp3⟩
    refine ⟨gaThree_inv_isGaThree hp, ?_, ?_, ?_⟩
    · rw [gaThree_inv_k hp, gaThree_inv_n hp]
      linear_combination -hp1
    · rw [gaThree_inv_l hp]
      linear_combination -hp2
    · rw [gaThree_inv_m hp]
      linear_combination -hp3

theorem mem_gapKOne {z : SqU6 gr3R} :
    z ∈ gapKOne ↔ z.IsGaThree ∧ 2 * z.k + 4 * z.m + 4 * z.n = 0 ∧ 2 * z.l + 4 * z.n = 0 :=
  Iff.rfl

theorem mem_gapKTwo {z : SqU6 gr3R} :
    z ∈ gapKTwo ↔ z.IsGaThree ∧ z.k + 4 * z.n = 0 ∧ 4 * z.l = 0 ∧ 2 * z.m = 0 := Iff.rfl

private theorem gr8 : (8 : gr3R) = 0 := by decide

/-- ⭐⭐ **The `gap-1` target is normalised by every even-`d` element.**  The class-three row is
conjugation-invariant and the class-four rows move by `g.a * z.k - z.j * g.d` and
`g.b * z.l - z.k * g.e`; the conditions force `4 k = 4 l = 0`, which kills three of those four
terms, and `2 ∣ g.d` kills the fourth. -/
theorem gapKOne_conj {g z : SqU6 gr3R} (hg : g ∈ gapEvenD) (hz : z ∈ gapKOne) :
    g * z * g⁻¹ ∈ gapKOne := by
  obtain ⟨hga, h1, h2⟩ := hz
  obtain ⟨t, ht⟩ := hg
  have h4k : (4 : gr3R) * z.k = 0 := by linear_combination 2 * h1 - z.m * gr8 - z.n * gr8
  have h4l : (4 : gr3R) * z.l = 0 := by linear_combination 2 * h2 - z.n * gr8
  refine ⟨gaThree_conj_isGaThree hga, ?_, ?_⟩
  · rw [gaThree_conj_k hga, gaThree_conj_m hga, gaThree_conj_n hga]
    linear_combination h1 + (g.a - g.e) * h4k + g.b * h4l - 4 * z.j * ht - z.j * t * gr8
  · rw [gaThree_conj_l hga, gaThree_conj_n hga]
    linear_combination h2 + g.b * h4l - g.e * h4k

/-- …and the `gap-2` target by every element whose `(4,5)`-column is divisible by `4`. -/
theorem gapKTwo_conj {g z : SqU6 gr3R} (hg : g ∈ gapQuadD) (hz : z ∈ gapKTwo) :
    g * z * g⁻¹ ∈ gapKTwo := by
  obtain ⟨hga, h1, h2, h3⟩ := hz
  obtain ⟨t, ht⟩ := hg
  have h2k : (2 : gr3R) * z.k = 0 := by linear_combination 2 * h1 - z.n * gr8
  have h4k : (4 : gr3R) * z.k = 0 := by linear_combination 2 * h2k
  refine ⟨gaThree_conj_isGaThree hga, ?_, ?_, ?_⟩
  · rw [gaThree_conj_k hga, gaThree_conj_n hga]
    linear_combination h1 + g.b * h2 - g.e * h4k
  · rw [gaThree_conj_l hga]
    linear_combination h2
  · rw [gaThree_conj_m hga]
    linear_combination h3 + g.a * h2k - 2 * z.j * ht - z.j * t * gr8

theorem gapEvenD_le_normalizer :
    (gapEvenD : Set (SqU6 gr3R))
      ⊆ Subgroup.normalizer ((gapKOne : Subgroup (SqU6 gr3R)) : Set (SqU6 gr3R)) :=
  subset_normalizer_of_conj (H := gapEvenD) fun _ hg _ hx => gapKOne_conj hg hx

theorem gapQuadD_le_normalizer :
    (gapQuadD : Set (SqU6 gr3R))
      ⊆ Subgroup.normalizer ((gapKTwo : Subgroup (SqU6 gr3R)) : Set (SqU6 gr3R)) :=
  subset_normalizer_of_conj (H := gapQuadD) fun _ hg _ hx => gapKTwo_conj hg hx

end GapLattice

/-! ## 5 The four markings, bounded -/

section GapBound

variable {h : ℕ} {j : Fin h}

/-- The six slot values of `OneA`, indexed so that the bracket census is a `decide` over
`Fin 6` rather than over a list of structures. -/
private def gapOneAL : Fin 6 → SqU6 gr3R
  | 0 => gapOneS
  | 1 => gapOneX
  | 2 => gapOneY
  | 3 => gapOneU
  | 4 => gapOneV
  | 5 => 1

/-- A weight-three bracket of three of them. -/
private def gapOneABr (a b c : Fin 6) : SqU6 gr3R :=
  ⁅⁅gapOneAL a, gapOneAL b⁆, gapOneAL c⁆

set_option maxHeartbeats 4000000 in
/-- ⭐⭐⭐ **THE 216 WEIGHT-THREE BRACKETS** of the letters of `OneA` are `gamma_3`-shaped and
satisfy the target's `Z/8`-linear conditions.  This is the entire arithmetic input to the
lattice bound, and it is a `decide` on `ZMod 8`. -/
private theorem gapOneA_brackets_raw : ∀ a b c : Fin 6,
    ((gapOneABr a b c).a = 0 ∧ (gapOneABr a b c).b = 0
      ∧ (gapOneABr a b c).c = 0 ∧ (gapOneABr a b c).d = 0 ∧ (gapOneABr a b c).e = 0
      ∧ (gapOneABr a b c).f = 0 ∧ (gapOneABr a b c).g = 0
      ∧ (gapOneABr a b c).h = 0 ∧ (gapOneABr a b c).i = 0)
      ∧ 2 * (gapOneABr a b c).k + 4 * (gapOneABr a b c).m + 4 * (gapOneABr a b c).n = 0
      ∧ 2 * (gapOneABr a b c).l + 4 * (gapOneABr a b c).n = 0 := by decide +kernel

theorem gapOneA_brackets (a b c : Fin 6) : gapOneABr a b c ∈ gapKOne :=
  gapOneA_brackets_raw a b c

theorem gapOneAMark_mem (i : Fin (sqRank h)) :
    ∃ a : Fin 6, gapOneMark h j i = gapOneAL a := by
  rcases gapTuple_cases gapOneS gapOneX gapOneY gapOneU gapOneV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapOneMark, h1]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem gapOneAMark_column (i : Fin (sqRank h)) :
    gapOneMark h j i ∈ gapEvenD := by
  rcases gapTuple_cases gapOneS gapOneX gapOneY gapOneU gapOneV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapOneMark, h1]
  exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨3, by decide⟩, ⟨0, by decide⟩]

/-- ⭐⭐⭐ **THE ACHIEVABLE LATTICE AT `OneA`, BOUNDED BY AN EXPLICIT `Z/8`-LINEAR TARGET.**
Every achievable stage-four dressing of `OneA` satisfies the target's conditions, at every handle
count and every handle.  Wave 62 measured that no per-coordinate congruence, no mod-`2` linear
condition and no letter-column chain can bound this lattice usefully; the generator reduction of
section 1 bounds it without relaxing the lattice mod `2` or mod `4` anywhere in the argument.

⚠ This is a ONE-SIDED containment, and the target is strictly bigger than the honest lattice:
index `16`, `1024` inside `16384`, per the Slack paragraph of the header.  That the method itself
loses nothing is the separate statement `LcsGens.lcsSeries_le_iff_of_gens`. -/
theorem forceLcs_two_le_gapOneA :
    forceLcs (Subgroup.closure (Set.range (gapOneMark h j))) 2 ≤ gapKOne := by
  refine forceLcs_two_le_of_gens ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact gapEvenD_le_normalizer (gapOneAMark_column i)
  · rintro _ ⟨i1, rfl⟩ _ ⟨i2, rfl⟩ _ ⟨i3, rfl⟩
    obtain ⟨a, ha⟩ := gapOneAMark_mem (h := h) (j := j) i1
    obtain ⟨b, hb⟩ := gapOneAMark_mem (h := h) (j := j) i2
    obtain ⟨c, hc⟩ := gapOneAMark_mem (h := h) (j := j) i3
    rw [ha, hb, hc]
    exact gapOneA_brackets a b c

/-- The six slot values of `OneB`, indexed so that the bracket census is a `decide` over
`Fin 6` rather than over a list of structures. -/
private def gapOneBL : Fin 6 → SqU6 gr3R
  | 0 => gapOneS
  | 1 => gapOneX
  | 2 => gapOneY'
  | 3 => gapOneU
  | 4 => gapOneV
  | 5 => 1

/-- A weight-three bracket of three of them. -/
private def gapOneBBr (a b c : Fin 6) : SqU6 gr3R :=
  ⁅⁅gapOneBL a, gapOneBL b⁆, gapOneBL c⁆

set_option maxHeartbeats 4000000 in
/-- ⭐⭐⭐ **THE 216 WEIGHT-THREE BRACKETS** of the letters of `OneB` are `gamma_3`-shaped and
satisfy the target's `Z/8`-linear conditions.  This is the entire arithmetic input to the
lattice bound, and it is a `decide` on `ZMod 8`. -/
private theorem gapOneB_brackets_raw : ∀ a b c : Fin 6,
    ((gapOneBBr a b c).a = 0 ∧ (gapOneBBr a b c).b = 0
      ∧ (gapOneBBr a b c).c = 0 ∧ (gapOneBBr a b c).d = 0 ∧ (gapOneBBr a b c).e = 0
      ∧ (gapOneBBr a b c).f = 0 ∧ (gapOneBBr a b c).g = 0
      ∧ (gapOneBBr a b c).h = 0 ∧ (gapOneBBr a b c).i = 0)
      ∧ 2 * (gapOneBBr a b c).k + 4 * (gapOneBBr a b c).m + 4 * (gapOneBBr a b c).n = 0
      ∧ 2 * (gapOneBBr a b c).l + 4 * (gapOneBBr a b c).n = 0 := by decide +kernel

theorem gapOneB_brackets (a b c : Fin 6) : gapOneBBr a b c ∈ gapKOne :=
  gapOneB_brackets_raw a b c

theorem gapOneBMark_mem (i : Fin (sqRank h)) :
    ∃ a : Fin 6, gapOneMark' h j i = gapOneBL a := by
  rcases gapTuple_cases gapOneS gapOneX gapOneY' gapOneU gapOneV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapOneMark', h1]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem gapOneBMark_column (i : Fin (sqRank h)) :
    gapOneMark' h j i ∈ gapEvenD := by
  rcases gapTuple_cases gapOneS gapOneX gapOneY' gapOneU gapOneV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapOneMark', h1]
  exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨3, by decide⟩, ⟨0, by decide⟩]

/-- ⭐⭐⭐ **THE ACHIEVABLE LATTICE AT `OneB`, BOUNDED BY AN EXPLICIT `Z/8`-LINEAR TARGET.**
Every achievable stage-four dressing of `OneB` satisfies the target's conditions, at every handle
count and every handle.  Wave 62 measured that no per-coordinate congruence, no mod-`2` linear
condition and no letter-column chain can bound this lattice usefully; the generator reduction of
section 1 bounds it without relaxing the lattice mod `2` or mod `4` anywhere in the argument.

⚠ This is a ONE-SIDED containment, and the target is strictly bigger than the honest lattice:
index `16`, `1024` inside `16384`, per the Slack paragraph of the header.  That the method itself
loses nothing is the separate statement `LcsGens.lcsSeries_le_iff_of_gens`. -/
theorem forceLcs_two_le_gapOneB :
    forceLcs (Subgroup.closure (Set.range (gapOneMark' h j))) 2 ≤ gapKOne := by
  refine forceLcs_two_le_of_gens ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact gapEvenD_le_normalizer (gapOneBMark_column i)
  · rintro _ ⟨i1, rfl⟩ _ ⟨i2, rfl⟩ _ ⟨i3, rfl⟩
    obtain ⟨a, ha⟩ := gapOneBMark_mem (h := h) (j := j) i1
    obtain ⟨b, hb⟩ := gapOneBMark_mem (h := h) (j := j) i2
    obtain ⟨c, hc⟩ := gapOneBMark_mem (h := h) (j := j) i3
    rw [ha, hb, hc]
    exact gapOneB_brackets a b c

/-- The six slot values of `TwoA`, indexed so that the bracket census is a `decide` over
`Fin 6` rather than over a list of structures. -/
private def gapTwoAL : Fin 6 → SqU6 gr3R
  | 0 => gapTwoS
  | 1 => gapTwoX
  | 2 => gapTwoY
  | 3 => gapTwoU
  | 4 => gapTwoV
  | 5 => 1

/-- A weight-three bracket of three of them. -/
private def gapTwoABr (a b c : Fin 6) : SqU6 gr3R :=
  ⁅⁅gapTwoAL a, gapTwoAL b⁆, gapTwoAL c⁆

set_option maxHeartbeats 4000000 in
/-- ⭐⭐⭐ **THE 216 WEIGHT-THREE BRACKETS** of the letters of `TwoA` are `gamma_3`-shaped and
satisfy the target's `Z/8`-linear conditions.  This is the entire arithmetic input to the
lattice bound, and it is a `decide` on `ZMod 8`. -/
private theorem gapTwoA_brackets_raw : ∀ a b c : Fin 6,
    ((gapTwoABr a b c).a = 0 ∧ (gapTwoABr a b c).b = 0
      ∧ (gapTwoABr a b c).c = 0 ∧ (gapTwoABr a b c).d = 0 ∧ (gapTwoABr a b c).e = 0
      ∧ (gapTwoABr a b c).f = 0 ∧ (gapTwoABr a b c).g = 0
      ∧ (gapTwoABr a b c).h = 0 ∧ (gapTwoABr a b c).i = 0)
      ∧ (gapTwoABr a b c).k + 4 * (gapTwoABr a b c).n = 0
      ∧ 4 * (gapTwoABr a b c).l = 0 ∧ 2 * (gapTwoABr a b c).m = 0 := by decide +kernel

theorem gapTwoA_brackets (a b c : Fin 6) : gapTwoABr a b c ∈ gapKTwo :=
  gapTwoA_brackets_raw a b c

theorem gapTwoAMark_mem (i : Fin (sqRank h)) :
    ∃ a : Fin 6, gapTwoMark h j i = gapTwoAL a := by
  rcases gapTuple_cases gapTwoS gapTwoX gapTwoY gapTwoU gapTwoV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapTwoMark, h1]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem gapTwoAMark_column (i : Fin (sqRank h)) :
    gapTwoMark h j i ∈ gapQuadD := by
  rcases gapTuple_cases gapTwoS gapTwoX gapTwoY gapTwoU gapTwoV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapTwoMark, h1]
  exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨1, by decide⟩, ⟨0, by decide⟩]

/-- ⭐⭐⭐ **THE ACHIEVABLE LATTICE AT `TwoA`, BOUNDED BY AN EXPLICIT `Z/8`-LINEAR TARGET.**
Every achievable stage-four dressing of `TwoA` satisfies the target's conditions, at every handle
count and every handle.  Wave 62 measured that no per-coordinate congruence, no mod-`2` linear
condition and no letter-column chain can bound this lattice usefully; the generator reduction of
section 1 bounds it without relaxing the lattice mod `2` or mod `4` anywhere in the argument.

⚠ This is a ONE-SIDED containment, and the target is strictly bigger than the honest lattice:
index `16`, `256` inside `4096`, per the Slack paragraph of the header.  That the method itself
loses nothing is the separate statement `LcsGens.lcsSeries_le_iff_of_gens`. -/
theorem forceLcs_two_le_gapTwoA :
    forceLcs (Subgroup.closure (Set.range (gapTwoMark h j))) 2 ≤ gapKTwo := by
  refine forceLcs_two_le_of_gens ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact gapQuadD_le_normalizer (gapTwoAMark_column i)
  · rintro _ ⟨i1, rfl⟩ _ ⟨i2, rfl⟩ _ ⟨i3, rfl⟩
    obtain ⟨a, ha⟩ := gapTwoAMark_mem (h := h) (j := j) i1
    obtain ⟨b, hb⟩ := gapTwoAMark_mem (h := h) (j := j) i2
    obtain ⟨c, hc⟩ := gapTwoAMark_mem (h := h) (j := j) i3
    rw [ha, hb, hc]
    exact gapTwoA_brackets a b c

/-- The six slot values of `TwoB`, indexed so that the bracket census is a `decide` over
`Fin 6` rather than over a list of structures. -/
private def gapTwoBL : Fin 6 → SqU6 gr3R
  | 0 => gapTwoS
  | 1 => gapTwoX
  | 2 => gapTwoY'
  | 3 => gapTwoU
  | 4 => gapTwoV
  | 5 => 1

/-- A weight-three bracket of three of them. -/
private def gapTwoBBr (a b c : Fin 6) : SqU6 gr3R :=
  ⁅⁅gapTwoBL a, gapTwoBL b⁆, gapTwoBL c⁆

set_option maxHeartbeats 4000000 in
/-- ⭐⭐⭐ **THE 216 WEIGHT-THREE BRACKETS** of the letters of `TwoB` are `gamma_3`-shaped and
satisfy the target's `Z/8`-linear conditions.  This is the entire arithmetic input to the
lattice bound, and it is a `decide` on `ZMod 8`. -/
private theorem gapTwoB_brackets_raw : ∀ a b c : Fin 6,
    ((gapTwoBBr a b c).a = 0 ∧ (gapTwoBBr a b c).b = 0
      ∧ (gapTwoBBr a b c).c = 0 ∧ (gapTwoBBr a b c).d = 0 ∧ (gapTwoBBr a b c).e = 0
      ∧ (gapTwoBBr a b c).f = 0 ∧ (gapTwoBBr a b c).g = 0
      ∧ (gapTwoBBr a b c).h = 0 ∧ (gapTwoBBr a b c).i = 0)
      ∧ (gapTwoBBr a b c).k + 4 * (gapTwoBBr a b c).n = 0
      ∧ 4 * (gapTwoBBr a b c).l = 0 ∧ 2 * (gapTwoBBr a b c).m = 0 := by decide +kernel

theorem gapTwoB_brackets (a b c : Fin 6) : gapTwoBBr a b c ∈ gapKTwo :=
  gapTwoB_brackets_raw a b c

theorem gapTwoBMark_mem (i : Fin (sqRank h)) :
    ∃ a : Fin 6, gapTwoMark' h j i = gapTwoBL a := by
  rcases gapTuple_cases gapTwoS gapTwoX gapTwoY' gapTwoU gapTwoV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapTwoMark', h1]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem gapTwoBMark_column (i : Fin (sqRank h)) :
    gapTwoMark' h j i ∈ gapQuadD := by
  rcases gapTuple_cases gapTwoS gapTwoX gapTwoY' gapTwoU gapTwoV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [gapTwoMark', h1]
  exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨1, by decide⟩, ⟨0, by decide⟩]

/-- ⭐⭐⭐ **THE ACHIEVABLE LATTICE AT `TwoB`, BOUNDED BY AN EXPLICIT `Z/8`-LINEAR TARGET.**
Every achievable stage-four dressing of `TwoB` satisfies the target's conditions, at every handle
count and every handle.  Wave 62 measured that no per-coordinate congruence, no mod-`2` linear
condition and no letter-column chain can bound this lattice usefully; the generator reduction of
section 1 bounds it without relaxing the lattice mod `2` or mod `4` anywhere in the argument.

⚠ This is a ONE-SIDED containment, and the target is strictly bigger than the honest lattice:
index `16`, `256` inside `4096`, per the Slack paragraph of the header.  That the method itself
loses nothing is the separate statement `LcsGens.lcsSeries_le_iff_of_gens`. -/
theorem forceLcs_two_le_gapTwoB :
    forceLcs (Subgroup.closure (Set.range (gapTwoMark' h j))) 2 ≤ gapKTwo := by
  refine forceLcs_two_le_of_gens ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact gapQuadD_le_normalizer (gapTwoBMark_column i)
  · rintro _ ⟨i1, rfl⟩ _ ⟨i2, rfl⟩ _ ⟨i3, rfl⟩
    obtain ⟨a, ha⟩ := gapTwoBMark_mem (h := h) (j := j) i1
    obtain ⟨b, hb⟩ := gapTwoBMark_mem (h := h) (j := j) i2
    obtain ⟨c, hc⟩ := gapTwoBMark_mem (h := h) (j := j) i3
    rw [ha, hb, hc]
    exact gapTwoB_brackets a b c

end GapBound

/-! ## 6 What the bound buys: the forcing, modulo one linear identity -/

section Certificate

variable {h : ℕ} {j : Fin h}

/-- The `gap-1` **certificate functional** on `gamma_3`: `l + 2 n + 4 o`.  It kills every
achievable shift and does not kill the class-five unit, which is exactly what a proof of the
forcing at a marking with an odd central relator needs.  Measured at
`scripts/w63_four/results/certify.txt`. -/
def psiOne (w : SqU6 gr3R) : gr3R := w.l + 2 * w.n + 4 * w.o

/-- The `gap-2` certificate functional: `m + 4 o`. -/
def psiTwo (w : SqU6 gr3R) : gr3R := w.m + 4 * w.o

/-- ⭐⭐ **THE FORCING AT `gap-1a`, REDUCED TO ONE LINEAR IDENTITY.**  Given that the
certificate functional kills the stage-four shift of every dressing whose slots satisfy the
`gap-1` target's conditions, the forcing holds at `gap-1a` - at every handle count and every
handle.  The lattice input is `forceLcs_two_le_gapOneA`, which is unconditional. -/
theorem stageForces_gapOneA_of_psi
    (hpsi : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ gapKOne) →
      psiOne (gaThreeShift h (gapOneMark h j) z) = 0) :
    StageForces (gapOneMark h j) := by
  intro z hz hkill
  exfalso
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have hs : sqRelWord (gapOneMark h j) * gaThreeShift h (gapOneMark h j) z = 1 := by
    rw [← sqRelWord_gaThreeDress hga]
    exact hkill
  have hshift : gaThreeShift h (gapOneMark h j) z = (SqU6.liftO (5 : gr3R))⁻¹ := by
    rw [← sqRelWord_gapOneMark (h := h) (j := j)]
    exact eq_inv_of_mul_eq_one_right hs
  have := hpsi z fun i => forceLcs_two_le_gapOneA (hz i)
  rw [hshift] at this
  exact absurd this (by decide)

/-- …at `gap-1b`. -/
theorem stageForces_gapOneB_of_psi
    (hpsi : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ gapKOne) →
      psiOne (gaThreeShift h (gapOneMark' h j) z) = 0) :
    StageForces (gapOneMark' h j) := by
  intro z hz hkill
  exfalso
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have hs : sqRelWord (gapOneMark' h j) * gaThreeShift h (gapOneMark' h j) z = 1 := by
    rw [← sqRelWord_gaThreeDress hga]
    exact hkill
  have hshift : gaThreeShift h (gapOneMark' h j) z = (SqU6.liftO (5 : gr3R))⁻¹ := by
    rw [← sqRelWord_gapOneMark' (h := h) (j := j)]
    exact eq_inv_of_mul_eq_one_right hs
  have := hpsi z fun i => forceLcs_two_le_gapOneB (hz i)
  rw [hshift] at this
  exact absurd this (by decide)

/-- …at `gap-2a`. -/
theorem stageForces_gapTwoA_of_psi
    (hpsi : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ gapKTwo) →
      psiTwo (gaThreeShift h (gapTwoMark h j) z) = 0) :
    StageForces (gapTwoMark h j) := by
  intro z hz hkill
  exfalso
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have hs : sqRelWord (gapTwoMark h j) * gaThreeShift h (gapTwoMark h j) z = 1 := by
    rw [← sqRelWord_gaThreeDress hga]
    exact hkill
  have hshift : gaThreeShift h (gapTwoMark h j) z = (SqU6.liftO (1 : gr3R))⁻¹ := by
    rw [← sqRelWord_gapTwoMark (h := h) (j := j)]
    exact eq_inv_of_mul_eq_one_right hs
  have := hpsi z fun i => forceLcs_two_le_gapTwoA (hz i)
  rw [hshift] at this
  exact absurd this (by decide)

/-- …and at `gap-2b`. -/
theorem stageForces_gapTwoB_of_psi
    (hpsi : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ gapKTwo) →
      psiTwo (gaThreeShift h (gapTwoMark' h j) z) = 0) :
    StageForces (gapTwoMark' h j) := by
  intro z hz hkill
  exfalso
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have hs : sqRelWord (gapTwoMark' h j) * gaThreeShift h (gapTwoMark' h j) z = 1 := by
    rw [← sqRelWord_gaThreeDress hga]
    exact hkill
  have hshift : gaThreeShift h (gapTwoMark' h j) z = (SqU6.liftO (1 : gr3R))⁻¹ := by
    rw [← sqRelWord_gapTwoMark' (h := h) (j := j)]
    exact eq_inv_of_mul_eq_one_right hs
  have := hpsi z fun i => forceLcs_two_le_gapTwoB (hz i)
  rw [hshift] at this
  exact absurd this (by decide)

end Certificate

/-! ## 7 Axiom pins -/

section AxiomPins

#print axioms subset_normalizer_of_conj
#print axioms commLeft
#print axioms mem_commLeft
#print axioms commRight
#print axioms mem_commRight
#print axioms commutator_mem_of_gens_right
#print axioms commutator_mem_of_gens_left
#print axioms commAll
#print axioms mem_commAll
#print axioms le_normalizer_commAll
#print axioms le_of_gens_three
#print axioms forceLcs_two_le_of_gens
#print axioms gaThree_conj_j
#print axioms gaThree_conj_k
#print axioms gaThree_conj_l
#print axioms gaThree_conj_m
#print axioms gaThree_conj_n
#print axioms gaThree_conj_isGaThree
#print axioms gaThree_inv_isGaThree
#print axioms gaThree_inv_k
#print axioms gaThree_inv_l
#print axioms gaThree_inv_m
#print axioms gaThree_inv_n
#print axioms gapOneS
#print axioms gapOneX
#print axioms gapOneY
#print axioms gapOneY'
#print axioms gapOneU
#print axioms gapOneV
#print axioms gapTwoS
#print axioms gapTwoX
#print axioms gapTwoY
#print axioms gapTwoY'
#print axioms gapTwoU
#print axioms gapTwoV
#print axioms gapOneMark
#print axioms gapOneMark'
#print axioms gapTwoMark
#print axioms gapTwoMark'
#print axioms sqRelWord_gapOneMark
#print axioms sqRelWord_gapOneMark'
#print axioms sqRelWord_gapTwoMark
#print axioms sqRelWord_gapTwoMark'
#print axioms gapEvenD
#print axioms gapQuadD
#print axioms gapKOne
#print axioms gapKTwo
#print axioms mem_gapKOne
#print axioms mem_gapKTwo
#print axioms gapKOne_conj
#print axioms gapKTwo_conj
#print axioms gapEvenD_le_normalizer
#print axioms gapQuadD_le_normalizer
#print axioms gapOneA_brackets
#print axioms gapOneAMark_mem
#print axioms gapOneAMark_column
#print axioms forceLcs_two_le_gapOneA
#print axioms gapOneB_brackets
#print axioms gapOneBMark_mem
#print axioms gapOneBMark_column
#print axioms forceLcs_two_le_gapOneB
#print axioms gapTwoA_brackets
#print axioms gapTwoAMark_mem
#print axioms gapTwoAMark_column
#print axioms forceLcs_two_le_gapTwoA
#print axioms gapTwoB_brackets
#print axioms gapTwoBMark_mem
#print axioms gapTwoBMark_column
#print axioms forceLcs_two_le_gapTwoB
#print axioms psiOne
#print axioms psiTwo
#print axioms stageForces_gapOneA_of_psi
#print axioms stageForces_gapOneB_of_psi
#print axioms stageForces_gapTwoA_of_psi
#print axioms stageForces_gapTwoB_of_psi

end AxiomPins

end SqCore

end Dyadic

end GQ2
