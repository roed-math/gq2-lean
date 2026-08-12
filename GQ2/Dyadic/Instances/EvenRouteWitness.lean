/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenEndpoint
import GQ2.Dyadic.Instances.EvenDeepIsotropy
import GQ2.Dyadic.Instances.Fields

/-!
# W55-AUDIT: non-vacuity and composition witnesses for the even route's endpoint chain

## What this file is

The adversarial audit of wave 55 asked whether the even route's endpoint chain can be broken.
It cannot, but the probing produced four reusable statements, and this file is those four.  Each
one answers a question that the audit had to settle and that no committed statement settled.

The audit note is `docs/dyadic/w55-audit-note.md`; this file carries only the Lean.

## The four questions, and the four answers

1. **Is the published `M` bundle's third field still an input?**  No.  `EvenRouteCarriedM` was
   published by W54-COMPOSE with three fields, the third being `EvenDeepMIsotropicSupply K`; in
   the same wave W54-BOCK proved that supply outright.  Neither lane imports the other, so no
   committed statement composes them, and the campaign's claim that both even branches carry the
   same two inputs is not witnessed anywhere in the tree.  §1 witnesses it:
   `evenRouteWitness_carriedM_of_two` builds the published bundle from the two inputs, and
   `evenRouteWitness_orientedEquivM` is the `M` endpoint with exactly the `N` endpoint's input
   list.

2. **Does the `∀ alpha ≥ 2` binder of the carried bundles demand more than the endpoint
   consumes?**  This is the wave-52 failure mode transposed: a hypothesis stated over a range
   the identity does not produce.  On the `N` branch the answer is no, and §2 proves it.  The
   orientation unit pins the depth (`evenRouteWitness_nUnit_mem_imChiN`): `nUnit alpha` lies in
   `imChiN beta` only when `alpha = beta`, because the two units are exactly `2 ^ min` apart.  So
   at every depth but the produced one the `N` stage tuples do not exist
   (`evenRouteWitness_nTuple_isEmpty`), the extra instances are vacuous, and the published bundle
   follows from its single-depth instance (`evenRouteWitness_carriedN_of_atDepth`).  The `N`
   bundle therefore asks for exactly what `evenEndpoint_orientedEquivN_atDepth` uses.

3. **Does that argument transpose to `M`?**  No, and §3 records the obstruction rather than
   hiding it.  `mUnit alpha` lies in `imChiM beta` for **every** `beta ≤ alpha`
   (`evenRouteWitness_mUnit_mem_imChiM`), so every row value of a wrong-depth `M` table is still
   a character value (`evenRouteWitness_vM_mem_range`) and the emptiness route of §2 is
   unavailable.  Nothing shows `EvenRouteCarriedM` inconsistent; what §3 shows is that its depth
   binder is not known to collapse, so the bundle may demand strictly more than
   `evenEndpoint_orientedEquivM_atDepth` consumes.  The repair is to state the bundle at a depth,
   which is what §5.2 of the endpoint file already does for the endpoints.

4. **Is the field-level hypothesis set satisfiable at all?**  Yes, and at literal fields.  §4
   instantiates both per-field endpoints at the pilot rows of `Instances/Fields.lean`: the `N`
   endpoint at `ℚ₂(√−2)` and the `M` endpoint at `ℚ₂(√2)`, both at `h = 0`.  Every field-level
   hypothesis is discharged from committed statements and the B5-K axiom, and what is left in
   each case is the branch sign condition together with the two supplies.  So the even endpoints
   are not empty for the wave-52 reason: their field-level binders are jointly satisfiable, and
   the residue is exactly the two named inputs.

   §4 also records `evenRouteWitness_imChiM_two_eq_top`: on the `α = 2` stratum the branch
   identification `range χ = imChiM 2` says nothing more than `range χ = ⊤`, since every 2-adic
   unit is `≡ ±1 (mod 4)`.  That is the cheapest possible reading of the `M` stratum's binder and
   is worth having on the page, because the stratum endpoints are the ones the paper quotes.

## What this file does not claim

Nothing here proves `Hfam` or the flip supply, and nothing here shows those two are consistent
with the rest at any field.  That question is open on both branches and is the campaign's named
frontier; §4 reduces it to exactly that and no further.

## Numbering

1. the `M` bundle from two inputs;
2. the `N` depth is rigid, and the `N` bundle collapses to one depth;
3. the `M` depth is not rigid;
4. the field-level hypotheses at literal fields;
5. axiom pins.
-/

namespace GQ2.Dyadic.EvenRouteWitness

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenFrameDeep
open GQ2.Dyadic.EvenEndpoint
open GQ2.Dyadic.EvenDeepIsotropy
open GQ2.Dyadic.Fields

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, declared exactly as the endpoint file declares it, so
that the statements below are the endpoint file's statements and not variants of them. -/
local instance evenRouteWitnessScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenRouteWitnessContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The `M` bundle from two inputs

W54-COMPOSE published `EvenRouteCarriedM` with three fields and W54-BOCK proved the third,
`EvenDeepMIsotropicSupply K`, in the same wave.  `Instances/EvenDeepIsotropy.lean` imports
`Instances/StageAbstractionEvenFrameDeep.lean` and `Instances/StageAbstractionEvenEndpoint.lean`
imports the same file, so the two are siblings and neither sees the other.  This section is the
one import that closes the gap. -/

section Composed

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The published `M` bundle costs two inputs, not three.**  `EvenRouteCarriedM`'s isotropy
field is `evenDeepMIsotropicSupply_holds`, a theorem of W54-BOCK.  So the `M` branch's carried
list is the `N` branch's, with the flips one slot shorter. -/
theorem evenRouteWitness_carriedM_of_two {h : ℕ} (Hfam : EvenEndpointMFamily h K)
    (Hflip : EvenEndpointMFlipOffTwo h K) : EvenRouteCarriedM h K :=
  ⟨Hfam, Hflip, evenDeepMIsotropicSupply_holds⟩

/-- **The even `M` route from the two inputs the campaign claims.**  This is the statement the
wave-54 live frontier asserts and that no committed theorem carried: `evenRoute_orientedEquivM`
demands the three-field bundle, and `evenDeepIsotropy_orientedEquivM` discharges the isotropy but
carries the raw-to-bracket input `Hup` rather than the flips.  Both halves at once are here. -/
theorem evenRouteWitness_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : EvenEndpointMFamily h K) (Hflip : EvenEndpointMFlipOffTwo h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM B hneg h hev evenDeepMIsotropicSupply_holds Hfam Hflip

end Composed

/-! ## §2 The `N` depth is rigid

The carried bundles of the endpoint file quantify over every `alpha ≥ 2`, while the range
identity produces one.  A hypothesis stated over more than the identity produces is exactly the
wave-52 defect (`rangeFinal_uniform_Hrange_imChiN_absurd`), so the binder has to be checked and
not merely noted.

On the `N` branch it is harmless, for an arithmetic reason.  `nUnit alpha` and `nUnit beta` are
`2 ^ min (alpha, beta)` apart, and `imChiN beta` pins its elements modulo `2 ^ (beta + 1)`
(`evenRange_mem_imChiN_dvd`), so the `N` orientation unit identifies its own depth.  The stage
tuple carries the value `nUnit alpha` in row `1`, hence exists only at the produced depth. -/

section NRigid

/-- `2` is not invertible in `ℤ₂`. -/
theorem evenRouteWitness_not_two_dvd_one : ¬ (2 : ℤ_[2]) ∣ 1 := fun hd ↦
  not_isUnit_two (isUnit_of_dvd_one hd)

/-- Two distinct powers of `2` differ at exactly the smaller exponent, so `2 ^ (beta + 1)` never
divides `2 ^ alpha - 2 ^ beta`. -/
theorem evenRouteWitness_not_dvd_pow_sub {alpha beta : ℕ} (hne : alpha ≠ beta) :
    ¬ (2 : ℤ_[2]) ^ (beta + 1) ∣ 2 ^ alpha - 2 ^ beta := by
  intro hdvd
  rcases Nat.lt_or_ge alpha beta with hlt | hge
  · have hfac : (2 : ℤ_[2]) ^ alpha - 2 ^ beta = 2 ^ alpha * (1 - 2 ^ (beta - alpha)) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    have hsplit : (2 : ℤ_[2]) ^ (beta + 1) = 2 ^ alpha * 2 ^ (beta + 1 - alpha) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hfac, hsplit] at hdvd
    have hcancel : (2 : ℤ_[2]) ^ (beta + 1 - alpha) ∣ 1 - 2 ^ (beta - alpha) :=
      (mul_dvd_mul_iff_left (a := (2 : ℤ_[2]) ^ alpha) (pow_ne_zero _ two_ne_zero)).mp hdvd
    have h2 : (2 : ℤ_[2]) ∣ 1 - 2 ^ (beta - alpha) :=
      (dvd_pow_self 2 (show beta + 1 - alpha ≠ 0 by omega)).trans hcancel
    exact evenRouteWitness_not_two_dvd_one
      (by simpa using h2.add (Dvd.dvd.mul_right (dvd_pow_self (2 : ℤ_[2])
        (show beta - alpha ≠ 0 by omega)) 1))
  · have hfac : (2 : ℤ_[2]) ^ alpha - 2 ^ beta = 2 ^ beta * (2 ^ (alpha - beta) - 1) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    have hsplit : (2 : ℤ_[2]) ^ (beta + 1) = 2 ^ beta * 2 := by rw [pow_succ]
    rw [hfac, hsplit] at hdvd
    have hcancel : (2 : ℤ_[2]) ∣ 2 ^ (alpha - beta) - 1 :=
      (mul_dvd_mul_iff_left (a := (2 : ℤ_[2]) ^ beta) (pow_ne_zero _ two_ne_zero)).mp hdvd
    exact evenRouteWitness_not_two_dvd_one
      (by simpa using (dvd_pow_self (2 : ℤ_[2]) (show alpha - beta ≠ 0 by omega)).sub hcancel)

/-- **The `N` orientation unit identifies its own depth.**  `nUnit alpha ∈ imChiN beta` forces
`alpha = beta`, for all `alpha, beta ≥ 2`.  The mod-four class rules out the `≡ 1` branch of
`evenRange_mem_imChiN_dvd`, and the two-power spacing rules out the other. -/
theorem evenRouteWitness_nUnit_mem_imChiN {alpha beta : ℕ} (halpha : 2 ≤ alpha) (hbeta : 2 ≤ beta)
    (hmem : nUnit alpha ∈ imChiN beta) : alpha = beta := by
  by_contra hne
  have hkey := nUnit_mul (show 1 ≤ alpha by omega)
  rcases evenRange_mem_imChiN_dvd hbeta hmem with hd | hd
  · have h4 : (2 : ℤ_[2]) ^ 2 ∣ ((nUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
      (pow_dvd_pow _ (show 2 ≤ beta + 1 by omega)).trans hd
    have hpow : (2 : ℤ_[2]) ^ 2 ∣ 2 ^ alpha * ((nUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) :=
      Dvd.dvd.mul_right (pow_dvd_pow _ halpha) _
    obtain ⟨c, hc⟩ := h4
    obtain ⟨d, hdd⟩ := hpow
    refine evenRouteWitness_not_two_dvd_one
      ⟨-(c + d), mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_⟩
    linear_combination hkey - hc - hdd
  · have hkeyb := nUnit_mul (show 1 ≤ beta by omega)
    refine evenRouteWitness_not_dvd_pow_sub hne ?_
    obtain ⟨c, hc⟩ := hd
    exact ⟨c * ((1 + 2 ^ alpha) * (1 + 2 ^ beta)), by
      linear_combination (1 + (2 : ℤ_[2]) ^ alpha) * (1 + (2 : ℤ_[2]) ^ beta) * hc -
        (1 + (2 : ℤ_[2]) ^ beta) * hkey + (1 + (2 : ℤ_[2]) ^ alpha) * hkeyb⟩

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- **Off the produced depth the `N` stage tuples do not exist.**  Row `1` of the `N` table is
`nUnit alpha`, a tuple demands a character value there, and the branch identification puts the
character values in `imChiN alpha₀`. -/
theorem evenRouteWitness_nTuple_isEmpty {alpha alpha₀ h k : ℕ} (halpha : 2 ≤ alpha)
    (halpha₀ : 2 ≤ alpha₀) (hne : alpha ≠ alpha₀) {hα₁ : 1 ≤ alpha}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀) :
    IsEmpty (Tuple (nStageWord alpha h hα₁) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) := by
  refine ⟨fun T ↦ ?_⟩
  obtain ⟨x, hx, -⟩ := T.rows 1
  rw [vN_one] at hx
  exact hne (evenRouteWitness_nUnit_mem_imChiN halpha halpha₀ (hrange ▸ ⟨x, hx⟩))

/-- **The published `N` bundle collapses to one depth.**  Given the branch identification, the
single-depth pair of inputs already gives `EvenRouteCarriedN`: every other depth is vacuous.  So
the `∀ alpha ≥ 2` binder of `EvenRouteCarriedN` is not a strengthening, and the bundle demands
exactly what `evenEndpoint_orientedEquivN_atDepth` consumes. -/
theorem evenRouteWitness_carriedN_of_atDepth {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha₀ h (Nat.le_of_succ_le halpha₀))
        (vN alpha₀) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupply alpha₀ (nStageWord alpha₀ h (Nat.le_of_succ_le halpha₀))
      (vN alpha₀) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenRouteCarriedN h K := by
  constructor
  case family =>
    intro alpha halpha k hk T
    by_cases hEq : alpha = alpha₀
    · subst hEq; exact Hfam k hk T
    · exact ((evenRouteWitness_nTuple_isEmpty (h := h) (k := k) halpha halpha₀ hEq hrange).false
        T).elim
  case flip =>
    intro alpha halpha k hk T
    by_cases hEq : alpha = alpha₀
    · subst hEq; exact Hflip k hk T
    · exact ((evenRouteWitness_nTuple_isEmpty (h := h) (k := k) halpha halpha₀ hEq hrange).false
        T).elim

end NRigid

/-! ## §3 The `M` depth is not rigid

The honest negative.  `mUnit alpha - 1 = 2 ^ alpha · mUnit alpha`, so `mUnit alpha` lies in every
shallower `imChiM beta`, and the `M` table's remaining values are `1` and `-1`, which lie in every
`imChiM beta` outright.  So a field whose identification is at `beta` has all row values of the
`M` table at every deeper `alpha` inside its character image, and §2's emptiness argument has no
`M` analogue.

This does not refute anything: no tuple is exhibited at a wrong depth, and the wrong-depth flip
demand is not shown false.  What it does is measure the risk.  `EvenRouteCarriedM` and
`EvenRouteCarriedMTwo` are the artefacts the paper is meant to quote, and the first of them is
not known to be equivalent to the single-depth data its own endpoint consumes. -/

section MNotRigid

/-- **The `M` orientation unit does not identify its depth.**  `mUnit alpha ∈ imChiM beta` for
every `2 ≤ beta ≤ alpha`. -/
theorem evenRouteWitness_mUnit_mem_imChiM {alpha beta : ℕ} (hbeta : 2 ≤ beta)
    (hle : beta ≤ alpha) : mUnit alpha ∈ imChiM beta :=
  (evenRange_mem_imChiM_iff hbeta).mpr (Or.inl
    ⟨2 ^ (alpha - beta) * ((mUnit alpha : ℤ_[2]ˣ) : ℤ_[2]), by
      rw [mUnit_sub_one (show 1 ≤ alpha by omega), ← mul_assoc, ← pow_add]
      congr 2
      omega⟩)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

omit [IsTopologicalGroup G] in
/-- **Every wrong-depth `M` row value is still a character value.**  Compare
`evenClimb_vM_mem_range`, which is this statement at `alpha = beta`.  The `N` twin is false as
soon as `alpha ≠ beta`, by §2. -/
theorem evenRouteWitness_vM_mem_range {alpha beta h : ℕ} (hbeta : 2 ≤ beta) (hle : beta ≤ alpha)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM beta)
    (i : Fin (MarkedCore.coreRank h)) : vM alpha i ∈ Set.range chi := by
  have hmem : ∀ u : ℤ_[2]ˣ, u ∈ imChiM beta → u ∈ Set.range chi := by
    intro u hu
    rw [← hrange] at hu
    obtain ⟨g, hg⟩ := hu
    exact ⟨g, hg⟩
  refine evenIndex_cases (P := fun i ↦ vM alpha i ∈ Set.range chi) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vM_zero]; exact hmem 1 (one_mem _)
  · rw [vM_one]; exact hmem (-1) (neg_one_mem_imChiM beta)
  · rw [vM_two]; exact hmem 1 (one_mem _)
  · rw [vM_three]; exact hmem _ (evenRouteWitness_mUnit_mem_imChiM hbeta hle)
  · intro j; rw [vM_handleU]; exact hmem 1 (one_mem _)
  · intro j; rw [vM_handleV]; exact hmem 1 (one_mem _)

end MNotRigid

/-! ## §4 The field-level hypotheses at literal fields

The wave-52 disaster was a hypothesis set with no model.  This section exhibits models, at the
pilot rows of `Instances/Fields.lean`, for everything the even endpoints ask of the field.

`ℚ₂(√−2)` and `ℚ₂(√2)` both have degree `2 = 2 + 2·0`, and both have `K(i)/K` ramified, so both
sit on the even route at `h = 0`.  The bundle binder is supplied by the B5-K axiom
`markedRecipAt`, which is what supplies it everywhere on this route.  What is left in each
statement is the branch sign condition and the two named inputs, and nothing else.

The sign conditions are the classical facts that `√−2 = ζ₈ − ζ₈⁻¹` is negated by complex
conjugation while `√2 = ζ₈ + ζ₈⁻¹` is fixed by it, so `−1 ∉ range χ` on the first field and
`−1 ∈ range χ` on the second.  (Status corrected at wave 67: both are now in the tree,
`EvenRangeModelFields.lean`, the first via exactly this period argument,
`evenRangeF_neg_one_notMem_sqrtNegTwo`, and the second over a base reciprocity bundle,
`evenRangeF_neg_one_mem_sqrtTwo`.) -/

section Literal

/-- **`imChiM 2` is everything.**  Every 2-adic unit is `≡ ±1 (mod 4)`, so on the `α = 2`
stratum the branch identification `range χ = imChiM 2` says exactly `range χ = ⊤`.  This is the
cheapest reading of the binder carried by `evenEndpoint_orientedEquivM_two` and
`evenRoute_orientedEquivM_two`. -/
theorem evenRouteWitness_imChiM_two_eq_top : imChiM 2 = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ (evenRange_mem_imChiM_iff (le_refl 2)).mpr
    (evenRange_four_dvd_sub_or_add u)

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The even `N` endpoint at `ℚ₂(√−2)`.**  Degree, ramification and the reciprocity bundle are
all discharged; the sign condition and the two supplies remain.  So the `N` endpoint is not empty
for any reason visible at the field layer. -/
theorem evenRouteWitness_orientedEquivN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom)
    (Hfam : EvenEndpointNFamily 0 KSqrtNegTwo) (Hflip : EvenEndpointNFlip 0 KSqrtNegTwo) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha 0) (chiCycKTwo (K := KSqrtNegTwo))) := by
  obtain ⟨deltaI, hdeltaI⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄₂) (n := 2) (by norm_num)
  exact evenEndpoint_orientedEquivN (markedRecipAt KSqrtNegTwo) deltaI hdeltaI
    (not_hasEqualNormValueGroups_KSqrtNegTwo deltaI hdeltaI) hneg 0
    (by rw [finrank_KSqrtNegTwo]) Hfam Hflip

/-- **The even `M` endpoint at `ℚ₂(√2)`, from two inputs.**  §1's endpoint at a literal field:
degree and the reciprocity bundle are discharged, the isotropy is W54-BOCK's theorem, and the
`M` branch carries no ramification datum at all.  The sign condition and the two supplies
remain. -/
theorem evenRouteWitness_orientedEquivM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom)
    (Hfam : EvenEndpointMFamily 0 KSqrtTwo) (Hflip : EvenEndpointMFlipOffTwo 0 KSqrtTwo) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha 0) (chiCycKTwo (K := KSqrtTwo))) :=
  evenRouteWitness_orientedEquivM (markedRecipAt KSqrtTwo) hneg 0
    (by rw [finrank_KSqrtTwo]) Hfam Hflip

end Literal

end

end GQ2.Dyadic.EvenRouteWitness

/-! ## §5 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included.

§2 and §3 are two-adic arithmetic and index bookkeeping and print at std-3, the `N` tuple
emptiness and the `N` bundle collapse included: no field cohomology is reached, which is the
point of those statements.

§1 and §4 reach the field layer and print exactly what the statements they compose print.
`evenRouteWitness_carriedM_of_two` prints std-3 plus `tateDualityAt`, which is the print of
`EvenDeepMIsotropicSupply` itself; the three endpoint statements print the endpoint file's
seven-element set, and the two literal-field statements add `markedRecipAt` and
`localReciprocity`, which is the census cost of supplying the bundle binder rather than carrying
it.  That addition is the honest price of §4 and is why the general statements are stated
separately from the literal ones.  No axiom of this file is new. -/

section AxiomPins

open GQ2.Dyadic.EvenRouteWitness

#print axioms evenRouteWitnessScalar
#print axioms evenRouteWitnessContinuousScalar

-- §1 the `M` bundle from two inputs
#print axioms evenRouteWitness_carriedM_of_two
#print axioms evenRouteWitness_orientedEquivM

-- §2 the `N` depth is rigid
#print axioms evenRouteWitness_not_two_dvd_one
#print axioms evenRouteWitness_not_dvd_pow_sub
#print axioms evenRouteWitness_nUnit_mem_imChiN
#print axioms evenRouteWitness_nTuple_isEmpty
#print axioms evenRouteWitness_carriedN_of_atDepth

-- §3 the `M` depth is not rigid
#print axioms evenRouteWitness_mUnit_mem_imChiM
#print axioms evenRouteWitness_vM_mem_range

-- §4 the field-level hypotheses at literal fields
#print axioms evenRouteWitness_imChiM_two_eq_top
#print axioms evenRouteWitness_orientedEquivN_sqrtNegTwo
#print axioms evenRouteWitness_orientedEquivM_sqrtTwo

end AxiomPins
