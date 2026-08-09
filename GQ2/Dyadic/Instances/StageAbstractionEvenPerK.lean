/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenCyclotomicRange
import GQ2.Dyadic.Instances.EvenDemushkin
import GQ2.Dyadic.Instances.StageAbstractionEvenClimbFinal

/-!
# W52-RECUT: the honest per-`K` endpoints of the even forward route

## The supersession this file records

Wave 51 closed the even route at `evenAssembly_orientedEquivN` and `evenAssembly_orientedEquivM`
(`GQ2/Dyadic/Instances/StageAbstractionEvenAssembly.lean` §3), behind six named hypotheses.  One
of the six, `Hrange`, demands the cyclotomic range identity
`MonoidHom.range chiCycKTwo = imChi{N,M} α` uniformly over *every* `K` at one *fixed* `α`.

W52-RANGE then proved the identity itself (`GQ2/Dyadic/Instances/EvenCyclotomicRange.lean`,
`evenRange_range_eq`) and, in the same file, machine-checked that the uniform demand is
inconsistent rather than merely unproved: `rangeFinal_uniform_Hrange_imChiN_absurd` derives
`False` from it, since an odd-degree `K` carrying a marked reciprocity bundle has range `⊤`
while `-1 ∉ imChiN α`.  The `M` twin `rangeFinal_uniform_Hrange_imChiM_forces_two` collapses the
`M` demand to `α = 2`, where `imChiM 2 = ⊤` and the identity says nothing.

So `evenAssembly_orientedEquivN` / `…M`, and with them the EV-1e corollaries
`ev1eFinal_orientedEquivN` / `…M` (`GQ2/Dyadic/Instances/EvenDemushkin.lean` §4), are vacuous as
stated: formally true, and undischargeable.  Those two files are left exactly as they stand, as
artifacts of the wave, with no deprecation attribute; this docstring is the record.  **Their
honest replacements are §6's `evenPerK_orientedEquivN` and `evenPerK_orientedEquivM`**, which
quantify `α` existentially at each field, exactly as the identity produces it, and consume
per-`K` instances of every supply.  The pattern is the committed
`rangeFinal_orientedAbstractEquiv_KTwoN`: because `α` is produced rather than chosen, every
hypothesis mentioning `α` is quantified over `α`.

## What the replacement endpoints land, and why it is the equivalence form

`evenPerK_orientedEquiv{N,M}` conclude `∃ alpha, 2 ≤ alpha ∧ Nonempty
(OrientedContinuousMulEquiv (chi{N,M} alpha h) chiCycKTwo)`, that is the *equivalence* form, not
the abstract-equivalence form of `rangeFinal_orientedAbstractEquiv_KTwoN`.  The reason is
structural, not a strengthening: the forward route
(`GQ2/Dyadic/Instances/EvenForwardRouteSkeleton.lean`) obtains the equivalence from a
forward-generator tuple through `demushkinEpimorphism_bijective`, so it needs no Labute
classification hypothesis, no `demushkinQ`, and no canonicity predicate, which is precisely what
`orientedAbstractEquiv_KTwoN` carries.  Following the abstract-equiv pattern here would mean
adding hypotheses the route does not use.

## The deep re-cut (§1 to §4)

The second correction of this file concerns the level-three frame inputs.
`EvenLevelThree{N,M}FrameInputSupply α` (`StageAbstractionEvenLevelThree.lean` §3) demands
`RowExactLevelFibreLiftSupply`, the depth-`1` fibre lift.  W51-EV4A refuted that statement at
the committed even images for `α ≥ 3` (`evenRow_not_rowSupply_imChiN/M`), and W52 landed the
corrected seam `EvenRowDeepFibreLiftSupply` at depth `s = α - 1`
(`StageAbstractionDeepCorrections.lean`).  This file carries the correction into the per-`K`
layer:

* §1 defines the re-cut per-`K` frame inputs `EvenPerK{N,M}DeepFrameInput` on
  `EvenRowDeepFibreLiftSupply (α - 1)` and discharges them outright from the range identity, on
  both branches and for every `α ≥ 2`;
* §2 machine-checks, per `K`, that the depth-`1` demand they replace is false at `α ≥ 3`, and
  that `EvenLevelThree{N,M}FrameInputSupply α` is therefore false as soon as one even-degree `K`
  realises that branch;
* §3 isolates what the committed frame layer actually consumes, namely the level-`2` instance
  `EvenPerKLevelTwoLift` (`evenFrameExactLift` calls the supply only at `m = 2`), recovers it on
  the `N` branch from the corrected deep seam for every `α ≥ 2`, and refutes it on the `M` branch
  at `α ≥ 3`;
* §4 records the `α = 2` stratum, where the depth-`1` demand is true on both branches and the
  committed level-three base is therefore free from the range identity alone.

**Deviation, machine-checked.**  Because of §2 and §3 the committed level-three station cannot be
run at `α ≥ 3` as it stands: `evenLevelThree{N,M}_stageBase` take the refuted depth-`1` supply,
and the frame assembly `evenFrame_of_kappaPin` takes it as a whole structure, so the level-`2`
instance recovered in §3 cannot be fed to it without re-cutting that file, which is out of scope
here (this file edits nothing).  The endpoints therefore carry the level-three base per `K` as a
named hypothesis `EvenPerK{N,M}StageBase`, in its conclusion shape `Nonempty (Tuple … 3)`, which
is exactly what the finite-level station consumes, and §4 discharges it at `α = 2`.  Nothing in
the chain below the base mentions the refuted supply: the climb consumes the corrected deep seam
`EvenRowDeepFibreLiftSupply (α - 1)`, discharged from the range identity.

## What is discharged and what is carried

Discharged here, per `K`: the range identity (W52-RANGE), the mod-eight image and attainment
seams that follow from it, the corrected deep row seam, the model-side Demushkin package
(W52-EV1E, `evenDem_{n,m}ModelDemushkin`), the topological finite generation of `G_K(2)`, and
the rank identity.

Carried, as named per-`K` hypotheses quantified over `α`, exactly as on the odd route: the
level-three base (`EvenPerK{N,M}StageBase`), the coordinate derivation family with its relator
kill (`EvenPerK{N,M}FamilySupply`), and the raw-to-bracket upgrade
(`EvenPerK{N,M}RawToBracket`).  The last two are the `Hfam` and `Hup` of
`evenClimbFinal_residualSupply{N,M}`, unchanged.

## Numbering

1. the re-cut deep frame inputs, discharged from the range identity;
2. the refuted depth-`1` demand, per `K` and uniform;
3. the level-two instance: recovery on `N`, refutation on `M`;
4. the `α = 2` stratum;
5. the carried per-`K` inputs;
6. the per-`K` endpoints;
7. axiom pins.
-/

namespace GQ2.Dyadic.EvenPerK

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The re-cut level-three frame inputs

`EvenLevelThree{N,M}FrameInputSupply α` pairs the mod-eight orientation seam with the depth-`1`
`RowExactLevelFibreLiftSupply`.  The re-cut keeps the first component and replaces the second by
the corrected seam at depth `α - 1`, and it is stated per field, since the range identity
produces `α` per field.  Unlike the statement it replaces, it is not a hypothesis: §1.2
discharges it from the range identity alone. -/

section DeepFrameInput

variable (α h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The re-cut `N`-row frame inputs at one field.**  The mod-eight orientation seam of EV-3c
together with the corrected row seam at depth `α - 1`, in place of the depth-`1` seam of
`EvenLevelThreeNFrameInputSupply`, which §2 refutes at `α ≥ 3`. -/
def EvenPerKNDeepFrameInput : Prop :=
  EvenDegreeNModEightImage (K := K) α ∧
    EvenRowDeepFibreLiftSupply (α - 1) (vN (h := h) α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))

/-- **The re-cut `M`-row frame inputs at one field.**  The `N` twin plus the attainment seam,
which is the third component of `EvenLevelThreeMFrameInputSupply`. -/
def EvenPerKMDeepFrameInput : Prop :=
  EvenDegreeMModEightImage (K := K) α ∧ EvenDegreeMModEightRowAttained (K := K) α ∧
    EvenRowDeepFibreLiftSupply (α - 1) (vM (h := h) α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))

variable {α h K}

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The `N` re-cut inputs hold**, for every `α ≥ 2`, from the range identity alone.  The
mod-eight seam is `evenRange_evenDegreeNModEightImage` and the deep seam is crux (ii) of the
stage climb, `evenClimb_deepRowSupply_n`. -/
theorem evenPerK_nDeepFrameInput_of_range (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α) :
    EvenPerKNDeepFrameInput α h K :=
  ⟨evenRange_evenDegreeNModEightImage hα hrange, evenClimb_deepRowSupply_n hα hrange⟩

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The `M` re-cut inputs hold**, for every `α ≥ 2`, from the range identity alone. -/
theorem evenPerK_mDeepFrameInput_of_range (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    EvenPerKMDeepFrameInput α h K :=
  ⟨evenRange_evenDegreeMModEightImage hα hrange,
    evenRange_evenDegreeMModEightRowAttained hrange, evenClimb_deepRowSupply_m hα hrange⟩

end DeepFrameInput

/-! ## §2 The depth-`1` demand, refuted per field

W51-EV4A's refutations are stated at an abstract character with a pinned image.  Read at
`chiCycKTwo` through the range identity they say that the second component of
`EvenLevelThree{N,M}FrameInputSupply α` is false at `α ≥ 3`, so that supply cannot be assumed:
one even-degree field on the branch refutes it. -/

section Refutation

variable {α h : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- The depth-`1` row seam is false at the `N` row for `α ≥ 3`: the row value `1` is a character
value, which is all `evenRow_not_rowSupply_imChiN` needs. -/
theorem evenPerK_not_rowSupplyN (hα3 : 3 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    ¬ RowExactLevelFibreLiftSupply (vN (h := h) α) G chi :=
  evenRow_not_rowSupply_imChiN hα3 hrange 0 (evenClimb_vN_mem_range hrange 0)

/-- The depth-`1` row seam is false at the `M` row for `α ≥ 3`. -/
theorem evenPerK_not_rowSupplyM (hα3 : 3 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    ¬ RowExactLevelFibreLiftSupply (vM (h := h) α) G chi :=
  evenRow_not_rowSupply_imChiM hα3 hrange 0 (evenClimb_vM_mem_range hrange 0)

/-- **The `N` frame-input supply is false at `α ≥ 3`.**  One even-degree field whose cyclotomic
range is `imChiN α` refutes the uniform `Prop` that the wave-51 level-three station consumes. -/
theorem evenPerK_not_levelThreeNFrameInputSupply (hα3 : 3 ≤ α)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α) :
    ¬ EvenLevelThreeNFrameInputSupply α := fun H ↦
  evenPerK_not_rowSupplyN hα3 hrange (H K h hdeg).2

/-- **The `M` frame-input supply is false at `α ≥ 3`.** -/
theorem evenPerK_not_levelThreeMFrameInputSupply (hα3 : 3 ≤ α)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    ¬ EvenLevelThreeMFrameInputSupply α := fun H ↦
  evenPerK_not_rowSupplyM hα3 hrange (H K h hdeg).2.2

end Refutation

/-! ## §3 The level-two instance: what the frame layer actually consumes

`evenFrameExactLift` (`StageAbstractionEvenFrameCore.lean` §3) is the only consumer of the row
seam inside the frame construction, and it calls `supply.lift` at `m = 2` and nowhere else: the
Frattini frame is a level-two object, and the sharp shadow it matches against is the mod-eight
datum of the row value.  `EvenPerKLevelTwoLift` is that single instance, stated on
representatives, so it is exactly `EvenRowDeepFibreLiftSupply 1` read at `m = 2`.

The two branches part company here.  On the `N` branch the corrected deep seam still delivers
it, for every `α ≥ 2`: the elements of `imChiN α` that are `≡ 1 (mod 8)` are already `≡ 1
(mod 2^(α+1))`, because the other class of the image is `nUnit α ≡ 3 (mod 4)`.  On the `M`
branch it is false at `α ≥ 3`, and by the same witness as the W51 refutation: `mUnit α` is a
character value, is `≡ 1 (mod 8)`, and has exact level `α`, one digit shallower than
`chi (λ_2 G)` allows. -/

section LevelTwo

variable {n h α : ℕ} {v : Fin n → ℤ_[2]ˣ} {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **The level-two fibre lift at the row values**, on representatives: an element whose
character value matches a row value modulo `8` can be moved, inside its level-two coset, to an
element whose character value is that row value exactly. -/
def EvenPerKLevelTwoLift {n : ℕ} (v : Fin n → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (i : Fin n) (g : G),
    Units.map (PadicInt.toZModPow 3).toMonoidHom (chi g) =
        Units.map (PadicInt.toZModPow 3).toMonoidHom (v i) →
      ∃ x : G, chi x = v i ∧ levelMk G 2 g = levelMk G 2 x

/-- The committed depth-`1` seam implies its level-two instance.  This is the direction that
makes the level-two statement the honest weakening: everything the frame layer takes from the
refuted supply is here. -/
theorem evenPerK_levelTwoLift_of_rowSupply (H : RowExactLevelFibreLiftSupply v G chi) :
    EvenPerKLevelTwoLift v G chi := by
  intro i g hg
  obtain ⟨x, hx1, hx2⟩ := H.lift 2 (le_refl 2) i (levelMk G 2 g)
    (by rw [LSquare.SqCyclotomicStageTuple.sharpChiLevel_levelMk]; exact hg)
  exact ⟨x, hx1, hx2⟩

/-- **The `N`-branch depth transfer.**  Two elements of `imChiN α` that agree modulo `8` agree
modulo `2^(α+1)`.  The four cases of the two-class description `evenRange_mem_imChiN_dvd` are
settled by one arithmetic fact, `nUnit α ≡ 3 (mod 4)`, which rules out the two mixed cases. -/
theorem evenPerK_dvd_of_modEight_imChiN (hα : 2 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : a ∈ imChiN α) (hb : b ∈ imChiN α)
    (h8 : (2 : ℤ_[2]) ^ 3 ∣ (a : ℤ_[2]) - (b : ℤ_[2])) :
    (2 : ℤ_[2]) ^ (α + 1) ∣ (a : ℤ_[2]) - (b : ℤ_[2]) := by
  have hn4 : ¬ ((2 : ℤ_[2]) ^ 2 ∣ ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
    intro hdvd
    have h1 : PadicInt.toZModPow 2 ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 1 :=
      evenRange_toZModPow_eq_one_iff.mpr hdvd
    rw [evenBridgeN_nUnit_modFour hα] at h1
    exact absurd h1 (by decide)
  obtain ⟨e, he⟩ : (2 : ℤ_[2]) ^ 2 ∣ (a : ℤ_[2]) - (b : ℤ_[2]) :=
    (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans h8
  have hred : ∀ {x : ℤ_[2]}, (2 : ℤ_[2]) ^ (α + 1) ∣ x → (2 : ℤ_[2]) ^ 2 ∣ x := fun hx ↦
    (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans hx
  rcases evenRange_mem_imChiN_dvd hα ha with ha' | ha' <;>
    rcases evenRange_mem_imChiN_dvd hα hb with hb' | hb'
  · obtain ⟨c, hc⟩ := ha'
    obtain ⟨d, hd⟩ := hb'
    exact ⟨c - d, by linear_combination hc - hd⟩
  · exfalso
    obtain ⟨c, hc⟩ := hred ha'
    obtain ⟨d, hd⟩ := hred hb'
    exact hn4 ⟨c - d - e, by linear_combination hc - hd - he⟩
  · exfalso
    obtain ⟨c, hc⟩ := hred ha'
    obtain ⟨d, hd⟩ := hred hb'
    exact hn4 ⟨e - c + d, by linear_combination he - hc + hd⟩
  · obtain ⟨c, hc⟩ := ha'
    obtain ⟨d, hd⟩ := hb'
    exact ⟨c - d, by linear_combination hc - hd⟩

/-- **The level-two recovery on the `N` branch.**  For every `α ≥ 2`, the corrected deep seam at
depth `α - 1` delivers the level-two instance the frame layer consumes, even though the depth-`1`
seam itself is false from `α = 3` on (§2). -/
theorem evenPerK_nLevelTwoLift_of_range (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    EvenPerKLevelTwoLift (vN (h := h) α) G chi := by
  intro i g hg
  have hamem : chi g ∈ imChiN α := by
    rw [← hrange]; exact ⟨g, rfl⟩
  have hbmem : vN (h := h) α i ∈ imChiN α := by
    obtain ⟨y, hy⟩ := evenClimb_vN_mem_range (h := h) hrange i
    rw [← hrange]; exact ⟨y, hy⟩
  have h8 : (2 : ℤ_[2]) ^ 3 ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - ((vN (h := h) α i : ℤ_[2]ˣ) : ℤ_[2]) :=
    evenRange_toZModPow_eq_iff.mp (by simpa using congrArg Units.val hg)
  have hdeep : (2 : ℤ_[2]) ^ (2 + (α - 1)) ∣
      ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - ((vN (h := h) α i : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [show 2 + (α - 1) = α + 1 by omega]
    exact evenPerK_dvd_of_modEight_imChiN hα hamem hbmem h8
  exact (evenClimb_deepRowSupply_n (h := h) hα hrange).lift 2 (le_refl 2) i g
    (Units.ext (by simpa using evenRange_toZModPow_eq_iff.mpr hdeep))

/-- **The level-two instance fails on the `M` branch at `α ≥ 3`.**  So the recovery of the
previous theorem is a genuinely `N`-branch phenomenon, and the `M` level-three station has no
route through the committed frame layer at `α ≥ 3`.  The proof is the level-two case of the W51
image-relative refutation, fed by the converse reading of the lift at that single level. -/
theorem evenPerK_not_mLevelTwoLift_of_range (hα3 : 3 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    ¬ EvenPerKLevelTwoLift (vM (h := h) α) G chi := by
  intro H
  refine evenSharp_not_imageRelLe_imChiM hα3 hrange 2 (le_refl 2) fun d hd ↦ ?_
  obtain ⟨hdrange, hdker⟩ := Subgroup.mem_inf.mp hd
  obtain ⟨c, hc⟩ := hdrange
  have hcval : chi c = d := hc
  have hshadow : Units.map (PadicInt.toZModPow 3).toMonoidHom (chi c⁻¹) =
      Units.map (PadicInt.toZModPow 3).toMonoidHom (vM (h := h) α 0) := by
    rw [vM_zero, map_one, map_inv, hcval]
    exact inv_eq_one.mpr (MonoidHom.mem_ker.mp hdker)
  obtain ⟨x, hx1, hx2⟩ := H 0 c⁻¹ hshadow
  have hxone : chi x = 1 := hx1.trans (vM_zero α)
  have hone : levelMk G 2 (c * x) = 1 := by
    rw [map_mul, ← hx2, map_inv, mul_inv_cancel]
  refine ⟨c * x, (QuotientGroup.eq_one_iff _).mp hone, ?_⟩
  show chi (c * x) = d
  rw [map_mul, hxone, mul_one, hcval]

end LevelTwo

/-! ## §4 The `α = 2` stratum

At `α = 2` the depth `α - 1` is `1`, so the corrected seam *is* the committed one, and both
branches satisfy it: on `M` because `imChiM 2 = ⊤` makes the character surjective, on `N`
without surjectivity, by `evenRow_rowSupply_imChiN_two`.  So on this stratum the level-three
base is not a hypothesis at all: the range identity, the ramified-`i` binder in the form
`κ ≠ 0`, and a marked reciprocity bundle produce it. -/

section AlphaTwo

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenPerKScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenPerKContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The level-three base at `α = 2`, `N` branch, with no frame-input hypothesis.**  Both
components of `EvenLevelThreeNFrameInputSupply 2` are consequences of the range identity here:
the mod-eight seam by `evenRange_evenDegreeNModEightImage`, and the depth-`1` row seam, refuted
from `α = 3` on, by `evenRow_rowSupply_imChiN_two`. -/
theorem evenPerK_stageBaseN_two {R : LocalReciprocity} (B : MarkedRecip R K) (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2) :
    Nonempty (Tuple (nStageWord 2 h one_le_two) (vN 2) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) 3) :=
  evenLevelThreeN_stageBase (le_refl 2) B h hdeg hkappa
    (evenRange_evenDegreeNModEightImage (le_refl 2) hrange)
    (evenRow_rowSupply_imChiN_two hrange (evenClimb_vN_mem_range hrange))

/-- **The level-three base at `α = 2`, `M` branch.**  Here `imChiM 2 = ⊤`, so the character is
surjective and the depth-`1` row seam holds for every table; the attainment seam is
`evenRange_evenDegreeMModEightRowAttained`. -/
theorem evenPerK_stageBaseM_two {R : LocalReciprocity} (B : MarkedRecip R K) (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2) :
    Nonempty (Tuple (mStageWord 2 h one_le_two) (vM 2) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) 3) :=
  evenLevelThreeM_stageBase (le_refl 2) B h hdeg hkappa
    (evenRange_evenDegreeMModEightImage (le_refl 2) hrange)
    (evenRange_evenDegreeMModEightRowAttained hrange)
    (evenRow_rowSupply_imChiM_two hrange (vM 2))

end AlphaTwo

/-! ## §5 The carried per-field inputs

Three `Prop`s per branch, each at one field and each quantified over the branch depth `α`, since
`α` is produced by the range identity rather than chosen.  The last two are the `Hfam` and `Hup`
of `evenClimbFinal_residualSupply{N,M}` verbatim; the first is the conclusion shape of the
level-three station, which is what the finite-level layer consumes.  This is the same endpoint
shape the odd route carries at
`nonempty_orientedEquiv_oddDegree_of_family_of_digitRepair`. -/

section Carried

variable (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N` level-three base at one field**, at every branch depth. -/
def EvenPerKNStageBase : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    Nonempty (Tuple (nStageWord alpha h halpha) (vN alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) 3)

/-- **The `M` level-three base at one field**, at every branch depth. -/
def EvenPerKMStageBase : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    Nonempty (Tuple (mStageWord alpha h halpha) (vM alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) 3)

/-- **`Hfam` at one field**: a coordinate derivation family with its relator kill, at every
level and every branch depth. -/
def EvenPerKNFamilySupply : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha) (k : ℕ), 3 ≤ k →
    ∀ T : Tuple (nStageWord alpha h halpha) (vN alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) k, ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **`Hfam` at one field**, `M` branch. -/
def EvenPerKMFamilySupply : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha) (k : ℕ), 3 ≤ k →
    ∀ T : Tuple (mStageWord alpha h halpha) (vM alpha) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)) k, ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **`Hup` at one field**: the raw-to-bracket upgrade at the corrected depth `α - 1`. -/
def EvenPerKNRawToBracket : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    EvenKernelRawToBracketSupply (alpha - 1) (nStageWord alpha h halpha) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **`Hup` at one field**, `M` branch. -/
def EvenPerKMRawToBracket : Prop :=
  ∀ (alpha : ℕ) (halpha : 1 ≤ alpha),
    EvenKernelRawToBracketSupply (alpha - 1) (mStageWord alpha h halpha) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

end Carried

/-! ## §6 The per-`K` endpoints

The replacements announced in the module docstring.  Each field with `K(i)/K` ramified gets its
own branch depth `α ≥ 2` from the range identity, and the whole even machinery is run at that
`α`: the corrected deep row seam (crux (ii)), the residual supply of the climb, the finite-level
inverse limit, the model-side Demushkin package, and the forward rigidity bypass.  No hypothesis
of any of these statements is quantified over fields.

The branch inputs are those of `evenRange_range_eq_imChi{N,M}`: the `N` endpoint carries the
ramified-`i` datum and `-1 ∉ im χ`, and the `M` endpoint carries `-1 ∈ im χ` and no ramification
input at all, since `-1` is itself a witness that the range escapes `1 + 4ℤ₂`. -/

section Endpoints

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N` forward-generator package at one field and one branch depth.**  The stage climb
with its two named inputs, against the corrected deep seam, then the finite-level station.  This
is `evenAssembly_nForwardSupply` with every uniform-in-`K` quantifier removed. -/
theorem evenPerK_forwardGeneratorDataN {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (base : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha))
        (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hup : EvenKernelRawToBracketSupply (alpha - 1)
      (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (NForwardGeneratorData alpha h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataN_of_base_and_corrections (Nat.le_of_succ_le halpha)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K) base fun _k hk T ↦
      evenClimb_defectReachable hk T (evenClimbFinal_residualSupplyN K halpha Hfam Hup)
        (evenSharpDbarShiftSupply_n halpha (Nat.le_of_succ_le halpha) hk)
        (evenClimb_deepRowSupply_n halpha hrange)

/-- **The `M` forward-generator package at one field and one branch depth.** -/
theorem evenPerK_forwardGeneratorDataM {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (base : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha))
        (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hup : EvenKernelRawToBracketSupply (alpha - 1)
      (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (MForwardGeneratorData alpha h (chiCycKTwo (K := K))) :=
  evenForwardGeneratorDataM_of_base_and_corrections (Nat.le_of_succ_le halpha)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K) base fun _k hk T ↦
      evenClimb_defectReachable hk T (evenClimbFinal_residualSupplyM K halpha Hfam Hup)
        (evenSharpDbarShiftSupply_m halpha (Nat.le_of_succ_le halpha) hk)
        (evenClimb_deepRowSupply_m halpha hrange)

/-- **The even `N` endpoint, per field.**  Every even-degree dyadic field of degree `2 + 2h`
whose `K(i)` is ramified and whose cyclotomic range omits `-1` has a branch depth `α ≥ 2`, its
own, at which its maximal pro-`2` Galois group is oriented-isomorphic to the presented `N` core.

This supersedes `evenAssembly_orientedEquivN` and `ev1eFinal_orientedEquivN`, whose uniform
`Hrange` is inconsistent by `rangeFinal_uniform_Hrange_imChiN_absurd`.  What is carried here is
carried per field and at every depth: the level-three base, the derivation family with its
relator kill, and the raw-to-bracket upgrade.  Everything else, in particular the image
identification and the corrected deep row seam, is discharged. -/
theorem evenPerK_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hbase : EvenPerKNStageBase h K) (Hfam : EvenPerKNFamilySupply h K)
    (Hup : EvenPerKNRawToBracket h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  obtain ⟨base⟩ := Hbase alpha (Nat.le_of_succ_le halpha)
  exact ⟨alpha, halpha, nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_nModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataN halpha hrange base
      (Hfam alpha (Nat.le_of_succ_le halpha)) (Hup alpha (Nat.le_of_succ_le halpha)))⟩

/-- **The even `M` endpoint, per field.**  The `M` twin, with `-1 ∈ im χ` in place of the two
`N` branch inputs; no ramification datum is needed, exactly as in `evenRange_range_eq_imChiM`.

This supersedes `evenAssembly_orientedEquivM` and `ev1eFinal_orientedEquivM`, whose uniform
`Hrange` forces `α = 2` by `rangeFinal_uniform_Hrange_imChiM_forces_two`, where `imChiM 2 = ⊤`
and the hypothesis carries no information. -/
theorem evenPerK_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hbase : EvenPerKMStageBase h K) (Hfam : EvenPerKMFamilySupply h K)
    (Hup : EvenPerKMRawToBracket h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  obtain ⟨base⟩ := Hbase alpha (Nat.le_of_succ_le halpha)
  exact ⟨alpha, halpha, nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_mModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataM halpha hrange base
      (Hfam alpha (Nat.le_of_succ_le halpha)) (Hup alpha (Nat.le_of_succ_le halpha)))⟩

end Endpoints

end

end GQ2.Dyadic.EvenPerK

/-! ## §7 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included.  §1 to §3 are character-level statements and are expected at std-3
(`propext`, `Classical.choice`, `Quot.sound`) together with whatever the committed range
identity and the committed refutations carry.  §4 and §6 additionally reach the field layer, so
they acquire exactly the census axioms of their committed inputs: the level-three base, the
marked reciprocity clauses of the range identity, and
`absGalQ2_isTopologicallyFinitelyGenerated`, which is where the odd route acquires its own
finite-generation input as well.  No axiom of this file is new. -/

section AxiomPins

open GQ2.Dyadic.EvenPerK

-- §1 the re-cut deep frame inputs
#print axioms EvenPerKNDeepFrameInput
#print axioms EvenPerKMDeepFrameInput
#print axioms evenPerK_nDeepFrameInput_of_range
#print axioms evenPerK_mDeepFrameInput_of_range

-- §2 the refuted depth-one demand
#print axioms evenPerK_not_rowSupplyN
#print axioms evenPerK_not_rowSupplyM
#print axioms evenPerK_not_levelThreeNFrameInputSupply
#print axioms evenPerK_not_levelThreeMFrameInputSupply

-- §3 the level-two instance
#print axioms EvenPerKLevelTwoLift
#print axioms evenPerK_levelTwoLift_of_rowSupply
#print axioms evenPerK_dvd_of_modEight_imChiN
#print axioms evenPerK_nLevelTwoLift_of_range
#print axioms evenPerK_not_mLevelTwoLift_of_range

-- §4 the `α = 2` stratum, and its two coefficient-action instances
#print axioms evenPerKScalar
#print axioms evenPerKContinuousScalar
#print axioms evenPerK_stageBaseN_two
#print axioms evenPerK_stageBaseM_two

-- §5 the carried per-field inputs
#print axioms EvenPerKNStageBase
#print axioms EvenPerKMStageBase
#print axioms EvenPerKNFamilySupply
#print axioms EvenPerKMFamilySupply
#print axioms EvenPerKNRawToBracket
#print axioms EvenPerKMRawToBracket

-- §6 the per-field endpoints
#print axioms evenPerK_forwardGeneratorDataN
#print axioms evenPerK_forwardGeneratorDataM
#print axioms evenPerK_orientedEquivN
#print axioms evenPerK_orientedEquivM

end AxiomPins
