/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.LabuteInterface

/-!
# What core automorphisms can and cannot do to the Labute orientation

The marked-correction automorphisms constructed for the `M`, `N`, and square-commutator
cores preserve their canonical character.  Consequently they can normalize the second marking
only after an abstract equivalence is oriented; they cannot turn an unoriented equivalence into
an oriented one.

This file makes that boundary formal.  It also proves the previously implicit exact image
equalities for `chiM` and `chiN`, and exhibits the inverse characters as continuous characters
with exactly the same image but different values.  Thus equality of character images is not, by
itself, an orientation-correction principle.

The positive interface is generator-level: the already-proved uniqueness of the `M`/`N`
Labute data, and the corresponding three-value contraction for `DSq`, turn concrete core-value
and handle-value calculations into an actually oriented equivalence.
-/

namespace GQ2.Dyadic

open GQ2
open MarkedCore SqCore

noncomputable section

/-! ## Generic composition and image lemmas -/

section Generic

variable {C G A : Type} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A]

/-- Pointwise orientation compatibility for an equivalence from a presented core to a target. -/
def OrientationMatches (chiC : C →* A) (chiG : G →* A) (e : ContinuousMulEquiv C G) : Prop :=
  ∀ x, chiG (e x) = chiC x

omit [IsTopologicalGroup C] [IsTopologicalGroup G] in
/-- Precomposing by a character-preserving core automorphism does not change whether an
equivalence is orientation-compatible. -/
theorem orientationMatches_trans_iff (chiC : C →* A) (chiG : G →* A)
    (e : ContinuousMulEquiv C G) (u : ContinuousMulEquiv C C)
    (hu : ∀ x, chiC (u x) = chiC x) :
    OrientationMatches chiC chiG (u.trans e) ↔ OrientationMatches chiC chiG e := by
  constructor
  · intro h x
    have hx := h (u.symm x)
    have hux := hu (u.symm x)
    have hx' : chiG (e x) = chiC (u.symm x) := by simpa using hx
    have hux' : chiC x = chiC (u.symm x) := by simpa using hux
    exact hx'.trans hux'.symm
  · intro h x
    exact (h (u x)).trans (hu x)

omit [IsTopologicalGroup C] [IsTopologicalGroup G] in
/-- In particular, a character-preserving marked correction cannot repair a pre-existing
orientation mismatch. -/
theorem not_orientationMatches_trans_iff (chiC : C →* A) (chiG : G →* A)
    (e : ContinuousMulEquiv C G) (u : ContinuousMulEquiv C C)
    (hu : ∀ x, chiC (u x) = chiC x) :
    ¬ OrientationMatches chiC chiG (u.trans e) ↔ ¬ OrientationMatches chiC chiG e := by
  rw [orientationMatches_trans_iff chiC chiG e u hu]

variable [TopologicalSpace A] [IsTopologicalGroup A]

/-- Pull a continuous character back along a continuous group equivalence. -/
def pullbackCharacter (chiG : ContinuousMonoidHom G A) (e : ContinuousMulEquiv C G) :
    ContinuousMonoidHom C A where
  toFun x := chiG (e x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := chiG.continuous_toFun.comp e.continuous_toFun

/-- An actual equivalence together with the orientation equation consumed by the marked-core
certificate layer. -/
def OrientedContinuousMulEquiv (chiC : ContinuousMonoidHom C A)
    (chiG : ContinuousMonoidHom G A) : Type :=
  {e : ContinuousMulEquiv C G // OrientationMatches chiC.toMonoidHom chiG.toMonoidHom e}

/-- A character predicate singles out `chi` uniquely.  This is deliberately a property of a
predicate already supplied by the mathematics, not a proposed definition of the (as yet
unformalized) dualizing-module orientation. -/
def CharacterizesCharacter (P : ContinuousMonoidHom C A → Prop)
    (chi : ContinuousMonoidHom C A) : Prop :=
  P chi ∧ ∀ chi', P chi' → chi' = chi

/-- Pullback naturality for character predicates across continuous group equivalences. -/
def PullbackNatural (PC : ContinuousMonoidHom C A → Prop)
    (PG : ContinuousMonoidHom G A → Prop) : Prop :=
  ∀ (e : ContinuousMulEquiv C G) (chi : ContinuousMonoidHom G A),
    PG chi → PC (pullbackCharacter chi e)

/-- **Naturality plus uniqueness orients an abstract equivalence.**  This is the exact formal
transport principle needed after an unoriented Labute-classification output: pull the target
character predicate back along the supplied equivalence, then use uniqueness on the standard
core.  The theorem assumes no new orientation or classification principle. -/
def orientedEquiv_of_natural_unique
    (PC : ContinuousMonoidHom C A → Prop) (PG : ContinuousMonoidHom G A → Prop)
    (chiC : ContinuousMonoidHom C A) (chiG : ContinuousMonoidHom G A)
    (hcore : CharacterizesCharacter PC chiC) (hnatural : PullbackNatural PC PG)
    (hG : PG chiG) (e : ContinuousMulEquiv C G) :
    OrientedContinuousMulEquiv chiC chiG := by
  have hpull : PC (pullbackCharacter chiG e) := hnatural e chiG hG
  have heq : pullbackCharacter chiG e = chiC := hcore.2 _ hpull
  exact ⟨e, fun x => DFunLike.congr_fun heq x⟩

/-- Pointwise inversion of a continuous character into a commutative topological group. -/
def inverseCharacter (chi : ContinuousMonoidHom C A) : ContinuousMonoidHom C A where
  toFun x := (chi x)⁻¹
  map_one' := by simp
  map_mul' x y := by rw [map_mul, mul_inv_rev, mul_comm]
  continuous_toFun := chi.continuous_toFun.inv

omit [IsTopologicalGroup C] in
/-- Inverting every value of a character leaves its image subgroup unchanged. -/
theorem range_inverseCharacter (chi : ContinuousMonoidHom C A) :
    MonoidHom.range (inverseCharacter chi).toMonoidHom = MonoidHom.range chi.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x⁻¹, ?_⟩
    change chi (x⁻¹) = (chi x)⁻¹
    simp
  · rintro ⟨x, rfl⟩
    refine ⟨x⁻¹, ?_⟩
    change (chi (x⁻¹))⁻¹ = chi x
    simp

end Generic

/-! ## Why the mod-two cup--Bockstein layer cannot choose the orientation

Every `2`-adic unit has the same reduction in `ZMod 2`.  Thus a character and its pointwise
inverse induce literally equal mod-two scalar functions.  This does not rule out a future
integral dualizing-module characterization, but it formally records why the repository's
present mod-two cup and Bockstein data cannot distinguish the counterexamples below. -/

section ModTwoBlindness

variable {C : Type} [Group C] [TopologicalSpace C]

/-- Every value of a `2`-adic-unit character reduces to `1` modulo `2`. -/
theorem character_toZModPow_one (chi : ContinuousMonoidHom C ℤ_[2]ˣ) (x : C) :
    PadicInt.toZModPow 1 ((chi x : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  haveI : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  have hunit : IsUnit (PadicInt.toZModPow 1 ((chi x : ℤ_[2]ˣ) : ℤ_[2])) :=
    (chi x).isUnit.map (PadicInt.toZModPow (p := 2) 1)
  exact (by decide : ∀ z : ZMod (2 ^ 1), z ≠ 0 → z = 1) _ hunit.ne_zero

/-- In particular, mod-two scalar reduction sees no difference between a character and its
pointwise inverse. -/
theorem inverseCharacter_modTwo_eq (chi : ContinuousMonoidHom C ℤ_[2]ˣ) :
    (fun x => PadicInt.toZModPow 1 (((inverseCharacter chi) x : ℤ_[2]ˣ) : ℤ_[2])) =
      fun x => PadicInt.toZModPow 1 ((chi x : ℤ_[2]ˣ) : ℤ_[2]) := by
  funext x
  rw [character_toZModPow_one, character_toZModPow_one]

end ModTwoBlindness

/-! ## Exact images of the standard even-rank characters -/

section Images

/-- The image of the canonical `M` character is exactly the closed subgroup used in
`MLabHypothesis`, not merely a subgroup containing its two displayed generators. -/
theorem range_chiM (alpha h : ℕ) :
    MonoidHom.range (chiM alpha h).toMonoidHom = imChiM alpha := by
  apply le_antisymm
  · let H := Subgroup.comap (chiM alpha h).toMonoidHom (imChiM alpha)
    have hgen : Subgroup.closure (Set.range (dmGen alpha h)) ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · change chiM alpha h (dmA alpha h) ∈ imChiM alpha
        simp
      · change chiM alpha h (dmB alpha h) ∈ imChiM alpha
        simpa using neg_one_mem_imChiM alpha
      · change chiM alpha h (dmC alpha h) ∈ imChiM alpha
        simp
      · change chiM alpha h (dmD alpha h) ∈ imChiM alpha
        simpa using mUnit_mem_imChiM alpha
      · change chiM alpha h (dmGen alpha h (handleIdxU j)) ∈ imChiM alpha
        simp
      · change chiM alpha h (dmGen alpha h (handleIdxV j)) ∈ imChiM alpha
        simp
    have hclosed : IsClosed (H : Set (DM alpha h : Type)) := by
      exact (Subgroup.isClosed_topologicalClosure _).preimage (chiM alpha h).continuous_toFun
    have htop : (Subgroup.closure (Set.range (dmGen alpha h))).topologicalClosure ≤ H :=
      Subgroup.topologicalClosure_minimal _ hgen hclosed
    rw [dm_topGen] at htop
    rintro y ⟨x, rfl⟩
    exact htop (Subgroup.mem_top x)
  · have hclosed : IsClosed (MonoidHom.range (chiM alpha h).toMonoidHom : Set ℤ_[2]ˣ) := by
      rw [MonoidHom.coe_range]
      exact (isCompact_range (chiM alpha h).continuous_toFun).isClosed
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨dmB alpha h, chiM_dmB alpha h⟩
    · exact ⟨dmD alpha h, chiM_dmD alpha h⟩

/-- The corresponding exact image theorem for the procyclic `N` character. -/
theorem range_chiN (alpha h : ℕ) :
    MonoidHom.range (chiN alpha h).toMonoidHom = imChiN alpha := by
  apply le_antisymm
  · let H := Subgroup.comap (chiN alpha h).toMonoidHom (imChiN alpha)
    have hgen : Subgroup.closure (Set.range (dnGen alpha h)) ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · change chiN alpha h (dnX0 alpha h) ∈ imChiN alpha
        simp
      · change chiN alpha h (dnX1 alpha h) ∈ imChiN alpha
        rw [chiN_dnX1, imChiN]
        exact Subgroup.le_topologicalClosure
          (Subgroup.closure {(nUnit alpha : ℤ_[2]ˣ)})
          (Subgroup.subset_closure (Set.mem_singleton (nUnit alpha)))
      · change chiN alpha h (dnSigma alpha h) ∈ imChiN alpha
        simp
      · change chiN alpha h (dnX2 alpha h) ∈ imChiN alpha
        simp
      · change chiN alpha h (dnGen alpha h (handleIdxU j)) ∈ imChiN alpha
        simp
      · change chiN alpha h (dnGen alpha h (handleIdxV j)) ∈ imChiN alpha
        simp
    have hclosed : IsClosed (H : Set (DN alpha h : Type)) := by
      exact (Subgroup.isClosed_topologicalClosure _).preimage (chiN alpha h).continuous_toFun
    have htop : (Subgroup.closure (Set.range (dnGen alpha h))).topologicalClosure ≤ H :=
      Subgroup.topologicalClosure_minimal _ hgen hclosed
    rw [dn_topGen] at htop
    rintro y ⟨x, rfl⟩
    exact htop (Subgroup.mem_top x)
  · have hclosed : IsClosed (MonoidHom.range (chiN alpha h).toMonoidHom : Set ℤ_[2]ˣ) := by
      rw [MonoidHom.coe_range]
      exact (isCompact_range (chiN alpha h).continuous_toFun).isClosed
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    rw [Subgroup.closure_le]
    rintro _ rfl
    exact ⟨dnX1 alpha h, chiN_dnX1 alpha h⟩

end Images

/-! ## Same-image noncanonical characters -/

section Counterexamples

/-- The inverse of the canonical `M` character. -/
def inverseChiM (alpha h : ℕ) : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ :=
  inverseCharacter (chiM alpha h)

/-- The inverse `M` character has exactly the classification image `imChiM`. -/
theorem range_inverseChiM (alpha h : ℕ) :
    MonoidHom.range (inverseChiM alpha h).toMonoidHom = imChiM alpha :=
  (range_inverseCharacter (chiM alpha h)).trans (range_chiM alpha h)

/-- At every valid depth, the inverse `M` character is not the canonical character. -/
theorem inverseChiM_ne_chiM {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ) :
    inverseChiM alpha h ≠ chiM alpha h := by
  intro heq
  have hd := DFunLike.congr_fun heq (dmD alpha h)
  change (chiM alpha h (dmD alpha h))⁻¹ = chiM alpha h (dmD alpha h) at hd
  have hd' : (mUnit alpha)⁻¹ = mUnit alpha := by simpa using hd
  have hneg : zpowZtwo isProP_two_unitsPadicInt (mUnit alpha) ((-1 : ℤ) : ℤ_[2]) =
      (mUnit alpha)⁻¹ :=
    (zpowZtwo_intCast isProP_two_unitsPadicInt (mUnit alpha) (-1)).trans
      (zpow_neg_one (mUnit alpha))
  have hone : zpowZtwo isProP_two_unitsPadicInt (mUnit alpha) ((1 : ℤ) : ℤ_[2]) =
      mUnit alpha :=
    (zpowZtwo_intCast isProP_two_unitsPadicInt (mUnit alpha) 1).trans
      (zpow_one (mUnit alpha))
  have hpow :
      zpowZtwo isProP_two_unitsPadicInt (mUnit alpha) ((-1 : ℤ) : ℤ_[2]) =
        zpowZtwo isProP_two_unitsPadicInt (mUnit alpha) ((1 : ℤ) : ℤ_[2]) := by
    exact hneg.trans (hd'.trans hone.symm)
  have hexp := mUnit_zpow_injective halpha hpow
  norm_num at hexp

/-- Hence image equality does not orient even the identity equivalence on the `M` core. -/
theorem inverseChiM_not_orientationMatches {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ) :
    ¬ OrientationMatches (chiM alpha h).toMonoidHom (inverseChiM alpha h).toMonoidHom
      (ContinuousMulEquiv.refl (DM alpha h : Type)) := by
  intro hmatch
  apply inverseChiM_ne_chiM halpha h
  exact ContinuousMonoidHom.ext fun x => hmatch x

/-- No automorphism in the stabilizer of `chiM` can correct the same-image inverse character. -/
theorem inverseChiM_not_correctable {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ)
    (u : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hu : ∀ x, chiM alpha h (u x) = chiM alpha h x) :
    ¬ OrientationMatches (chiM alpha h).toMonoidHom (inverseChiM alpha h).toMonoidHom u := by
  have hno := (not_orientationMatches_trans_iff (chiM alpha h).toMonoidHom
    (inverseChiM alpha h).toMonoidHom (ContinuousMulEquiv.refl _) u hu).2
      (inverseChiM_not_orientationMatches halpha h)
  intro hmatch
  apply hno
  intro x
  simpa [OrientationMatches] using hmatch x

/-- The inverse of the canonical `N` character. -/
def inverseChiN (alpha h : ℕ) : ContinuousMonoidHom (DN alpha h : Type) ℤ_[2]ˣ :=
  inverseCharacter (chiN alpha h)

/-- The inverse `N` character has exactly the classification image `imChiN`. -/
theorem range_inverseChiN (alpha h : ℕ) :
    MonoidHom.range (inverseChiN alpha h).toMonoidHom = imChiN alpha :=
  (range_inverseCharacter (chiN alpha h)).trans (range_chiN alpha h)

/-- At every valid depth, the inverse `N` character is not the canonical character. -/
theorem inverseChiN_ne_chiN {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ) :
    inverseChiN alpha h ≠ chiN alpha h := by
  intro heq
  have hx1 := DFunLike.congr_fun heq (dnX1 alpha h)
  change (chiN alpha h (dnX1 alpha h))⁻¹ = chiN alpha h (dnX1 alpha h) at hx1
  have hx1' : (nUnit alpha)⁻¹ = nUnit alpha := by simpa using hx1
  have hneg : zpowZtwo isProP_two_unitsPadicInt (nUnit alpha) ((-1 : ℤ) : ℤ_[2]) =
      (nUnit alpha)⁻¹ :=
    (zpowZtwo_intCast isProP_two_unitsPadicInt (nUnit alpha) (-1)).trans
      (zpow_neg_one (nUnit alpha))
  have hone : zpowZtwo isProP_two_unitsPadicInt (nUnit alpha) ((1 : ℤ) : ℤ_[2]) =
      nUnit alpha :=
    (zpowZtwo_intCast isProP_two_unitsPadicInt (nUnit alpha) 1).trans
      (zpow_one (nUnit alpha))
  have hpow :
      zpowZtwo isProP_two_unitsPadicInt (nUnit alpha) ((-1 : ℤ) : ℤ_[2]) =
        zpowZtwo isProP_two_unitsPadicInt (nUnit alpha) ((1 : ℤ) : ℤ_[2]) := by
    exact hneg.trans (hx1'.trans hone.symm)
  have hexp := nUnit_zpowZtwo_injective halpha hpow
  norm_num at hexp

/-- Hence image equality does not orient even the identity equivalence on the `N` core. -/
theorem inverseChiN_not_orientationMatches {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ) :
    ¬ OrientationMatches (chiN alpha h).toMonoidHom (inverseChiN alpha h).toMonoidHom
      (ContinuousMulEquiv.refl (DN alpha h : Type)) := by
  intro hmatch
  apply inverseChiN_ne_chiN halpha h
  exact ContinuousMonoidHom.ext fun x => hmatch x

/-- No automorphism in the stabilizer of `chiN` can correct the same-image inverse character. -/
theorem inverseChiN_not_correctable {alpha : ℕ} (halpha : 2 ≤ alpha) (h : ℕ)
    (u : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (hu : ∀ x, chiN alpha h (u x) = chiN alpha h x) :
    ¬ OrientationMatches (chiN alpha h).toMonoidHom (inverseChiN alpha h).toMonoidHom u := by
  have hno := (not_orientationMatches_trans_iff (chiN alpha h).toMonoidHom
    (inverseChiN alpha h).toMonoidHom (ContinuousMulEquiv.refl _) u hu).2
      (inverseChiN_not_orientationMatches halpha h)
  intro hmatch
  apply hno
  intro x
  simpa [OrientationMatches] using hmatch x

end Counterexamples

/-! ## Positive recognition from the presentation-level data -/

section Recognition

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The actual presented-core predicates

These predicates package the improved closed-form four-letter descent data together with
triviality on all appended handles.  They are presentation-level recognition predicates, not a
definition of the intrinsic dualizing orientation on an arbitrary profinite group. -/

/-- The complete presentation-level orientation predicate for the improved `M` core. -/
def IsPresentedOrientationM (alpha h : ℕ)
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ) : Prop :=
  IsLabuteOrientationDatumM alpha
      (chi (dmA alpha h)) (chi (dmB alpha h)) (chi (dmC alpha h)) (chi (dmD alpha h)) ∧
    (∀ j : Fin h, chi (dmGen alpha h (handleIdxU j)) = 1) ∧
    ∀ j : Fin h, chi (dmGen alpha h (handleIdxV j)) = 1

/-- The complete presentation-level orientation predicate for the improved `N` core. -/
def IsPresentedOrientationN (alpha h : ℕ)
    (chi : ContinuousMonoidHom (DN alpha h : Type) ℤ_[2]ˣ) : Prop :=
  IsLabuteOrientationDatumN alpha
      (chi (dnX0 alpha h)) (chi (dnX1 alpha h)) (chi (dnSigma alpha h))
      (chi (dnX2 alpha h)) ∧
    (∀ j : Fin h, chi (dnGen alpha h (handleIdxU j)) = 1) ∧
    ∀ j : Fin h, chi (dnGen alpha h (handleIdxV j)) = 1

/-- The improved closed-form `M` character satisfies its full presented-core predicate. -/
theorem isPresentedOrientationM_chiM {alpha : ℕ} (h : ℕ) (halpha : 1 ≤ alpha) :
    IsPresentedOrientationM alpha h (chiM alpha h) := by
  exact ⟨chiM_isLabuteOrientationDatum h halpha,
    fun j => chiM_handleU alpha h j, fun j => chiM_handleV alpha h j⟩

/-- The improved closed-form `N` character satisfies its full presented-core predicate. -/
theorem isPresentedOrientationN_chiN {alpha : ℕ} (h : ℕ) (halpha : 1 ≤ alpha) :
    IsPresentedOrientationN alpha h (chiN alpha h) := by
  exact ⟨chiN_isLabuteOrientationDatum h halpha,
    fun j => chiN_handleU alpha h j, fun j => chiN_handleV alpha h j⟩

/-- The full `M` presented-core predicate characterizes `chiM` pointwise. -/
theorem isPresentedOrientationM_iff {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (chi : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ) :
    IsPresentedOrientationM alpha h chi ↔ chi = chiM alpha h := by
  constructor
  · rintro ⟨hdatum, hU, hV⟩
    exact ContinuousMonoidHom.ext fun x => chiM_matching halpha chi hdatum hU hV x
  · rintro rfl
    exact isPresentedOrientationM_chiM h halpha

/-- The full `N` presented-core predicate characterizes `chiN` pointwise. -/
theorem isPresentedOrientationN_iff {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (chi : ContinuousMonoidHom (DN alpha h : Type) ℤ_[2]ˣ) :
    IsPresentedOrientationN alpha h chi ↔ chi = chiN alpha h := by
  constructor
  · rintro ⟨hdatum, hU, hV⟩
    exact ContinuousMonoidHom.ext fun x => chiN_matching halpha chi hdatum hU hV x
  · rintro rfl
    exact isPresentedOrientationN_chiN h halpha

/-- Uniqueness package for the improved `M` presentation. -/
theorem characterizes_isPresentedOrientationM {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    CharacterizesCharacter (IsPresentedOrientationM alpha h) (chiM alpha h) :=
  ⟨isPresentedOrientationM_chiM h halpha,
    fun chi hchi => (isPresentedOrientationM_iff halpha chi).mp hchi⟩

/-- Uniqueness package for the improved `N` presentation. -/
theorem characterizes_isPresentedOrientationN {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    CharacterizesCharacter (IsPresentedOrientationN alpha h) (chiN alpha h) :=
  ⟨isPresentedOrientationN_chiN h halpha,
    fun chi hchi => (isPresentedOrientationN_iff halpha chi).mp hchi⟩

/-- A target-side intrinsic predicate orients every abstract `M` equivalence as soon as it is
natural under pullback to the proved presentation-level predicate. -/
def orientedEquivM_of_pullback_natural {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (PG : ContinuousMonoidHom G ℤ_[2]ˣ → Prop)
    (hnatural : PullbackNatural (IsPresentedOrientationM alpha h) PG)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) (hG : PG chiG)
    (f : ContinuousMulEquiv (DM alpha h : Type) G) :
    OrientedContinuousMulEquiv (chiM alpha h) chiG :=
  orientedEquiv_of_natural_unique _ _ _ _
    (characterizes_isPresentedOrientationM halpha) hnatural hG f

/-- The corresponding transport theorem for the improved `N` presentation. -/
def orientedEquivN_of_pullback_natural {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (PG : ContinuousMonoidHom G ℤ_[2]ˣ → Prop)
    (hnatural : PullbackNatural (IsPresentedOrientationN alpha h) PG)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) (hG : PG chiG)
    (f : ContinuousMulEquiv (DN alpha h : Type) G) :
    OrientedContinuousMulEquiv (chiN alpha h) chiG :=
  orientedEquiv_of_natural_unique _ _ _ _
    (characterizes_isPresentedOrientationN halpha) hnatural hG f

/-- The precise positive precursor on the `M` side: no automorphism is required.  Once the
pulled character satisfies the unique four-value Labute datum and is trivial on every handle,
the supplied abstract equivalence itself is oriented. -/
def orientedEquivM_of_datum {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ)
    (f : ContinuousMulEquiv (DM alpha h : Type) G)
    (hdatum : IsLabuteOrientationDatumM alpha
      (chiG (f (dmA alpha h))) (chiG (f (dmB alpha h)))
      (chiG (f (dmC alpha h))) (chiG (f (dmD alpha h))))
    (hU : ∀ j : Fin h, chiG (f (dmGen alpha h (handleIdxU j))) = 1)
    (hV : ∀ j : Fin h, chiG (f (dmGen alpha h (handleIdxV j))) = 1) :
    OrientedContinuousMulEquiv (chiM alpha h) chiG :=
  ⟨f, chiM_matching halpha (pullbackCharacter chiG f) hdatum hU hV⟩

/-- The corresponding positive precursor on the `N` side. -/
def orientedEquivN_of_datum {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ)
    (f : ContinuousMulEquiv (DN alpha h : Type) G)
    (hdatum : IsLabuteOrientationDatumN alpha
      (chiG (f (dnX0 alpha h))) (chiG (f (dnX1 alpha h)))
      (chiG (f (dnSigma alpha h))) (chiG (f (dnX2 alpha h))))
    (hU : ∀ j : Fin h, chiG (f (dnGen alpha h (handleIdxU j))) = 1)
    (hV : ∀ j : Fin h, chiG (f (dnGen alpha h (handleIdxV j))) = 1) :
    OrientedContinuousMulEquiv (chiN alpha h) chiG :=
  ⟨f, chiN_matching halpha (pullbackCharacter chiG f) hdatum hU hV⟩

/-- The odd square-commutator precursor is deliberately stated separately.  At general handle
count the repository has generator-value recognition, but no theorem transporting the rank-three
`BLabHypothesis` or the `DR` descent predicate to arbitrary `DSq h`. -/
def orientedEquivSq_of_values {h : ℕ} (chiG : ContinuousMonoidHom G ℤ_[2]ˣ)
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (hsigma : chiG (f (dsqSigma h)) = Roe.SvalUnit)
    (hx0 : chiG (f (dsqX0 h)) = Roe.rootXUnit)
    (hx1 : chiG (f (dsqX1 h)) = Roe.YvalUnit)
    (hU : ∀ j : Fin h, chiG (f (sqGen h (sqHandleIdxU j))) = 1)
    (hV : ∀ j : Fin h, chiG (f (sqGen h (sqHandleIdxV j))) = 1) :
    OrientedContinuousMulEquiv (chiSq h) chiG := by
  have hsigma' : (pullbackCharacter chiG f) (dsqSigma h) = Roe.SvalUnit := by
    exact hsigma
  have hx0' : (pullbackCharacter chiG f) (dsqX0 h) = Roe.rootXUnit := by
    exact hx0
  have hx1' : (pullbackCharacter chiG f) (dsqX1 h) = Roe.YvalUnit := by
    exact hx1
  have hU' : ∀ j : Fin h, (pullbackCharacter chiG f) (sqGen h (sqHandleIdxU j)) = 1 :=
    hU
  have hV' : ∀ j : Fin h, (pullbackCharacter chiG f) (sqGen h (sqHandleIdxV j)) = 1 :=
    hV
  exact ⟨f, chiSq_matching (pullbackCharacter chiG f) hsigma' hx0' hx1' hU' hV'⟩

end Recognition

/-! ## Orientation recovery from the existing even-rank classification interfaces

These two theorems consume the *existing* `MLabHypothesis`/`NLabHypothesis` outputs.  Their
extra premise is exactly the still-missing intrinsic statement: a target-side canonical
predicate must pull back to the proved presentation-level predicate.  In particular the
theorems neither strengthen the Labute hypotheses nor infer character equality from image
equality. -/

section AbstractClassificationOrientation

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]

omit [FiniteDimensional ℚ_[2] K] in
/-- `MLabHypothesis` yields an oriented equivalence once its own canonical predicate is proved
pullback-natural to the complete `M` presentation predicate. -/
theorem orientedAbstractEquiv_KTwoM (alpha h : ℕ) (halpha : 1 ≤ alpha)
    (mIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (hLab : MLabHypothesis alpha h mIsCanonical)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hcanonical : mIsCanonical (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)).toMonoidHom)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hnatural : PullbackNatural (IsPresentedOrientationM alpha h)
      (fun chi => mIsCanonical (maxProPQuotient 2 (GalK K)) chi.toMonoidHom)) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨f⟩ := abstractEquiv_KTwoM alpha h mIsCanonical hLab hD hrank hq hcanonical hrange
  exact ⟨orientedEquivM_of_pullback_natural halpha _ hnatural _ hcanonical f⟩

omit [FiniteDimensional ℚ_[2] K] in
/-- `NLabHypothesis` yields an oriented equivalence after supplying an intrinsic target
predicate, its truth for the cyclotomic character, and pullback naturality to the complete `N`
presentation predicate.  The separate predicate is essential because `NLabHypothesis` itself
records only the image invariant. -/
theorem orientedAbstractEquiv_KTwoN (alpha h : ℕ) (halpha : 1 ≤ alpha)
    (nIsCanonical : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) ℤ_[2]ˣ → Prop)
    (hLab : NLabHypothesis alpha h)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hcanonical : nIsCanonical (chiCycKTwo (K := K)))
    (hnatural : PullbackNatural (IsPresentedOrientationN alpha h) nIsCanonical) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨f⟩ := abstractEquiv_KTwoN alpha h hLab hD hrank hq hrange
  exact ⟨orientedEquivN_of_pullback_natural halpha _ hnatural _ hcanonical f⟩

end AbstractClassificationOrientation

end

end GQ2.Dyadic
