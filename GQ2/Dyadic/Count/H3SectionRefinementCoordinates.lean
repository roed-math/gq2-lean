/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxReverse

/-!
# Relation-module reduction for section-refinement coordinates

The reverse finite bar comparison is natural across a quotient only up to the Fox derivative of
the normalized-section defect.  This file identifies exactly when that defect can be corrected
by the displayed presentation relators.

First, a general Fox-calculus lemma proves that every word in the abstract normal closure of a
relator family has derivative in the range of its finite Fox matrix.  Applied to the improved
square word, this constructs the required coordinate whenever each section-refinement defect
belongs to the normal closure of that one word.

The converse condition needed for the reverse comparison is weaker: only the derivatives of the
specific section defects need lie in the Fox range.  We prove that this restricted range condition
is equivalent to nonemptiness of `FiniteSectionRefinementRelatorCoordinates`.  An explicit parity
quotient then shows that this target-level condition is false: after projection to the terminal
group, its section defect has a nonzero first exponent coordinate while the improved Fox row is
zero.

The final section replaces that refuted pointwise target with the correct inverse-system object.
A relation syzygy is given by compatible coefficients over every open-normal quotient; this is
proved equivalent to an additive map into the completed relation module.  Reconstruction may
occur at a chosen finer `W ≤ V`.  The resulting finite-input chain package is exactly equivalent
in nonemptiness to `SqFiniteToCompletedBarFoxHomotopyAt`, and adapters in both directions retain
all chain identities.  No condition asks for a degree-three primitive or cohomological vanishing.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

variable {Q I rel : Type} [Group Q]

/-! ## Fox range and normal closure -/

/-- The range of a finite Fox matrix is stable under regular translation. -/
theorem modTwoFoxRelationMatrixLinear_range_translate
    (m : I → Q) (w : rel → FreeGroup I) (g : Q)
    {c : RegularModTwoRelationModule Q I}
    (hc : c ∈ (modTwoFoxRelationMatrixLinear m w).range) :
    regularModTwoTranslate Q I g c ∈
      (modTwoFoxRelationMatrixLinear m w).range := by
  obtain ⟨a, rfl⟩ := hc
  refine ⟨regularModTwoTranslate Q rel g a, ?_⟩
  rw [modTwoFoxRelationMatrixLinear_apply,
    modTwoFoxRelationMatrixLinear_apply,
    modTwoFoxRelationMatrix_translate]

/-- Free words which evaluate to one and whose mod-two Fox derivative lies in the displayed
Fox range. -/
def modTwoFoxRangeKernel (m : I → Q) (w : rel → FreeGroup I) :
    Subgroup (FreeGroup I) where
  carrier := {f | FreeGroup.lift m f = 1 ∧
    modTwoFoxDerivative m f ∈ (modTwoFoxRelationMatrixLinear m w).range}
  one_mem' := by
    constructor
    · simp
    · exact ⟨0, by simp [modTwoFoxRelationMatrixLinear_apply]⟩
  mul_mem' := by
    rintro a b ⟨haeval, ha⟩ ⟨hbeval, hb⟩
    constructor
    · simp [haeval, hbeval]
    · let ar : FreeRelationKernel m := ⟨a, haeval⟩
      let br : FreeRelationKernel m := ⟨b, hbeval⟩
      change modTwoFoxDerivative m (ar * br : FreeGroup I) ∈ _
      rw [modTwoFoxDerivative_mul_kernel]
      exact (modTwoFoxRelationMatrixLinear m w).range.add_mem ha hb
  inv_mem' := by
    rintro a ⟨haeval, ha⟩
    constructor
    · simp [haeval]
    · simp only [modTwoFoxDerivative, map_inv, WordLift.inv_u,
        lift_foxLift_g, haeval, inv_one, one_smul, ZModModule.neg_eq_self]
      exact ha

/-- The preceding Fox-range kernel is normal in the whole free group. -/
instance modTwoFoxRangeKernel_normal (m : I → Q) (w : rel → FreeGroup I) :
    (modTwoFoxRangeKernel m w).Normal where
  conj_mem n hn g := by
    rcases hn with ⟨hneval, hnfox⟩
    constructor
    · simp only [map_mul, map_inv, hneval]
      group
    · let nr : FreeRelationKernel m := ⟨n, hneval⟩
      have hfox := congrArg Multiplicative.toAdd
        (modTwoRelationFoxMap_conjugation m g nr)
      change modTwoFoxDerivative m (g * n * g⁻¹) =
        regularModTwoTranslate Q I (FreeGroup.lift m g)
          (modTwoFoxDerivative m n) at hfox
      rw [hfox]
      exact modTwoFoxRelationMatrixLinear_range_translate m w _ hnfox

/-- **Normal-closure Fox generation.** If all displayed relators evaluate to one, every word in
their abstract normal closure has its universal mod-two Fox derivative in the range of the
displayed finite Fox matrix. -/
theorem modTwoFoxDerivative_mem_range_of_mem_normalClosure
    (m : I → Q) (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    {f : FreeGroup I} (hf : f ∈ Subgroup.normalClosure (Set.range w)) :
    modTwoFoxDerivative m f ∈ (modTwoFoxRelationMatrixLinear m w).range := by
  have hle : Subgroup.normalClosure (Set.range w) ≤ modTwoFoxRangeKernel m w :=
    Subgroup.normalClosure_le_normal <| by
      rintro _ ⟨k, rfl⟩
      refine ⟨hrel k, ?_⟩
      refine ⟨Finsupp.single ((1 : Q), k) 1, ?_⟩
      rw [modTwoFoxRelationMatrixLinear_apply,
        modTwoFoxRelationMatrix_basis]
  exact (hle hf).2

/-! ## Exact restricted range criterion -/

variable {Q' : Type} [Group Q']

/-- The strictly minimal generation statement for corrected degree-one naturality: only the
Fox derivatives of the normalized section-refinement defects must lie in the relator row's
range. -/
def SectionRefinementDefectsInFoxRange
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I) : Prop :=
  ∀ q,
    modTwoFoxDerivative (fun i ↦ phi (m i))
        (relationSectionRefinementDefect phi m heval heval' q).1 ∈
      (modTwoFoxRelationMatrixLinear (fun i ↦ phi (m i)) w).range

/-- The restricted range statement is exactly nonemptiness of the coordinate data used by the
corrected naturality theorem. -/
theorem nonempty_finiteSectionRefinementRelatorCoordinates_iff
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I) :
    Nonempty (FiniteSectionRefinementRelatorCoordinates
        phi m heval heval' rel w) ↔
      SectionRefinementDefectsInFoxRange phi m heval heval' w := by
  constructor
  · rintro ⟨C⟩ q
    refine ⟨C.coordinate q, ?_⟩
    simpa [modTwoFoxRelationMatrixLinear_apply] using C.fox q
  · intro hrange
    choose coordinate hcoordinate using hrange
    refine ⟨{
      coordinate := coordinate
      fox := fun q ↦ ?_
    }⟩
    simpa [modTwoFoxRelationMatrixLinear_apply] using hcoordinate q

/-- Abstract-normal-closure membership of every section defect is a sufficient, stronger
group-theoretic criterion for the restricted Fox-range condition. -/
theorem sectionRefinementDefectsInFoxRange_of_normalClosure
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift (fun i ↦ phi (m i)) (w k) = 1)
    (hnormal : ∀ q,
      (relationSectionRefinementDefect phi m heval heval' q).1 ∈
        Subgroup.normalClosure (Set.range w)) :
    SectionRefinementDefectsInFoxRange phi m heval heval' w := by
  intro q
  exact modTwoFoxDerivative_mem_range_of_mem_normalClosure
    (fun i ↦ phi (m i)) w hrel (hnormal q)

/-- Consequently the normal-closure criterion constructs the exact degree-one refinement
coordinate data. -/
theorem nonempty_finiteSectionRefinementRelatorCoordinates_of_normalClosure
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift (fun i ↦ phi (m i)) (w k) = 1)
    (hnormal : ∀ q,
      (relationSectionRefinementDefect phi m heval heval' q).1 ∈
        Subgroup.normalClosure (Set.range w)) :
    Nonempty (FiniteSectionRefinementRelatorCoordinates
      phi m heval heval' rel w) :=
  (nonempty_finiteSectionRefinementRelatorCoordinates_iff
    phi m heval heval' w).2
      (sectionRefinementDefectsInFoxRange_of_normalClosure
        phi m heval heval' w hrel hnormal)

/-! ## The terminal-target obstruction for the actual improved square core -/

/-- The mod-two parity marking which reads the first improved-square generator. -/
def sqFirstParityMark (h : ℕ) :
    Fin (sqRank h) → Multiplicative (ZMod 2) :=
  fun i ↦ heisEps (0 : Fin (sqRank h)) (FreeGroup.of i)

@[simp] theorem sqFirstParityMark_zero (h : ℕ) :
    sqFirstParityMark h 0 = Multiplicative.ofAdd 1 := by
  simp [sqFirstParityMark, heisEps]

/-- The improved square relator dies under the first parity marking. -/
theorem sqFirstParityMark_relator (h : ℕ) :
    sqRelWord (sqFirstParityMark h) = 1 := by
  rw [sqRelWord_comm]
  have hsquare (z : Multiplicative (ZMod 2)) : z ^ 2 = 1 := by
    rw [pow_two]
    revert z
    decide
  have hfourth (z : Multiplicative (ZMod 2)) : z ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by omega, pow_mul, hsquare]
  rw [hfourth, hsquare]
  simp

/-- The continuous parity quotient of `DSq h` detecting its first marked generator. -/
noncomputable def sqFirstParityHom (h : ℕ) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) :=
  sqLiftHom h
    (isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
      (by rw [Nat.card_eq_fintype_card]; decide)))
    (sqFirstParityMark h) (sqFirstParityMark_relator h)

@[simp] theorem sqFirstParityHom_gen (h : ℕ) (i : Fin (sqRank h)) :
    sqFirstParityHom h (sqGen h i) = sqFirstParityMark h i := by
  rw [sqFirstParityHom, sqLiftHom_gen]

@[simp] theorem sqFirstParityHom_gen_zero (h : ℕ) :
    sqFirstParityHom h (sqGen h 0) = Multiplicative.ofAdd 1 := by
  rw [sqFirstParityHom, sqLiftHom_gen, sqFirstParityMark_zero]

/-- The open-normal kernel of the first parity quotient. -/
noncomputable def sqFirstParityKernel (h : ℕ) :
    OpenNormalSubgroup (DSq h : Type) where
  toSubgroup := (sqFirstParityHom h).toMonoidHom.ker
  isOpen' := by
    change IsOpen ((sqFirstParityHom h) ⁻¹'
      ({1} : Set (Multiplicative (ZMod 2))))
    exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod 2)))).preimage
      (sqFirstParityHom h).continuous_toFun

/-- The induced map from the parity quotient to `Multiplicative (ZMod 2)`. -/
noncomputable def sqFirstParityQuotientHom (h : ℕ) :
    ((DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup) →*
      Multiplicative (ZMod 2) :=
  QuotientGroup.lift (sqFirstParityKernel h).toSubgroup
    (sqFirstParityHom h).toMonoidHom (by
      change (sqFirstParityHom h).toMonoidHom.ker ≤ _
      exact le_refl _)

/-- The first marked generator remains parity-nontrivial in the parity quotient. -/
theorem sqFirstParityQuotientHom_marking_zero (h : ℕ) :
    sqFirstParityQuotientHom h
        (sqOpenQuotientMarking h (sqFirstParityKernel h) 0) =
      Multiplicative.ofAdd 1 := by
  exact (QuotientGroup.lift_mk' _ _ (sqGen h 0)).trans
    (sqFirstParityHom_gen_zero h)

/-- The unique homomorphism from a group to the terminal group. -/
def groupToUnit (Q : Type) [Group Q] : Q →* Unit where
  toFun _ := ()
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Surjectivity of free evaluation at the terminal pushed marking. -/
theorem freeGroupLift_groupToUnit_surjective
    {Q : Type} [Group Q] (m : I → Q) :
    Function.Surjective (FreeGroup.lift (fun i ↦ groupToUnit Q (m i))) :=
  Function.surjective_to_subsingleton _

private abbrev SqFirstParityQuotient (h : ℕ) :=
  (DSq h : Type) ⧸ (sqFirstParityKernel h).toSubgroup

/-- The terminal homomorphism out of the actual first-parity quotient. -/
def sqFirstParityToUnit (h : ℕ) : SqFirstParityQuotient h →* Unit :=
  groupToUnit (SqFirstParityQuotient h)

/-- Surjectivity of the pushed first-parity marking at the terminal target. -/
theorem sqFirstParityTerminalEvaluation_surjective (h : ℕ) :
    Function.Surjective (FreeGroup.lift (fun i ↦
      sqFirstParityToUnit h
        (sqOpenQuotientMarking h (sqFirstParityKernel h) i))) :=
  freeGroupLift_groupToUnit_surjective
    (sqOpenQuotientMarking h (sqFirstParityKernel h))

/-- The canonical section word of the parity generator has odd first exponent. -/
theorem heisEps_relationSection_sqFirstParityGenerator (h : ℕ) :
    heisEps (0 : Fin (sqRank h))
        (relationSection
          (sqOpenQuotientFreeEvaluation_surjective h (sqFirstParityKernel h))
          (sqOpenQuotientMarking h (sqFirstParityKernel h) 0)) =
      Multiplicative.ofAdd 1 := by
  let W := sqFirstParityKernel h
  let m := sqOpenQuotientMarking h W
  let heval := sqOpenQuotientFreeEvaluation_surjective h W
  let q := m 0
  have hmap := map_freeGroup_lift (sqFirstParityQuotientHom h) m
    (relationSection heval q)
  rw [relationSection_spec] at hmap
  have hmark : (fun i ↦ sqFirstParityQuotientHom h (m i)) =
      sqFirstParityMark h := by
    funext i
    dsimp [m]
    exact (QuotientGroup.lift_mk' _ _ (sqGen h i)).trans
      (sqFirstParityHom_gen h i)
  rw [hmark] at hmap
  have hlift : FreeGroup.lift (sqFirstParityMark h) =
      heisEps (0 : Fin (sqRank h)) := by
    apply FreeGroup.ext_hom
    intro i
    simp [sqFirstParityMark]
  rw [hlift, sqFirstParityQuotientHom_marking_zero] at hmap
  exact hmap.symm

/-- At the terminal target, the section-refinement defect of the parity generator has nonzero
first Fox coordinate. -/
theorem terminalSectionDefect_sqFirstParityGenerator_apply_zero (h : ℕ) :
    modTwoFoxDerivative
        (fun i ↦ sqFirstParityToUnit h
          (sqOpenQuotientMarking h (sqFirstParityKernel h) i))
        (relationSectionRefinementDefect
          (sqFirstParityToUnit h)
          (sqOpenQuotientMarking h (sqFirstParityKernel h))
          (sqOpenQuotientFreeEvaluation_surjective h (sqFirstParityKernel h))
          (sqFirstParityTerminalEvaluation_surjective h)
          (sqOpenQuotientMarking h (sqFirstParityKernel h) 0)).1
        ((1 : Unit), (0 : Fin (sqRank h))) = 1 := by
  rw [GQ2.Dyadic.LSquare.modTwoFoxDerivative_unit_apply_eq_heisEps]
  simp only [relationSectionRefinementDefect, Subgroup.coe_mk, map_mul, map_inv]
  rw [relationSection_one]
  simp only [map_one, one_mul]
  rw [heisEps_relationSection_sqFirstParityGenerator]
  decide

/-- **Terminal pointwise-coordinate no-go.** For the actual parity quotient of `DSq h`, the
section defect along the map to the trivial target cannot be expressed by the improved square
Fox row: that row is zero, while the defect has nonzero first exponent coordinate.

Thus a pointwise same-target coordinate system over all finite quotients is impossible.  The
continuous proof must allow eventual correction after passing to a finer level (or work directly
in the completed inverse system). -/
theorem not_nonempty_sqFirstParity_terminalSectionRefinementRelatorCoordinates (h : ℕ) :
    ¬ Nonempty (FiniteSectionRefinementRelatorCoordinates
      (sqFirstParityToUnit h)
      (sqOpenQuotientMarking h (sqFirstParityKernel h))
      (sqOpenQuotientFreeEvaluation_surjective h (sqFirstParityKernel h))
      (sqFirstParityTerminalEvaluation_surjective h)
      Unit (fun _ : Unit ↦ sqDiscreteRelator h)) := by
  rintro ⟨C⟩
  let q := sqOpenQuotientMarking h (sqFirstParityKernel h) 0
  have hfox := C.fox q
  change modTwoFoxRelationMatrixLinear
      (fun _ : Fin (sqRank h) ↦ (1 : Unit))
      (fun _ : Unit ↦ sqDiscreteRelator h) (C.coordinate q) =
    modTwoFoxDerivative (fun _ : Fin (sqRank h) ↦ (1 : Unit))
      (relationSectionRefinementDefect
        (sqFirstParityToUnit h)
        (sqOpenQuotientMarking h (sqFirstParityKernel h))
        (sqOpenQuotientFreeEvaluation_surjective h (sqFirstParityKernel h))
        (sqFirstParityTerminalEvaluation_surjective h) q).1 at hfox
  rw [sqFiniteLevelModTwoFoxBoundary_unit_eq_zero h] at hfox
  have hcoord := congrArg
    (fun z : RegularModTwoRelationModule Unit (Fin (sqRank h)) ↦
      z ((1 : Unit), (0 : Fin (sqRank h)))) hfox
  simp [q, terminalSectionDefect_sqFirstParityGenerator_apply_zero h] at hcoord

/-! ## The correct eventual/completed replacement -/

private abbrev SqFiniteInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

/-- A relation syzygy for one finite input quotient, presented by all of its compatible finite
coordinates.  Unlike the refuted pointwise section coordinates, the coefficient is not required
to be manufactured at the target quotient: it is retained throughout the inverse system, so a
nonzero correction may first become visible after passage to a finer quotient. -/
structure SqCompatibleFiniteRelationSyzygyAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  /-- The relation coefficient at every finite quotient. -/
  coordinate : ∀ U : OpenNormalSubgroup (DSq h : Type),
    SqFiniteInputThree h V →+
      RegularModTwoRelationModule ((DSq h : Type) ⧸ U.toSubgroup) Unit
  /-- The coordinates form an inverse-limit compatible family. -/
  compatible : ∀ {U U' : OpenNormalSubgroup (DSq h : Type)}
    (hUU' : U ≤ U') (c : SqFiniteInputThree h V),
    modTwoRegularModuleTransition (DSq h : Type) hUU' Unit
        (coordinate U c) = coordinate U' c

/-- Assemble a compatible family of finite relation coefficients into the completed relation
module. -/
def SqCompatibleFiniteRelationSyzygyAt.toCompleted
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteRelationSyzygyAt h V) :
    SqFiniteInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) Unit where
  toFun c := ⟨fun U ↦ S.coordinate U c, fun _ _ hUU' ↦ S.compatible hUU' c⟩
  map_zero' := by
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) Unit
    intro U
    exact map_zero (S.coordinate U)
  map_add' c d := by
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) Unit
    intro U
    exact map_add (S.coordinate U) c d

@[simp] theorem SqCompatibleFiniteRelationSyzygyAt.coordinate_toCompleted
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteRelationSyzygyAt h V) (c : SqFiniteInputThree h V) :
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit U
        (S.toCompleted c) = S.coordinate U c :=
  rfl

/-- Expose an already completed relation syzygy as its compatible family of finite
coordinates. -/
def sqCompatibleFiniteRelationSyzygyAtOfCompleted
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqFiniteInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) Unit) :
    SqCompatibleFiniteRelationSyzygyAt h V where
  coordinate U := {
    toFun := fun c ↦
      ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit U (S c)
    map_zero' := by simp
    map_add' := by simp
  }
  compatible hUU' c :=
    ModTwoCompletedRegularModule.coordinate_compatible
      (DSq h : Type) Unit (S c) hUU'

/-- Passing from a completed syzygy to its coordinates and assembling them again loses no
information. -/
@[simp] theorem toCompleted_sqCompatibleFiniteRelationSyzygyAtOfCompleted
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqFiniteInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) Unit) :
    (sqCompatibleFiniteRelationSyzygyAtOfCompleted S).toCompleted = S := by
  apply AddMonoidHom.ext
  intro c
  apply ModTwoCompletedRegularModule.ext (DSq h : Type) Unit
  intro U
  rfl

/-- Replacing a compatible family by the coordinates of its assembled completed syzygy also
loses no information. -/
@[simp] theorem sqCompatibleFiniteRelationSyzygyAtOfCompleted_toCompleted
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteRelationSyzygyAt h V) :
    sqCompatibleFiniteRelationSyzygyAtOfCompleted S.toCompleted = S := by
  cases S with
  | mk coordinate compatible =>
      congr

/-- Compatible finite relation coordinates are canonically equivalent to an additive map into
the completed relation module. -/
def sqCompatibleFiniteRelationSyzygyAtEquiv
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :
    SqCompatibleFiniteRelationSyzygyAt h V ≃
      (SqFiniteInputThree h V →+
        ModTwoCompletedRegularModule (DSq h : Type) Unit) where
  toFun := SqCompatibleFiniteRelationSyzygyAt.toCompleted
  invFun := sqCompatibleFiniteRelationSyzygyAtOfCompleted
  left_inv := sqCompatibleFiniteRelationSyzygyAtOfCompleted_toCompleted
  right_inv := toCompleted_sqCompatibleFiniteRelationSyzygyAtOfCompleted

/-- Thus compatible finite relation coordinates and a completed relation syzygy are exactly
equivalent descriptions. -/
theorem nonempty_sqCompatibleFiniteRelationSyzygyAt_iff_completed
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :
    Nonempty (SqCompatibleFiniteRelationSyzygyAt h V) ↔
      Nonempty (SqFiniteInputThree h V →+
        ModTwoCompletedRegularModule (DSq h : Type) Unit) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toCompleted⟩
  · rintro ⟨S⟩
    exact ⟨sqCompatibleFiniteRelationSyzygyAtOfCompleted S⟩

/-- The finite-input, eventual form of the missing bar--Fox comparison.

For a three-cochain at `V`, the comparison may first pass to a chosen `W ≤ V`.  Its relation
syzygy is a compatible family over *all* finite quotients, and reconstruction uses its
`W`-coordinate.  Both identities are imposed on every cochain and both defects factor through
`d³`; this is strictly chain-level data and contains neither a cocycle primitive nor a vanishing
claim. -/
structure SqFiniteInputEventualBarFoxCorrectionAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  /-- The quotient where finite reconstruction is performed. -/
  W : OpenNormalSubgroup (DSq h : Type)
  /-- Reconstruction is allowed to refine the finite input quotient. -/
  le : W.toSubgroup ≤ V.toSubgroup
  /-- The degree-lowering part of the bar homotopy. -/
  homotopyTwo :
    SqFiniteInputThree h V →+
      FiniteModTwoBarCochainTwo ((DSq h : Type) ⧸ W.toSubgroup)
  /-- The relation syzygy as compatible finite coordinates. -/
  relationSyzygy : SqCompatibleFiniteRelationSyzygyAt h V
  /-- Reconstruction of the finite bar error from the chosen `W`-coordinate. -/
  relationError :
    RegularModTwoRelationModule ((DSq h : Type) ⧸ W.toSubgroup) Unit →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  /-- The completed Fox-boundary defect factors through the degree-four coboundary. -/
  boundaryDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))
  /-- The residual bar error also factors through the degree-four coboundary. -/
  barDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  /-- Chain-map identity in the completed relation module. -/
  boundary_relationSyzygy : ∀ c,
    (sqCompletedModTwoFoxBoundary h).map (relationSyzygy.toCompleted c) =
      boundaryDefect (finiteModTwoBarDThree _ c)
  /-- Reconstruction after passing to the chosen finer quotient. -/
  reconstruct : ∀ c,
    finiteModTwoBarDTwo _ (homotopyTwo c) +
        relationError (relationSyzygy.coordinate W c) +
        barDefect (finiteModTwoBarDThree _ c) =
      sqFiniteModTwoBarRefineThree h le c

/-- Assemble the finite-coordinate version into the existing completed bar--Fox homotopy
interface. -/
def SqFiniteInputEventualBarFoxCorrectionAt.toCompletedHomotopy
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputEventualBarFoxCorrectionAt h V) :
    SqFiniteToCompletedBarFoxHomotopyAt h V where
  W := C.W
  le := C.le
  homotopyTwo := C.homotopyTwo
  relationSyzygy := C.relationSyzygy.toCompleted
  relationError := C.relationError
  boundaryDefect := C.boundaryDefect
  barDefect := C.barDefect
  boundary_relationSyzygy := C.boundary_relationSyzygy
  reconstruct c := by
    rw [SqCompatibleFiniteRelationSyzygyAt.coordinate_toCompleted]
    exact C.reconstruct c

/-- Conversely, the existing completed homotopy exposes a compatible family at every finite
quotient. -/
def sqFiniteInputEventualBarFoxCorrectionAtOfCompleted
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteToCompletedBarFoxHomotopyAt h V) :
    SqFiniteInputEventualBarFoxCorrectionAt h V where
  W := C.W
  le := C.le
  homotopyTwo := C.homotopyTwo
  relationSyzygy :=
    sqCompatibleFiniteRelationSyzygyAtOfCompleted C.relationSyzygy
  relationError := C.relationError
  boundaryDefect := C.boundaryDefect
  barDefect := C.barDefect
  boundary_relationSyzygy c := by
    simpa using C.boundary_relationSyzygy c
  reconstruct c := by
    exact C.reconstruct c

/-- **Exact adapter.** The eventual finite-coordinate condition is equivalent to the existing
finite-to-completed homotopy datum at each input quotient. -/
theorem nonempty_sqFiniteInputEventualBarFoxCorrectionAt_iff
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :
    Nonempty (SqFiniteInputEventualBarFoxCorrectionAt h V) ↔
      Nonempty (SqFiniteToCompletedBarFoxHomotopyAt h V) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toCompletedHomotopy⟩
  · rintro ⟨C⟩
    exact ⟨sqFiniteInputEventualBarFoxCorrectionAtOfCompleted C⟩

/-- At the chosen finer quotient, the finite coordinate of the syzygy satisfies the literal
improved-square Fox identity.  This is the finite-coordinate form of the completed chain-map
field, and ensures that the eventual package cannot silently substitute a different relator
row. -/
theorem SqFiniteInputEventualBarFoxCorrectionAt.finite_boundary_relationSyzygy
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputEventualBarFoxCorrectionAt h V)
    (c : SqFiniteInputThree h V) :
    (sqFiniteLevelModTwoFoxBoundary h
        (fun i ↦ QuotientGroup.mk' C.W.toSubgroup (sqGen h i))).map
        (C.relationSyzygy.coordinate C.W c) =
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) C.W
        (C.boundaryDefect (finiteModTwoBarDThree _ c)) := by
  have hboundary := C.toCompletedHomotopy.finite_boundary_relationSyzygy c
  change (sqFiniteLevelModTwoFoxBoundary h
      (fun i ↦ QuotientGroup.mk' C.W.toSubgroup (sqGen h i))).map
      (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit C.W
        (C.relationSyzygy.toCompleted c)) = _ at hboundary
  rw [C.relationSyzygy.coordinate_toCompleted] at hboundary
  exact hboundary

/-- Eventual finite-coordinate correction data at every finite input quotient. -/
abbrev SqFiniteInputEventualBarFoxAssembly (h : ℕ) :=
  ∀ V : OpenNormalSubgroup (DSq h : Type),
    SqFiniteInputEventualBarFoxCorrectionAt h V

/-- Eventual finite-coordinate data at every input quotient supplies the completed assembly. -/
def sqFiniteToCompletedBarFoxAssembly_of_eventual
    (h : ℕ)
    (S : SqFiniteInputEventualBarFoxAssembly h) :
    SqFiniteToCompletedBarFoxAssembly h :=
  fun V ↦ (S V).toCompletedHomotopy

/-- The assembly conversely exposes the finite-coordinate, eventually reconstructed form. -/
def sqFiniteInputEventualBarFoxCorrection_of_assembly
    (h : ℕ) (S : SqFiniteToCompletedBarFoxAssembly h)
    (V : OpenNormalSubgroup (DSq h : Type)) :
    SqFiniteInputEventualBarFoxCorrectionAt h V :=
  sqFiniteInputEventualBarFoxCorrectionAtOfCompleted (S V)

/-- A completed assembly conversely supplies eventual finite-coordinate correction data at
every input quotient. -/
def sqFiniteInputEventualBarFoxAssembly_of_completed
    (h : ℕ) (S : SqFiniteToCompletedBarFoxAssembly h) :
    SqFiniteInputEventualBarFoxAssembly h :=
  fun V ↦ sqFiniteInputEventualBarFoxCorrection_of_assembly h S V

/-- **Global exact adapter.** Existence of eventual compatible finite-coordinate data at every
input quotient is equivalent to existence of the completed bar--Fox assembly. -/
theorem nonempty_sqFiniteInputEventualBarFoxAssembly_iff (h : ℕ) :
    Nonempty (SqFiniteInputEventualBarFoxAssembly h) ↔
      Nonempty (SqFiniteToCompletedBarFoxAssembly h) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨sqFiniteToCompletedBarFoxAssembly_of_eventual h S⟩
  · rintro ⟨S⟩
    exact ⟨sqFiniteInputEventualBarFoxAssembly_of_completed h S⟩

/-- The earlier parity-to-terminal calculation rules out replacing the completed family above
by a coefficient in the target-level relation module.  The eventual `W` and the finer
coordinates are therefore essential, rather than administrative weakening. -/
theorem sqFirstParity_pointwise_terminal_obstruction (h : ℕ) :
    ¬ Nonempty (FiniteSectionRefinementRelatorCoordinates
      (sqFirstParityToUnit h)
      (sqOpenQuotientMarking h (sqFirstParityKernel h))
      (sqOpenQuotientFreeEvaluation_surjective h (sqFirstParityKernel h))
      (sqFirstParityTerminalEvaluation_surjective h)
      Unit (fun _ : Unit ↦ sqDiscreteRelator h)) :=
  not_nonempty_sqFirstParity_terminalSectionRefinementRelatorCoordinates h

end

end GQ2.Dyadic.Count
