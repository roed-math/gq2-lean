/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqRowInitialForms
import GQ2.Dyadic.Instances.GammaLUniversalFox

/-!
# The first Fox--Magnus jet of the improved square relator

This file supplies the word-calculus bridge deliberately left open in
`H3SqRowInitialForms`.  For a marking in an elementary abelian mod-two group, the linear
moment

`sum_g (coefficient of [g] in the i-th Fox derivative) * chi(g)`

is identified with a central-extension evaluation of the original word.  The proof is an
honest induction on free words: the extra term in the moment of a translated derivative is
exactly the cocycle term in the central extension.  Applying the already-proved quadratic
Gram calculation to `sqDiscreteRelator` then identifies every entry of the literal Fox row
with `sqQuadraticFoxLinearInitialCoefficient`.

No completed-row regularity, PBW theorem, associated-graded identification, or cohomological
vanishing is assumed.  The remaining completed obligation is precisely to identify these
finite word-level moments with the canonical coordinates of `I/I^2` in the completed group
algebra (and then propagate the quadratic cancellation through all graded layers).
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore GQ2.Dyadic.MarkedCore
open Multiplicative

/-! ## Linear moments of a literal finite Fox row -/

variable {I L : Type} [DecidableEq I] [Group L]

/-- The coefficient-sum of one generator component of a regular mod-two relation module.
It is expressed as pushforward to the trivial group so that Fox naturality applies directly. -/
def regularModTwoComponentAugmentation (i : I) :
    RegularModTwoRelationModule L I →+ ZMod 2 :=
  (AddMonoidHom.mk' (fun c =>
      regularModTwoPushforward (1 : L →* Unit) I c ((1 : Unit), i))
    (fun c d => by simp) : RegularModTwoRelationModule L I →+ ZMod 2)

@[simp] theorem regularModTwoComponentAugmentation_single
    (i j : I) (g : L) (a : ZMod 2) :
    regularModTwoComponentAugmentation (L := L) i (Finsupp.single (g, j) a) =
      if j = i then a else 0 := by
  classical
  change regularModTwoPushforward (1 : L →* Unit) I
    (Finsupp.single (g, j) a) ((1 : Unit), i) = _
  rw [regularModTwoPushforward_single]
  by_cases hji : j = i
  · subst j; simp
  · simp [hji]

/-- The first Magnus moment of the `i`-th component, measured by a mod-two character
`chi : L -> F_2`. -/
def regularModTwoLinearMoment (chi : L →* Multiplicative (ZMod 2)) (i : I) :
    RegularModTwoRelationModule L I →+ ZMod 2 :=
  Finsupp.liftAddHom (fun p : L × I =>
    AddMonoidHom.mk' (fun a : ZMod 2 =>
      if p.2 = i then a * toAdd (chi p.1) else 0) (by
        intro a b
        split <;> simp_all [add_mul]))

@[simp] theorem regularModTwoLinearMoment_single
    (chi : L →* Multiplicative (ZMod 2)) (i j : I) (g : L) (a : ZMod 2) :
    regularModTwoLinearMoment chi i (Finsupp.single (g, j) a) =
      if j = i then a * toAdd (chi g) else 0 := by
  classical
  simp [regularModTwoLinearMoment]

/-- Translating a regular row adds `chi(g)` times its augmentation to its linear moment.
This is the degree-one multiplication rule `[g][q] = 1 + (chi(g)+chi(q)) epsilon`. -/
theorem regularModTwoLinearMoment_translate
    (chi : L →* Multiplicative (ZMod 2)) (i : I) (g : L)
    (c : RegularModTwoRelationModule L I) :
    regularModTwoLinearMoment chi i (regularModTwoTranslate L I g c) =
      regularModTwoLinearMoment chi i c +
        toAdd (chi g) * regularModTwoComponentAugmentation i c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, j⟩
      simp only [map_add, regularModTwoTranslate_single, ih,
        regularModTwoLinearMoment_single,
        regularModTwoComponentAugmentation_single]
      by_cases hji : j = i
      · subst j
        simp only [if_pos]
        simp only [map_mul, toAdd_mul]
        ring
      · simp [hji]

/-- The augmentation of the literal `i`-th Fox derivative is its mod-two exponent sum. -/
theorem regularModTwoComponentAugmentation_modTwoFoxDerivative
    [Fintype I] (m : I → L) (f : FreeGroup I) (i : I) :
    regularModTwoComponentAugmentation i (modTwoFoxDerivative m f) =
      toAdd (heisEps i f) := by
  have hnat := regularModTwoPushforward_modTwoFoxDerivative
    (1 : L →* Unit) m f
  have happ := congrArg (fun c : RegularModTwoRelationModule Unit I => c ((1 : Unit), i)) hnat
  change regularModTwoPushforward (1 : L →* Unit) I
    (modTwoFoxDerivative m f) ((1 : Unit), i) = _
  rw [happ]
  exact GQ2.Dyadic.LSquare.modTwoFoxDerivative_unit_apply_eq_heisEps f i

/-- Product rule for the literal universal derivative, in regular-translation notation. -/
theorem modTwoFoxDerivative_mul
    (m : I → L) (f g : FreeGroup I) :
    modTwoFoxDerivative m (f * g) =
      modTwoFoxDerivative m f +
        regularModTwoTranslate L I (FreeGroup.lift m f) (modTwoFoxDerivative m g) := by
  simp only [modTwoFoxDerivative, map_mul, WordLift.mul_u,
    GQ2.Dyadic.Count.lift_foxLift_g]
  rfl

/-- Inverse-generator rule for the literal universal derivative. -/
theorem modTwoFoxDerivative_inv_of
    (m : I → L) (j : I) :
    modTwoFoxDerivative m (FreeGroup.of j)⁻¹ =
      -regularModTwoTranslate L I (m j)⁻¹ (modTwoFoxGenerator j) := by
  simp only [modTwoFoxDerivative, map_inv, WordLift.inv_u, FreeGroup.lift_apply_of,
    foxLift_g]
  rfl

/-! ## The central extension representing the first moment -/

/-- The elementary abelian base used by the chain rule.  Its first coordinate is the value of
the original marking; its second coordinate records the exponent of the differentiated letter. -/
abbrev FoxMagnusJetBase (V : Type) := Multiplicative (V × ZMod 2)

variable {V : Type} [AddCommGroup V]

/-- An additive mod-two character, regarded as a multiplicative character of the tagged
elementary abelian group. -/
def multiplicativeModTwoCharacter (chi : V →+ ZMod 2) :
    Multiplicative V →* Multiplicative (ZMod 2) where
  toFun v := ofAdd (chi (toAdd v))
  map_one' := by simp
  map_mul' v w := by
    apply toAdd.injective
    simp

/-- Append the mod-two exponent of the differentiated generator to an elementary marking. -/
def foxMagnusJetMark (m : I → Multiplicative V) (i : I) (j : I) :
    FoxMagnusJetBase V :=
  ofAdd (toAdd (m j), if j = i then 1 else 0)

/-- The cup cocycle whose central coordinate is the `chi`-moment of the `i`-th derivative. -/
def foxMagnusJetCocycle (chi : V →+ ZMod 2) :
    GQ2.DRCoh.TwoCocycle (FoxMagnusJetBase V) where
  κ p q := chi (toAdd p).1 * (toAdd q).2
  norm := by simp
  cocyc p q r := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, map_add]
    ring

/-- The jet cocycle is a genuine cup cocycle whenever the additive base has exponent two. -/
theorem foxMagnusJetCocycle_isCup
    (hVtwo : ∀ v : V, v + v = 0) (chi : V →+ ZMod 2) :
    IsCupCocycle (foxMagnusJetCocycle chi) where
  comm p q := by
    apply toAdd.injective
    simp only [toAdd_mul]
    exact add_comm _ _
  expTwo p := by
    apply toAdd.injective
    change toAdd p + toAdd p = 0
    ext
    · exact hVtwo _
    · exact CharTwo.add_self_eq_zero _
  addLeft p q r := by
    simp [foxMagnusJetCocycle, add_mul, map_add]
  addRight p q r := by
    simp [foxMagnusJetCocycle, mul_add]

@[simp] theorem foxMagnusJetCocycle_mark
    (chi : V →+ ZMod 2) (m : I → Multiplicative V)
    (i j k : I) :
    (foxMagnusJetCocycle chi).κ
        (foxMagnusJetMark m i j) (foxMagnusJetMark m i k) =
      chi (toAdd (m j)) * (if k = i then 1 else 0) := by
  simp [foxMagnusJetCocycle, foxMagnusJetMark]

/-- The base coordinate of the jet lift is the pair consisting of the original word value and
the differentiated letter's mod-two exponent. -/
theorem FreeGroup.lift_foxMagnusJetMark
    (m : I → Multiplicative V) (i : I) (f : FreeGroup I) :
    FreeGroup.lift (foxMagnusJetMark m i) f =
      ofAdd (toAdd (FreeGroup.lift m f), toAdd (heisEps i f)) := by
  let rhs : FreeGroup I →* FoxMagnusJetBase V :=
    { toFun := fun f => ofAdd (toAdd (FreeGroup.lift m f), toAdd (heisEps i f))
      map_one' := by simp
      map_mul' := by
        intro f g
        apply toAdd.injective
        simp }
  have hhom : FreeGroup.lift (foxMagnusJetMark m i) = rhs := by
    apply FreeGroup.ext_hom
    intro j
    simp [rhs, foxMagnusJetMark, heisEps]
  exact DFunLike.congr_fun hhom f

/-- Projecting an offset-zero central lift recovers the underlying base word evaluation. -/
theorem FreeGroup.lift_centLift_base
    {B : Type} [Group B] (c : GQ2.DRCoh.TwoCocycle B)
    (b : I → B) (f : FreeGroup I) :
    (FreeGroup.lift (fun j => centLift c (b j)) f).base = FreeGroup.lift b f := by
  have hhom : (GQ2.DRCoh.CentExt.proj c).comp
      (FreeGroup.lift (fun j => centLift c (b j))) = FreeGroup.lift b := by
    apply FreeGroup.ext_hom
    intro j
    rfl
  exact DFunLike.congr_fun hhom f

/-- **Word-level Fox--Magnus chain rule.**  The first character moment of the literal
universal Fox derivative is exactly the central fibre of the jet cocycle evaluation. -/
theorem regularModTwoLinearMoment_modTwoFoxDerivative
    [Fintype I]
    (chi : V →+ ZMod 2)
    (m : I → Multiplicative V) (i : I) (f : FreeGroup I) :
    regularModTwoLinearMoment
        (multiplicativeModTwoCharacter chi) i
        (modTwoFoxDerivative m f) =
      (FreeGroup.lift
        (fun j => centLift (foxMagnusJetCocycle chi) (foxMagnusJetMark m i j)) f).fib := by
  induction f using FreeGroup.induction_on with
  | C1 => simp
  | of j =>
      simp [modTwoFoxDerivative_of, modTwoFoxGenerator,
        regularModTwoLinearMoment_single, foxMagnusJetMark]
  | inv_of j ih =>
      rw [modTwoFoxDerivative_inv_of]
      rw [map_inv, centExt_inv_fib, map_neg,
        regularModTwoLinearMoment_translate]
      rw [FreeGroup.lift_apply_of]
      simp only [centLift_fib, centLift_base, zero_add,
        modTwoFoxGenerator,
        regularModTwoLinearMoment_single,
        regularModTwoComponentAugmentation_single, foxMagnusJetCocycle,
        foxMagnusJetMark, toAdd_inv, toAdd_ofAdd,
        Prod.snd_neg, multiplicativeModTwoCharacter, map_inv]
      by_cases hji : j = i
      · subst j
        simp only [if_pos, one_mul]
        simp only [show ∀ z : ZMod 2, -z = z by decide]
        change chi 0 + chi (toAdd (m i)) * 1 = chi (toAdd (m i)) * 1
        simp
      · simp [hji]
  | mul f g ihf ihg =>
      rw [modTwoFoxDerivative_mul, map_add,
        regularModTwoLinearMoment_translate, ihf, ihg]
      rw [regularModTwoComponentAugmentation_modTwoFoxDerivative]
      rw [map_mul, GQ2.DRCoh.CentExt.mul_fib,
        FreeGroup.lift_centLift_base, FreeGroup.lift_centLift_base,
        FreeGroup.lift_foxMagnusJetMark, FreeGroup.lift_foxMagnusJetMark]
      simp only [foxMagnusJetCocycle, toAdd_ofAdd,
        multiplicativeModTwoCharacter]
      simp [mul_comm, add_assoc]

/-! ## The literal improved square row -/

/-- The elementary abelian Magnus marking on the square alphabet. -/
def sqMagnusOneMark (h : ℕ) (i : Fin (sqRank h)) :
    Multiplicative (Fin (sqRank h) → ZMod 2) :=
  ofAdd (Pi.single i 1)

/-- Coordinate extraction on the elementary abelian Magnus quotient. -/
def sqMagnusOneCoordinate (h : ℕ) (a : Fin (sqRank h)) :
    (Fin (sqRank h) → ZMod 2) →+ ZMod 2 :=
  Pi.evalAddMonoidHom (fun _ : Fin (sqRank h) => ZMod 2) a

@[simp] theorem sqMagnusOneCoordinate_mark
    (h : ℕ) (a j : Fin (sqRank h)) :
    sqMagnusOneCoordinate h a (toAdd (sqMagnusOneMark h j)) =
      if j = a then 1 else 0 := by
  classical
  rw [sqMagnusOneCoordinate, sqMagnusOneMark]
  change Pi.single j 1 a = _
  by_cases hja : j = a
  · subst j; simp
  · simp [hja]

@[simp] theorem sqHandleIdxU_eq_iff {h : ℕ} (j k : Fin h) :
    sqHandleIdxU j = sqHandleIdxU k ↔ j = k := by
  constructor
  · intro e
    have e' := congrArg (sqInitialAlphabetEquiv h) e
    simpa using e'
  · exact congrArg sqHandleIdxU

@[simp] theorem sqHandleIdxV_eq_iff {h : ℕ} (j k : Fin h) :
    sqHandleIdxV j = sqHandleIdxV k ↔ j = k := by
  constructor
  · intro e
    have e' := congrArg (sqInitialAlphabetEquiv h) e
    simpa using e'
  · exact congrArg sqHandleIdxV

@[simp] theorem sqHandleIdxU_ne_handleV {h : ℕ} (j k : Fin h) :
    sqHandleIdxU j ≠ sqHandleIdxV k := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqHandleIdxV_ne_handleU {h : ℕ} (j k : Fin h) :
    sqHandleIdxV j ≠ sqHandleIdxU k :=
  Ne.symm (sqHandleIdxU_ne_handleV k j)

@[simp] theorem sqCoreZero_ne_handleU {h : ℕ} (j : Fin h) :
    (0 : Fin (sqRank h)) ≠ sqHandleIdxU j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqCoreZero_ne_handleV {h : ℕ} (j : Fin h) :
    (0 : Fin (sqRank h)) ≠ sqHandleIdxV j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqCoreOne_ne_handleU {h : ℕ} (j : Fin h) :
    (1 : Fin (sqRank h)) ≠ sqHandleIdxU j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqCoreOne_ne_handleV {h : ℕ} (j : Fin h) :
    (1 : Fin (sqRank h)) ≠ sqHandleIdxV j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqCoreTwo_ne_handleU {h : ℕ} (j : Fin h) :
    (2 : Fin (sqRank h)) ≠ sqHandleIdxU j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqCoreTwo_ne_handleV {h : ℕ} (j : Fin h) :
    (2 : Fin (sqRank h)) ≠ sqHandleIdxV j := by
  intro e
  have e' := congrArg (sqInitialAlphabetEquiv h) e
  simpa using e'

@[simp] theorem sqHandleU_ne_coreZero {h : ℕ} (j : Fin h) :
    sqHandleIdxU j ≠ (0 : Fin (sqRank h)) := Ne.symm (sqCoreZero_ne_handleU j)

@[simp] theorem sqHandleV_ne_coreZero {h : ℕ} (j : Fin h) :
    sqHandleIdxV j ≠ (0 : Fin (sqRank h)) := Ne.symm (sqCoreZero_ne_handleV j)

@[simp] theorem sqHandleU_ne_coreOne {h : ℕ} (j : Fin h) :
    sqHandleIdxU j ≠ (1 : Fin (sqRank h)) := Ne.symm (sqCoreOne_ne_handleU j)

@[simp] theorem sqHandleV_ne_coreOne {h : ℕ} (j : Fin h) :
    sqHandleIdxV j ≠ (1 : Fin (sqRank h)) := Ne.symm (sqCoreOne_ne_handleV j)

@[simp] theorem sqHandleU_ne_coreTwo {h : ℕ} (j : Fin h) :
    sqHandleIdxU j ≠ (2 : Fin (sqRank h)) := Ne.symm (sqCoreTwo_ne_handleU j)

@[simp] theorem sqHandleV_ne_coreTwo {h : ℕ} (j : Fin h) :
    sqHandleIdxV j ≠ (2 : Fin (sqRank h)) := Ne.symm (sqCoreTwo_ne_handleV j)

theorem eq_sqInitialPartner_iff (h : ℕ) (i a : Fin (sqRank h)) :
    i = sqInitialPartner h a ↔ a = sqInitialPartner h i := by
  constructor <;> intro e
  · have e' := congrArg (sqInitialPartner h) e
    simpa only [sqInitialPartner_involutive] using e'.symm
  · have e' := congrArg (sqInitialPartner h) e
    simpa only [sqInitialPartner_involutive] using e'.symm

/-- The literal finite Fox derivative at the universal elementary-abelian marking has the
formal quadratic coefficient as every first Magnus moment. -/
theorem modTwoFoxDerivative_sqDiscreteRelator_linearMoment
    (h : ℕ) (i a : Fin (sqRank h)) :
    regularModTwoLinearMoment
        (multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)) i
        (modTwoFoxDerivative (sqMagnusOneMark h) (sqDiscreteRelator h)) =
      sqQuadraticFoxLinearInitialCoefficient h i a := by
  classical
  rw [regularModTwoLinearMoment_modTwoFoxDerivative (sqMagnusOneCoordinate h a)]
  rw [FreeGroup.lift_sqDiscreteRelator]
  rw [sqRelWord_centLift_fib_eq_quadraticInitialGram
    (foxMagnusJetCocycle_isCup
      (fun v => funext fun _ => CharTwo.add_self_eq_zero _)
      (sqMagnusOneCoordinate h a))]
  simp only [foxMagnusJetCocycle_mark, sqMagnusOneCoordinate_mark,
    sqRelatorQuadraticInitialGram, sqQuadraticFoxLinearInitialCoefficient,
    sqRelatorQuadraticInitialCoefficient]
  simp only [eq_sqInitialPartner_iff]
  rcases hi : sqInitialAlphabetEquiv h i with c | p
  · fin_cases c
    · have hzero : i = 0 := by
        apply (sqInitialAlphabetEquiv h).injective
        rw [hi, sqInitialAlphabetEquiv_zero]
        rfl
      subst i
      rw [sqInitialPartner_zero]
      have hv0 : (0 : Fin (sqRank h)).val = 0 := Nat.zero_mod _
      have hv1 : (1 : Fin (sqRank h)).val = 1 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have hv2 : (2 : Fin (sqRank h)).val = 2 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have h02 : (0 : Fin (sqRank h)) ≠ 2 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv0, hv2] at e'
        omega
      have h01 : (0 : Fin (sqRank h)) ≠ 1 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv0, hv1] at e'
        omega
      have hrank1 : sqRank h ≠ 1 := by simp only [sqRank]; omega
      simp [h02, h01, Ne.symm h02, Ne.symm h01, hrank1,
        sqHandleV_ne_coreZero, sqHandleU_ne_coreZero, eq_comm]
    · have hone : i = 1 := by
        apply (sqInitialAlphabetEquiv h).injective
        rw [hi, sqInitialAlphabetEquiv_one]
        rfl
      subst i
      rw [sqInitialPartner_one]
      have hv0 : (0 : Fin (sqRank h)).val = 0 := Nat.zero_mod _
      have hv1 : (1 : Fin (sqRank h)).val = 1 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have hv2 : (2 : Fin (sqRank h)).val = 2 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have h12 : (1 : Fin (sqRank h)) ≠ 2 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv1, hv2] at e'
        omega
      have h10 : (1 : Fin (sqRank h)) ≠ 0 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv1, hv0] at e'
        omega
      have hrank1 : sqRank h ≠ 1 := by simp only [sqRank]; omega
      simp [h12, h10, Ne.symm h12, Ne.symm h10, hrank1,
        sqHandleV_ne_coreOne, sqHandleU_ne_coreOne, eq_comm]
    · have htwo : i = 2 := by
        apply (sqInitialAlphabetEquiv h).injective
        rw [hi, sqInitialAlphabetEquiv_two]
        rfl
      subst i
      rw [sqInitialPartner_two]
      have hv0 : (0 : Fin (sqRank h)).val = 0 := Nat.zero_mod _
      have hv1 : (1 : Fin (sqRank h)).val = 1 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have hv2 : (2 : Fin (sqRank h)).val = 2 :=
        Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
      have h21 : (2 : Fin (sqRank h)) ≠ 1 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv2, hv1] at e'
        omega
      have h20 : (2 : Fin (sqRank h)) ≠ 0 := by
        intro e
        have e' := congrArg Fin.val e
        rw [hv2, hv0] at e'
        omega
      have hrank1 : sqRank h ≠ 1 := by simp only [sqRank]; omega
      simp [h21, h20, Ne.symm h21, Ne.symm h20, hrank1,
        sqHandleV_ne_coreTwo, sqHandleU_ne_coreTwo, eq_comm]
  · rcases p with ⟨j, b⟩
    fin_cases b
    · have hu : i = sqHandleIdxU j := by
        apply (sqInitialAlphabetEquiv h).injective
        rw [hi, sqInitialAlphabetEquiv_handleU]
        rfl
      subst i
      simp [eq_comm]
    · have hv : i = sqHandleIdxV j := by
        apply (sqInitialAlphabetEquiv h).injective
        rw [hi, sqInitialAlphabetEquiv_handleV]
        rfl
      subst i
      simp [eq_comm]

end

end GQ2.ContCoh
