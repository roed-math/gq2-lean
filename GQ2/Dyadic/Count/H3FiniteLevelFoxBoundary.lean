/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3OneRelatorAsphericity
import GQ2.Dyadic.Count.HTwoRelationFox
import GQ2.Dyadic.Instances.GammaLUniversalFox

/-!
# Finite-level mod-two Fox boundaries

The completed Fox boundary of a one-relator pro-2 presentation is assembled from its values on
finite quotients.  This file constructs the honest finite-level maps.  For a marking
`m : I → Q` and a family of discrete relators `w : rel → FreeGroup I`, the boundary is

`F₂[Q]^(rel) → F₂[Q]^(I)`

and is exactly the universal mod-two Fox relation matrix already used by the relation-module
development.  It is packaged as a `ContCoh.ModTwoFoxBoundary` and shown natural under every
homomorphism of quotient groups.

No finite-level injectivity is asserted.  Indeed the final regression proves that the improved
square relator has zero Fox row at the trivial quotient.  Thus the completed injectivity theorem
must use compatibility across the inverse system, not a left inverse at each finite target.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH GQ2.Dyadic GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## Linear form of the existing universal Fox matrix -/

variable {I rel Q : Type} [Group Q]

/-- The universal Fox matrix as an `F₂`-linear map.  It sends the regular basis vector
`[g,k]` to the translate by `g` of the existing `modTwoFoxDerivative m (w k)`. -/
def modTwoFoxRelationMatrixLinear (m : I → Q) (w : rel → FreeGroup I) :
    RegularModTwoRelationModule Q rel →ₗ[ZMod 2]
      RegularModTwoRelationModule Q I :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × rel =>
    LinearMap.toSpanSingleton (ZMod 2)
      (RegularModTwoRelationModule Q I)
      (regularModTwoTranslate Q I p.1 (modTwoFoxDerivative m (w p.2)))

@[simp] theorem modTwoFoxRelationMatrixLinear_apply
    (m : I → Q) (w : rel → FreeGroup I)
    (c : RegularModTwoRelationModule Q rel) :
    modTwoFoxRelationMatrixLinear m w c =
      modTwoFoxRelationMatrix m w c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, k⟩
      rw [map_add, map_add, ih, modTwoFoxRelationMatrixLinear,
        Finsupp.lsum_single, modTwoFoxRelationMatrix,
        regularModTwoRelationEval_single]
      congr 1
      simp only [LinearMap.toSpanSingleton_apply]
      change a • regularModTwoTranslate Q I g (modTwoFoxDerivative m (w k)) =
        a.val • regularModTwoTranslate Q I g (modTwoFoxDerivative m (w k))
      rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul,
        ZMod.val_natCast]
      exact congrArg
        (fun n : ℕ => n • regularModTwoTranslate Q I g
          (modTwoFoxDerivative m (w k)))
        (Nat.mod_eq_of_lt (show a.val < 2 from a.isLt)).symm

/-- The universal finite-level Fox matrix, with its regular equivariance, is an instance of the
abstract Fox-boundary interface used by the continuous bar comparison. -/
def finiteLevelModTwoFoxBoundary (m : I → Q) (w : rel → FreeGroup I) :
    ModTwoFoxBoundary Q
      (RegularModTwoRelationModule Q rel)
      (RegularModTwoRelationModule Q I) where
  map := modTwoFoxRelationMatrixLinear m w
  equivariant g c := by
    rw [modTwoFoxRelationMatrixLinear_apply,
      modTwoFoxRelationMatrixLinear_apply]
    exact modTwoFoxRelationMatrix_translate m w g c

@[simp] theorem finiteLevelModTwoFoxBoundary_map_apply
    (m : I → Q) (w : rel → FreeGroup I)
    (c : RegularModTwoRelationModule Q rel) :
    (finiteLevelModTwoFoxBoundary m w).map c =
      modTwoFoxRelationMatrixLinear m w c :=
  rfl

@[simp] theorem finiteLevelModTwoFoxBoundary_single
    (m : I → Q) (w : rel → FreeGroup I)
    (g : Q) (k : rel) (a : ZMod 2) :
    (finiteLevelModTwoFoxBoundary m w).map
        (Finsupp.single (g, k) a) =
      a • regularModTwoTranslate Q I g (modTwoFoxDerivative m (w k)) := by
  classical
  rw [finiteLevelModTwoFoxBoundary_map_apply,
    modTwoFoxRelationMatrixLinear, Finsupp.lsum_single]
  simp

@[simp] theorem finiteLevelModTwoFoxBoundary_basis
    (m : I → Q) (w : rel → FreeGroup I) (k : rel) :
    (finiteLevelModTwoFoxBoundary m w).map
        (Finsupp.single ((1 : Q), k) 1) =
      modTwoFoxDerivative m (w k) :=
  by simp

/-! ## Pushforward along a refinement map -/

variable {Q' : Type} [Group Q']

/-- Extension of scalars on finite regular modules along a group homomorphism.  On basis vectors
it sends `[g,j]` to `[φ(g),j]`; if `φ` is a quotient map, coefficients over a fibre are summed.
-/
def regularModTwoPushforward (φ : Q →* Q') (J : Type) :
    RegularModTwoRelationModule Q J →ₗ[ZMod 2]
      RegularModTwoRelationModule Q' J :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × J =>
    LinearMap.toSpanSingleton (ZMod 2)
      (RegularModTwoRelationModule Q' J)
      (Finsupp.single (φ p.1, p.2) 1)

@[simp] theorem regularModTwoPushforward_single
    (φ : Q →* Q') (J : Type) (g : Q) (j : J) (a : ZMod 2) :
    regularModTwoPushforward φ J (Finsupp.single (g, j) a) =
      Finsupp.single (φ g, j) a := by
  classical
  rw [regularModTwoPushforward, Finsupp.lsum_single]
  ext p
  simp [smul_eq_mul]

@[simp] theorem regularModTwoPushforward_id
    (J : Type) (c : RegularModTwoRelationModule Q J) :
    regularModTwoPushforward (MonoidHom.id Q) J c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, j⟩
      simp [ih]

@[simp] theorem regularModTwoPushforward_comp
    {Q'' : Type} [Group Q''] (ψ : Q' →* Q'') (φ : Q →* Q')
    (J : Type) (c : RegularModTwoRelationModule Q J) :
    regularModTwoPushforward ψ J (regularModTwoPushforward φ J c) =
      regularModTwoPushforward (ψ.comp φ) J c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, j⟩
      simp [ih]

/-- Pushforward intertwines regular translation with translation by the image element. -/
theorem regularModTwoPushforward_translate
    (φ : Q →* Q') (J : Type) (g : Q)
    (c : RegularModTwoRelationModule Q J) :
    regularModTwoPushforward φ J (regularModTwoTranslate Q J g c) =
      regularModTwoTranslate Q' J (φ g) (regularModTwoPushforward φ J c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨h, j⟩
      simp only [map_add, regularModTwoTranslate_single,
        regularModTwoPushforward_single, ih]
      rw [map_mul]

/-- The semidirect-product map induced by pushforward of regular coefficients and the base
homomorphism. -/
def regularModTwoWordLiftPush (φ : Q →* Q') (J : Type) :
    WordLift (RegularModTwoRelationModule Q J) Q →*
      WordLift (RegularModTwoRelationModule Q' J) Q' where
  toFun p := ⟨regularModTwoPushforward φ J p.u, φ p.g⟩
  map_one' := by
    apply WordLift.ext
    · simp
    · simp
  map_mul' p q := by
    apply WordLift.ext
    · simp only [WordLift.mul_u, map_add]
      change regularModTwoPushforward φ J p.u +
          regularModTwoPushforward φ J
            (regularModTwoTranslate Q J p.g q.u) =
        regularModTwoPushforward φ J p.u +
          regularModTwoTranslate Q' J (φ p.g)
            (regularModTwoPushforward φ J q.u)
      rw [regularModTwoPushforward_translate]
    · simp

/-- The universal Fox derivative is natural under a homomorphism of finite quotient groups. -/
theorem regularModTwoPushforward_modTwoFoxDerivative
    (φ : Q →* Q') (m : I → Q) (f : FreeGroup I) :
    regularModTwoPushforward φ I (modTwoFoxDerivative m f) =
      modTwoFoxDerivative (fun i => φ (m i)) f := by
  let push := regularModTwoWordLiftPush φ I
  have hlift :
      push.comp
          (FreeGroup.lift (foxLift m (modTwoFoxGenerator (L := Q)))) =
        FreeGroup.lift
          (foxLift (fun i => φ (m i)) (modTwoFoxGenerator (L := Q'))) := by
    apply FreeGroup.ext_hom
    intro i
    apply WordLift.ext
    · simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      change regularModTwoPushforward φ I
          (Finsupp.single ((1 : Q), i) 1) =
        Finsupp.single ((1 : Q'), i) 1
      simp
    · simp [push, regularModTwoWordLiftPush, foxLift]
  have h := congrArg (fun F : FreeGroup I →* WordLift
      (RegularModTwoRelationModule Q' I) Q' => (F f).u) hlift
  exact h

/-- Naturality of the finite Fox boundary under quotient refinement.  This is the commuting
square needed to form an inverse system of finite boundaries. -/
theorem finiteLevelModTwoFoxBoundary_natural
    (φ : Q →* Q') (m : I → Q) (w : rel → FreeGroup I)
    (c : RegularModTwoRelationModule Q rel) :
    regularModTwoPushforward φ I
        ((finiteLevelModTwoFoxBoundary m w).map c) =
      (finiteLevelModTwoFoxBoundary (fun i => φ (m i)) w).map
        (regularModTwoPushforward φ rel c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, k⟩
      simp only [map_add, ih, regularModTwoPushforward_single]
      congr 1
      rw [finiteLevelModTwoFoxBoundary_single,
        finiteLevelModTwoFoxBoundary_single, map_smul]
      congr 1
      rw [regularModTwoPushforward_translate,
        regularModTwoPushforward_modTwoFoxDerivative]

/-! ## The improved square relator -/

/-- The discrete free-group word with the same literal shape as the profinite `sqRelator`.
Every finite-level Fox boundary is computed from this word. -/
def sqDiscreteRelator (h : ℕ) : FreeGroup (Fin (sqRank h)) :=
  sqRelWord fun i => FreeGroup.of i

/-- Evaluating the discrete square relator at any marking gives the intrinsic group-valued
square relator shape. -/
theorem FreeGroup.lift_sqDiscreteRelator
    {G : Type} [Group G] (h : ℕ) (m : Fin (sqRank h) → G) :
    FreeGroup.lift m (sqDiscreteRelator h) = sqRelWord m := by
  rw [sqDiscreteRelator, map_sqRelWord]
  congr 1
  funext i
  simp

/-- The one-relator finite Fox boundary for the improved square presentation. -/
def sqFiniteLevelModTwoFoxBoundary (h : ℕ) (m : Fin (sqRank h) → Q) :
    ModTwoFoxBoundary Q
      (RegularModTwoRelationModule Q Unit)
      (RegularModTwoRelationModule Q (Fin (sqRank h))) :=
  finiteLevelModTwoFoxBoundary m (fun _ => sqDiscreteRelator h)

@[simp] theorem sqFiniteLevelModTwoFoxBoundary_basis
    (h : ℕ) (m : Fin (sqRank h) → Q) :
    (sqFiniteLevelModTwoFoxBoundary h m).map
        (Finsupp.single ((1 : Q), ()) 1) =
      modTwoFoxDerivative m (sqDiscreteRelator h) :=
  finiteLevelModTwoFoxBoundary_basis m (fun _ => sqDiscreteRelator h) ()

/-- The full coordinate formula for the single-relator boundary: the coefficient at `(u,i)`
of the image of `a[g]` is `a` times the `(g⁻¹u,i)` Fox coefficient of the relator. -/
theorem sqFiniteLevelModTwoFoxBoundary_single_apply
    (h : ℕ) (m : Fin (sqRank h) → Q)
    (g u : Q) (i : Fin (sqRank h)) (a : ZMod 2) :
    (sqFiniteLevelModTwoFoxBoundary h m).map
        (Finsupp.single (g, ()) a) (u, i) =
      a * modTwoFoxDerivative m (sqDiscreteRelator h) (g⁻¹ * u, i) := by
  change (finiteLevelModTwoFoxBoundary m (fun _ : Unit => sqDiscreteRelator h)).map
      (Finsupp.single (g, ()) a) (u, i) = _
  rw [finiteLevelModTwoFoxBoundary_single]
  change a * regularModTwoTranslate Q (Fin (sqRank h)) g
      (modTwoFoxDerivative m (sqDiscreteRelator h)) (u, i) = _
  rw [regularModTwoTranslate_apply]

/-- Square finite-level boundaries are compatible with every refinement homomorphism. -/
theorem sqFiniteLevelModTwoFoxBoundary_natural
    (φ : Q →* Q') (h : ℕ) (m : Fin (sqRank h) → Q)
    (c : RegularModTwoRelationModule Q Unit) :
    regularModTwoPushforward φ (Fin (sqRank h))
        ((sqFiniteLevelModTwoFoxBoundary h m).map c) =
      (sqFiniteLevelModTwoFoxBoundary h (fun i => φ (m i))).map
        (regularModTwoPushforward φ Unit c) :=
  finiteLevelModTwoFoxBoundary_natural φ m (fun _ => sqDiscreteRelator h) c

/-- At the trivial quotient the improved square relator has zero mod-two Fox derivative: its
abelian exponent vector is `-4 x₁ + 2 x₂`.  This is the concrete reason finite-level
injectivity cannot be demanded target by target. -/
theorem modTwoFoxDerivative_sqDiscreteRelator_unit (h : ℕ) :
    modTwoFoxDerivative
        (fun _ : Fin (sqRank h) => (1 : Unit))
        (sqDiscreteRelator h) = 0 := by
  classical
  ext p
  rcases p with ⟨⟨⟩, i⟩
  rw [GQ2.Dyadic.LSquare.modTwoFoxDerivative_unit_apply_eq_heisEps]
  change Multiplicative.toAdd
      (FreeGroup.lift
        (fun j : Fin (sqRank h) =>
          Multiplicative.ofAdd (if j = i then 1 else 0))
        (sqDiscreteRelator h)) = 0
  rw [FreeGroup.lift_sqDiscreteRelator, sqRelWord_comm]
  have hsquare (z : Multiplicative (ZMod 2)) : z ^ 2 = 1 := by
    rw [pow_two]
    revert z
    decide
  have hfourth (z : Multiplicative (ZMod 2)) : z ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by omega, pow_mul, hsquare]
  rw [hfourth, hsquare]
  simp

/-- Regression: the entire one-relator boundary at the trivial quotient is the zero map. -/
theorem sqFiniteLevelModTwoFoxBoundary_unit_eq_zero (h : ℕ)
    (c : RegularModTwoRelationModule Unit Unit) :
    modTwoFoxRelationMatrixLinear
      (fun _ : Fin (sqRank h) => (1 : Unit))
      (fun _ : Unit => sqDiscreteRelator h) c = 0 := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨⟨⟩, ⟨⟩⟩
      rw [map_add, ih, add_zero, modTwoFoxRelationMatrixLinear,
        Finsupp.lsum_single, modTwoFoxDerivative_sqDiscreteRelator_unit]
      simp

end

end GQ2.Dyadic.Count
