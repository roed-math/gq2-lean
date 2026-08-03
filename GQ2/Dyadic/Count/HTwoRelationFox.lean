/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationBasis

/-!
# A universal Fox-matrix criterion for mod-two relation coordinates

The target `ModTwoRelationBasisCoordinates` is a homomorphism on the whole relation kernel.
This file constructs it from genuinely first-order data.  The universal Fox derivative takes
values in the free regular mod-two module on the generators.  A family of relators therefore
defines a matrix

`𝔽₂[L]^(rel) → 𝔽₂[L]^(X)`.

An explicit equivariant left inverse of this matrix gives coordinates on every relation-kernel
element by first taking its universal Fox derivative and then applying the left inverse.  This
is the usual Fox/Jacobian route to a strongly-free relation basis; it does not mention relation
characters, cocycles, cohomology, or the desired coordinate map.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH GQ2.Dyadic

/-! ## The regular action and universal Fox derivative -/

section UniversalFox

variable (L I : Type) [Group L]

/-- The regular module carries the left-translation action used by relation coordinates. -/
instance regularModTwoRelationModuleDistribMulAction :
    DistribMulAction L (RegularModTwoRelationModule L I) where
  smul g c := regularModTwoTranslate L I g c
  one_smul c := by
    ext p
    rcases p with ⟨h, i⟩
    change c (1⁻¹ * h, i) = c (h, i)
    rw [inv_one, one_mul]
  mul_smul g h c := by
    ext p
    rcases p with ⟨k, i⟩
    change c ((g * h)⁻¹ * k, i) = c (h⁻¹ * (g⁻¹ * k), i)
    rw [mul_inv_rev, mul_assoc]
  smul_zero g := (regularModTwoTranslate L I g).map_zero
  smul_add g a b := (regularModTwoTranslate L I g).map_add a b

omit [Group L] in
/-- Every free regular mod-two module is elementary abelian. -/
theorem regularModTwoRelationModule_add_self
    (c : RegularModTwoRelationModule L I) : c + c = 0 := by
  ext p
  exact CharTwo.add_self_eq_zero (c p)

variable {L I}

/-- The universal Fox offset of a free generator: the basis vector at `(1,i)`. -/
def modTwoFoxGenerator (i : I) : RegularModTwoRelationModule L I :=
  Finsupp.single (1, i) 1

/-- The universal mod-two Fox derivative of a free word at the marking `m`.

It is the fibre coordinate of the free-group lift into the split extension by the regular
module, with generator `i` lifted by the basis vector `(1,i)`. -/
def modTwoFoxDerivative (m : I → L) (f : FreeGroup I) :
    RegularModTwoRelationModule L I :=
  (FreeGroup.lift (foxLift m (modTwoFoxGenerator (L := L))) f).u

@[simp] theorem modTwoFoxDerivative_one (m : I → L) :
    modTwoFoxDerivative m 1 = 0 := by
  simp [modTwoFoxDerivative]

@[simp] theorem modTwoFoxDerivative_of (m : I → L) (i : I) :
    modTwoFoxDerivative m (FreeGroup.of i) = modTwoFoxGenerator (L := L) i := by
  simp [modTwoFoxDerivative, modTwoFoxGenerator, foxLift]

/-- On the relation kernel, the universal Fox derivative is additive. -/
theorem modTwoFoxDerivative_mul_kernel (m : I → L)
    (r s : FreeRelationKernel m) :
    modTwoFoxDerivative m (r * s : FreeGroup I) =
      modTwoFoxDerivative m r + modTwoFoxDerivative m s := by
  rw [modTwoFoxDerivative, map_mul, WordLift.mul_u,
    lift_foxLift_g, r.property, one_smul]
  rfl

/-- The universal Fox derivative restricted to the relation kernel, as a homomorphism. -/
def modTwoRelationFoxMap (m : I → L) :
    FreeRelationKernel m →*
      Multiplicative (RegularModTwoRelationModule L I) where
  toFun r := Multiplicative.ofAdd (modTwoFoxDerivative m r)
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    exact modTwoFoxDerivative_mul_kernel m r s

/-- Conjugation of a kernel word translates its universal Fox derivative. -/
theorem modTwoRelationFoxMap_conjugation (m : I → L)
    (f : FreeGroup I) (s : FreeRelationKernel m) :
    modTwoRelationFoxMap m (relationKernelConj m f s) =
      Multiplicative.ofAdd
        (regularModTwoTranslate L I (FreeGroup.lift m f)
          (Multiplicative.toAdd (modTwoRelationFoxMap m s))) := by
  apply Multiplicative.toAdd.injective
  change modTwoFoxDerivative m (f * s.1 * f⁻¹) =
    (FreeGroup.lift m f) • modTwoFoxDerivative m s.1
  simp only [modTwoFoxDerivative, map_mul, map_inv, WordLift.mul_u, WordLift.mul_g,
    WordLift.inv_u]
  rw [lift_foxLift_g, lift_foxLift_g, s.property]
  rw [mul_one, smul_neg, smul_inv_smul]
  abel

/-- Evaluating the universal Fox derivative at offsets in any elementary `L`-module recovers
the ordinary split-extension Fox derivative at those offsets. -/
theorem regularModTwoRelationEval_modTwoFoxDerivative
    {A : Type} [AddCommGroup A] [DistribMulAction L A]
    (hA₂ : ∀ a : A, a + a = 0) (m : I → L) (a : I → A)
    (f : FreeGroup I) :
    regularModTwoRelationEval hA₂ a (modTwoFoxDerivative m f) =
      (FreeGroup.lift (foxLift m a) f).u := by
  let ev : RegularModTwoRelationModule L I →+ A :=
    regularModTwoRelationEval hA₂ a
  have hev : ∀ (g : L) (c : RegularModTwoRelationModule L I),
      ev (g • c) = g • ev c := by
    intro g c
    exact regularModTwoRelationEval_translate hA₂ a g c
  have hlift :
      (WordLift.map ev hev).comp
          (FreeGroup.lift (foxLift m (modTwoFoxGenerator (L := L)))) =
        FreeGroup.lift (foxLift m a) := by
    apply FreeGroup.ext_hom
    intro i
    apply WordLift.ext
    · simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, WordLift.map_u]
      change regularModTwoRelationEval hA₂ a
          (Finsupp.single ((1 : L), i) 1) = a i
      exact regularModTwoRelationEval_basis hA₂ a i
    · simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, WordLift.map_g]
      rfl
  have hf := congrArg
    (fun F : FreeGroup I →* WordLift A L => (F f).u) hlift
  simpa [modTwoFoxDerivative, ev] using hf

end UniversalFox

/-! ## The relation Fox matrix -/

section RelationMatrix

variable {I rel L : Type} [Group L]

/-- The universal Fox relation matrix.  Its `k`th regular basis vector is sent to the universal
Fox derivative of the `k`th relator. -/
def modTwoFoxRelationMatrix (m : I → L) (w : rel → FreeGroup I) :
    RegularModTwoRelationModule L rel →+
      RegularModTwoRelationModule L I :=
  regularModTwoRelationEval
    (fun a => regularModTwoRelationModule_add_self L I a)
    (fun k => modTwoFoxDerivative m (w k))

@[simp] theorem modTwoFoxRelationMatrix_basis
    (m : I → L) (w : rel → FreeGroup I) (k : rel) :
    modTwoFoxRelationMatrix m w (Finsupp.single ((1 : L), k) 1) =
      modTwoFoxDerivative m (w k) :=
  regularModTwoRelationEval_basis
    (fun a => regularModTwoRelationModule_add_self L I a)
    (fun k => modTwoFoxDerivative m (w k)) k

/-- The universal Fox relation matrix is equivariant for regular translation. -/
theorem modTwoFoxRelationMatrix_translate
    (m : I → L) (w : rel → FreeGroup I) (g : L)
    (c : RegularModTwoRelationModule L rel) :
    modTwoFoxRelationMatrix m w (regularModTwoTranslate L rel g c) =
      regularModTwoTranslate L I g (modTwoFoxRelationMatrix m w c) :=
  regularModTwoRelationEval_translate
    (fun a => regularModTwoRelationModule_add_self L I a)
    (fun k => modTwoFoxDerivative m (w k)) g c

/-- The `k`th row of the universal relation matrix specializes to the existing word-complex
Fox differential in every elementary coefficient module. -/
theorem regularModTwoRelationEval_foxMatrix_basis
    {A : Type} [AddCommGroup A] [DistribMulAction L A]
    (hA₂ : ∀ a : A, a + a = 0) (m : I → L)
    (w : rel → FreeGroup I) (a : I → A) (k : rel) :
    regularModTwoRelationEval hA₂ a
        (modTwoFoxRelationMatrix m w (Finsupp.single ((1 : L), k) 1)) =
      heisD1 (A := A) m w a k := by
  rw [modTwoFoxRelationMatrix_basis,
    regularModTwoRelationEval_modTwoFoxDerivative,
    heisD1_eq_lift_foxLift_u]

/-- A split-injective universal Fox relation matrix.  This is first-order data in the free
regular generator module, not a coordinate map on the relation kernel. -/
structure ModTwoFoxRelationRetraction (m : I → L) (w : rel → FreeGroup I) where
  retraction : RegularModTwoRelationModule L I →+
    RegularModTwoRelationModule L rel
  leftInverse : Function.LeftInverse retraction (modTwoFoxRelationMatrix m w)
  equivariant : ∀ (g : L) (c : RegularModTwoRelationModule L I),
    retraction (regularModTwoTranslate L I g c) =
      regularModTwoTranslate L rel g (retraction c)

/-- Any universal Fox retraction forces the relation matrix to be injective.  This small
regression is useful for rejecting over-strong finite-target criteria before attempting a
normal-form construction. -/
theorem ModTwoFoxRelationRetraction.matrix_injective
    {m : I → L} {w : rel → FreeGroup I}
    (R : ModTwoFoxRelationRetraction m w) :
    Function.Injective (modTwoFoxRelationMatrix m w) :=
  R.leftInverse.injective

/-- A noninjective universal Fox matrix admits no equivariant left retraction. -/
theorem not_nonempty_modTwoFoxRelationRetraction_of_not_injective
    {m : I → L} {w : rel → FreeGroup I}
    (h : ¬ Function.Injective (modTwoFoxRelationMatrix m w)) :
    ¬ Nonempty (ModTwoFoxRelationRetraction m w) := by
  rintro ⟨R⟩
  exact h R.matrix_injective

/-! ### An explicit pivot normal form -/

/-- Embed the regular relator basis into selected generator pivots. -/
def regularModTwoPivotEmbedding (pivot : rel ↪ I) : L × rel ↪ L × I where
  toFun p := (p.1, pivot p.2)
  inj' := by
    intro p q hpq
    change (p.1, pivot p.2) = (q.1, pivot q.2) at hpq
    apply Prod.ext
    · exact congrArg (fun x : L × I => x.1) hpq
    · exact pivot.injective (congrArg (fun x : L × I => x.2) hpq)

/-- The standard pivot inclusion `𝔽₂[L]^(rel) → 𝔽₂[L]^(I)`. -/
def regularModTwoPivotEmbed (pivot : rel ↪ I) :
    RegularModTwoRelationModule L rel →+
      RegularModTwoRelationModule L I :=
  Finsupp.embDomain.addMonoidHom (regularModTwoPivotEmbedding (L := L) pivot)

/-- Projection from the generator regular module onto selected relator pivots. -/
def regularModTwoPivotProject (pivot : rel ↪ I) :
    RegularModTwoRelationModule L I →+
      RegularModTwoRelationModule L rel :=
  Finsupp.comapDomain.addMonoidHom
    (regularModTwoPivotEmbedding (L := L) pivot).injective

omit [Group L] in
/-- Pivot projection is a left inverse to pivot inclusion. -/
theorem regularModTwoPivotProject_leftInverse (pivot : rel ↪ I) :
    Function.LeftInverse (regularModTwoPivotProject (L := L) pivot)
      (regularModTwoPivotEmbed (L := L) pivot) := by
  intro c
  exact Finsupp.comapDomain_embDomain
    (regularModTwoPivotEmbedding (L := L) pivot) c

/-- Pivot projection commutes with regular translation. -/
theorem regularModTwoPivotProject_translate (pivot : rel ↪ I) (g : L)
    (c : RegularModTwoRelationModule L I) :
    regularModTwoPivotProject (L := L) pivot
        (regularModTwoTranslate L I g c) =
      regularModTwoTranslate L rel g
        (regularModTwoPivotProject (L := L) pivot c) := by
  ext p
  rcases p with ⟨h, k⟩
  change (regularModTwoTranslate L I g c) (h, pivot k) =
    c (g⁻¹ * h, pivot k)
  rw [regularModTwoTranslate_apply]

/-- A Fox relation matrix reduced by an equivariant generator-coordinate change to a standard
pivot inclusion.  This is the direct universal-module analogue of a certified Fox normal form. -/
structure ModTwoFoxRelationNormalForm (m : I → L) (w : rel → FreeGroup I) where
  pivot : rel ↪ I
  columnEquiv : RegularModTwoRelationModule L I ≃+
    RegularModTwoRelationModule L I
  columnEquivariant : ∀ (g : L) (c : RegularModTwoRelationModule L I),
    columnEquiv (regularModTwoTranslate L I g c) =
      regularModTwoTranslate L I g (columnEquiv c)
  reduces : columnEquiv.toAddMonoidHom.comp (modTwoFoxRelationMatrix m w) =
    regularModTwoPivotEmbed (L := L) pivot

/-- A certified universal Fox pivot normal form gives an equivariant Fox retraction. -/
noncomputable def ModTwoFoxRelationNormalForm.toRetraction
    {m : I → L} {w : rel → FreeGroup I}
    (N : ModTwoFoxRelationNormalForm m w) :
    ModTwoFoxRelationRetraction m w where
  retraction :=
    (regularModTwoPivotProject (L := L) N.pivot).comp
      N.columnEquiv.toAddMonoidHom
  leftInverse c := by
    change regularModTwoPivotProject (L := L) N.pivot
      (N.columnEquiv (modTwoFoxRelationMatrix m w c)) = c
    have hc := DFunLike.congr_fun N.reduces c
    rw [AddMonoidHom.comp_apply] at hc
    change N.columnEquiv (modTwoFoxRelationMatrix m w c) =
      regularModTwoPivotEmbed (L := L) N.pivot c at hc
    rw [hc]
    exact regularModTwoPivotProject_leftInverse N.pivot c
  equivariant g c := by
    change regularModTwoPivotProject (L := L) N.pivot
        (N.columnEquiv (regularModTwoTranslate L I g c)) =
      regularModTwoTranslate L rel g
        (regularModTwoPivotProject (L := L) N.pivot (N.columnEquiv c))
    rw [N.columnEquivariant, regularModTwoPivotProject_translate]

/-- An equivariant left inverse to the universal Fox matrix constructs the desired mod-two
relation coordinates. -/
noncomputable def ModTwoRelationBasisCoordinates.ofFoxRetraction
    {m : I → L} {w : rel → FreeGroup I}
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (R : ModTwoFoxRelationRetraction m w) :
    ModTwoRelationBasisCoordinates w hrel where
  coordinates :=
    (AddMonoidHom.toMultiplicative R.retraction).comp (modTwoRelationFoxMap m)
  conjugation f s := by
    change Multiplicative.ofAdd
        (R.retraction
          (Multiplicative.toAdd
            (modTwoRelationFoxMap m (relationKernelConj m f s)))) = _
    rw [modTwoRelationFoxMap_conjugation]
    change Multiplicative.ofAdd
        (R.retraction (regularModTwoTranslate L I (FreeGroup.lift m f)
          (Multiplicative.toAdd (modTwoRelationFoxMap m s)))) = _
    rw [R.equivariant]
    rfl
  relator k := by
    change Multiplicative.ofAdd (R.retraction (modTwoFoxDerivative m (w k))) = _
    rw [← modTwoFoxRelationMatrix_basis m w k, R.leftInverse]

/-- A certified equivariant Fox pivot normal form directly constructs mod-two relation-basis
coordinates. -/
noncomputable def ModTwoRelationBasisCoordinates.ofFoxNormalForm
    {m : I → L} {w : rel → FreeGroup I}
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (N : ModTwoFoxRelationNormalForm m w) :
    ModTwoRelationBasisCoordinates w hrel :=
  .ofFoxRetraction hrel N.toRetraction

/-- In the square case, bijectivity of the universal Fox matrix supplies its equivariant
inverse and hence a Fox retraction automatically. -/
noncomputable def ModTwoFoxRelationRetraction.ofBijective
    (m : I → L) (w : rel → FreeGroup I)
    (hbij : Function.Bijective (modTwoFoxRelationMatrix m w)) :
    ModTwoFoxRelationRetraction m w := by
  let e : RegularModTwoRelationModule L rel ≃+
      RegularModTwoRelationModule L I :=
    AddEquiv.ofBijective (modTwoFoxRelationMatrix m w) hbij
  refine {
    retraction := e.symm.toAddMonoidHom
    leftInverse := by
      intro c
      exact e.left_inv c
    equivariant := ?_
  }
  intro g c
  apply e.injective
  change e (e.symm (regularModTwoTranslate L I g c)) =
    e (regularModTwoTranslate L rel g (e.symm c))
  rw [e.apply_symm_apply]
  change regularModTwoTranslate L I g c =
    modTwoFoxRelationMatrix m w
      (regularModTwoTranslate L rel g (e.symm c))
  rw [modTwoFoxRelationMatrix_translate]
  change regularModTwoTranslate L I g c =
    regularModTwoTranslate L I g (e (e.symm c))
  rw [e.apply_symm_apply]

/-- A bijective universal Fox relation matrix directly constructs mod-two relation-basis
coordinates. -/
noncomputable def ModTwoRelationBasisCoordinates.ofBijectiveFoxMatrix
    {m : I → L} {w : rel → FreeGroup I}
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (hbij : Function.Bijective (modTwoFoxRelationMatrix m w)) :
    ModTwoRelationBasisCoordinates w hrel :=
  .ofFoxRetraction hrel (.ofBijective m w hbij)

end RelationMatrix

end


end GQ2.Dyadic.Count
