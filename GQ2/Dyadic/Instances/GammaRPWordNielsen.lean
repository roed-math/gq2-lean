import GQ2.Dyadic.Instances.GammaRNielsenTransport

/-!
# Syntactic Nielsen pairs for the dyadic alphabet
-/

namespace GQ2.Dyadic.Instances.GammaRPWordNielsen

noncomputable section

open GQ2 GQ2.Dyadic CategoryTheory
open GQ2.Dyadic.Instances.GammaRNielsenTransport

private theorem freeHom_ext {X : Type} {P : ProfiniteGrp}
    {f g : FreeProfiniteGroup X ⟶ P}
    (h : ∀ x, f (FreeProfiniteGroup.of x) = g (FreeProfiniteGroup.of x)) : f = g :=
  (FreeProfiniteGroup.homEquiv X P).injective <| funext fun x => by
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]
    exact h x

/-- The continuous endomorphism of the free profinite group defined by a word substitution. -/
noncomputable def freeWordHom {n : ℕ} (φ : Generator n → PWord (Generator n)) :
    FreeProfiniteGroup (Generator n) ⟶ FreeProfiniteGroup (Generator n) :=
  (FreeProfiniteGroup.homEquiv (Generator n) (FreeProfiniteGroup (Generator n))).symm
    fun g => (freeMarking n).eval (φ g)

@[simp] theorem freeWordHom_of {n : ℕ} (φ : Generator n → PWord (Generator n))
    (g : Generator n) :
    freeWordHom φ (FreeProfiniteGroup.of g) = (freeMarking n).eval (φ g) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem freeWordHom_eval {n : ℕ} (φ : Generator n → PWord (Generator n))
    (w : PWord (Generator n)) :
    freeWordHom φ ((freeMarking n).eval w) =
      (freeMarking n).eval (PWord.subst φ w) := by
  rw [Marking.map_eval]
  simp only [Marking.eval_def, PWord.eval_subst]
  congr 1
  funext g
  exact freeWordHom_of φ g

/-- Two word substitutions inverse after evaluation in the free profinite group. -/
structure PWordNielsenPair (n : ℕ) where
  forward : Generator n → PWord (Generator n)
  backward : Generator n → PWord (Generator n)
  backward_forward : ∀ g : Generator n,
    (freeMarking n).eval (PWord.subst backward (forward g)) =
      FreeProfiniteGroup.of g
  forward_backward : ∀ g : Generator n,
    (freeMarking n).eval (PWord.subst forward (backward g)) =
      FreeProfiniteGroup.of g

theorem PWordNielsenPair.forward_comp_backward {n : ℕ} (T : PWordNielsenPair n) :
    (freeWordHom T.forward) ≫ (freeWordHom T.backward) = 𝟙 _ := by
  apply freeHom_ext
  intro g
  change freeWordHom T.backward (freeWordHom T.forward (FreeProfiniteGroup.of g)) = _
  rw [freeWordHom_of, freeWordHom_eval, T.backward_forward]
  rfl

theorem PWordNielsenPair.backward_comp_forward {n : ℕ} (T : PWordNielsenPair n) :
    (freeWordHom T.backward) ≫ (freeWordHom T.forward) = 𝟙 _ := by
  apply freeHom_ext
  intro g
  change freeWordHom T.forward (freeWordHom T.backward (FreeProfiniteGroup.of g)) = _
  rw [freeWordHom_of, freeWordHom_eval, T.forward_backward]
  rfl

/-- The continuous free-profinite equivalence denoted by an inverse word-substitution pair. -/
noncomputable def PWordNielsenPair.freeEquiv {n : ℕ} (T : PWordNielsenPair n) :
    ContinuousMulEquiv ((FreeProfiniteGroup (Generator n)) : Type)
      ((FreeProfiniteGroup (Generator n)) : Type) where
  toFun := (freeWordHom T.forward).hom
  invFun := (freeWordHom T.backward).hom
  left_inv := fun w => by
    change ((freeWordHom T.forward) ≫ (freeWordHom T.backward)) w = w
    rw [T.forward_comp_backward]
    rfl
  right_inv := fun w => by
    change ((freeWordHom T.backward) ≫ (freeWordHom T.forward)) w = w
    rw [T.backward_comp_forward]
    rfl
  map_mul' := map_mul (freeWordHom T.forward).hom
  continuous_toFun := (freeWordHom T.forward).hom.continuous_toFun
  continuous_invFun := (freeWordHom T.backward).hom.continuous_toFun

@[simp] theorem PWordNielsenPair.freeEquiv_of {n : ℕ} (T : PWordNielsenPair n)
    (g : Generator n) :
    T.freeEquiv (FreeProfiniteGroup.of g) = (freeMarking n).eval (T.forward g) :=
  freeWordHom_of T.forward g

@[simp] theorem PWordNielsenPair.freeEquiv_symm_of {n : ℕ} (T : PWordNielsenPair n)
    (g : Generator n) :
    T.freeEquiv.symm (FreeProfiniteGroup.of g) = (freeMarking n).eval (T.backward g) :=
  freeWordHom_of T.backward g

/-- The finite checklist making a syntactic Nielsen pair admissible for two corrected words. -/
structure AdmissiblePWordNielsenEquiv (n q : ℕ) (R₀ R₁ : PWord (Generator n)) where
  pair : PWordNielsenPair n
  forward_tame :
    gammaMk n q R₀ ((freeWordHom pair.forward) (tameRelatorGen n q)) = 1
  forward_word :
    gammaMk n q R₀ ((freeMarking n).eval (PWord.subst pair.forward R₁)) = 1
  backward_tame :
    gammaMk n q R₁ ((freeWordHom pair.backward) (tameRelatorGen n q)) = 1
  backward_word :
    gammaMk n q R₁ ((freeMarking n).eval (PWord.subst pair.backward R₀)) = 1
  forward_wild : ∀ i : Fin (n + 1),
    (freeMarking n).eval (pair.forward (.wild i)) ∈
      Subgroup.normalClosure (wildFree n)
  backward_wild : ∀ i : Fin (n + 1),
    (freeMarking n).eval (pair.backward (.wild i)) ∈
      Subgroup.normalClosure (wildFree n)

/-- The syntactic checklist supplies the concrete wild-preserving free Nielsen packet. -/
noncomputable def AdmissiblePWordNielsenEquiv.toWildPreserving
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissiblePWordNielsenEquiv n q R₀ R₁) :
    WildPreservingFreeNielsenEquiv n q R₀ R₁ where
  freeEquiv := T.pair.freeEquiv
  forward_rel := by
    intro r hr
    rcases hr with rfl | rfl
    · exact T.forward_tame
    · rw [show T.pair.freeEquiv ((freeMarking n).eval R₁) =
          (freeMarking n).eval (PWord.subst T.pair.forward R₁) from
        freeWordHom_eval T.pair.forward R₁]
      exact T.forward_word
  backward_rel := by
    intro r hr
    rcases hr with rfl | rfl
    · exact T.backward_tame
    · rw [show T.pair.freeEquiv.symm ((freeMarking n).eval R₀) =
          (freeMarking n).eval (PWord.subst T.pair.backward R₀) from
        freeWordHom_eval T.pair.backward R₀]
      exact T.backward_word
  forward_wild := fun i => T.pair.freeEquiv_of (.wild i) ▸ T.forward_wild i
  backward_wild := fun i => T.pair.freeEquiv_symm_of (.wild i) ▸ T.backward_wild i

/-- The corrected presentation equivalence denoted by an admissible word-substitution pair. -/
noncomputable def AdmissiblePWordNielsenEquiv.gammaEquiv
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissiblePWordNielsenEquiv n q R₀ R₁) :
    ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type) :=
  T.toWildPreserving.toAdmissible.gammaEquiv

#print axioms PWordNielsenPair
#print axioms PWordNielsenPair.freeEquiv
#print axioms PWordNielsenPair.freeEquiv_of
#print axioms AdmissiblePWordNielsenEquiv
#print axioms AdmissiblePWordNielsenEquiv.toWildPreserving
#print axioms AdmissiblePWordNielsenEquiv.gammaEquiv

end

end GQ2.Dyadic.Instances.GammaRPWordNielsen
