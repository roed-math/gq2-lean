import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificateTransport

/-!
# Nielsen transport for corrected dyadic presentations

An invertible transformation of the free profinite alphabet descends to the corrected
`GammaR` quotients once it kills the two target relators in both directions and satisfies the
restricted wild-core clause in both directions.  This is the presentation-theoretic layer
needed before checking the two boundary squares of W327.
-/

namespace GQ2.Dyadic.Instances.GammaRNielsenTransport

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Count
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificateTransport
open TameSpec

/-- The restricted wild-core clause for a free-profinite endomorphism into one corrected
presentation. -/
def FreeWildCore (n q : ℕ) (R : PWord (Generator n))
    (e : ContinuousMonoidHom
      ((FreeProfiniteGroup (Generator n)) : Type)
      ((FreeProfiniteGroup (Generator n)) : Type)) : Prop :=
  ∀ V : OpenNormalSubgroup ((GammaR n q R) : Type),
    IsPGroup 2 ((Subgroup.normalClosure (wildFree n)).map
      ((QuotientGroup.mk' V.toSubgroup).comp
        ((gammaMk n q R).comp e).toMonoidHom))

/-- An invertible free-profinite transformation admissible for two corrected presentations. -/
structure AdmissibleFreeNielsenEquiv (n q : ℕ) (R₀ R₁ : PWord (Generator n)) where
  freeEquiv : ContinuousMulEquiv
    ((FreeProfiniteGroup (Generator n)) : Type)
    ((FreeProfiniteGroup (Generator n)) : Type)
  forward_rel : ∀ r ∈ gammaRelators n q R₁,
    gammaMk n q R₀ (freeEquiv r) = 1
  backward_rel : ∀ r ∈ gammaRelators n q R₀,
    gammaMk n q R₁ (freeEquiv.symm r) = 1
  forward_core : FreeWildCore n q R₀
    (freeEquiv : ContinuousMonoidHom _ _)
  backward_core : FreeWildCore n q R₁
    (freeEquiv.symm : ContinuousMonoidHom _ _)

/-- The wild-core clause follows if a free transformation sends every wild generator into the
normal closure of the target wild generators. -/
theorem wildCore_of_generator_images
    {n q : ℕ} {R : PWord (Generator n)}
    (e : ContinuousMonoidHom
      ((FreeProfiniteGroup (Generator n)) : Type)
      ((FreeProfiniteGroup (Generator n)) : Type))
    (hwild : ∀ i : Fin (n + 1),
      e (FreeProfiniteGroup.of (Generator.wild i)) ∈
        Subgroup.normalClosure (wildFree n))
    : FreeWildCore n q R e := by
  intro V
  let ψ : ((FreeProfiniteGroup (Generator n)) : Type) →*
      ((GammaR n q R) : Type) ⧸ V.toSubgroup :=
    (QuotientGroup.mk' V.toSubgroup).comp (gammaMk n q R).toMonoidHom
  let ρ : ((FreeProfiniteGroup (Generator n)) : Type) →*
      ((GammaR n q R) : Type) ⧸ V.toSubgroup := ψ.comp e.toMonoidHom
  let H : Subgroup (((GammaR n q R) : Type) ⧸ V.toSubgroup) :=
    Subgroup.normalClosure ((QuotientGroup.mk' V.toSubgroup) ''
      Set.range fun i : Fin (n + 1) => gammaGen n q R (.wild i))
  have hψ : (Subgroup.normalClosure (wildFree n)).map ψ ≤ H := by
    refine (Subgroup.map_normalClosure_le _ _).trans ?_
    apply Subgroup.normalClosure_mono
    rw [image_wildFree]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact ⟨gammaGen n q R (.wild i), ⟨i, rfl⟩, rfl⟩
  have hle : (Subgroup.normalClosure (wildFree n)).map ρ ≤ H := by
    refine (Subgroup.map_normalClosure_le _ _).trans ?_
    refine Subgroup.normalClosure_le_normal fun y hy => ?_
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨i, rfl⟩
    exact hψ ⟨e (FreeProfiniteGroup.of (Generator.wild i)), hwild i, rfl⟩
  exact (isPGroup_two_wildNormalClosure V).to_le hle

/-- A free Nielsen equivalence with concrete wild-generator control.  Unlike the restricted
universal-property packet above, this form asks only for finite relator checks and membership in
the wild normal closure. -/
structure WildPreservingFreeNielsenEquiv (n q : ℕ) (R₀ R₁ : PWord (Generator n)) where
  freeEquiv : ContinuousMulEquiv
    ((FreeProfiniteGroup (Generator n)) : Type)
    ((FreeProfiniteGroup (Generator n)) : Type)
  forward_rel : ∀ r ∈ gammaRelators n q R₁,
    gammaMk n q R₀ (freeEquiv r) = 1
  backward_rel : ∀ r ∈ gammaRelators n q R₀,
    gammaMk n q R₁ (freeEquiv.symm r) = 1
  forward_wild : ∀ i : Fin (n + 1),
    freeEquiv (FreeProfiniteGroup.of (Generator.wild i)) ∈
      Subgroup.normalClosure (wildFree n)
  backward_wild : ∀ i : Fin (n + 1),
    freeEquiv.symm (FreeProfiniteGroup.of (Generator.wild i)) ∈
      Subgroup.normalClosure (wildFree n)

noncomputable def WildPreservingFreeNielsenEquiv.forwardHom
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : WildPreservingFreeNielsenEquiv n q R₀ R₁) :
    ContinuousMonoidHom ((FreeProfiniteGroup (Generator n)) : Type)
      ((FreeProfiniteGroup (Generator n)) : Type) :=
  T.freeEquiv

noncomputable def WildPreservingFreeNielsenEquiv.backwardHom
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : WildPreservingFreeNielsenEquiv n q R₀ R₁) :
    ContinuousMonoidHom ((FreeProfiniteGroup (Generator n)) : Type)
      ((FreeProfiniteGroup (Generator n)) : Type) :=
  T.freeEquiv.symm

theorem WildPreservingFreeNielsenEquiv.forward_core
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : WildPreservingFreeNielsenEquiv n q R₀ R₁)
    : FreeWildCore n q R₀ T.forwardHom :=
  wildCore_of_generator_images (n := n) (q := q) (R := R₀)
    T.forwardHom T.forward_wild

theorem WildPreservingFreeNielsenEquiv.backward_core
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : WildPreservingFreeNielsenEquiv n q R₀ R₁)
    : FreeWildCore n q R₁ T.backwardHom :=
  wildCore_of_generator_images (n := n) (q := q) (R := R₁)
    T.backwardHom T.backward_wild

/-- Wild-generator control discharges both restricted admissibility clauses. -/
noncomputable def WildPreservingFreeNielsenEquiv.toAdmissible
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : WildPreservingFreeNielsenEquiv n q R₀ R₁) :
    AdmissibleFreeNielsenEquiv n q R₀ R₁ where
  freeEquiv := T.freeEquiv
  forward_rel := T.forward_rel
  backward_rel := T.backward_rel
  forward_core := T.forward_core
  backward_core := T.backward_core

/-- The forward homomorphism induced by an admissible Nielsen transformation. -/
noncomputable def AdmissibleFreeNielsenEquiv.forward
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁) :
    ContinuousMonoidHom ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type) :=
  gammaLift n q R₁
    ((gammaMk n q R₀).comp
      (T.freeEquiv : ContinuousMonoidHom
        ((FreeProfiniteGroup (Generator n)) : Type)
        ((FreeProfiniteGroup (Generator n)) : Type)))
    T.forward_rel T.forward_core

/-- The inverse homomorphism induced by an admissible Nielsen transformation. -/
noncomputable def AdmissibleFreeNielsenEquiv.backward
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁) :
    ContinuousMonoidHom ((GammaR n q R₀) : Type) ((GammaR n q R₁) : Type) :=
  gammaLift n q R₀
    ((gammaMk n q R₁).comp
      (T.freeEquiv.symm : ContinuousMonoidHom
        ((FreeProfiniteGroup (Generator n)) : Type)
        ((FreeProfiniteGroup (Generator n)) : Type)))
    T.backward_rel T.backward_core

@[simp] theorem AdmissibleFreeNielsenEquiv.forward_gammaMk
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (w : ((FreeProfiniteGroup (Generator n)) : Type)) :
    T.forward (gammaMk n q R₁ w) = gammaMk n q R₀ (T.freeEquiv w) :=
  rfl

@[simp] theorem AdmissibleFreeNielsenEquiv.backward_gammaMk
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (w : ((FreeProfiniteGroup (Generator n)) : Type)) :
    T.backward (gammaMk n q R₀ w) = gammaMk n q R₁ (T.freeEquiv.symm w) :=
  rfl

theorem AdmissibleFreeNielsenEquiv.backward_forward
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (g : ((GammaR n q R₁) : Type)) : T.backward (T.forward g) = g := by
  obtain ⟨w, rfl⟩ := gammaMk_surjective n q R₁ g
  simp

theorem AdmissibleFreeNielsenEquiv.forward_backward
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (g : ((GammaR n q R₀) : Type)) : T.forward (T.backward g) = g := by
  obtain ⟨w, rfl⟩ := gammaMk_surjective n q R₀ g
  simp

/-- The corrected presentation equivalence induced by an admissible free Nielsen move. -/
noncomputable def AdmissibleFreeNielsenEquiv.gammaEquiv
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁) :
    ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type) where
  toFun := T.forward
  invFun := T.backward
  left_inv := T.backward_forward
  right_inv := T.forward_backward
  map_mul' := map_mul T.forward
  continuous_toFun := T.forward.continuous_toFun
  continuous_invFun := T.backward.continuous_toFun

@[simp] theorem AdmissibleFreeNielsenEquiv.gammaEquiv_gammaMk
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)}
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (w : ((FreeProfiniteGroup (Generator n)) : Type)) :
    T.gammaEquiv (gammaMk n q R₁ w) = gammaMk n q R₀ (T.freeEquiv w) :=
  rfl

/-! ## The two boundary squares, reduced to free-generator rows -/

/-- Generator-level data sufficient for the tame and pro-2 boundary squares. -/
structure NielsenBoundaryRows
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {hq0 : q ≠ 0} {hqe : Even q}
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (C : FlexibleCoreLeavesRN n R₁ P nuP)
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁) where
  tame_row : ∀ g : Generator n,
    tameOfSpec n q R₀ W.tameSpecialization
        (gammaMk n q R₀ (T.freeEquiv (FreeProfiniteGroup.of g))) =
      tameMarking n q g
  pro2_row : ∀ g : Generator n,
    W.pro2 (gammaMk n q R₀ (T.freeEquiv (FreeProfiniteGroup.of g))) =
      C.presentation.mark g

/-- Generator-level Nielsen rows produce the exact W327 boundary-compatible transport packet. -/
noncomputable def BoundaryCompatibleWordEquivRN.ofNielsen
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {hq0 : q ≠ 0} {hqe : Even q}
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (C : FlexibleCoreLeavesRN n R₁ P nuP)
    (hspec : TameSpecializes n q R₁)
    (T : AdmissibleFreeNielsenEquiv n q R₀ R₁)
    (H : NielsenBoundaryRows (hq0 := hq0) (hqe := hqe) W C T) :
    BoundaryCompatibleWordEquivRN hq0 hqe W C hspec where
  equiv := T.gammaEquiv
  tame_eq := by
    refine gammaR_hom_ext fun g => ?_
    rw [tameOfSpec_gammaGen]
    change tameMarking n q g = tameOfSpec n q R₀ W.tameSpecialization
      (gammaMk n q R₀ (T.freeEquiv (FreeProfiniteGroup.of g)))
    exact (H.tame_row g).symm
  pro2_eq := by
    refine gammaR_hom_ext fun g => ?_
    rw [FlexibleCoreLeavesRN.pro2, CorePresentation.coreHom_gammaGen]
    change C.presentation.mark g =
      W.pro2 (gammaMk n q R₀ (T.freeEquiv (FreeProfiniteGroup.of g)))
    exact (H.pro2_row g).symm

#print axioms AdmissibleFreeNielsenEquiv
#print axioms WildPreservingFreeNielsenEquiv
#print axioms WildPreservingFreeNielsenEquiv.toAdmissible
#print axioms AdmissibleFreeNielsenEquiv.gammaEquiv
#print axioms AdmissibleFreeNielsenEquiv.gammaEquiv_gammaMk
#print axioms NielsenBoundaryRows
#print axioms BoundaryCompatibleWordEquivRN.ofNielsen

end

end GQ2.Dyadic.Instances.GammaRNielsenTransport
