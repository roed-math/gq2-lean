module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.FieldTheory.GaloisCohomology.Restriction
public import GQ2.Foundations.LiteratureInputs

/-!
# Prototype for A1 (and the Tau Ceti half of B11a), lane `galois`

Sorry-free.  `kEmb`/`range_extend_kEmb` follow
`TauCeti.ClassFieldTheory.range_absoluteGaloisGroupExtend_shapiroFieldEmbedding`.
`cup_gq2KummerChar_eq_zero_iff` is B11a with the gq2 cohomology replaced by Tau Ceti's
`continuousCohomology _ (trivialF2 ↥k.fixingSubgroup)`; the remaining B11a step is A2.
-/

noncomputable section

namespace GaloisLaneProto

variable (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]

def kEmb : k →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] :=
  IntermediateField.inclusion fun x _ ↦
    (mem_separableClosure_iff (F := ℚ_[2])).2 (Algebra.IsSeparable.isSeparable ℚ_[2] x)

theorem range_extend_kEmb :
    (TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (kEmb k)).range = k.fixingSubgroup := by
  ext g
  rw [TauCeti.mem_range_absoluteGaloisGroupExtend_iff, TauCeti.mem_galoisSubgroup_iff]
  refine ⟨fun h ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_,
    fun h x ↦ Subtype.ext ?_⟩
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).symm.trans
      (congrArg Subtype.val (h ⟨x, hx⟩))
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 h x x.2)

/-- `↥k.fixingSubgroup` is compact (not found by instance search); this gives the
`LocallyCompactSpace` argument of `explicitH2AddEquivContinuousCohomology`.  Works with this
light import set only; see the import-pathology note in `section.md`. -/
theorem compactSpace_fixingSubgroup : CompactSpace k.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed k).isCompact

example : LocallyCompactSpace k.fixingSubgroup := by
  have := compactSpace_fixingSubgroup k
  infer_instance

/-- A1: gq2's `G_k = ↥k.fixingSubgroup` is Mathlib's `G_k`. -/
def galEquivFixing : Field.absoluteGaloisGroup k ≃ₜ*
    ↥(k.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])) :=
  TauCeti.absoluteGaloisGroupExtendEquiv ℚ_[2] k (kEmb k) (range_extend_kEmb k)

theorem galEquivFixing_apply (g : Field.absoluteGaloisGroup k) :
    ((galEquivFixing k g : k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (kEmb k) g :=
  TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply _ _ _ _ g

/-- A1: gq2's `G_k` is Tau Ceti's `G_k = Gal(kˢ/k)`. -/
def fixingEquivTC : k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup k :=
  (galEquivFixing k).symm.trans (TauCeti.absoluteGaloisGroupRestrictEquiv k)

theorem mem_galoisSubgroup_of_mem (g : GQ2.Kummer.GaloisGroup ℚ_[2]) (hg : g ∈ k.fixingSubgroup) :
    TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] g ∈ TauCeti.galoisSubgroup ℚ_[2] k (kEmb k) :=
  (TauCeti.mem_range_absoluteGaloisGroupExtend_iff ℚ_[2] k (kEmb k)).1
    (by rw [range_extend_kEmb]; exact hg)

theorem mem_of_mem_galoisSubgroup (h : TauCeti.AbsoluteGaloisGroup ℚ_[2])
    (hh : h ∈ TauCeti.galoisSubgroup ℚ_[2] k (kEmb k)) :
    (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h ∈ k.fixingSubgroup := by
  have := (TauCeti.mem_range_absoluteGaloisGroupExtend_iff ℚ_[2] k (kEmb k)
    (g := (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h)).2
    (by rwa [ContinuousMulEquiv.apply_symm_apply])
  rwa [range_extend_kEmb] at this

/-- `ρ : G_k (gq2) ≃ₜ* galoisSubgroup ℚ₂ k σ` (restriction to `ℚ₂ˢ`). -/
def rho : k.fixingSubgroup ≃ₜ*
    ↥(TauCeti.galoisSubgroup ℚ_[2] k (kEmb k)).toSubgroup where
  toFun g := ⟨TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] (g : GQ2.Kummer.GaloisGroup ℚ_[2]),
    mem_galoisSubgroup_of_mem k g g.2⟩
  invFun h := ⟨(TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h,
    mem_of_mem_galoisSubgroup k h h.2⟩
  left_inv _ := Subtype.ext ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm_apply_apply _)
  right_inv _ := Subtype.ext ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]) _ _)
  continuous_toFun :=
    ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_rho_apply (g : k.fixingSubgroup) :
    (rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]) =
      TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] (g : GQ2.Kummer.GaloisGroup ℚ_[2]) := rfl

/-- the gq2 Kummer cocycle of `a` (with `sqrtCl`), as a continuous character of `G_k` -/
def gq2KummerChar (a : (↥k)ˣ) :
    k.fixingSubgroup →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd
    (GQ2.Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : k) : AlgebraicClosure ℚ_[2]))
      ((g : k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]))
  map_one' := by simp [GQ2.Kummer.kummerCocycleFun]
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    exact GQ2.kummerCocycleFun_hom_on (GQ2.sqrtCl_sq _)
      (GQ2.sqrtCl_ne_zero (GQ2.unitCoe_ne_zero k a))
      (fun _ hg' ↦ GQ2.fixingSubgroup_smul k hg' (a : ↥k)) g h

omit [FiniteDimensional ℚ_[2] k] in
theorem continuous_gq2KummerChar (a : (↥k)ˣ) : Continuous (gq2KummerChar k a) :=
  continuous_ofAdd.comp ((GQ2.Kummer.kummerCocycleFun_continuous _).comp continuous_subtype_val)

/-- the separable square root used on the Tau Ceti side -/
def sepRoot (a : (↥k)ˣ) : SeparableClosure ℚ_[2] :=
  ⟨GQ2.sqrtCl ((a : k) : AlgebraicClosure ℚ_[2]),
    (mem_separableClosure_iff (F := ℚ_[2])).2 (Algebra.IsSeparable.isSeparable ℚ_[2] _)⟩

omit [FiniteDimensional ℚ_[2] k] in
theorem sepRoot_sq (a : (↥k)ˣ) : sepRoot k a ^ 2 = kEmb k (a : k) :=
  Subtype.ext (by simp [sepRoot, kEmb])

theorem gq2KummerChar_eq (a : (↥k)ˣ) :
    gq2KummerChar k a =
      (TauCeti.galoisKummerCharacter (kEmb k) a (sepRoot k a) (sepRoot_sq k a)).comp
        (rho k : k.fixingSubgroup →* _) := by
  ext g
  simp only [gq2KummerChar, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply,
    toAdd_ofAdd]
  rw [TauCeti.toAdd_galoisKummerCharacter]
  have key : ((rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]) (sepRoot k a) :
      AlgebraicClosure ℚ_[2]) = (g : GQ2.Kummer.GaloisGroup ℚ_[2])
        (GQ2.sqrtCl ((a : k) : AlgebraicClosure ℚ_[2])) :=
    by rw [coe_rho_apply]; exact TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) _ _
  unfold GQ2.Kummer.kummerCocycleFun
  by_cases h : (g : GQ2.Kummer.GaloisGroup ℚ_[2]) (GQ2.sqrtCl ((a : k) : AlgebraicClosure ℚ_[2]))
      = GQ2.sqrtCl ((a : k) : AlgebraicClosure ℚ_[2])
  · rw [ite_eq_left (show _ • _ = _ from h)]
    exact (TauCeti.rootSign_of_apply_eq (r := sepRoot k a)
      (g := (rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2])) (Subtype.ext (key.trans h))).symm
  · rw [ite_eq_right (show ¬ (_ • _ = _) from h)]
    exact (TauCeti.rootSign_of_apply_ne (r := sepRoot k a)
      (g := (rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]))
      (fun h' ↦ h (key.symm.trans (congrArg Subtype.val h')))).symm

/-- The Tau Ceti side of B11a, transported to gq2's `G_k = ↥k.fixingSubgroup`. -/
theorem cup_gq2KummerChar_eq_zero_iff (a b : (↥k)ˣ) :
    letI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
    (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
        (TauCeti.ContCohomology.homClass _ (gq2KummerChar k a) (continuous_gq2KummerChar k a))
        (TauCeti.ContCohomology.homClass _ (gq2KummerChar k b) (continuous_gq2KummerChar k b))
        = 0 ↔
      ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 := by
  let _ : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  -- Φ n : H^n(G_k^{TC}) → H^n(G_k^{gq2}), an isomorphism
  let Φ : ∀ n, CategoryTheory.Iso
      (continuousCohomology n (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup k)))
      (continuousCohomology n (TauCeti.trivialF2 k.fixingSubgroup)) := fun n ↦
    (TauCeti.galoisF2Iso ℚ_[2] k (kEmb k) n).symm ≪≫ TauCeti.trivialF2Iso (rho k).symm n
  have hΦ : ∀ c : (↥k)ˣ, (Φ 1).hom (TauCeti.kummerClass c) =
      TauCeti.ContCohomology.homClass _ (gq2KummerChar k c) (continuous_gq2KummerChar k c) := by
    intro c
    simp only [Φ, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      TauCeti.trivialF2Iso_hom, ContinuousMulEquiv.symm_symm]
    rw [CategoryTheory.comp_apply, TauCeti.galoisF2Iso_inv_kummerClass (kEmb k) c (sepRoot k c)
      (sepRoot_sq k c), TauCeti.ContCohomology.trivialF2Map_homClass]
    refine (TauCeti.ContCohomology.homClass_inj _ _ _).2 ?_
    rw [gq2KummerChar_eq]
    rfl
  have hcup : (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
      ((Φ 1).hom (TauCeti.kummerClass a)) ((Φ 1).hom (TauCeti.kummerClass b)) =
      (Φ (1 + 1)).hom ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup k)).cup 1 1
        (TauCeti.kummerClass a) (TauCeti.kummerClass b)) := by
    simp only [Φ, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      TauCeti.trivialF2Iso_hom, CategoryTheory.comp_apply, TauCeti.galoisF2Iso_inv_cup,
      TauCeti.trivialF2Map_cup]
  rw [← hΦ a, ← hΦ b, hcup, ← TauCeti.cup_kummerClass_eq_zero_iff a b]
  constructor
  · intro h
    have h' := congrArg (Φ (1 + 1)).inv.hom h
    simpa using h'
  · intro h
    rw [h, map_zero]

end GaloisLaneProto
