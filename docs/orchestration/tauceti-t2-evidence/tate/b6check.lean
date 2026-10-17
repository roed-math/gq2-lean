module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Topology.Instances.ZMod
public import GQ2.TateDuality

/-! Q4 check: from `IsLocalDualizingGroup G n` to a finite `K/ℚ₂` and
`G ≃ₜ* Field.absoluteGaloisGroup K`. -/

open IntermediateField

namespace T2Tate

local notation "Qbar" => AlgebraicClosure ℚ_[2]

/- With Tau Ceti's Brauer/Duality modules imported, the default searches for these three time out
at 20000 heartbeats (they wander into `Module.Finite ℚ_[2] ℚ̄₂` via
`TauCeti.FinitePadicExtension.toModuleFinite`); pinning them as local instances fixes it. -/
local instance instTF : Module.IsTorsionFree ℚ_[2] Qbar := DivisionSemiring.to_moduleIsTorsionFree
local instance instAC : IsAlgClosure ℚ_[2] Qbar := AlgebraicClosure.instIsAlgClosure ℚ_[2]
local instance instGal : IsGalois ℚ_[2] Qbar := IsAlgClosure.isGalois _ _

example : IsGalois ℚ_[2] Qbar := inferInstance

/-- The image of an open embedding is an open subgroup. -/
theorem isOpen_range {G : Type} [Group G] [TopologicalSpace G] (ι : G →* GQ2.AbsGalQ2)
    (hι : Topology.IsOpenEmbedding ι) : IsOpen (ι.range : Set GQ2.AbsGalQ2) := by
  rw [MonoidHom.coe_range]
  exact hι.isOpen_range

/-- The fixed field of the image. -/
noncomputable def fixedK {G : Type} [Group G] (ι : G →* GQ2.AbsGalQ2) :
    IntermediateField ℚ_[2] Qbar :=
  fixedField (ι.range : Subgroup (Qbar ≃ₐ[ℚ_[2]] Qbar))

/-- Krull: an open (hence closed) subgroup is the fixing subgroup of its fixed field. -/
theorem fixingSubgroup_fixedK {G : Type} [Group G] [TopologicalSpace G] (ι : G →* GQ2.AbsGalQ2)
    (hι : Topology.IsOpenEmbedding ι) :
    (fixedK ι).fixingSubgroup = (ι.range : Subgroup (Qbar ≃ₐ[ℚ_[2]] Qbar)) :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨ι.range, Subgroup.isClosed_of_isOpen _ (isOpen_range ι hι)⟩

/-- Its fixed field is finite over `ℚ₂` (`InfiniteGalois.isOpen_iff_finite`). -/
theorem finiteDimensional_fixedK {G : Type} [Group G] [TopologicalSpace G]
    (ι : G →* GQ2.AbsGalQ2) (hι : Topology.IsOpenEmbedding ι) :
    FiniteDimensional ℚ_[2] (fixedK ι) := by
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_fixedK ι hι]
  exact isOpen_range ι hι

/-- Alternative: the degree is the index (`IntermediateField.finrank_eq_fixingSubgroup_index`). -/
theorem finrank_fixedK {G : Type} [Group G] [TopologicalSpace G]
    (ι : G →* GQ2.AbsGalQ2) (hι : Topology.IsOpenEmbedding ι) :
    Module.finrank ℚ_[2] (fixedK ι) = ι.range.index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedK ι hι]
  rfl

/-- The inclusion of an intermediate field of `ℚ̄₂` into the separable closure (char 0). -/
noncomputable def sepEmb (E : IntermediateField ℚ_[2] Qbar) : E →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] :=
  IntermediateField.inclusion fun x _ ↦
    (mem_separableClosure_iff (F := ℚ_[2])).2 (Algebra.IsSeparable.isSeparable ℚ_[2] x)

/-- **General form of `range_absoluteGaloisGroupExtend_shapiroFieldEmbedding`**: for any finite
intermediate field `E` of `ℚ̄₂/ℚ₂`, the image of `G_E` in `G_ℚ₂` is `E.fixingSubgroup`. Same proof
as Tau Ceti's Shapiro lemma, with `fixingSubgroup_shapiroField` dropped. -/
theorem range_absoluteGaloisGroupExtend_sepEmb (E : IntermediateField ℚ_[2] Qbar)
    [FiniteDimensional ℚ_[2] E] :
    (TauCeti.absoluteGaloisGroupExtend ℚ_[2] E (sepEmb E)).range = E.fixingSubgroup := by
  ext g
  rw [TauCeti.mem_range_absoluteGaloisGroupExtend_iff, TauCeti.mem_galoisSubgroup_iff]
  refine ⟨fun h ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_,
    fun h x ↦ Subtype.ext ?_⟩
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).symm.trans
      (congrArg Subtype.val (h ⟨x, hx⟩))
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 h x x.2)

/-- **The B6 reconstruction**: from the data of `IsLocalDualizingGroup G n`, a finite `K/ℚ₂` and
`e : G ≃ₜ* Field.absoluteGaloisGroup K` with `absoluteGaloisGroupExtend (e g) = ι g`. -/
theorem exists_absoluteGaloisGroup_equiv {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}
    [NeZero n] [DistribMulAction G (GQ2.MuN n)] (hloc : GQ2.IsLocalDualizingGroup G n) :
    ∃ (K : IntermediateField ℚ_[2] Qbar) (_ : FiniteDimensional ℚ_[2] K)
      (ι : G →* GQ2.AbsGalQ2) (e : G ≃ₜ* Field.absoluteGaloisGroup K),
      (ι.range : Subgroup (Qbar ≃ₐ[ℚ_[2]] Qbar)) = K.fixingSubgroup ∧
      (∀ g, TauCeti.absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) (e g) = ι g) ∧
      ∀ (g : G) (x : GQ2.MuN n), g • x = ι g • x := by
  obtain ⟨ι, hι, -, hμ⟩ := hloc
  have := finiteDimensional_fixedK ι hι
  have hU : (TauCeti.absoluteGaloisGroupExtend ℚ_[2] (fixedK ι) (sepEmb (fixedK ι))).range =
      ι.range :=
    (range_absoluteGaloisGroupExtend_sepEmb (fixedK ι)).trans (fixingSubgroup_fixedK ι hι)
  let f : G →ₜ* GQ2.AbsGalQ2 := ⟨ι, hι.continuous⟩
  refine ⟨fixedK ι, inferInstance, ι,
    (f.equivRangeOfIsEmbedding hι.isEmbedding).trans
      (TauCeti.absoluteGaloisGroupExtendEquiv ℚ_[2] (fixedK ι) (sepEmb (fixedK ι)) hU).symm,
    (fixingSubgroup_fixedK ι hι).symm, fun g ↦ ?_, hμ⟩
  rw [ContinuousMulEquiv.trans_apply,
    ← TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply ℚ_[2] (fixedK ι) (sepEmb (fixedK ι)) hU,
    ContinuousMulEquiv.apply_symm_apply]
  exact congrArg Subtype.val (ContinuousMonoidHom.equivRangeOfIsEmbedding_apply f _ g)


/-! ### Applying the Tau Ceti theorem at a finite `K` (instance package test) -/

section Apply

variable (K : IntermediateField ℚ_[2] Qbar) [FiniteDimensional ℚ_[2] K]

example : CharZero K := inferInstance

/-- `tateDualityPairing_perfect_mixed` at a finite `K ⊆ ℚ̄₂`, for `A` built from a finite
discrete `n`-torsion `G_K`-module `M : Type`. -/
example (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [Finite M] [DistribMulAction (Field.absoluteGaloisGroup K) M]
    [ContinuousSMul (Field.absoluteGaloisGroup K) M] (htor : ∀ x : M, n • x = 0) : True := by
  let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[2] Qbar K
  let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[2] Qbar K
  have hLF := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[2] Qbar K
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule htor
  let A : TauCeti.ClassFieldTheory.GalRep n K :=
    TauCeti.ofDiscreteModule (ZMod n) (Field.absoluteGaloisGroup K) M
  have : Fact (TauCeti.IsSmoothDiscrete (ZMod n) A) :=
    ⟨TauCeti.ofDiscreteModule_isSmoothDiscrete (ZMod n) _ M⟩
  have hD : DiscreteTopology A.V := inferInstanceAs (DiscreteTopology M)
  have hA : Finite A.V := inferInstanceAs (Finite M)
  obtain ⟨tr⟩ := TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed K n (NeZero.ne n)
  -- With `A` a `let`, `[DiscreteTopology ↑A]` is "stuck" unless passed explicitly (`@`); with `A` a
  -- bound variable or a `def` it is found by instance search.
  have h02 := @TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed (↥K) _ _ _ _ hLF n
    (NeZero.ne n) A tr hA hD _ 0 2 rfl
  have h11 := @TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed (↥K) _ _ _ _ hLF n
    (NeZero.ne n) A tr hA hD _ 1 1 rfl
  have h20 := @TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed (↥K) _ _ _ _ hLF n
    (NeZero.ne n) A tr hA hD _ 2 0 rfl
  trivial

/-- Bijectivity of `x ↦ (y ↦ ⟨x, y⟩)` from the two conjuncts (Q3: no counting needed). -/
theorem bijective_of_perfect {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (Φ : X →+ Y →+ ZMod n)
    (h : (∀ x, (∀ y, Φ x y = 0) → x = 0) ∧ ∀ φ : Y →+ ZMod n, ∃ x, ∀ y, Φ x y = φ y) :
    Function.Bijective Φ :=
  ⟨(injective_iff_map_eq_zero Φ).2 fun x hx ↦ h.1 x fun y ↦ DFunLike.congr_fun hx y,
    fun φ ↦ (h.2 φ).imp fun _ hx ↦ AddMonoidHom.ext hx⟩

end Apply

#check @TauCeti.kummerCoeffMap
#check @TauCeti.kummerCoeffMap_smul
#check @TauCeti.absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend
#check @TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply
#check @TauCeti.ofDiscreteModule_isSmoothDiscrete
#check @AddCommGroup.zmodModule

#print axioms exists_absoluteGaloisGroup_equiv
#print axioms bijective_of_perfect

end T2Tate
