module

public import TauCeti.NumberTheory.LocalField.ProP.RatPadic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Orientation
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation
public import GQ2.Orientation
public import GQ2.Prop32


theorem isProP_iff' (p : ℕ) (P : Type*) [Group P] [TopologicalSpace P] :
    GQ2.IsProP p P ↔ TauCeti.IsProP p P := by
  rw [TauCeti.isProP_iff]; rfl

theorem isProP_D0 : TauCeti.IsProP 2 GQ2.D0 :=
  (isProP_iff' 2 _).mp GQ2.isProP_maxProPQuotient

noncomputable def toGQ2D0 : TauCeti.demushkinD0 →ₜ* GQ2.D0 :=
  TauCeti.d0Lift isProP_D0 GQ2.d0A GQ2.d0S GQ2.d0Y GQ2.d0_relation

theorem toGQ2D0_d0A : toGQ2D0 TauCeti.d0A = GQ2.d0A := TauCeti.d0Lift_d0A _ _ _ _ _
theorem toGQ2D0_d0S : toGQ2D0 TauCeti.d0S = GQ2.d0S := TauCeti.d0Lift_d0S _ _ _ _ _
theorem toGQ2D0_d0Y : toGQ2D0 TauCeti.d0Y = GQ2.d0Y := TauCeti.d0Lift_d0Y _ _ _ _ _

/-- The free-profinite map `F(Fin 3) → D₀(TC)`, `A,S,Y ↦ A,S,Y`. -/
noncomputable def freeToTC :
    GQ2.FreeProfiniteGroup (Fin 3) ⟶ ProfiniteGrp.of TauCeti.demushkinD0 :=
  (GQ2.FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of TauCeti.demushkinD0)).symm
    ![TauCeti.d0A, TauCeti.d0S, TauCeti.d0Y]

theorem freeToTC_of (i : Fin 3) :
    freeToTC.hom.toMonoidHom (GQ2.FreeProfiniteGroup.of i) =
      ![TauCeti.d0A, TauCeti.d0S, TauCeti.d0Y] i :=
  GQ2.FreeProfiniteGroup.homEquiv_symm_of _ _ i

theorem freeToTC_relator : freeToTC.hom.toMonoidHom GQ2.d0Relator = 1 := by
  rw [GQ2.d0Relator]
  simp only [GQ2.commP, map_mul, map_pow, map_inv]
  rw [freeToTC_of 0, freeToTC_of 1, freeToTC_of 2]
  exact TauCeti.d0_relation

noncomputable def ofGQ2D0 : GQ2.D0 →ₜ* TauCeti.demushkinD0 :=
  GQ2.quotientLift (GQ2.proPKernel 2 GQ2.D0Full)
    (GQ2.presentationLift {GQ2.d0Relator} freeToTC.hom
      (fun r hr => by rcases hr with rfl; exact freeToTC_relator))
    (GQ2.proPKernel_le_ker ((isProP_iff' 2 _).mpr TauCeti.isProP_demushkinD0) _)

theorem ofGQ2D0_d0A : ofGQ2D0 GQ2.d0A = TauCeti.d0A := freeToTC_of 0
theorem ofGQ2D0_d0S : ofGQ2D0 GQ2.d0S = TauCeti.d0S := freeToTC_of 1
theorem ofGQ2D0_d0Y : ofGQ2D0 GQ2.d0Y = TauCeti.d0Y := freeToTC_of 2

theorem of_to : ofGQ2D0.comp toGQ2D0 = ContinuousMonoidHom.id _ :=
  TauCeti.d0_hom_ext
    (show ofGQ2D0 (toGQ2D0 TauCeti.d0A) = TauCeti.d0A by rw [toGQ2D0_d0A, ofGQ2D0_d0A])
    (show ofGQ2D0 (toGQ2D0 TauCeti.d0S) = TauCeti.d0S by rw [toGQ2D0_d0S, ofGQ2D0_d0S])
    (show ofGQ2D0 (toGQ2D0 TauCeti.d0Y) = TauCeti.d0Y by rw [toGQ2D0_d0Y, ofGQ2D0_d0Y])

/-- The evaluation `F₃ → D₀`, `A ↦ A, S ↦ S, Y ↦ Y` (copy of the non-module
`GQ2.SectionThree.evalD0`). -/
noncomputable def evalD0' : ContinuousMonoidHom (GQ2.FreeProfiniteGroup (Fin 3)) GQ2.D0 :=
  (GQ2.maxProPMk 2 GQ2.D0Full).comp (GQ2.quotientMk (GQ2.relatorSubgroup {GQ2.d0Relator}))

/-- Copy of the non-module `GQ2.SectionThree.topGen_d0`. -/
theorem topGen_d0' :
    (Subgroup.closure {GQ2.d0A, GQ2.d0S, GQ2.d0Y}).topologicalClosure = ⊤ := by
  have h := GQ2.SectionThree.topGen_map (f := evalD0'.toMonoidHom) evalD0'.continuous_toFun
    ((GQ2.quotientMk_surjective _).comp (GQ2.quotientMk_surjective _))
    (GQ2.SectionThree.topGen_freeProfiniteGroup (Fin 3))
  have h1 : (⇑evalD0'.toMonoidHom) '' Set.range (GQ2.FreeProfiniteGroup.of (X := Fin 3))
      = {GQ2.d0A, GQ2.d0S, GQ2.d0Y} := by
    rw [← Set.range_comp]
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  rwa [h1] at h

theorem to_of (x : GQ2.D0) : toGQ2D0 (ofGQ2D0 x) = x :=
  GQ2.SectionThree.monoidHom_eq_of_topGen
    (f := toGQ2D0.toMonoidHom.comp ofGQ2D0.toMonoidHom) (g := MonoidHom.id GQ2.D0)
    (toGQ2D0.continuous.comp ofGQ2D0.continuous) continuous_id topGen_d0'
    (by
      rintro z (rfl | rfl | rfl)
      · exact (congrArg toGQ2D0 ofGQ2D0_d0A).trans toGQ2D0_d0A
      · exact (congrArg toGQ2D0 ofGQ2D0_d0S).trans toGQ2D0_d0S
      · exact (congrArg toGQ2D0 ofGQ2D0_d0Y).trans toGQ2D0_d0Y) x

noncomputable def d0Equiv : TauCeti.demushkinD0 ≃ₜ* GQ2.D0 where
  toFun := toGQ2D0
  invFun := ofGQ2D0
  left_inv x := DFunLike.congr_fun of_to x
  right_inv := to_of
  map_mul' := map_mul toGQ2D0
  continuous_toFun := toGQ2D0.continuous
  continuous_invFun := ofGQ2D0.continuous

theorem d0Equiv_d0A : d0Equiv TauCeti.d0A = GQ2.d0A := toGQ2D0_d0A
theorem d0Equiv_d0S : d0Equiv TauCeti.d0S = GQ2.d0S := toGQ2D0_d0S
theorem d0Equiv_d0Y : d0Equiv TauCeti.d0Y = GQ2.d0Y := toGQ2D0_d0Y

theorem proPKernel_eq (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

section
variable [CompactSpace GQ2.AbsGalQ2] [TotallyDisconnectedSpace GQ2.AbsGalQ2]

noncomputable def galEquiv :
    GQ2.maxProPQuotient 2 GQ2.AbsGalQ2 ≃ₜ* TauCeti.absoluteGaloisGroupProP 2 ℚ_[2] where
  toMulEquiv := QuotientGroup.quotientMulEquivOfEq (proPKernel_eq 2 GQ2.AbsGalQ2)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk (GQ2.proPKernel 2 GQ2.AbsGalQ2)).continuous_iff.mpr ?_
    exact QuotientGroup.continuous_mk
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk (TauCeti.proPKernel 2 GQ2.AbsGalQ2)).continuous_iff.mpr ?_
    exact QuotientGroup.continuous_mk

theorem galEquiv_mk (g : GQ2.AbsGalQ2) :
    galEquiv (GQ2.maxProPMk 2 GQ2.AbsGalQ2 g) = (QuotientGroup.mk g : TauCeti.absoluteGaloisGroupProP 2 ℚ_[2]) :=
  rfl

/-- `chiTwo` as the transported cyclotomic orientation. -/
noncomputable def chiTwoTC : GQ2.maxProPQuotient 2 GQ2.AbsGalQ2 →* ℤ_[2]ˣ :=
  ((TauCeti.cyclotomicOrientation 2 ℚ_[2] TauCeti.ratPadicTwo_hasPrimitiveRoot).comp
    (galEquiv : GQ2.maxProPQuotient 2 GQ2.AbsGalQ2 →ₜ* TauCeti.absoluteGaloisGroupProP 2 ℚ_[2])).toMonoidHom

theorem chiTwoTC_factors (g : GQ2.AbsGalQ2) :
    chiTwoTC (GQ2.maxProPMk 2 GQ2.AbsGalQ2 g) = GQ2.chiCyc g := by
  show TauCeti.cyclotomicOrientation 2 ℚ_[2] _ (galEquiv (GQ2.maxProPMk 2 GQ2.AbsGalQ2 g)) = _
  rw [galEquiv_mk, TauCeti.cyclotomicOrientation_mk]
  exact TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] g

/-- Assembly of `DyadicOrientation` from a generator-compatible `ι : demushkinD0 ≃ₜ* GQ2.D0`
(to be supplied by P1 / the B3c adapter). -/
noncomputable def dyadicOrientationOf (ι : TauCeti.demushkinD0 ≃ₜ* GQ2.D0)
    (hA : ι TauCeti.d0A = GQ2.d0A) (hS : ι TauCeti.d0S = GQ2.d0S) (hY : ι TauCeti.d0Y = GQ2.d0Y) :
    GQ2.DyadicOrientation :=
  let h := TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked
  let e := Classical.choose h
  have he := Classical.choose_spec h
  -- cyc x = standard (e x)
  have hval : ∀ x, TauCeti.cyclotomicOrientation 2 ℚ_[2] TauCeti.ratPadicTwo_hasPrimitiveRoot x =
      TauCeti.standardD0Orientation (e x) := fun x => by
    rw [← he.1]; rfl
  have hsymm : ∀ (a : TauCeti.demushkinD0) (b : GQ2.D0), ι a = b →
      chiTwoTC (((galEquiv.trans e).trans ι).symm b) = TauCeti.standardD0Orientation a := by
    rintro a b rfl
    show TauCeti.cyclotomicOrientation 2 ℚ_[2] _ (galEquiv (galEquiv.symm (e.symm (ι.symm (ι a))))) = _
    rw [hval]; simp
  { equiv := (galEquiv.trans e).trans ι
    chiTwo := chiTwoTC
    continuous_chiTwo := by
      show Continuous fun x => TauCeti.cyclotomicOrientation 2 ℚ_[2]
        TauCeti.ratPadicTwo_hasPrimitiveRoot (galEquiv x)
      exact (map_continuous _).comp (map_continuous galEquiv)
    chiTwo_factors := chiTwoTC_factors
    surjective_chiTwo := he.2.comp galEquiv.surjective
    chi_A := by rw [hsymm _ _ hA, TauCeti.standardD0Orientation_d0A]
    chi_S := by rw [hsymm _ _ hS, TauCeti.standardD0Orientation_d0S]
    chi_Y := fun y hy => by
      rw [hsymm _ _ hY, TauCeti.standardD0Orientation_d0Y]
      congr 1
      exact (Units.ext (by rw [hy, TauCeti.negThreeUnit_coe])).symm }

end

section
variable [CompactSpace GQ2.AbsGalQ2] [TotallyDisconnectedSpace GQ2.AbsGalQ2]
noncomputable def dyadicOrientation_tauceti : GQ2.DyadicOrientation :=
  dyadicOrientationOf d0Equiv d0Equiv_d0A d0Equiv_d0S d0Equiv_d0Y
end

noncomputable def dyadicOrientation_tauceti' : GQ2.DyadicOrientation :=
  dyadicOrientation_tauceti

#print axioms dyadicOrientation_tauceti
#print axioms dyadicOrientation_tauceti'

-- the exact shape of the `LiteratureInputs.dyadicOrientation` field
noncomputable example : ∀ [CompactSpace GQ2.AbsGalQ2] [TotallyDisconnectedSpace GQ2.AbsGalQ2],
    GQ2.DyadicOrientation := @dyadicOrientation_tauceti
