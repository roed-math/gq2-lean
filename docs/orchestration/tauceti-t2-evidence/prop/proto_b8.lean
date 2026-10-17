module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic
public import GQ2.PeripheralAction
public import GQ2.ProfinitePresentation
public import GQ2.AppendixB

universe u

namespace Scratch

open Multiplicative


-- (1) carriers / objects
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := rfl
example (X : Type u) : (GQ2.FreeProfiniteGroup X : Type u) = (TauCeti.freeProfiniteGroup X : Type u) := rfl

theorem of_eq {X : Type u} (x : X) : GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := by
  rw [← TauCeti.freeProfiniteGroup.fromFreeGroup_of, TauCeti.freeProfiniteGroup.coe_fromFreeGroup]
  rfl

-- (2) IsProP, proPKernel
theorem isProP_iff (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] :
    GQ2.IsProP p G ↔ TauCeti.IsProP p G := TauCeti.isProP_iff.symm

theorem proPKernel_eq (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

noncomputable def maxProPEquiv (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    GQ2.maxProPQuotient p G ≃ₜ* TauCeti.maximalProPQuotient p G :=
  (ContinuousMulEquiv.refl G).quotientCongr (GQ2.proPKernel p G) (TauCeti.proPKernel p G)
    (by rw [proPKernel_eq]; exact Subgroup.map_id _)

theorem maxProPEquiv_mk (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (g : G) :
    maxProPEquiv p G (GQ2.maxProPMk p G g) = TauCeti.maximalProPQuotient.mk p G g :=
  ContinuousMulEquiv.quotientCongr_mk _ _ _ _ g

-- Delta
example : (TauCeti.maximalProPQuotient 2 (GQ2.FreeProfiniteGroup (Fin 2))) = TauCeti.freeProP 2 (Fin 2) := rfl

noncomputable def deltaEquiv : GQ2.Delta ≃ₜ* TauCeti.freeProP 2 (Fin 2) :=
  maxProPEquiv 2 (GQ2.FreeProfiniteGroup (Fin 2))

theorem deltaEquiv_deltaP : deltaEquiv GQ2.deltaP = TauCeti.freeProP.of 0 := by
  rw [← TauCeti.freeProP.fromFreeProfiniteGroup_of, TauCeti.freeProP.fromFreeProfiniteGroup_apply,
    ← of_eq]
  exact maxProPEquiv_mk 2 _ _

theorem deltaEquiv_deltaT : deltaEquiv GQ2.deltaT = TauCeti.freeProP.of 1 := by
  rw [← TauCeti.freeProP.fromFreeProfiniteGroup_of, TauCeti.freeProP.fromFreeProfiniteGroup_apply,
    ← of_eq]
  exact maxProPEquiv_mk 2 _ _

-- presentation carrier
example {X : Type u} (rels : Set (GQ2.FreeProfiniteGroup X)) :
    (GQ2.profinitePresentation rels : Type u) = TauCeti.presentedProfiniteGroup X rels := rfl

-- instance checks on Delta
#synth IsTopologicalGroup GQ2.Delta
#synth CompactSpace GQ2.Delta
#synth TotallyDisconnectedSpace GQ2.Delta
#synth T2Space GQ2.Delta
#synth Fact (Nat.Prime 2)

theorem isProP_delta : TauCeti.IsProP 2 GQ2.Delta :=
  (isProP_iff 2 _).1 GQ2.isProP_maxProPQuotient

-- zpowZtwo = padicPow
theorem zpowZtwo_eq_padicPow {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : GQ2.IsProP 2 P) (x : P)
    (u : ℤ_[2]) : GQ2.zpowZtwo hP x u = ((isProP_iff 2 P).1 hP).padicPow x u :=
  TauCeti.IsProP.eq_padicPow_of_continuous _ (GQ2.continuous_zpowZtwo hP x)
    (GQ2.zpowZtwo_natCast hP x) u



open Multiplicative

/-- forward: `γ ↦ gen ^ᶻ γ`. -/
noncomputable def zhatFwd : GQ2.Zhat →ₜ* TauCeti.zHat.{0} :=
  (GQ2.zpowHatHom (G := TauCeti.zHat.{0}) TauCeti.zHat.gen).hom

noncomputable def zhatBwd : TauCeti.zHat.{0} →ₜ* GQ2.Zhat :=
  TauCeti.zHat.lift (GQ2.Zhat.ofInt 1)

theorem zhatFwd_ofInt (n : ℤ) : zhatFwd (GQ2.Zhat.ofInt n) = TauCeti.zHat.ofInt (ofAdd n) := by
  rw [TauCeti.zHat.ofInt_ofAdd]
  exact GQ2.zpowHat_ofInt (G := TauCeti.zHat.{0}) TauCeti.zHat.gen n

theorem zhatBwd_gen : zhatBwd TauCeti.zHat.gen = GQ2.Zhat.ofInt 1 := TauCeti.zHat.lift_gen _

noncomputable def zhatEquiv : GQ2.Zhat ≃ₜ* TauCeti.zHat.{0} where
  toFun := zhatFwd
  invFun := zhatBwd
  left_inv γ := by
    have h := GQ2.Zhat.funext_ofInt (f := fun γ => zhatBwd (zhatFwd γ)) (g := id)
      (zhatBwd.continuous.comp zhatFwd.continuous) continuous_id (fun n => by
        simp only [id, zhatFwd_ofInt, TauCeti.zHat.ofInt_ofAdd, map_zpow, zhatBwd_gen,
          GQ2.Zhat.ofInt_one_zpow])
    exact congrFun h γ
  right_inv x := by
    have h : zhatFwd.comp zhatBwd = ContinuousMonoidHom.id _ := by
      refine TauCeti.zHat.hom_ext ?_
      simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.id_toFun]
      rw [zhatBwd_gen, zhatFwd_ofInt, TauCeti.zHat.ofInt_ofAdd, zpow_one]
    exact DFunLike.congr_fun h x
  map_mul' := map_mul zhatFwd
  continuous_toFun := zhatFwd.continuous
  continuous_invFun := zhatBwd.continuous

theorem zhatEquiv_ofInt (n : ℤ) :
    zhatEquiv (GQ2.Zhat.ofInt n) = TauCeti.zHat.ofInt (ofAdd n) := zhatFwd_ofInt n

theorem zhatProjTwo_eq_component (γ : GQ2.Zhat) :
    GQ2.zhatProjTwo γ = ofAdd (TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ))) := by
  have h := GQ2.Zhat.funext_ofInt (f := fun γ => GQ2.zhatProjTwo γ)
    (g := fun γ => ofAdd (TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ))))
    GQ2.zhatProjTwo.continuous
    (continuous_ofAdd.comp ((TauCeti.zHat.continuous_component 2).comp
      (continuous_ofMul.comp zhatEquiv.continuous))) (fun n => by
        simp only [zhatEquiv_ofInt, TauCeti.zHat.ofMul_ofInt, map_intCast, toAdd_ofAdd]
        show GQ2.zpowHat (ofAdd (1 : ℤ_[2])) (GQ2.Zhat.ofInt n) = _
        rw [GQ2.zpowHat_ofInt, ← ofAdd_zsmul, zsmul_eq_mul, mul_one])
  exact congrFun h γ


/-! ## B8 seams -/

open scoped GQ2 in
/-- local copy of `GQ2.zpowHat_omega2_eq_self` (`GQ2/AnabelianBridge/Construction.lean:74`, a
non-`module` file, so not importable from a `module` adapter). -/
theorem zpowHat_omega2_eq_self {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : GQ2.IsProP 2 P) (x : P) : x ^ᶻ GQ2.omega2 = x := by
  have hmem : ∀ U : OpenNormalSubgroup P, (x ^ᶻ GQ2.omega2) * x⁻¹ ∈ U := by
    intro U
    have : DiscreteTopology (P ⧸ U.toSubgroup) := by
      refine discreteTopology_of_isOpen_singleton_one ?_
      have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1}
          = (U.toSubgroup : Set P) := by
        ext δ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          QuotientGroup.eq_one_iff]
      rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
      exact U.isOpen'
    have : Finite (P ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
    have hω := GQ2.map_zpowHat_omega2 (P := P ⧸ U.toSubgroup)
      { toMonoidHom := QuotientGroup.mk' U.toSubgroup
        continuous_toFun := continuous_quot_mk } x
    have hω' : QuotientGroup.mk' U.toSubgroup (x ^ᶻ GQ2.omega2)
        = GQ2.powOmega2 (QuotientGroup.mk' U.toSubgroup x) := hω
    obtain ⟨k, hk⟩ := (hP U) (QuotientGroup.mk' U.toSubgroup x)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hself : GQ2.powOmega2 (QuotientGroup.mk' U.toSubgroup x)
        = QuotientGroup.mk' U.toSubgroup x := GQ2.powOmega2_eq_self_of_orderOf_two_pow hj
    have hone : QuotientGroup.mk' U.toSubgroup ((x ^ᶻ GQ2.omega2) * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hω', hself, mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
  have hprod := GQ2.eq_one_of_forall_mem_openNormalSubgroup hmem
  rwa [mul_inv_eq_one] at hprod

theorem zhatProjTwo_omega2 : GQ2.zhatProjTwo GQ2.omega2 = ofAdd (1 : ℤ_[2]) :=
  zpowHat_omega2_eq_self GQ2.PropOneOne.isProP_two_multPadicInt (ofAdd (1 : ℤ_[2]))

theorem component_two_omega2 :
    TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv GQ2.omega2)) = 1 := by
  have h := zhatProjTwo_omega2
  rw [zhatProjTwo_eq_component] at h
  exact ofAdd.injective h

/-- `2 ↦ v`, other primes `↦ 0`. -/
noncomputable def single2 (v : ℤ_[2]) : ∀ ℓ : Nat.Primes, ℤ_[(ℓ : ℕ)] :=
  Pi.single (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) (⟨2, Nat.prime_two⟩ : Nat.Primes) v

theorem single2_two (v : ℤ_[2]) : single2 v ⟨2, Nat.prime_two⟩ = v :=
  Pi.single_eq_same (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) _ _

theorem single2_zero : single2 0 = 0 :=
  Pi.single_zero (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) _

theorem continuous_single2 : Continuous single2 := by
  unfold single2
  exact continuous_single (A := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) (⟨2, Nat.prime_two⟩ : Nat.Primes)

/-- a continuous map with `2`-component `u` and value `1` at `u = 1`. -/
noncomputable def sec (u : ℤ_[2]) : Additive TauCeti.zHat.{0} :=
  TauCeti.zHat.ringEquivPiPadicInt.symm (single2 (u - 1)) + 1

theorem component_sec (u : ℤ_[2]) : TauCeti.zHat.component 2 (sec u) = u := by
  have h := TauCeti.zHat.component_ringEquivPiPadicInt_symm (single2 (u - 1)) ⟨2, Nat.prime_two⟩
  rw [single2_two] at h
  rw [sec, map_add, map_one]
  erw [h]
  ring

theorem sec_one : sec 1 = 1 := by
  rw [sec, sub_self, single2_zero, map_zero, zero_add]

noncomputable def iota (u : ℤ_[2]ˣ) : GQ2.Zhat :=
  zhatEquiv.symm (Additive.toMul (Additive.ofMul (zhatEquiv GQ2.omega2) * sec (u : ℤ_[2])))

theorem iota_one : iota 1 = GQ2.omega2 := by
  simp [iota, sec_one]

theorem iota_proj (u : ℤ_[2]ˣ) : GQ2.zhatProjTwo (iota u) = ofAdd (u : ℤ_[2]) := by
  rw [zhatProjTwo_eq_component, iota, ContinuousMulEquiv.apply_symm_apply, ofMul_toMul, map_mul,
    component_two_omega2, component_sec, one_mul]

theorem continuous_iota : Continuous iota := by
  unfold iota sec
  refine zhatEquiv.symm.continuous.comp (continuous_toMul.comp (continuous_const.mul ?_))
  refine (TauCeti.zHat.continuous_ringEquivPiPadicInt_symm.comp ?_).add continuous_const
  exact continuous_single2.comp (Units.continuous_val.sub continuous_const)

theorem periphP_deltaEquiv : TauCeti.Peripheral.periphP deltaEquiv = GQ2.deltaP := by
  rw [TauCeti.Peripheral.periphP_eq_basis, TauCeti.Peripheral.basis_apply,
    ContinuousMulEquiv.symm_apply_eq, deltaEquiv_deltaP]

theorem periphT_deltaEquiv : TauCeti.Peripheral.periphT deltaEquiv = GQ2.deltaT := by
  rw [TauCeti.Peripheral.periphT_eq_basis, TauCeti.Peripheral.basis_apply,
    ContinuousMulEquiv.symm_apply_eq, deltaEquiv_deltaT]

theorem periphC_deltaEquiv : TauCeti.Peripheral.periphC deltaEquiv = GQ2.deltaC := by
  rw [TauCeti.Peripheral.periphC_def, periphP_deltaEquiv, periphT_deltaEquiv]; rfl

open scoped GQ2 in
theorem zpowHat_iota (x : GQ2.Delta) (u : ℤ_[2]ˣ) :
    x ^ᶻ iota u = isProP_delta.padicPow x (u : ℤ_[2]) := by
  rw [GQ2.zpowHat_eq_zpowZtwo GQ2.isProP_maxProPQuotient x (iota u), iota_proj, toAdd_ofAdd,
    zpowZtwo_eq_padicPow]

open scoped GQ2 in
theorem autSpec (u : ℤ_[2]ˣ) :
    ∃ (φ : ContinuousMulEquiv GQ2.Delta GQ2.Delta) (cP cT cC : GQ2.Delta),
      φ GQ2.deltaP = GQ2.conjP (GQ2.deltaP ^ᶻ iota u) cP ∧
      φ GQ2.deltaT = GQ2.conjP (GQ2.deltaT ^ᶻ iota u) cT ∧
      φ GQ2.deltaC = GQ2.conjP (GQ2.deltaC ^ᶻ iota u) cC := by
  obtain ⟨φ, cP, cT, cC, -, hP, hT, hC⟩ :=
    TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two isProP_delta deltaEquiv u
  rw [periphP_deltaEquiv] at hP
  rw [periphT_deltaEquiv] at hT
  rw [periphC_deltaEquiv] at hC
  exact ⟨φ, cP, cT, cC, by rw [hP, zpowHat_iota]; rfl, by rw [hT, zpowHat_iota]; rfl,
    by rw [hC, zpowHat_iota]; rfl⟩

noncomputable def b8 : GQ2.PeripheralCyclotomicAction where
  ι := iota
  hι_cont := continuous_iota
  hι_one := iota_one
  hι_proj := iota_proj
  aut u := (autSpec u).choose
  cP u := (autSpec u).choose_spec.choose
  cT u := (autSpec u).choose_spec.choose_spec.choose
  cC u := (autSpec u).choose_spec.choose_spec.choose_spec.choose
  hP u := (autSpec u).choose_spec.choose_spec.choose_spec.choose_spec.1
  hT u := (autSpec u).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  hC u := (autSpec u).choose_spec.choose_spec.choose_spec.choose_spec.2.2

end Scratch

#print axioms Scratch.b8
