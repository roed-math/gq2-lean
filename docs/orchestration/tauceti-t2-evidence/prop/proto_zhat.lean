module

public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import GQ2.ZtwoPowering

namespace Scratch

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

end Scratch

#print axioms Scratch.zhatEquiv
#print axioms Scratch.zhatProjTwo_eq_component
