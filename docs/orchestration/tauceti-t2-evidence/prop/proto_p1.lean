module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import GQ2.ProfinitePresentation
public import GQ2.MaxProP
public import GQ2.PeripheralAction
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import GQ2.DyadicPresentation
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic

universe u

namespace Scratch


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



section Gen
variable (p : ℕ) {X : Type u} (rels : Set (TauCeti.freeProfiniteGroup X))

local notation "Pres" => TauCeti.presentedProfiniteGroup X rels
local notation "Rels'" => (TauCeti.freeProP.fromFreeProfiniteGroup p X '' rels)

noncomputable def toProP : TauCeti.maximalProPQuotient p Pres →ₜ* TauCeti.presentedProP p X Rels' :=
  ⟨TauCeti.maximalProPQuotient.lift (TauCeti.presentedProP.isProP p X _)
      (TauCeti.presentedProfiniteGroup.toPresentedProP p rels).toMonoidHom
      (TauCeti.presentedProfiniteGroup.toPresentedProP p rels).continuous,
    TauCeti.maximalProPQuotient.continuous_lift _ _ _⟩

noncomputable def psi : TauCeti.freeProP p X →ₜ* TauCeti.maximalProPQuotient p Pres :=
  ⟨TauCeti.maximalProPQuotient.lift TauCeti.isProP_maximalProPQuotient
      ((TauCeti.maximalProPQuotient.mk p Pres).comp
        (TauCeti.presentedProfiniteGroup.mk rels).toMonoidHom)
      ((TauCeti.maximalProPQuotient.continuous_mk p _).comp
        (TauCeti.presentedProfiniteGroup.mk rels).continuous),
    TauCeti.maximalProPQuotient.continuous_lift _ _ _⟩

theorem psi_mk (x : TauCeti.freeProfiniteGroup X) :
    psi p rels (TauCeti.freeProP.fromFreeProfiniteGroup p X x) =
      TauCeti.maximalProPQuotient.mk p Pres (TauCeti.presentedProfiniteGroup.mk rels x) := by
  rw [TauCeti.freeProP.fromFreeProfiniteGroup_apply]
  exact TauCeti.maximalProPQuotient.lift_mk _ _ _ x

noncomputable def ofProP : TauCeti.presentedProP p X Rels' →ₜ* TauCeti.maximalProPQuotient p Pres :=
  TauCeti.presentedProP.lift (psi p rels) (by
    rintro _ ⟨r, hr, rfl⟩
    rw [psi_mk, TauCeti.presentedProfiniteGroup.mk_relator r hr, map_one])

theorem toProP_mk (x : TauCeti.freeProfiniteGroup X) :
    toProP p rels (TauCeti.maximalProPQuotient.mk p Pres (TauCeti.presentedProfiniteGroup.mk rels x)) =
      TauCeti.presentedProP.mk p Rels' (TauCeti.freeProP.fromFreeProfiniteGroup p X x) := by
  show TauCeti.maximalProPQuotient.lift _ _ _ (QuotientGroup.mk _) = _
  rw [TauCeti.maximalProPQuotient.lift_mk]
  exact TauCeti.presentedProfiniteGroup.toPresentedProP_mk p rels x

theorem ofProP_mk (x : TauCeti.freeProfiniteGroup X) :
    ofProP p rels (TauCeti.presentedProP.mk p Rels' (TauCeti.freeProP.fromFreeProfiniteGroup p X x)) =
      TauCeti.maximalProPQuotient.mk p Pres (TauCeti.presentedProfiniteGroup.mk rels x) := by
  rw [ofProP, TauCeti.presentedProP.lift_mk, psi_mk]

noncomputable def maxProPPresentedEquiv :
    TauCeti.maximalProPQuotient p Pres ≃ₜ* TauCeti.presentedProP p X Rels' where
  toFun := toProP p rels
  invFun := ofProP p rels
  left_inv y := by
    obtain ⟨z, rfl⟩ := TauCeti.maximalProPQuotient.mk_surjective p _ y
    obtain ⟨x, rfl⟩ := TauCeti.presentedProfiniteGroup.mk_surjective rels z
    rw [toProP_mk, ofProP_mk]
  right_inv y := by
    obtain ⟨z, rfl⟩ := TauCeti.presentedProP.mk_surjective p _ y
    obtain ⟨x, rfl⟩ := TauCeti.freeProP.fromFreeProfiniteGroup_surjective (p := p) (X := X) z
    rw [ofProP_mk, toProP_mk]
  map_mul' := map_mul (toProP p rels)
  continuous_toFun := (toProP p rels).continuous
  continuous_invFun := (ofProP p rels).continuous

end Gen

/-- the gq2 relator, read in Tau Ceti's free profinite group. -/
noncomputable abbrev d0RelatorT : TauCeti.freeProfiniteGroup (Fin 3) := GQ2.d0Relator

open TauCeti.freeProfiniteGroup in
theorem d0RelatorT_eq : d0RelatorT =
    (of 0 ^ 2 * of 1 ^ 4 * ((of 1)⁻¹ * (of 2)⁻¹ * of 1 * of 2) :
      TauCeti.freeProfiniteGroup (Fin 3)) := by
  simp only [d0RelatorT, GQ2.d0Relator, GQ2.commP, of_eq]
  rfl

theorem fromFree_d0Relator :
    TauCeti.freeProP.fromFreeProfiniteGroup 2 (Fin 3) d0RelatorT = TauCeti.d0Relator := by
  rw [TauCeti.d0Relator_def, d0RelatorT_eq]
  simp only [map_mul, map_pow, map_inv, TauCeti.freeProP.fromFreeProfiniteGroup_of]

theorem d0Relator_image :
    TauCeti.freeProP.fromFreeProfiniteGroup 2 (Fin 3) '' {d0RelatorT} = {TauCeti.d0Relator} := by
  rw [Set.image_singleton, fromFree_d0Relator]

noncomputable def d0Equiv : GQ2.D0 ≃ₜ* TauCeti.demushkinD0 :=
  ((maxProPEquiv 2 GQ2.D0Full).trans
    (maxProPPresentedEquiv 2 (X := Fin 3) {d0RelatorT})).trans
    (TauCeti.presentedProP.congrOfClosureEq (by rw [d0Relator_image]))

end Scratch

#print axioms Scratch.d0Equiv
#print axioms Scratch.maxProPPresentedEquiv
#print axioms Scratch.deltaEquiv_deltaP
#print axioms Scratch.zpowZtwo_eq_padicPow
