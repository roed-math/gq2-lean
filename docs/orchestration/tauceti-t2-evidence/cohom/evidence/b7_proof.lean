module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import GQ2.Cohomology
public import GQ2.Statement

set_option linter.unusedSectionVars false
namespace Scratch
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

theorem H0_eq : GQ2.ContCoh.H0 G M = TauCeti.ContCohomology.H0 G M := rfl

theorem C1_eq : GQ2.ContCoh.C1 G M = TauCeti.ContCohomology.C1 G M := by
  ext f; rw [GQ2.ContCoh.mem_C1_iff, TauCeti.ContCohomology.mem_C1_iff]

theorem dZero_eq : GQ2.ContCoh.dZero G M = TauCeti.ContCohomology.d0 G M := by
  ext m g; simp [GQ2.ContCoh.dZero]

theorem dOne_eq : GQ2.ContCoh.dOne G M = TauCeti.ContCohomology.d1 G M := by
  ext f ⟨g, h⟩; simp [GQ2.ContCoh.dOne]

theorem dTwo_eq : GQ2.ContCoh.dTwo G M = TauCeti.ContCohomology.d2 G M := by
  ext f ⟨g, h, k⟩; simp [GQ2.ContCoh.dTwo]

theorem Z1_eq : GQ2.ContCoh.Z1 G M = TauCeti.ContCohomology.Z1 G M := by
  ext f
  rw [GQ2.ContCoh.mem_Z1_iff, TauCeti.ContCohomology.mem_Z1_iff]
  refine and_congr_right fun _ => forall₂_congr fun g h => ?_
  rw [add_comm (f g)]

theorem B1_eq : GQ2.ContCoh.B1 G M = TauCeti.ContCohomology.B1 G M := by
  ext f
  rw [TauCeti.ContCohomology.mem_B1_iff]
  simp [GQ2.ContCoh.B1, GQ2.ContCoh.dZero, groupCohomology.IsCoboundary₁, funext_iff]

theorem Z2_eq : GQ2.ContCoh.Z2 G M = TauCeti.ContCohomology.Z2 G M := by
  ext f
  rw [GQ2.ContCoh.mem_Z2_iff, TauCeti.ContCohomology.mem_Z2_iff]
  refine and_congr_right fun _ => forall₃_congr fun g h k => ?_
  exact ⟨fun H => (H).symm, fun H => H.symm⟩

theorem B2_eq : GQ2.ContCoh.B2 G M = TauCeti.ContCohomology.B2 G M := by
  ext f
  rw [GQ2.ContCoh.B2, TauCeti.ContCohomology.mem_B2_iff, AddSubgroup.mem_map, dOne_eq]
  simp only [GQ2.ContCoh.mem_C1_iff]

noncomputable def quotCongr {X : Type} [AddCommGroup X] {A A' B B' : AddSubgroup X}
    (hA : A = A') (hB : B = B') :
    (A ⧸ B.addSubgroupOf A) ≃+ (A' ⧸ B'.addSubgroupOf A') :=
  QuotientAddGroup.congr _ _ (AddEquiv.addSubgroupCongr hA) (by
    subst hA hB
    ext ⟨x, hx⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, he⟩
      obtain rfl : y.1 = x := congrArg Subtype.val he
      exact hy
    · intro h; exact ⟨⟨x, hx⟩, h, rfl⟩)

noncomputable def h1Equiv : GQ2.ContCoh.H1 G M ≃+ TauCeti.ContCohomology.H1 G M :=
  quotCongr (Z1_eq G M) (B1_eq G M)

noncomputable def h2Equiv : GQ2.ContCoh.H2 G M ≃+ TauCeti.ContCohomology.H2 G M :=
  quotCongr (Z2_eq G M) (B2_eq G M)

theorem h1Equiv_mk (z : GQ2.ContCoh.Z1 G M) :
    h1Equiv G M (GQ2.ContCoh.H1mk G M z) =
      TauCeti.ContCohomology.H1pi G M ⟨z.1, Z1_eq G M ▸ z.2⟩ := rfl
end Scratch

namespace ScratchB7
open GQ2 GQ2.ContCoh

variable (M : Type) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
      [Finite M]

theorem card_ne_zero : Nat.card M ≠ 0 := Nat.card_pos.ne'

@[instance_reducible] noncomputable def zmodMod : Module (ZMod (Nat.card M)) M :=
  haveI : NeZero (Nat.card M) := ⟨card_ne_zero M⟩
  AddCommGroup.zmodModule (fun _ => card_nsmul_eq_zero')

attribute [local instance] zmodMod

noncomputable def galRepOf : TauCeti.ClassFieldTheory.GalRep (Nat.card M) ℚ_[2] :=
  TauCeti.ofDiscreteModule (ZMod (Nat.card M)) (Field.absoluteGaloisGroup ℚ_[2]) M

instance : Finite (galRepOf M).V := inferInstanceAs (Finite M)

theorem galRepOf_smooth : TauCeti.IsSmoothDiscrete (ZMod (Nat.card M)) (galRepOf M) :=
  TauCeti.ofDiscreteModule_isSmoothDiscrete _ _ M

attribute [local instance] TopRep.distribMulAction

instance : DiscreteTopology (galRepOf M).V := inferInstanceAs (DiscreteTopology M)
instance : ContinuousSMul AbsGalQ2 (galRepOf M).V := inferInstanceAs (ContinuousSMul AbsGalQ2 M)

noncomputable def e0 : H0 AbsGalQ2 M ≃+ continuousCohomology 0 (galRepOf M) :=
  ((TauCeti.ContCohomology.explicitH0IsoContinuousCohomology AbsGalQ2
      (galRepOf M).V).toContinuousLinearEquiv.toAddEquiv).trans
    (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv (galRepOf M) 0)

noncomputable def e1 : H1 AbsGalQ2 M ≃+ continuousCohomology 1 (galRepOf M) :=
  (Scratch.h1Equiv AbsGalQ2 M).trans (galRepOf M).explicitH1AddEquivContinuousCohomologyOfDiscrete

noncomputable def e2 : H2 AbsGalQ2 M ≃+ continuousCohomology 2 (galRepOf M) :=
  (Scratch.h2Equiv AbsGalQ2 M).trans (galRepOf M).explicitH2AddEquivContinuousCohomologyOfDiscrete

attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in
theorem b7 :
      Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
        Nat.card (H1 AbsGalQ2 M) =
          Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) *
            2 ^ padicValNat 2 (Nat.card M) := by
  have hn : ((Nat.card M : ℕ) : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero M)
  have hA := galRepOf_smooth M
  haveI : Fact (TauCeti.IsSmoothDiscrete (ZMod (Nat.card M)) (galRepOf M)) := ⟨hA⟩
  have f0 := TauCeti.ClassFieldTheory.finite_H hn (galRepOf M) hA (i := 0) (by omega)
  have f1 := TauCeti.ClassFieldTheory.finite_H hn (galRepOf M) hA (i := 1) (by omega)
  have f2 := TauCeti.ClassFieldTheory.finite_H hn (galRepOf M) hA (i := 2) le_rfl
  have hE := TauCeti.ClassFieldTheory.eulerCharacteristic_mixed 2 ℚ_[2] (Nat.card M)
    (card_ne_zero M) (galRepOf M) inferInstance
  rw [Module.finrank_self, one_mul] at hE
  refine ⟨Finite.of_equiv _ (e0 M).toEquiv.symm, Finite.of_equiv _ (e1 M).toEquiv.symm,
    Finite.of_equiv _ (e2 M).toEquiv.symm, ?_⟩
  rw [Nat.card_congr (e0 M).toEquiv, Nat.card_congr (e1 M).toEquiv, Nat.card_congr (e2 M).toEquiv]
  exact hE

#print axioms b7
end ScratchB7
