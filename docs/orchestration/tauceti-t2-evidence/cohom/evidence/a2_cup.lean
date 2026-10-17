module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import GQ2.Demushkin

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

namespace Scratch
section Cup
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
variable {P : Type} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
variable (μ : M →+ N →+ P) (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

theorem h2Equiv_cup11 (x : GQ2.ContCoh.H1 G M) (y : GQ2.ContCoh.H1 G N) :
    h2Equiv G P (GQ2.ContCoh.cup11 μ hμ x y) =
      TauCeti.ContCohomology.explicitCup11 G M N P μ continuous_of_discreteTopology hμ
        (h1Equiv G M x) (h1Equiv G N y) := by
  induction x using QuotientAddGroup.induction_on with
  | H a => induction y using QuotientAddGroup.induction_on with
    | H b =>
      exact (TauCeti.ContCohomology.explicitCup11_mk G M N P μ _ hμ ⟨a.1, Z1_eq G M ▸ a.2⟩
        ⟨b.1, Z1_eq G N ▸ b.2⟩).symm
end Cup

section F2
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)

attribute [local instance] TopRep.distribMulAction

local instance : ContinuousSMul G (TauCeti.trivialF2 G).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul

include htriv

theorem equivar : ∀ (g : G) (m : ZMod 2),
    (TauCeti.trivialF2Equiv G).symm ((ContinuousMulEquiv.refl G) g • m) =
      g • (TauCeti.trivialF2Equiv G).symm m := by
  intro g m
  rw [htriv, TopRep.distribMulAction_smul, TauCeti.trivialF2_ρ_apply_apply]

noncomputable def toF2 : TauCeti.ContCohomology.H1 G (ZMod 2) ≃+ TauCeti.ContCohomology.H1 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.explicitMap1Equiv G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm
    continuous_of_discreteTopology continuous_of_discreteTopology (equivar G htriv)

noncomputable def toF2two : TauCeti.ContCohomology.H2 G (ZMod 2) ≃+ TauCeti.ContCohomology.H2 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.explicitMap2Equiv G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm
    continuous_of_discreteTopology continuous_of_discreteTopology (equivar G htriv)

noncomputable def cont1 (x : GQ2.ContCoh.H1 G (ZMod 2)) : continuousCohomology 1 (TauCeti.trivialF2 G) :=
    (CategoryTheory.eqToHom (congrArg (continuousCohomology 1)
        (TauCeti.ofDiscreteModule_trivialF2 G))).hom
      (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
        (toF2 G htriv (h1Equiv G _ x)))

noncomputable def cont2 (x : GQ2.ContCoh.H2 G (ZMod 2)) : continuousCohomology 2 (TauCeti.trivialF2 G) :=
    (CategoryTheory.eqToHom (congrArg (continuousCohomology 2)
        (TauCeti.ofDiscreteModule_trivialF2 G))).hom
      (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
        (toF2two G htriv (h2Equiv G _ x)))

theorem cont_cup (x y : GQ2.ContCoh.H1 G (ZMod 2)) :
  cont2 G htriv (GQ2.trivialCupPairing 2 G htriv x y) =
    (TauCeti.trivialF2TopPairing G).cup 1 1 (cont1 G htriv x) (cont1 G htriv y) := by
  rw [cont1, cont1, cont2, TauCeti.trivialF2TopPairing_cup_one_one_explicitH1]
  congr 2
  rw [GQ2.trivialCupPairing, h2Equiv_cup11]
  simp only [toF2, toF2two, TauCeti.ContCohomology.explicitMap1Equiv_apply,
    TauCeti.ContCohomology.explicitMap2Equiv_apply]
  exact TauCeti.ContCohomology.explicitMap2_explicitCup11 G _ _ _ _ _ _ G _ _ _ _ _ _
    (ContinuousMulEquiv.refl G) _ _ _ _ _ _ _ _ _ (fun m n => by simp)
    (h1Equiv G (ZMod 2) x) (h1Equiv G (ZMod 2) y)
end F2
end Scratch
#print axioms Scratch.cont_cup
#print axioms Scratch.h1Equiv
