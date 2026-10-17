module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import GQ2.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
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
theorem h1Equiv_res1 (U : Subgroup G) (x : GQ2.ContCoh.H1 G M) :
    h1Equiv U M (GQ2.ContCoh.res1 G M U x) =
      TauCeti.ContCohomology.explicitRes1 G M U (h1Equiv G M x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitRes1_mk G M U ⟨z.1, Z1_eq G M ▸ z.2⟩).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z1 U M => (w : TauCeti.ContCohomology.H1 U M))
      (Subtype.ext (funext fun g => by rw [TauCeti.ContCohomology.cocyclesMap1_apply]; rfl))

theorem h2Equiv_res2 (U : Subgroup G) (x : GQ2.ContCoh.H2 G M) :
    h2Equiv U M (GQ2.ContCoh.res2 G M U x) =
      TauCeti.ContCohomology.explicitRes2 G M U (h2Equiv G M x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitRes2_mk G M U ⟨z.1, Z2_eq G M ▸ z.2⟩).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z2 U M => (w : TauCeti.ContCohomology.H2 U M))
      (Subtype.ext (funext fun ⟨g, h⟩ => by rw [TauCeti.ContCohomology.cocyclesMap2_apply]; rfl))
end Scratch
