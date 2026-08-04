/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SylowPreimageDevissage
import GQ2.FrattiniCriterion
import GQ2.MaxProPCohomology

/-!
# The maximal pro-2 route for the Sylow-preimage H² tail

Let `U = rho⁻¹(P)`, where `P` is a Sylow `2`-subgroup of a finite action image.  The
action map `U → P` factors through the maximal pro-2 quotient `U(2)`, and the resulting map
`U(2) → P` is onto.  Thus all coefficient actions in the Sylow-local problem genuinely live
on `U(2)`.

This observation does not by itself prove the scalar-kernel H² tail.  Two independent inputs
remain:

* degree-two inflation `H²(U(2), M) → H²(U, M)` must be onto for the finite elementary
  target coefficient `M`;
* `U(2)` must satisfy the finite-elementary CD-2/right-exactness tail.

The first input is not a formal consequence of the maximal pro-2 universal property.  The
existing `MaxProPCohomology` theorem proves only injectivity for trivial `ZMod 2` coefficients.
The second input is stronger than the repository's deliberately scalar `IsDemushkin` record.
In particular, a Reidemeister--Schreier or one-relator identification of `U(2)` still needs a
genuine asphericity/CD-2 theorem before it can fill the package below.

This file proves the complete transport theorem from precisely those two premises and no Tate
duality, field realization, or unformalized presentation theorem.
-/

namespace GQ2.ContCoh

noncomputable section

/-! ## Naturality and the inflation diagram chase -/

section InflationNaturality

variable {G Q A B : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction Q A] [ContinuousSMul Q A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction Q B] [ContinuousSMul Q B]

/-- Coefficient functoriality commutes with degree-two inflation. -/
theorem mapCoeff2_inf2
    (pi : ContinuousMonoidHom G Q)
    (hcompatA : ∀ (x : G) (a : A), pi x • a = x • a)
    (hcompatB : ∀ (x : G) (b : B), pi x • b = x • b)
    (f : A →+ B) (hf : Continuous f)
    (hfG : ∀ (x : G) (a : A), f (x • a) = x • f a)
    (hfQ : ∀ (x : Q) (a : A), f (x • a) = x • f a)
    (z : H2 Q A) :
    mapCoeff2 f hf hfG (inf2 pi hcompatA z) =
      inf2 pi hcompatB (mapCoeff2 f hf hfQ z) := by
  obtain ⟨c, rfl⟩ := H2mk_surjective (G := Q) (M := A) z
  rfl

/-- If inflation is onto for the target coefficient, right exactness on the quotient group
pulls back to right exactness on the original group. -/
theorem H2RightExactAt.of_inflation_surjective
    (pi : ContinuousMonoidHom G Q)
    (hcompatA : ∀ (x : G) (a : A), pi x • a = x • a)
    (hcompatB : ∀ (x : G) (b : B), pi x • b = x • b)
    (f : A →+ B) (hf : Continuous f)
    (hfG : ∀ (x : G) (a : A), f (x • a) = x • f a)
    (hfQ : ∀ (x : Q) (a : A), f (x • a) = x • f a)
    (hinfB : Function.Surjective (inf2 pi hcompatB))
    (hQ : H2RightExactAt (G := Q) f hf hfQ) :
    H2RightExactAt (G := G) f hf hfG := by
  intro y
  obtain ⟨yQ, rfl⟩ := hinfB y
  obtain ⟨xQ, hxQ⟩ := hQ yQ
  refine ⟨inf2 pi hcompatA xQ, ?_⟩
  rw [mapCoeff2_inf2 pi hcompatA hcompatB f hf hfG hfQ, hxQ]

end InflationNaturality

/-! ## Exact pro-2 comparison and CD-2 premises -/

/-- Surjectivity of degree-two inflation for every finite elementary coefficient on which the
two actions agree.  This is the exact comparison direction used by the transport theorem.

The existing maximal-pro-2 cohomology API proves injectivity for trivial scalar coefficients;
it does not construct this supply. -/
def FiniteElementaryH2InflationSurjective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pi : ContinuousMonoidHom G Q) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction Q M] [ContinuousSMul Q M],
    (∀ m : M, m + m = 0) →
    ∀ hcompat : ∀ (x : G) (m : M), pi x • m = x • m,
      Function.Surjective (inf2 pi hcompat)

/-- The genuine finite-elementary CD-2 premise on one profinite group.  It is deliberately
stronger than scalar Demushkin H¹/H²/cup data and is exactly what a presentation-asphericity
theorem would have to construct. -/
def FiniteElementaryH2RightExactSupply
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction G B] [ContinuousSMul G B]
    (f : A →+ B) (hf : Continuous f)
    (hfG : ∀ (x : G) (a : A), f (x • a) = x • f a),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective f → H2RightExactAt f hf hfG

/-- A full finite-elementary CD-2 supply implies the scalar-kernel tail for any finite action
quotient. -/
theorem twoGroupActionScalarKernelH2Tail_of_finiteElementaryRightExact
    {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom G C)
    (S : FiniteElementaryH2RightExactSupply G) :
    TwoGroupActionScalarKernelH2Tail rho := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG _hgC _hcompatA _hcompatB
    hA₂ hB₂ hsurj _hker
  exact S A B g continuous_of_discreteTopology hgG hA₂ hB₂ hsurj

private theorem continuousSMul_comp_finite_proTwo
    {G C M : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace M] [DiscreteTopology M] [SMul C M]
    (rho : ContinuousMonoidHom G C) [SMul G M]
    (hcompat : ∀ (g : G) (m : M), g • m = rho g • m) : ContinuousSMul G M := by
  constructor
  have hfac : (fun p : G × M ↦ p.1 • p.2) =
      (fun p : C × M ↦ p.1 • p.2) ∘ (fun p : G × M ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The abstract maximal-pro-2 transport step.  If the finite action map `rhoG` factors as
`rhoQ ∘ pi`, degree-two inflation is onto for finite elementary coefficients, and `Q` has the
scalar CD-2 tail, then `G` has the scalar tail.

Only inflation for the target coefficient `B` is consumed in each application, but the supply
form is convenient for coefficient-uniform callers. -/
theorem twoGroupActionScalarKernelH2Tail_of_quotient
    {G Q C : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (pi : ContinuousMonoidHom G Q)
    (rhoG : ContinuousMonoidHom G C) (rhoQ : ContinuousMonoidHom Q C)
    (hfactor : ∀ x : G, rhoQ (pi x) = rhoG x)
    (hinf : FiniteElementaryH2InflationSurjective pi)
    (tailQ : TwoGroupActionScalarKernelH2Tail rhoQ) :
    TwoGroupActionScalarKernelH2Tail rhoG := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f hfG hfC hcompatA hcompatB
    hA₂ hB₂ hsurj hker
  letI : DistribMulAction Q A := DistribMulAction.compHom A rhoQ.toMonoidHom
  letI : ContinuousSMul Q A :=
    continuousSMul_comp_finite_proTwo rhoQ (fun _ _ ↦ rfl)
  letI : DistribMulAction Q B := DistribMulAction.compHom B rhoQ.toMonoidHom
  letI : ContinuousSMul Q B :=
    continuousSMul_comp_finite_proTwo rhoQ (fun _ _ ↦ rfl)
  have hfQ : ∀ (x : Q) (a : A), f (x • a) = x • f a := by
    intro x a
    exact hfC (rhoQ x) a
  have hpiA : ∀ (x : G) (a : A), pi x • a = x • a := by
    intro x a
    change rhoQ (pi x) • a = x • a
    rw [hfactor, ← hcompatA]
  have hpiB : ∀ (x : G) (b : B), pi x • b = x • b := by
    intro x b
    change rhoQ (pi x) • b = x • b
    rw [hfactor, ← hcompatB]
  have hrightQ : H2RightExactAt (G := Q) f continuous_of_discreteTopology hfQ :=
    tailQ A B f hfQ hfC (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hA₂ hB₂ hsurj hker
  exact H2RightExactAt.of_inflation_surjective pi hpiA hpiB f
    continuous_of_discreteTopology hfG hfQ (hinf B hB₂ hpiB) hrightQ

/-! ## The Sylow preimage and its maximal pro-2 quotient -/

/-- Restricting a surjection to an odd-index compact subgroup is still onto when the target is
pro-2.  Indeed, containment of the restricted image in an index-two open normal subgroup would
make `2` divide the subgroup index.  The pro-2 Frattini criterion then detects surjectivity.

This is the useful content of the odd-index structure at the pro-2 level.  It gives an
epimorphism of maximal pro-2 quotients, not an isomorphism. -/
theorem surjective_restrict_of_odd_index_to_proTwo
    {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : IsProP 2 K) (f : ContinuousMonoidHom G K)
    (hf : Function.Surjective f) (U : Subgroup G) [CompactSpace U]
    (hodd : Odd U.index) :
    Function.Surjective (f.comp (subgroupIncl G U)) := by
  apply surjective_of_forall_not_le_index_p hK
  intro M hM hle
  apply hodd.not_two_dvd_nat
  have hUle : U ≤ M.toSubgroup.comap f.toMonoidHom := by
    intro u hu
    apply hle
    exact ⟨⟨u, hu⟩, rfl⟩
  have hdvd : (M.toSubgroup.comap f.toMonoidHom).index ∣ U.index :=
    Subgroup.index_dvd_of_le hUle
  rw [Subgroup.index_comap_of_surjective M.toSubgroup hf, hM] at hdvd
  exact hdvd

section SylowPreimage

variable {G C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- An open Sylow preimage is compact, so its maximal pro-2 quotient is available. -/
noncomputable instance compactSpace_sylowTwoPreimage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) :
    CompactSpace (sylowTwoPreimage rho P) := by
  apply isCompact_iff_compactSpace.mp
  exact (Subgroup.isClosed_of_isOpen _ (isOpen_sylowTwoPreimage rho P)).isCompact

/-- The restriction of any ambient pro-2 quotient to the Sylow preimage is onto. -/
theorem sylowTwoPreimage_restrict_surjective_to_proTwo
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho)
    (P : Sylow 2 C) (hK : IsProP 2 K)
    (f : ContinuousMonoidHom G K) (hf : Function.Surjective f) :
    Function.Surjective
      (f.comp (subgroupIncl G (sylowTwoPreimage rho P))) :=
  surjective_restrict_of_odd_index_to_proTwo hK f hf
    (sylowTwoPreimage rho P) (odd_sylowTwoPreimage_index rho hrho P)

/-- The map from `U(2)` to an ambient pro-2 quotient obtained by restricting first to `U`. -/
noncomputable def sylowPreimageMaxProTwoLift
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hK : IsProP 2 K) (f : ContinuousMonoidHom G K) :
    ContinuousMonoidHom
      (maxProPQuotient 2 (sylowTwoPreimage rho P)) K :=
  (maxProPHomEquiv hK).symm
    (f.comp (subgroupIncl G (sylowTwoPreimage rho P)))

/-- The preceding factor agrees with the restricted ambient quotient map. -/
@[simp] theorem sylowPreimageMaxProTwoLift_mk
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hK : IsProP 2 K) (f : ContinuousMonoidHom G K)
    (u : sylowTwoPreimage rho P) :
    sylowPreimageMaxProTwoLift rho P hK f
        (maxProPMk 2 (sylowTwoPreimage rho P) u) = f u.1 := by
  exact DFunLike.congr_fun
    ((maxProPHomEquiv hK).apply_symm_apply
      (f.comp (subgroupIncl G (sylowTwoPreimage rho P)))) u

/-- Odd index therefore gives an epimorphism `U(2) → K` for every ambient pro-2 quotient
`G → K`.  No injectivity claim is made: in general it is false. -/
theorem sylowPreimageMaxProTwoLift_surjective
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho)
    (P : Sylow 2 C) (hK : IsProP 2 K)
    (f : ContinuousMonoidHom G K) (hf : Function.Surjective f) :
    Function.Surjective (sylowPreimageMaxProTwoLift rho P hK f) := by
  intro k
  obtain ⟨u, hu⟩ :=
    sylowTwoPreimage_restrict_surjective_to_proTwo rho hrho P hK f hf k
  refine ⟨maxProPMk 2 (sylowTwoPreimage rho P) u, ?_⟩
  rw [sylowPreimageMaxProTwoLift_mk]
  change f u.1 = k at hu
  exact hu

/-- The action map `U → P` factored through `U(2)`. -/
noncomputable def sylowPreimageMaxProTwoHom
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) :
    ContinuousMonoidHom
      (maxProPQuotient 2 (sylowTwoPreimage rho P)) P :=
  (maxProPHomEquiv (isProP_of_isPGroup P.2)).symm
    (sylowTwoPreimageHom rho P)

/-- The maximal-pro-2 factor agrees with the original action map on `U`. -/
@[simp] theorem sylowPreimageMaxProTwoHom_mk
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (u : sylowTwoPreimage rho P) :
    sylowPreimageMaxProTwoHom rho P
        (maxProPMk 2 (sylowTwoPreimage rho P) u) =
      sylowTwoPreimageHom rho P u := by
  exact DFunLike.congr_fun
    ((maxProPHomEquiv (isProP_of_isPGroup P.2)).apply_symm_apply
      (sylowTwoPreimageHom rho P)) u

/-- Because `U → P` is onto, its factor `U(2) → P` is onto as well.  Hence the entire
finite Sylow action is already visible on the maximal pro-2 quotient. -/
theorem sylowPreimageMaxProTwoHom_surjective
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho)
    (P : Sylow 2 C) :
    Function.Surjective (sylowPreimageMaxProTwoHom rho P) := by
  intro p
  obtain ⟨u, hu⟩ := sylowTwoPreimageHom_surjective rho hrho P p
  exact ⟨maxProPMk 2 (sylowTwoPreimage rho P) u, by simpa using hu⟩

/-- The two honest premises needed to obtain the scalar H² tail from `U(2)`:

1. finite-elementary H² inflation from `U(2)` to `U` is onto;
2. `U(2)` has the genuine finite-elementary CD-2/right-exactness property.

A one-relator or improved-L presentation of `U(2)` is useful only after an asphericity/CD-2
theorem fills `cdTwo`; the scalar `IsDemushkin` record is insufficient. -/
structure SylowPreimageMaxProTwoCDTwoPackage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) : Prop where
  inflation : FiniteElementaryH2InflationSurjective
    (maxProPMk 2 (sylowTwoPreimage rho P))
  cdTwo : FiniteElementaryH2RightExactSupply
    (maxProPQuotient 2 (sylowTwoPreimage rho P))

/-- A maximal-pro-2 comparison/CD-2 package proves the residual scalar tail on `U`. -/
theorem SylowPreimageMaxProTwoCDTwoPackage.toScalarKernelH2Tail
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (D : SylowPreimageMaxProTwoCDTwoPackage rho P) :
    TwoGroupActionScalarKernelH2Tail (sylowTwoPreimageHom rho P) := by
  apply twoGroupActionScalarKernelH2Tail_of_quotient
    (maxProPMk 2 (sylowTwoPreimage rho P))
    (sylowTwoPreimageHom rho P) (sylowPreimageMaxProTwoHom rho P)
    (sylowPreimageMaxProTwoHom_mk rho P) D.inflation
  exact twoGroupActionScalarKernelH2Tail_of_finiteElementaryRightExact
    (sylowPreimageMaxProTwoHom rho P) D.cdTwo

end SylowPreimage

end

end GQ2.ContCoh
