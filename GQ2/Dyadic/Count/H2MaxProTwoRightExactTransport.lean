/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2MaxProTwoTransport

/-!
# Descending the finite-elementary H² right-exactness supply

This file records the reverse of the inflation transport already available in
`H2MaxProTwoTransport`.  In the naturality square for a coefficient surjection `A → B`,
right exactness descends from `G` to a quotient `Q` provided inflation is surjective for the
source coefficient `A` and injective for the target coefficient `B`.

Consequently, a coefficient-uniform surjectivity supply together with a coefficient-uniform
injectivity supply transports `FiniteElementaryH2RightExactSupply G` to
`FiniteElementaryH2RightExactSupply Q`.  For the maximal pro-`2` quotient, surjectivity is
available elsewhere only from additional kernel/transgression hypotheses; it is not automatic.
After such a surjectivity input is supplied, the other exact comparison input is injectivity of
degree-two inflation for every finite elementary quotient module.  The existing scalar
`ZMod 2` theorem does not provide this action-dependent assertion.
-/

namespace GQ2.ContCoh

noncomputable section

/-! ## The sharp reverse inflation diagram chase -/

section InflationDescent

variable {G Q A B : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction Q A] [ContinuousSMul Q A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction Q B] [ContinuousSMul Q B]

/-- Right exactness descends through the inflation square when inflation is onto on the source
coefficient and one-to-one on the target coefficient.

Both directions are sharp for this diagram chase: source surjectivity lifts the bottom
preimage, while target injectivity reflects the resulting equality back upstairs. -/
theorem H2RightExactAt.of_inflation_source_surjective_target_injective
    (pi : ContinuousMonoidHom G Q)
    (hcompatA : ∀ (x : G) (a : A), pi x • a = x • a)
    (hcompatB : ∀ (x : G) (b : B), pi x • b = x • b)
    (f : A →+ B) (hf : Continuous f)
    (hfG : ∀ (x : G) (a : A), f (x • a) = x • f a)
    (hfQ : ∀ (x : Q) (a : A), f (x • a) = x • f a)
    (hinfA : Function.Surjective (inf2 pi hcompatA))
    (hinfB : Function.Injective (inf2 pi hcompatB))
    (hG : H2RightExactAt (G := G) f hf hfG) :
    H2RightExactAt (G := Q) f hf hfQ := by
  intro yQ
  obtain ⟨xG, hxG⟩ := hG (inf2 pi hcompatB yQ)
  obtain ⟨xQ, hxQ⟩ := hinfA xG
  refine ⟨xQ, hinfB ?_⟩
  rw [← mapCoeff2_inf2 pi hcompatA hcompatB f hf hfG hfQ, hxQ, hxG]

end InflationDescent

/-! ## Uniform comparison supplies -/

/-- Injectivity of degree-two inflation for every finite elementary coefficient on which the
two actions agree. -/
def FiniteElementaryH2InflationInjective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pi : ContinuousMonoidHom G Q) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction Q M] [ContinuousSMul Q M],
    (∀ m : M, m + m = 0) →
    ∀ hcompat : ∀ (x : G) (m : M), pi x • m = x • m,
      Function.Injective (inf2 pi hcompat)

/-- Bijectivity of degree-two inflation for every finite elementary compatible coefficient. -/
def FiniteElementaryH2InflationBijective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pi : ContinuousMonoidHom G Q) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction Q M] [ContinuousSMul Q M],
    (∀ m : M, m + m = 0) →
    ∀ hcompat : ∀ (x : G) (m : M), pi x • m = x • m,
      Function.Bijective (inf2 pi hcompat)

/-- Forget the injectivity half of a finite-elementary H² inflation bijectivity supply. -/
theorem FiniteElementaryH2InflationBijective.surjective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    {pi : ContinuousMonoidHom G Q}
    (h : FiniteElementaryH2InflationBijective pi) :
    FiniteElementaryH2InflationSurjective pi := by
  intro M _ _ _ _ _ _ _ _ _ hM hcompat
  exact (h M hM hcompat).surjective

/-- Forget the surjectivity half of a finite-elementary H² inflation bijectivity supply. -/
theorem FiniteElementaryH2InflationBijective.injective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    {pi : ContinuousMonoidHom G Q}
    (h : FiniteElementaryH2InflationBijective pi) :
    FiniteElementaryH2InflationInjective pi := by
  intro M _ _ _ _ _ _ _ _ _ hM hcompat
  exact (h M hM hcompat).injective

private theorem continuousSMul_comp
    {G Q M : Type} [Monoid G] [TopologicalSpace G]
    [Monoid Q] [TopologicalSpace Q]
    [TopologicalSpace M] [SMul Q M] [ContinuousSMul Q M]
    (pi : ContinuousMonoidHom G Q) [SMul G M]
    (hcompat : ∀ (g : G) (m : M), g • m = pi g • m) : ContinuousSMul G M := by
  constructor
  have hfac : (fun p : G × M ↦ p.1 • p.2) =
      (fun p : Q × M ↦ p.1 • p.2) ∘ (fun p : G × M ↦ (pi p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_smul.comp
    ((pi.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-! ## Descent of the full right-exactness supply -/

/-- A finite-elementary H² right-exactness supply descends from `G` to `Q` when inflation is
uniformly surjective on source coefficients and uniformly injective on target coefficients. -/
theorem finiteElementaryH2RightExactSupply_of_inflation_surjective_injective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pi : ContinuousMonoidHom G Q)
    (hG : FiniteElementaryH2RightExactSupply G)
    (hsurj : FiniteElementaryH2InflationSurjective pi)
    (hinj : FiniteElementaryH2InflationInjective pi) :
    FiniteElementaryH2RightExactSupply Q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ f hf hfQ hA₂ hB₂ hsurjF
  letI : DistribMulAction G A := DistribMulAction.compHom A pi.toMonoidHom
  letI : ContinuousSMul G A := continuousSMul_comp pi (fun _ _ ↦ rfl)
  letI : DistribMulAction G B := DistribMulAction.compHom B pi.toMonoidHom
  letI : ContinuousSMul G B := continuousSMul_comp pi (fun _ _ ↦ rfl)
  have hfG : ∀ (x : G) (a : A), f (x • a) = x • f a := by
    intro x a
    exact hfQ (pi x) a
  have hcompatA : ∀ (x : G) (a : A), pi x • a = x • a := fun _ _ ↦ rfl
  have hcompatB : ∀ (x : G) (b : B), pi x • b = x • b := fun _ _ ↦ rfl
  apply H2RightExactAt.of_inflation_source_surjective_target_injective
    pi hcompatA hcompatB f hf hfG hfQ
      (hsurj A hA₂ hcompatA) (hinj B hB₂ hcompatB)
  exact hG A B f hf hfG hA₂ hB₂ hsurjF

/-- Bijective inflation is a convenient one-premise form of the preceding transport theorem. -/
theorem finiteElementaryH2RightExactSupply_of_inflation_bijective
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pi : ContinuousMonoidHom G Q)
    (hG : FiniteElementaryH2RightExactSupply G)
    (hbij : FiniteElementaryH2InflationBijective pi) :
    FiniteElementaryH2RightExactSupply Q :=
  finiteElementaryH2RightExactSupply_of_inflation_surjective_injective pi hG
    hbij.surjective hbij.injective

/-! ## Maximal pro-two specializations -/

section MaxProTwo

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The source-surjective/target-injective comparison package descends right exactness to the
maximal pro-`2` quotient. -/
theorem finiteElementaryH2RightExactSupply_maxProPQuotient_of_inflation_surjective_injective
    (hG : FiniteElementaryH2RightExactSupply G)
    (hsurj : FiniteElementaryH2InflationSurjective (maxProPMk 2 G))
    (hinj : FiniteElementaryH2InflationInjective (maxProPMk 2 G)) :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 G) :=
  finiteElementaryH2RightExactSupply_of_inflation_surjective_injective
    (maxProPMk 2 G) hG hsurj hinj

/-- The bijective-inflation form of right-exactness descent to the maximal pro-`2` quotient. -/
theorem finiteElementaryH2RightExactSupply_maxProPQuotient_of_inflation_bijective
    (hG : FiniteElementaryH2RightExactSupply G)
    (hbij : FiniteElementaryH2InflationBijective (maxProPMk 2 G)) :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 G) :=
  finiteElementaryH2RightExactSupply_of_inflation_bijective (maxProPMk 2 G) hG hbij

end MaxProTwo

end

end GQ2.ContCoh
