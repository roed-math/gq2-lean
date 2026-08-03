/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LUniformHeisenbergResolver

/-!
# Simple-coefficient source data for the improved L presentation

Full `TateDualityG (gamma h q : Type) 2` is stronger than the L exact-lifting argument needs.
It quantifies over every finite exponent-two module for the full profinite source.  The available
`IsDemushkin` API, on the other hand, is scalar and pro-`2`; it therefore cannot populate that
bundle for `gamma h q`.

There is also no coefficient short-exact-sequence long exact sequence for `ContCoh.H0/H1/H2`
in the present repository.  Thus the word-complex theorem `stokesDuality_of_simple` cannot be
ported silently to continuous cohomology.

This file records the stronger usable reduction which avoids that missing infrastructure.  At
one **fixed** resolved L word, provide the already-isolated continuous source comparison data
only for simple elementary `F_2[C]`-modules.  Each such package gives Stokes duality for that
simple module, and the proved word-complex devissage `stokesDuality_of_simple` gives Stokes
duality for every finite elementary module.

The fixed-word qualification is essential.  An exponent chosen separately from each simple
`V` would change the Fox complex during the induction and does not feed
`stokesDuality_of_simple`.  The uniform order bound below instead supplies the single,
coefficient-independent exponent `omega2Exp (4 * Monoid.exponent C)` for every simple module.

No new axiom and no final source/field equivalence is used.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

/-! ## The exact continuous data at one coefficient -/

section Data

variable {Gamma C A : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [Group C] [Finite C]
  [AddCommGroup A] [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Gamma (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
  {iota rel : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]

variable (c : iota → C) (w : rel → FreeGroup iota) [DistribMulAction C A]
  (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
  (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
    dualEval A (g • a) (g • lam) = g • dualEval A a lam)

/-- The exact continuous-cohomology comparison data at one coefficient.

The four low-degree equivalences are fields because, without a target resolver, even the
degree-one comparison is not currently automatic.  The remaining nine obligations are the
existing `SourceComparisonPackage`: three degree-two comparisons, three cup-perfectness maps,
and three comparison squares. -/
structure SimpleSourceData where
  h0A : H0 Gamma A ≃+ ↥(heisD0 (A := A) c).ker
  h1A : H1 Gamma A ≃+ WordH1 c w A
  h0Dual : H0 Gamma (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker
  h1Dual : H1 Gamma (ElemDual A) ≃+ WordH1 c w (ElemDual A)
  package : SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual

/-- One coefficient's continuous source data gives its three Stokes cohomology bijections. -/
theorem SimpleSourceData.stokesCohomologyBijections
    (D : SimpleSourceData c w hr hend hpair) :
    StokesCohomologyBijections c w A hr hend :=
  D.package.stokesCohomologyBijections

/-- One coefficient's continuous source data gives Stokes duality for its word complex. -/
theorem SimpleSourceData.stokesDuality
    (D : SimpleSourceData c w hr hend hpair) : StokesDuality c w A :=
  (stokesDuality_iff_cohomologyBijections c w A hr hend).mpr
    D.stokesCohomologyBijections

end Data

/-! ## Installing the canonical source actions through a finite target -/

section LTarget

/-- Continuity of an action pulled back from a finite discrete quotient. -/
private theorem continuousSMul_comp_finite_simple
    {G C A : Type*} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A => p.1 • p.2) =
      (fun p : C × A => p.1 • p.2) ∘ (fun p : G × A => (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The exact simple-coefficient source obligation at a fixed pushed L word.

All source-side structures are installed canonically: the source action is pulled back through
`rho`, coefficient topologies are discrete, and the scalar action is trivial.  Unlike
`SourceComparisonAt`, no `ResolvesAt` hypothesis is hidden here; if no common resolver is
available, the degree-one and degree-two comparisons remain visible fields of
`SimpleSourceData`. -/
noncomputable abbrev SimpleSourceAt {h q : ℕ}
    (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) (e : ℕ)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hr : ∀ k, FreeGroup.lift
      (fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g))
      (lSqFam h q e k) = 1)
    (hend : IsStokesEndpoint (lSqFam h q e)) : Type _ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((gamma h q : Type)) A :=
    continuousSMul_comp_finite_simple rho (fun _ _ => rfl)
  letI : TopologicalSpace (ElemDual A) := ⊥
  letI : DiscreteTopology (ElemDual A) := ⟨rfl⟩
  letI : ContinuousSMul ((gamma h q : Type)) (ElemDual A) :=
    continuousSMul_comp_finite_simple rho (fun g lam => by
      apply ElemDual.ext
      intro a
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (g⁻¹) • a) = lam ((rho g)⁻¹ • a)
      rw [map_inv])
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let c : Generator (2 * h + 1) → C :=
    fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g)
  let w : Fin 2 → FreeGroup (Generator (2 * h + 1)) := lSqFam h q e
  let hpair : ∀ (g : (gamma h q : Type)) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam := by
    intro g a lam
    rw [scalarActionZmodTwo_triv]
    show (g • lam) (g • a) = lam a
    rw [ElemDual.smul_apply, inv_smul_smul]
  exact SimpleSourceData c w hr hend hpair

/-- A simple-coefficient provider at one fixed pushed L word.

The exponent `e` is outside the coefficient binder: every simple module is compared to the
same word complex, exactly as required by word-complex devissage. -/
def SimpleSourceProviderAt {h q : ℕ}
    (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) (e : ℕ)
    (hr : ∀ k, FreeGroup.lift
      (fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g))
      (lSqFam h q e k) = 1)
    (hend : IsStokesEndpoint (lSqFam h q e)) : Type _ :=
  ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
    (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
      SimpleSourceAt C rho e V hr hend

/-- Fixed-word simple source data suffices for every finite elementary coefficient module.

The only induction here is the already-proved word-complex theorem
`stokesDuality_of_simple`; no continuous-cohomology LES is assumed. -/
theorem stokesDuality_of_simpleSourceProviderAt {h q e : ℕ}
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C)
    (hr : ∀ k, FreeGroup.lift
      (fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g))
      (lSqFam h q e k) = 1)
    (hend : IsStokesEndpoint (lSqFam h q e))
    (provider : SimpleSourceProviderAt C rho e hr hend)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g))
      (lSqFam h q e) A := by
  let c : Generator (2 * h + 1) → C :=
    fun g => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) g)
  exact stokesDuality_of_simple c (lSqFam h q e) hr hend
    (fun V _ _ _ hV₂ hsimp => by
      let D := provider V hV₂ hsimp
      -- Reinstall exactly the canonical structures used by `SimpleSourceAt`.
      letI : TopologicalSpace V := ⊥
      letI : DiscreteTopology V := ⟨rfl⟩
      letI : DistribMulAction ((gamma h q : Type)) V :=
        DistribMulAction.compHom V rho.toMonoidHom
      letI : ContinuousSMul ((gamma h q : Type)) V :=
        continuousSMul_comp_finite_simple rho (fun _ _ => rfl)
      letI : TopologicalSpace (ElemDual V) := ⊥
      letI : DiscreteTopology (ElemDual V) := ⟨rfl⟩
      letI : ContinuousSMul ((gamma h q : Type)) (ElemDual V) :=
        continuousSMul_comp_finite_simple rho (fun g lam => by
          apply ElemDual.ext
          intro v
          rw [ElemDual.smul_apply, ElemDual.smul_apply]
          change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
          rw [map_inv])
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
      letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo_continuousSMul _
      exact D.stokesDuality) A hA₂

end LTarget

section UniformProvider

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "levelC" => 4 * Monoid.exponent C
local notation "eC" => omega2Exp levelC
local notation "wC" => lSqFam h q eC

/-- Relator death at the coefficient-independent L word.

The scalar split target is already killed by `2 * exponent C`, hence by `levelC`; pushing its
resolution down to `C` supplies the word-lane relator hypothesis. -/
theorem lUniform_rel_death
    (rho : ContinuousMonoidHom GammaL C) :
    ∀ k, FreeGroup.lift (fun g => rho (genL g)) (wC k) = 1 := by
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : TopologicalSpace (WordLift (ZMod 2) C) := ⊥
  letI : DiscreteTopology (WordLift (ZMod 2) C) := ⟨rfl⟩
  have hbase : ∀ g : C, orderOf g ∣ Monoid.exponent C :=
    fun g => Monoid.order_dvd_exponent g
  have horder : ∀ p : WordLift (ZMod 2) C, orderOf p ∣ levelC := fun p =>
    (WordLift.orderOf_dvd_two_mul (by decide) hbase p).trans ⟨2, by ring⟩
  have hres : ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h)) wC
      (WordLift (ZMod 2) C) :=
    resolvesAt_lSqFam (fourMulExponent_ne_zero_and_even C).1 horder h q
  exact fun k => lower_rel (A := ZMod 2) rho (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hres k

/-- The weakest fixed-word provider at the coefficient-independent common level.

It is strictly coefficient-local: for each simple module it asks only for the exact
`SimpleSourceData` consumed by one source comparison.  It neither constructs nor entails the
all-module `TateDualityG` bundle. -/
noncomputable abbrev UniformSimpleSourceProvider
    (rho : ContinuousMonoidHom GammaL C) (hq : Even q) : Type _ :=
  SimpleSourceProviderAt C rho eC (lUniform_rel_death rho)
    (lSq_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2))

/-- Uniform regression: simple coefficient-local source data at the single word `wC` gives
Stokes duality for every finite elementary `C`-module. -/
theorem stokesDuality_lUniform_of_simpleSourceProvider
    (rho : ContinuousMonoidHom GammaL C) (hq : Even q)
    (provider : UniformSimpleSourceProvider rho hq)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (genL g)) wC A :=
  stokesDuality_of_simpleSourceProviderAt rho (lUniform_rel_death rho)
    (lSq_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2))
    provider A hA₂

end UniformProvider

end


end GQ2.Dyadic.LSquare
