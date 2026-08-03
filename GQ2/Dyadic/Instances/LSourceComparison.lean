/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LExact
import GQ2.Dyadic.LiftingDualityG

/-!
# The continuous-cohomology source package for the improved L presentation

`LSquare.ResolvedPushedHsimp` is the last source-facing hypothesis of the improved odd/L
exact-lifting chain.  This file gives an exact, coefficient-by-coefficient reduction of that
hypothesis to continuous cohomology.

The reduction deliberately does not postulate `ResolvedPushedHsimp` or the three word maps.
At one finite target it asks for precisely:

* the still-missing `H²` comparison equivalences, for `A`, `ElemDual A`, and the scalar
  coefficient `ZMod 2`;
* bijectivity of the three continuous Tate cup maps `(0,2)`, `(1,1)`, and `(2,0)`;
* commutativity of the three squares comparing those cup maps with the Stokes word maps.

Degree zero is supplied by `Count.h0Equiv`.  Degree one, for both `A` and `ElemDual A`, is
supplied by `Count.h1Equiv_gammaR_range`; importantly, it uses the two resolvers already carried
by `ResolvedPushedHsimp`, and therefore makes no surjectivity assumption on the finite target
map.  Universal coefficients on the word side and the three stated `H²` comparisons assemble
the right vertical maps.

The original `SourceComparisonPackage` below records the cup bijectivities because its consumer
runs from continuous cohomology to word cohomology.  The noncircular
`SourceComparisonCore` removes those three fields.  If word-level `StokesDuality` is obtained
independently, the same comparison squares run backwards and *prove* all three continuous cup
maps bijective; `SourceComparisonCore.toSourceComparisonPackage` then recovers the legacy
package.  Thus the new direction isolates the genuinely remaining inputs: word Stokes duality,
the three degree-two comparisons/orientation, and square compatibility.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count

/-! ## Transporting scalar-valued duals

The targets of the three word Stokes maps are universal-coefficient duals.  The targets of the
continuous cup maps are homomorphisms into `H²(Γ, ZMod 2)`.  An `H²` comparison for the dual
coefficient and a scalar orientation `H²(Γ, ZMod 2) ≃ ZMod 2` identify those two spellings.
-/

/-- Transport an elementary dual across a source comparison and a scalar orientation. -/
noncomputable def scalarDualTransport
    {X Y S : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup S]
    (eX : X ≃+ Y) (eS : S ≃+ ZMod 2) :
    ElemDual Y ≃+ (X →+ S) where
  toFun lam :=
    { toFun := fun x => eS.symm (lam (eX x))
      map_zero' := by simp
      map_add' := by simp }
  invFun f :=
    { toFun := fun y => eS (f (eX.symm y))
      map_zero' := by simp
      map_add' := by simp }
  left_inv lam := by
    apply ElemDual.ext
    intro y
    change eS (eS.symm (lam (eX (eX.symm y)))) = lam y
    simp
  right_inv f := by
    ext x
    change eS.symm (eS (f (eX.symm (eX x)))) = f x
    simp
  map_add' lam mu := by
    ext x
    simp

/-- A perfect finite elementary pairing is perfect after transposition.

The conclusion is not a formal consequence of currying alone: it uses the equal-cardinality
theorem for finite elementary `ZMod 2`-modules.  This is the generic counting step needed to
pass from the `ElemDual` orientation of the L source cups to the opposite orientation used by
the Tate interface. -/
theorem transpose_bijective_of_bijective
    {V W H : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup H]
    [Finite V] [Finite W] [Finite H]
    (hVtwo : ∀ v : V, v + v = 0) (hWtwo : ∀ w : W, w + w = 0)
    (tau : H ≃+ ZMod 2) (Phi : V →+ W →+ H) (Psi : W →+ V →+ H)
    (hPhi : Function.Bijective Phi)
    (htranspose : ∀ v w, Psi w v = Phi v w) : Function.Bijective Psi := by
  have hcard : Nat.card W = Nat.card V := by
    calc
      Nat.card W = Nat.card (W →+ ZMod 2) :=
        (GQ2.LocalLiftingDuality.card_addHom_zmod2 hWtwo).symm
      _ = Nat.card (W →+ H) :=
        (Nat.card_congr tau.addMonoidHomCongrRight.toEquiv).symm
      _ = Nat.card V := (Nat.card_congr (Equiv.ofBijective Phi hPhi)).symm
  apply GQ2.LocalLiftingDuality.bijective_cup hWtwo hVtwo hcard tau Psi
  intro f
  let fH : W →+ H := tau.symm.toAddMonoidHom.comp f
  obtain ⟨v, hv⟩ := hPhi.2 fH
  refine ⟨v, fun w => ?_⟩
  rw [htranspose]
  have hw := DFunLike.congr_fun hv w
  change tau (Phi v w) = f w
  rw [hw]
  exact tau.apply_symm_apply (f w)

/-! ## One-target source comparison package -/

section Package

variable {Γ C A : Type*}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group C] [Finite C]
  [AddCommGroup A] [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Γ (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  {ι rel : Type*} [Fintype ι] [DecidableEq ι] [Fintype rel]

variable (c : ι → C) (w : rel → FreeGroup ι) [DistribMulAction C A]
  (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
  (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
    dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam)

/-- The three continuous source cup maps, in the order of the Stokes ladder. -/
noncomputable abbrev sourceCup02 : H0 Γ A → (H2 Γ (ElemDual A) →+ H2 Γ (ZMod 2)) :=
  fun x => cup02 (dualEval A) hpair x

noncomputable abbrev sourceCup11 : H1 Γ A → (H1 Γ (ElemDual A) →+ H2 Γ (ZMod 2)) :=
  fun x => cup11 (dualEval A) hpair x

noncomputable abbrev sourceCup20 : H2 Γ A → (H0 Γ (ElemDual A) →+ H2 Γ (ZMod 2)) :=
  fun x => cup20 (dualEval A) hpair x

/-- The noncircular core of a source comparison package.

Unlike `SourceComparisonPackage`, this structure does not assume that any continuous cup
product is perfect.  It contains only the three degree-two comparisons and the three
comparison squares.  Consequently, word-level Stokes duality can be transported through it
to *prove* source cup-product perfectness. -/
structure SourceComparisonCore
    (h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1A : H1 Γ A ≃+ WordH1 c w A)
    (h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker)
    (h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)) where
  /-- The general-coefficient comparison in degree two, primal side. -/
  h2A : H2 Γ A ≃+ WordH2 c w A
  /-- The general-coefficient comparison in degree two, dual side. -/
  h2Dual : H2 Γ (ElemDual A) ≃+ WordH2 c w (ElemDual A)
  /-- The scalar degree-two comparison/orientation used to read cup values in `ZMod 2`. -/
  h2Scalar : H2 Γ (ZMod 2) ≃+ ZMod 2
  /-- Compatibility of the Stokes `(0,2)` map with continuous cup product. -/
  square02_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC0 (heisD1 (A := ElemDual A) c w))
        (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
      (scalarDualTransport h2Dual h2Scalar))
        (stokesH0Map (stokes_square₀ (A := A) c w hr hend) x)
      = sourceCup02 hpair (h0A.symm x)
  /-- Compatibility of the Stokes `(1,1)` map with continuous cup product. -/
  square11_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
        (wordH1_target_uc (A := A) c w hr)).trans
      (scalarDualTransport h1Dual h2Scalar))
        (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
          (stokes_square₁ (A := A) c w hr hend) x)
      = sourceCup11 hpair (h1A.symm x)
  /-- Compatibility of the Stokes `(2,0)` map with continuous cup product. -/
  square20_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC2 (heisD0 (A := ElemDual A) c))
        (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
          (heisD0 (A := ElemDual A) c))).trans
      (scalarDualTransport h0Dual h2Scalar))
        (stokesH2Map (stokes_square₁ (A := A) c w hr hend) x)
      = sourceCup20 hpair (h2A.symm x)

/--
The exact continuous-cohomology obligations at one finite target.

`h0A`, `h1A`, `h0Dual`, and `h1Dual` are parameters rather than fields because the L-specific
constructor below fills them with already-proved comparison theorems.  The structure fields are
therefore exactly the missing `H²`, Tate-perfectness, and square-commutativity inputs.
-/
structure SourceComparisonPackage
    (h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker)
    (h1A : H1 Γ A ≃+ WordH1 c w A)
    (h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker)
    (h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)) where
  /-- The missing general-coefficient comparison in degree two, primal side. -/
  h2A : H2 Γ A ≃+ WordH2 c w A
  /-- The missing general-coefficient comparison in degree two, dual side. -/
  h2Dual : H2 Γ (ElemDual A) ≃+ WordH2 c w (ElemDual A)
  /-- The scalar degree-two comparison/orientation used to read cup values in `ZMod 2`. -/
  h2Scalar : H2 Γ (ZMod 2) ≃+ ZMod 2
  /-- Tate perfectness in bidegree `(0,2)`. -/
  cup02_bijective : Function.Bijective (sourceCup02 hpair)
  /-- Tate perfectness in bidegree `(1,1)`. -/
  cup11_bijective : Function.Bijective (sourceCup11 hpair)
  /-- Tate perfectness in bidegree `(2,0)`. -/
  cup20_bijective : Function.Bijective (sourceCup20 hpair)
  /-- Compatibility of the Stokes `(0,2)` map with continuous cup product. -/
  square02_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC0 (heisD1 (A := ElemDual A) c w))
        (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
      (scalarDualTransport h2Dual h2Scalar))
        (stokesH0Map (stokes_square₀ (A := A) c w hr hend) x)
      = sourceCup02 hpair (h0A.symm x)
  /-- Compatibility of the Stokes `(1,1)` map with continuous cup product. -/
  square11_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
        (wordH1_target_uc (A := A) c w hr)).trans
      (scalarDualTransport h1Dual h2Scalar))
        (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
          (stokes_square₁ (A := A) c w hr hend) x)
      = sourceCup11 hpair (h1A.symm x)
  /-- Compatibility of the Stokes `(2,0)` map with continuous cup product. -/
  square20_commutes : ∀ x,
    ((AddEquiv.ofBijective
        (stokesUC2 (heisD0 (A := ElemDual A) c))
        (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
          (heisD0 (A := ElemDual A) c))).trans
      (scalarDualTransport h0Dual h2Scalar))
        (stokesH2Map (stokes_square₁ (A := A) c w hr hend) x)
      = sourceCup20 hpair (h2A.symm x)

/-- Word-level Stokes cohomology bijections and the noncircular comparison core prove the
three continuous source cup maps bijective. -/
theorem SourceComparisonCore.sourceCupBijections
    {h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker}
    {h1A : H1 Γ A ≃+ WordH1 c w A}
    {h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker}
    {h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)}
    (P : SourceComparisonCore c w hr hend hpair h0A h1A h0Dual h1Dual)
    (hword : StokesCohomologyBijections c w A hr hend) :
    Function.Bijective (sourceCup02 hpair) ∧
      Function.Bijective (sourceCup11 hpair) ∧
      Function.Bijective (sourceCup20 hpair) := by
  let square02 : CohomologyComparisonSquare
      (stokesH0Map (stokes_square₀ (A := A) c w hr hend)) (sourceCup02 hpair) :=
    { left := h0A.symm
      right := (AddEquiv.ofBijective
        (stokesUC0 (heisD1 (A := ElemDual A) c w))
        (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
        (scalarDualTransport P.h2Dual P.h2Scalar)
      commutes := P.square02_commutes }
  let square11 : CohomologyComparisonSquare
      (stokesH1Map (stokes_square₀ (A := A) c w hr hend)
        (stokes_square₁ (A := A) c w hr hend)) (sourceCup11 hpair) :=
    { left := h1A.symm
      right := (AddEquiv.ofBijective
        (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
        (wordH1_target_uc (A := A) c w hr)).trans
        (scalarDualTransport h1Dual P.h2Scalar)
      commutes := P.square11_commutes }
  let square20 : CohomologyComparisonSquare
      (stokesH2Map (stokes_square₁ (A := A) c w hr hend)) (sourceCup20 hpair) :=
    { left := P.h2A.symm
      right := (AddEquiv.ofBijective
        (stokesUC2 (heisD0 (A := ElemDual A) c))
        (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
          (heisD0 (A := ElemDual A) c))).trans
        (scalarDualTransport h0Dual P.h2Scalar)
      commutes := P.square20_commutes }
  exact ⟨square02.source_bijective hword.1,
    square11.source_bijective hword.2.1,
    square20.source_bijective hword.2.2⟩

/-- Representative-level word Stokes duality plus the noncircular comparison core proves all
three continuous source cup products perfect.  In particular, none of these three
bijectivities is an input to this theorem. -/
theorem SourceComparisonCore.sourceCupBijections_of_stokesDuality
    {h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker}
    {h1A : H1 Γ A ≃+ WordH1 c w A}
    {h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker}
    {h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)}
    (P : SourceComparisonCore c w hr hend hpair h0A h1A h0Dual h1Dual)
    (hword : StokesDuality c w A) :
    Function.Bijective (sourceCup02 hpair) ∧
      Function.Bijective (sourceCup11 hpair) ∧
      Function.Bijective (sourceCup20 hpair) :=
  SourceComparisonCore.sourceCupBijections
    (c := c) (w := w) (hr := hr) (hend := hend) (hpair := hpair) P
    ((stokesDuality_iff_cohomologyBijections c w A hr hend).mp hword)

/-- Complete the old source package without assuming Tate perfectness: it is supplied by
word-level Stokes duality through the comparison squares. -/
def SourceComparisonCore.toSourceComparisonPackage
    {h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker}
    {h1A : H1 Γ A ≃+ WordH1 c w A}
    {h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker}
    {h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)}
    (P : SourceComparisonCore c w hr hend hpair h0A h1A h0Dual h1Dual)
    (hword : StokesCohomologyBijections c w A hr hend) :
    SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual := by
  let hcups := SourceComparisonCore.sourceCupBijections
    (c := c) (w := w) (hr := hr) (hend := hend) (hpair := hpair) P hword
  exact
    { h2A := P.h2A
      h2Dual := P.h2Dual
      h2Scalar := P.h2Scalar
      cup02_bijective := hcups.1
      cup11_bijective := hcups.2.1
      cup20_bijective := hcups.2.2
      square02_commutes := P.square02_commutes
      square11_commutes := P.square11_commutes
      square20_commutes := P.square20_commutes }

/-- The same completion theorem with word Stokes duality in its representative-level form. -/
def SourceComparisonCore.toSourceComparisonPackage_of_stokesDuality
    {h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker}
    {h1A : H1 Γ A ≃+ WordH1 c w A}
    {h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker}
    {h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)}
    (P : SourceComparisonCore c w hr hend hpair h0A h1A h0Dual h1Dual)
    (hword : StokesDuality c w A) :
    SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual :=
  SourceComparisonCore.toSourceComparisonPackage
    (c := c) (w := w) (hr := hr) (hend := hend) (hpair := hpair) P
    ((stokesDuality_iff_cohomologyBijections c w A hr hend).mp hword)

/-- A one-target source package proves the three word-cohomology bijections. -/
theorem SourceComparisonPackage.stokesCohomologyBijections
    {h0A : H0 Γ A ≃+ ↥(heisD0 (A := A) c).ker}
    {h1A : H1 Γ A ≃+ WordH1 c w A}
    {h0Dual : H0 Γ (ElemDual A) ≃+ ↥(heisD0 (A := ElemDual A) c).ker}
    {h1Dual : H1 Γ (ElemDual A) ≃+ WordH1 c w (ElemDual A)}
    (P : SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual) :
    StokesCohomologyBijections c w A hr hend := by
  apply stokesCohomologyBijections_of_source_comparison c w A hr hend
    (sourceCup02 hpair)
    (sourceCup11 hpair)
    (sourceCup20 hpair)
    P.cup02_bijective P.cup11_bijective P.cup20_bijective
  · exact
      { left := h0A.symm
        right := (AddEquiv.ofBijective
          (stokesUC0 (heisD1 (A := ElemDual A) c w))
          (stokesUC0_bijective (heisD1 (A := ElemDual A) c w))).trans
          (scalarDualTransport P.h2Dual P.h2Scalar)
        commutes := P.square02_commutes }
  · exact
      { left := h1A.symm
        right := (AddEquiv.ofBijective
          (stokesUC1 (heisD0 (A := ElemDual A) c) (heisD1 (A := ElemDual A) c w))
          (wordH1_target_uc (A := A) c w hr)).trans
          (scalarDualTransport h1Dual P.h2Scalar)
        commutes := P.square11_commutes }
  · exact
      { left := P.h2A.symm
        right := (AddEquiv.ofBijective
          (stokesUC2 (heisD0 (A := ElemDual A) c))
          (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
            (heisD0 (A := ElemDual A) c))).trans
          (scalarDualTransport h0Dual P.h2Scalar)
        commutes := P.square20_commutes }

end Package

/-! ## Specialization to the improved L presentation

All module structures below are canonical.  The source group acts through `rho`; both `A` and
its elementary dual are given the discrete topology; and the scalar action is the unique
trivial action.  These choices are data-free consequences of a finite target representation,
not additional mathematical hypotheses.
-/

section LTarget

/-- Continuity of an action pulled back from a finite discrete quotient. -/
private theorem continuousSMul_comp_finite
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

/--
The source-comparison obligations at one actual `ResolvedPushedHsimp` target.

Unfolding this abbreviation displays a `SourceComparisonPackage` whose `H⁰` and `H¹`
equivalences are definitionally the current formalization's `Count.h0Equiv` and
`Count.h1Equiv_gammaR_range`, on the primal and dual resolvers respectively.
-/
noncomputable abbrev SourceComparisonAt {h q : ℕ}
    (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) (e : ℕ)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
    [TopologicalSpace (WordLift (ElemDual A) C)]
    [DiscreteTopology (WordLift (ElemDual A) C)]
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift A C))
    (hresDual : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift (ElemDual A) C))
    (hend : IsStokesEndpoint (lSqFam h q e)) : Type _ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI actA : DistribMulAction ((gamma h q : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((gamma h q : Type)) A :=
    continuousSMul_comp_finite rho (fun _ _ => rfl)
  letI : TopologicalSpace (ElemDual A) := ⊥
  letI : DiscreteTopology (ElemDual A) := ⟨rfl⟩
  letI : ContinuousSMul ((gamma h q : Type)) (ElemDual A) :=
    continuousSMul_comp_finite rho (fun γ lam => by
      apply ElemDual.ext
      intro a
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (γ⁻¹) • a) = lam ((rho γ)⁻¹ • a)
      rw [map_inv])
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let c : Generator (2 * h + 1) → C :=
    fun g => rho (gammaGen (2 * h + 1) q (lSqW h) g)
  let w : Fin 2 → FreeGroup (Generator (2 * h + 1)) := lSqFam h q e
  let hr : ∀ k, FreeGroup.lift c (w k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres k
  let hcompatA : ∀ (γ : (gamma h q : Type)) (a : A), γ • a = rho γ • a :=
    fun _ _ => rfl
  let hcompatDual : ∀ (γ : (gamma h q : Type)) (lam : ElemDual A),
      γ • lam = rho γ • lam := fun γ lam => by
    apply ElemDual.ext
    intro a
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (γ⁻¹) • a) = lam ((rho γ)⁻¹ • a)
    rw [map_inv]
  let hpair : ∀ (γ : (gamma h q : Type)) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam := by
    intro γ a lam
    rw [scalarActionZmodTwo_triv]
    show (γ • lam) (γ • a) = lam a
    rw [ElemDual.smul_apply, inv_smul_smul]
  let h0A := Count.h0Equiv rho hcompatA (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
  let h1A := Count.h1Equiv_gammaR_range rho hcompatA hres hA₂
  let h0Dual := Count.h0Equiv rho hcompatDual (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
  let h1Dual := Count.h1Equiv_gammaR_range rho hcompatDual hresDual
    (fun lam : ElemDual A => lam.add_self_eq_zero)
  exact SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual

/-- A uniform continuous-cohomology supplier for the L row. -/
def SourceComparisonProvider (h q : ℕ) : Type _ :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((gamma h q : Type)) C) (e : ℕ), Odd e →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
      [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
      [TopologicalSpace (WordLift (ElemDual A) C)]
      [DiscreteTopology (WordLift (ElemDual A) C)],
      (hA₂ : ∀ a : A, a + a = 0) →
      (hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
        (lSqFam h q e) (WordLift A C)) →
      (hresDual : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
        (lSqFam h q e) (WordLift (ElemDual A) C)) →
      (hend : IsStokesEndpoint (lSqFam h q e)) →
      SourceComparisonAt C rho e A hA₂ hres hresDual hend

/-- A uniform provider of the explicit continuous source package proves the exact L residue. -/
theorem resolvedPushedHsimp_of_sourceComparison {h q : ℕ}
    (provider : SourceComparisonProvider h q) : ResolvedPushedHsimp h q := by
  intro C _ _ _ _ rho e he A _ _ _ _ _ _ _ hA₂ hres hresDual hend
  let P := provider C rho e he A hA₂ hres hresDual hend
  -- Reinstall exactly the canonical source structures used by `SourceComparisonAt`.
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI actA : DistribMulAction ((gamma h q : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((gamma h q : Type)) A :=
    continuousSMul_comp_finite rho (fun _ _ => rfl)
  letI : TopologicalSpace (ElemDual A) := ⊥
  letI : DiscreteTopology (ElemDual A) := ⟨rfl⟩
  letI : ContinuousSMul ((gamma h q : Type)) (ElemDual A) :=
    continuousSMul_comp_finite rho (fun γ lam => by
      apply ElemDual.ext
      intro a
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (γ⁻¹) • a) = lam ((rho γ)⁻¹ • a)
      rw [map_inv])
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let c : Generator (2 * h + 1) → C :=
    fun g => rho (gammaGen (2 * h + 1) q (lSqW h) g)
  let w : Fin 2 → FreeGroup (Generator (2 * h + 1)) := lSqFam h q e
  let hr : ∀ k, FreeGroup.lift c (w k) = 1 := fun k =>
    lower_rel (A := A) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres k
  let hcompatA : ∀ (γ : (gamma h q : Type)) (a : A), γ • a = rho γ • a :=
    fun _ _ => rfl
  let hcompatDual : ∀ (γ : (gamma h q : Type)) (lam : ElemDual A),
      γ • lam = rho γ • lam := fun γ lam => by
    apply ElemDual.ext
    intro a
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (γ⁻¹) • a) = lam ((rho γ)⁻¹ • a)
    rw [map_inv]
  let hpair : ∀ (γ : (gamma h q : Type)) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam := by
    intro γ a lam
    rw [scalarActionZmodTwo_triv]
    show (γ • lam) (γ • a) = lam a
    rw [ElemDual.smul_apply, inv_smul_smul]
  let h0A := Count.h0Equiv rho hcompatA (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
  let h1A := Count.h1Equiv_gammaR_range rho hcompatA hres hA₂
  let h0Dual := Count.h0Equiv rho hcompatDual (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
  let h1Dual := Count.h1Equiv_gammaR_range rho hcompatDual hresDual
    (fun lam : ElemDual A => lam.add_self_eq_zero)
  change SourceComparisonPackage c w hr hend hpair h0A h1A h0Dual h1Dual at P
  exact P.stokesCohomologyBijections

end LTarget

end

end GQ2.Dyadic.LSquare
