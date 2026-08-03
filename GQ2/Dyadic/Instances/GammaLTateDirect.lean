/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LSourceComparison

/-!
# Direct Tate-duality assembly from the improved L presentation

This file gives the non-field-theoretic assembly route from the abstract L presentation to
`TateDualityG`.  Its first ingredient is structural: every continuous action on a finite discrete
coefficient module has a canonical finite discrete target, namely the full additive
automorphism group of the coefficient.  This avoids choosing an arbitrary quotient before a
uniform source-comparison provider is applied.

The final constructor consumes
`SourceComparisonCore`, not `SourceComparisonPackage`: continuous cup perfectness is a
conclusion of word Stokes duality and the comparison squares, never an input.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh GQ2.LocalLiftingDuality GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates.LSqStokes

/-! ## The canonical finite action target -/

/-- The additive automorphism group used as a finite action target carries the discrete
topology.  The instance is useful even before finiteness is installed on the coefficient. -/
instance finiteActionTargetTopologicalSpace {M : Type*} [AddCommGroup M] :
    TopologicalSpace (Multiplicative (AddAut M)) := ⊥

/-- The canonical topology on the additive automorphism action target is discrete. -/
instance finiteActionTargetDiscreteTopology {M : Type*} [AddCommGroup M] :
    DiscreteTopology (Multiplicative (AddAut M)) := ⟨rfl⟩

/-- The tautological distributive action of the multiplicative additive-automorphism group. -/
noncomputable instance finiteActionTargetDistribMulAction {M : Type*} [AddCommGroup M] :
    DistribMulAction (Multiplicative (AddAut M)) M where
  smul g m := Multiplicative.toAdd g m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := map_zero (Multiplicative.toAdd g)
  smul_add g := map_add (Multiplicative.toAdd g)

/-- The kernel of the homomorphism to additive automorphisms is the intersection of all point
stabilizers. -/
theorem finiteActionMonoidHom_ker
    {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] :
    ((DistribMulAction.toAddAut G M).ker : Set G) =
      ((⨅ m : M, MulAction.stabilizer G m : Subgroup G) : Set G) := by
  ext g
  change g ∈ (DistribMulAction.toAddAut G M).ker ↔
    g ∈ (⨅ m : M, MulAction.stabilizer G m : Subgroup G)
  rw [Subgroup.mem_iInf]
  change (DistribMulAction.toAddAut G M g = 1) ↔ ∀ m : M, g • m = m
  constructor
  · intro hg m
    exact DFunLike.congr_fun (congrArg Multiplicative.toAdd hg) m
  · intro hg
    apply Multiplicative.ofAdd.injective
    ext m
    exact hg m

/-- The canonical continuous homomorphism recording the action on a finite discrete module.

Its target is finite because `M` is finite.  Continuity follows from continuity of the original
action: the kernel is the finite intersection of its open point stabilizers. -/
noncomputable def finiteActionHom
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] :
    ContinuousMonoidHom G (Multiplicative (AddAut M)) := by
  refine ⟨DistribMulAction.toAddAut G M, ?_⟩
  change Continuous (DistribMulAction.toAddAut G M : G → Multiplicative (AddAut M))
  apply continuous_of_continuousAt_one (DistribMulAction.toAddAut G M)
  rw [ContinuousAt]
  simp only [map_one]
  rw [show nhds (1 : Multiplicative (AddAut M)) = pure 1 from
      congrFun (nhds_discrete (Multiplicative (AddAut M))) 1,
    Filter.tendsto_pure]
  have hker : IsOpen ((DistribMulAction.toAddAut G M).ker : Set G) := by
    rw [finiteActionMonoidHom_ker]
    exact isOpen_iInf_stabilizer (G := G) (M := M)
  exact hker.mem_nhds (Subgroup.one_mem _)

/-- The action pulled back through `finiteActionHom` is definitionally the original action. -/
@[simp] theorem finiteActionHom_smul
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (g : G) (m : M) : finiteActionHom (G := G) (M := M) g • m = g • m := rfl

/-! ## Coefficient transport for the three Tate cups -/

section CupTransport

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction G (ElemDual A)] [ContinuousSMul G (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

variable
  (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
  (hpair : ∀ (g : G) (a : A) (lam : ElemDual A),
    dualEval A (g • a) (g • lam) = g • dualEval A a lam)

/-- Coefficient naturality of the Tate `(0,2)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

This is a representative calculation only; it assumes no duality or finiteness of cohomology. -/
theorem H2congr_cup02_muDualPairing
    (c : H0 G (MuDual 2 A)) (d : H2 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup02 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H0congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨b, rfl⟩ := H2mk_surjective (G := G) (M := A) d
  rw [cup02_mk_mk, cup02_mk_mk, H2congr_mk]
  congr 1

/-- Coefficient naturality of the Tate `(1,1)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

The equality is proved on two `H¹` representatives and introduces no mathematical hypothesis. -/
theorem H2congr_cup11_muDualPairing
    (c : H1 G (MuDual 2 A)) (d : H1 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup11 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H1congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := G) (M := MuDual 2 A) c
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := G) (M := A) d
  rw [H1congr_mk, cup11_mk_mk, cup11_mk_mk, H2congr_mk]
  congr 1

/-- Coefficient naturality of the Tate `(2,0)` cup under
`MuDual 2 A ≃ ElemDual A` and `MuN 2 ≃ ZMod 2`.

As in the other degrees, this is the direct normalized-cocycle computation. -/
theorem H2congr_cup20_muDualPairing
    (c : H2 G (MuDual 2 A)) (d : H0 G A) :
    H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
        (cup20 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c d) =
      cup20 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H2congr dualAddEquiv (edEquivariantG hpair htriv) c) d := by
  obtain ⟨a, rfl⟩ := H2mk_surjective (G := G) (M := MuDual 2 A) c
  rw [H2congr_mk, cup20_mk_mk, cup20_mk_mk, H2congr_mk]
  congr 1

end CupTransport

/-! ## A no-cup provider for the L presentation -/

/-- Bijectivity is unchanged when both arguments and values of a curried pairing are
transported through additive equivalences. -/
theorem pairing_bijective_of_transport
    {X Y V H S : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup V]
    [AddCommGroup H] [AddCommGroup S]
    (e : X ≃+ Y) (tau : H ≃+ S) (Psi : Y →+ V →+ H) (F : X → V →+ S)
    (hPsi : Function.Bijective Psi)
    (hF : ∀ x v, F x v = tau (Psi (e x) v)) : Function.Bijective F := by
  constructor
  · intro x y hxy
    apply e.injective
    apply hPsi.1
    ext v
    apply tau.injective
    have hv := DFunLike.congr_fun hxy v
    rw [hF x v, hF y v] at hv
    exact hv
  · intro f
    let fH : V →+ H := tau.symm.toAddMonoidHom.comp f
    obtain ⟨y, hy⟩ := hPsi.2 fH
    refine ⟨e.symm y, ?_⟩
    ext v
    rw [hF]
    have hv := DFunLike.congr_fun hy v
    rw [e.apply_symm_apply]
    change tau (Psi y v) = f v
    rw [hv]
    exact tau.apply_symm_apply (f v)

/-- The canonical action on the elementary dual of a finite discrete continuous module is
continuous.  The proof factors it through `finiteActionHom`. -/
@[reducible] noncomputable def finiteElemDualContinuousSMul
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)] :
    ContinuousSMul G (ElemDual M) := by
  constructor
  let rho : ContinuousMonoidHom G (Multiplicative (AddAut M)) := finiteActionHom
  have hcompat : ∀ (g : G) (lam : ElemDual M), g • lam = rho g • lam := by
    intro g lam
    apply ElemDual.ext
    intro m
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (g⁻¹) • m) = lam ((rho g)⁻¹ • m)
    rw [map_inv]
  have hfac : (fun p : G × ElemDual M => p.1 • p.2) =
      (fun p : Multiplicative (AddAut M) × ElemDual M => p.1 • p.2) ∘
        (fun p : G × ElemDual M => (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- Evaluation against the contragredient elementary dual is equivariant into a trivial
`ZMod 2`-module. -/
theorem dualEval_equivariant_of_trivial
    {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction G (ZMod 2)]
    (htriv : ∀ (g : G) (s : ZMod 2), g • s = s) :
    ∀ (g : G) (m : M) (lam : ElemDual M),
      dualEval M (g • m) (g • lam) = g • dualEval M m lam := by
  intro g m lam
  rw [dualEval_apply, ElemDual.smul_apply, inv_smul_smul, dualEval_apply, htriv]

/-- The images of the improved L generators in the canonical finite action target. -/
noncomputable def finiteActionGenerators (h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    Generator (2 * h + 1) → Multiplicative (AddAut M) :=
  fun i => finiteActionHom (G := (gamma h q : Type)) (M := M)
    (gammaGen (2 * h + 1) q (lSqW h) i)

/-- The coefficient-wise contents of the uniform provider.  It contains degree-zero and
degree-one identifications only so that the `SourceComparisonCore` can be stated; the actual
mathematical hypotheses are the core and an independently proved word `StokesDuality`.
There is deliberately no continuous cup-perfectness field. -/
structure LNoCupModuleData (h q e : ℕ) (hq : Even q) (he : Odd e)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul ((gamma h q : Type)) (ElemDual M)]
    [TopologicalSpace (WordLift M (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift M (Multiplicative (AddAut M)))]
    [TopologicalSpace (WordLift (ElemDual M) (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift (ElemDual M) (Multiplicative (AddAut M)))]
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s)
    (invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2) where
  /-- Death of the two improved L relators in the action target. -/
  relator_death : ∀ k, FreeGroup.lift (finiteActionGenerators h q M) (lSqFam h q e k) = 1
  /-- The already-proved degree-zero comparison, primal side. -/
  h0M : H0 (gamma h q : Type) M ≃+
    ↥(heisD0 (A := M) (finiteActionGenerators h q M)).ker
  /-- The already-proved degree-one comparison, primal side. -/
  h1M : H1 (gamma h q : Type) M ≃+
    WordH1 (finiteActionGenerators h q M) (lSqFam h q e) M
  /-- The already-proved degree-zero comparison, dual side. -/
  h0Dual : H0 (gamma h q : Type) (ElemDual M) ≃+
    ↥(heisD0 (A := ElemDual M) (finiteActionGenerators h q M)).ker
  /-- The already-proved degree-one comparison, dual side. -/
  h1Dual : H1 (gamma h q : Type) (ElemDual M) ≃+
    WordH1 (finiteActionGenerators h q M) (lSqFam h q e) (ElemDual M)
  /-- The three `H²` comparisons and comparison squares, but no cup perfectness. -/
  core : SourceComparisonCore (finiteActionGenerators h q M) (lSqFam h q e)
    relator_death (lSq_isStokesEndpoint hq he)
    (dualEval_equivariant_of_trivial htriv) h0M h1M h0Dual h1Dual
  /-- Every coefficient uses the provider's one common scalar orientation. -/
  scalar_eq : core.h2Scalar = invZ
  /-- Word Stokes duality, proved independently of continuous Tate duality. -/
  stokes : StokesDuality (finiteActionGenerators h q M) (lSqFam h q e) M

set_option maxHeartbeats 800000 in
/-- A uniform source provider for every finite exponent-two module.  Its only scalar datum is
one common orientation, and its coefficient-wise output is `LNoCupModuleData`. -/
structure LNoCupTateProviderCore (h q e : ℕ) (hq : Even q) (he : Odd e)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)] where
  /-- The common scalar orientation. -/
  invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2
  /-- Triviality of the fixed scalar action. -/
  htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s
  /-- Uniform noncircular comparison and independent Stokes data. -/
  moduleData : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul ((gamma h q : Type)) (ElemDual M)]
    [TopologicalSpace (WordLift M (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift M (Multiplicative (AddAut M)))]
    [TopologicalSpace (WordLift (ElemDual M) (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift (ElemDual M) (Multiplicative (AddAut M)))],
    (∀ m : M, m + m = 0) →
      LNoCupModuleData (h := h) (q := q) (e := e) hq he M htriv invZ

/-- The public provider fixes the scalar topology and action canonically. -/
noncomputable abbrev LNoCupTateProvider (h q e : ℕ) (hq : Even q) (he : Odd e) : Type _ := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  exact LNoCupTateProviderCore h q e hq he

/-! ## Direct assembly of the three Tate cup clauses -/

set_option maxHeartbeats 800000 in
/-- One coefficient-wise provider output gives the three cup clauses in the exact
`MuDual`/`MuN` spelling of `TateDualityG`.  Continuous source-cup bijectivity is first deduced
from word Stokes duality, then transposed using cup symmetry, and only then transported through
`dualAddEquiv` and `muNTwoEquiv`. -/
theorem LNoCupModuleData.tateCupBijections
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    [TopologicalSpace (ElemDual M)] [DiscreteTopology (ElemDual M)]
    [ContinuousSMul ((gamma h q : Type)) (ElemDual M)]
    [TopologicalSpace (WordLift M (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift M (Multiplicative (AddAut M)))]
    [TopologicalSpace (WordLift (ElemDual M) (Multiplicative (AddAut M)))]
    [DiscreteTopology (WordLift (ElemDual M) (Multiplicative (AddAut M)))]
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (htriv : ∀ (g : (gamma h q : Type)) (s : ZMod 2), g • s = s)
    (invZ : H2 (gamma h q : Type) (ZMod 2) ≃+ ZMod 2)
    (hMtwo : ∀ m : M, m + m = 0)
    (Q : LNoCupModuleData h q e hq he M htriv invZ) :
    Function.Bijective (fun c : H0 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H1 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H2 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).trans invZ).toAddMonoidHom.comp
        (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) := by
  let hpair := dualEval_equivariant_of_trivial (M := M) htriv
  let hcups := SourceComparisonCore.sourceCupBijections_of_stokesDuality
    (c := finiteActionGenerators h q M) (w := lSqFam h q e)
    (hr := Q.relator_death) (hend := lSq_isStokesEndpoint hq he)
    (hpair := hpair) Q.core Q.stokes
  letI : Finite (H0 (gamma h q : Type) M) :=
    Finite.of_equiv _ Q.h0M.symm.toEquiv
  letI : Finite (H1 (gamma h q : Type) M) :=
    Finite.of_equiv _ Q.h1M.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) M) :=
    Finite.of_equiv _ Q.core.h2A.symm.toEquiv
  letI : Finite (H0 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ Q.h0Dual.symm.toEquiv
  letI : Finite (H1 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ Q.h1Dual.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) (ElemDual M)) :=
    Finite.of_equiv _ Q.core.h2Dual.symm.toEquiv
  letI : Finite (H2 (gamma h q : Type) (ZMod 2)) :=
    Finite.of_equiv _ invZ.symm.toEquiv
  let e0 := H0congr dualAddEquiv (edEquivariantG hpair htriv)
  let e1 := H1congr dualAddEquiv (edEquivariantG hpair htriv)
  let e2 := H2congr dualAddEquiv (edEquivariantG hpair htriv)
  let psi02 := cup02 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  let psi11 := cup11 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  let psi20 := cup20 (dualEval M).flip (flip_equivariant (dualEval M) hpair)
  have hpsi02 : Function.Bijective psi02 := by
    apply transpose_bijective_of_bijective
      (H2_two_torsionG hMtwo)
      (fun x : H0 (gamma h q : Type) (ElemDual M) =>
        Subtype.ext (by simpa using ElemDual.add_self_eq_zero x.1))
      invZ (cup20 (dualEval M) hpair) psi02 hcups.2.2
    intro v w
    exact (cup20_eq_cup02_flip (dualEval M) hpair v w).symm
  have hpsi11 : Function.Bijective psi11 := by
    apply transpose_bijective_of_bijective
      (H1_two_torsionG hMtwo) (H1_two_torsionG ElemDual.add_self_eq_zero)
      invZ (cup11 (dualEval M) hpair) psi11 hcups.2.1
    intro v w
    exact (cup11_comm (dualEval M) hpair
      (fun s : ZMod 2 => CharTwo.add_self_eq_zero s) v w).symm
  have hpsi20 : Function.Bijective psi20 := by
    apply transpose_bijective_of_bijective
      (fun x : H0 (gamma h q : Type) M => Subtype.ext (by simpa using hMtwo x.1))
      (H2_two_torsionG ElemDual.add_self_eq_zero)
      invZ (cup02 (dualEval M) hpair) psi20 hcups.1
    intro v w
    exact (cup02_eq_cup20_flip (dualEval M) hpair v w).symm
  constructor
  · apply pairing_bijective_of_transport e0 invZ psi02 _ hpsi02
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup02 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e0 c) d)
    rw [H2congr_cup02_muDualPairing htriv hpair]
  constructor
  · apply pairing_bijective_of_transport e1 invZ psi11 _ hpsi11
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup11 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e1 c) d)
    rw [H2congr_cup11_muDualPairing htriv hpair]
  · apply pairing_bijective_of_transport e2 invZ psi20 _ hpsi20
    intro c d
    change invZ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)
      (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c d)) =
        invZ (cup20 (dualEval M).flip (flip_equivariant (dualEval M) hpair) (e2 c) d)
    rw [H2congr_cup20_muDualPairing htriv hpair]

set_option maxHeartbeats 800000 in
/-- Apply a uniform provider to an arbitrary finite continuous exponent-two module.  The
elementary-dual continuity and both word-lift topologies are installed canonically here, so the
caller sees exactly the coefficient signature quantified by `TateDualityG`. -/
theorem LNoCupTateProviderCore.tateCupBijections
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateProviderCore h q e hq he)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hMtwo : ∀ m : M, m + m = 0) :
    Function.Bijective (fun c : H0 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG P.htriv)).trans
        P.invZ).toAddMonoidHom.comp
          (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H1 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG P.htriv)).trans
        P.invZ).toAddMonoidHom.comp
          (cup11 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) ∧
    Function.Bijective (fun c : H2 (gamma h q : Type) (MuDual 2 M) =>
      ((H2congr muNTwoEquiv (muNTwoEquiv_equivariantG P.htriv)).trans
        P.invZ).toAddMonoidHom.comp
          (cup20 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)) := by
  letI : TopologicalSpace (ElemDual M) := ⊥
  letI : DiscreteTopology (ElemDual M) := ⟨rfl⟩
  letI : ContinuousSMul ((gamma h q : Type)) (ElemDual M) :=
    finiteElemDualContinuousSMul
  letI : TopologicalSpace (WordLift M (Multiplicative (AddAut M))) := ⊥
  letI : DiscreteTopology (WordLift M (Multiplicative (AddAut M))) := ⟨rfl⟩
  letI : TopologicalSpace (WordLift (ElemDual M) (Multiplicative (AddAut M))) := ⊥
  letI : DiscreteTopology (WordLift (ElemDual M) (Multiplicative (AddAut M))) := ⟨rfl⟩
  let Q := P.moduleData M hMtwo
  exact Q.tateCupBijections P.htriv P.invZ hMtwo

/-- The final direct constructor: a common scalar orientation, noncircular L comparison cores,
and independent word Stokes duality for all finite exponent-two modules imply the full
`TateDualityG` bundle. -/
noncomputable def tateDualityG_of_lNoCupTateProviderCore
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
    [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateProviderCore h q e hq he) :
    TateDualityG (gamma h q : Type) 2 where
  inv := (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG P.htriv)).trans P.invZ
  perfect02 := by
    intro M _ _ _ _ _ _ htor
    have hMtwo : ∀ m : M, m + m = 0 := fun m => by
      simpa only [two_nsmul] using htor m
    exact (P.tateCupBijections M hMtwo).1
  perfect11 := by
    intro M _ _ _ _ _ _ htor
    have hMtwo : ∀ m : M, m + m = 0 := fun m => by
      simpa only [two_nsmul] using htor m
    exact (P.tateCupBijections M hMtwo).2.1
  perfect20 := by
    intro M _ _ _ _ _ _ htor
    have hMtwo : ∀ m : M, m + m = 0 := fun m => by
      simpa only [two_nsmul] using htor m
    exact (P.tateCupBijections M hMtwo).2.2

/-- Public wrapper using the canonical discrete/trivial `ZMod 2` coefficient structure. -/
noncomputable def tateDualityG_of_lNoCupTateProvider
    {h q e : ℕ} {hq : Even q} {he : Odd e}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (P : LNoCupTateProvider h q e hq he) : TateDualityG (gamma h q : Type) 2 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  change LNoCupTateProviderCore h q e hq he at P
  exact tateDualityG_of_lNoCupTateProviderCore P

/-! ## Mathematical frontier

For every finite exponent-two `G`-module `M`, `LNoCupTateProvider` applies the L provider with

* `C := Multiplicative (AddAut M)`,
* `rho := finiteActionHom`, and
* the tautological target action above.

The provider returns a `SourceComparisonCore` and an independently proved word
`StokesDuality`, sharing a scalar orientation `H²(G, ZMod 2) ≃+ ZMod 2`.  The theorem
`SourceComparisonCore.sourceCupBijections_of_stokesDuality` proves the three continuous
evaluation-cup maps perfect.  `transpose_bijective_of_bijective` and cup symmetry reverse the
currying, after which `dualAddEquiv`/`edEquivariantG` and
`muNTwoEquiv`/`muNTwoEquiv_equivariantG` transport the result to the exact `MuDual` and `MuN`
spelling of `TateDualityG`.  This entire assembly is implemented by
`tateDualityG_of_lNoCupTateProvider`.

Thus the remaining mathematical data are the all-coefficient `H²` comparisons, a scalar
orientation/trace proved without Tate duality, and independent word Stokes duality.  No
coefficient-congruence calculation remains hidden in an assumed cup-perfectness field here.
-/

end


end GQ2.Dyadic.LSquare
