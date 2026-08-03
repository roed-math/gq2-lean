/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleNaturality
import GQ2.Dyadic.Instances.LFlexibleH2

/-!
# Continuous-cup/word-Stokes comparison squares

The edge comparison squares do not require a new presentation calculation.  They reduce to
coefficient naturality of the module obstruction and one scalar orientation identity: the
chosen scalar `H²` orientation must read a cocycle as the trace of its relator obstruction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Count

section EdgeSquares

variable {Gamma C A : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A] [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Gamma (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [DistribMulAction Gamma (ZMod 2)]
  [ContinuousSMul Gamma (ZMod 2)] [DistribMulAction C (ZMod 2)]
  {iota rel : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]

/-- The single scalar orientation identity needed by both edge squares: the scalar `H²`
coordinate is the trace of the choice-independent relator obstruction. -/
def ScalarTraceCompatible (W : rel → PWord iota) (gen : iota → Gamma)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompatScalar : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (h2Scalar : H2 Gamma (ZMod 2) ≃+ ZMod 2) : Prop :=
  ∀ f : Z2 Gamma (ZMod 2),
    h2Scalar (H2mk Gamma (ZMod 2) f) =
      ∑ k, moduleObsFun W gen rho hcompatScalar f k

/-- The `(0,2)` source comparison square follows from the representative formula for the
dual-valued `H²` comparison and scalar trace compatibility. -/
theorem square02_commutes_of_scalarTrace
    (W : rel → PWord iota) (gen : iota → Gamma)
    (rho : ContinuousMonoidHom Gamma C)
    (w : rel → FreeGroup iota)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hend : IsStokesEndpoint w)
    (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam)
    (h0A : H0 Gamma A ≃+ ↥(heisD0 (A := A) (fun i ↦ rho (gen i))).ker)
    (h0A_coe : ∀ x,
      ((h0A.symm x : H0 Gamma A) : A) = (x : A))
    (h2Dual : H2 Gamma (ElemDual A) ≃+
      WordH2 (fun i ↦ rho (gen i)) w (ElemDual A))
    (h2Dual_mk : ∀ f : Z2 Gamma (ElemDual A),
      h2Dual (H2mk Gamma (ElemDual A) f) =
        QuotientAddGroup.mk'
          (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w).range
          (moduleObsFam W gen rho hcompatDual f))
    (h2Scalar : H2 Gamma (ZMod 2) ≃+ ZMod 2)
    (htrace : ScalarTraceCompatible W gen rho hcompatScalar h2Scalar) :
    ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC0 (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))
          (stokesUC0_bijective
            (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))).trans
        (scalarDualTransport h2Dual h2Scalar))
          (stokesH0Map
            (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup02 hpair (h0A.symm x) := by
  intro x
  ext u
  obtain ⟨f, rfl⟩ := H2mk_surjective (G := Gamma) (M := ElemDual A) u
  apply h2Scalar.injective
  rw [show h2Scalar
      (sourceCup02 hpair (h0A.symm x) (H2mk Gamma (ElemDual A) f)) =
        ∑ k, moduleObsFun W gen rho hcompatScalar
          ⟨cup02Fun (dualEval A) (h0A.symm x).1 f.1,
            cup02_mem_Z2 (dualEval A) hpair (h0A.symm x) f⟩ k by
      exact htrace _]
  rw [moduleObsFun_cup02 W gen rho hcompatDual hcompatScalar hpair]
  simp only [h0A_coe]
  change h2Scalar (h2Scalar.symm
      (stokesUC0 (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w)
        (stokesH0Map
          (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        (h2Dual (H2mk Gamma (ElemDual A) f)))) = _
  rw [h2Scalar.apply_symm_apply, h2Dual_mk]
  rfl

/-- The `(2,0)` source comparison square follows from the representative formula for the
primal-valued `H²` comparison and the same scalar trace compatibility. -/
theorem square20_commutes_of_scalarTrace
    (W : rel → PWord iota) (gen : iota → Gamma)
    (rho : ContinuousMonoidHom Gamma C)
    (w : rel → FreeGroup iota)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatScalar : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hend : IsStokesEndpoint w)
    (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam)
    (h0Dual : H0 Gamma (ElemDual A) ≃+
      ↥(heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))).ker)
    (h0Dual_coe : ∀ lam,
      ((h0Dual lam : ↥(heisD0 (A := ElemDual A)
        (fun i ↦ rho (gen i))).ker) : ElemDual A) = (lam : ElemDual A))
    (h2A : H2 Gamma A ≃+ WordH2 (fun i ↦ rho (gen i)) w A)
    (h2A_mk : ∀ f : Z2 Gamma A,
      h2A (H2mk Gamma A f) =
        QuotientAddGroup.mk'
          (heisD1 (A := A) (fun i ↦ rho (gen i)) w).range
          (moduleObsFam W gen rho hcompatA f))
    (h2Scalar : H2 Gamma (ZMod 2) ≃+ ZMod 2)
    (htrace : ScalarTraceCompatible W gen rho hcompatScalar h2Scalar) :
    ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC2 (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))))
          (stokesUC2_bijective ElemDual.add_self_eq_zero wordDual_two_torsion
            (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i))))).trans
        (scalarDualTransport h0Dual h2Scalar))
          (stokesH2Map
            (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup20 hpair (h2A.symm x) := by
  intro x
  obtain ⟨f, hf⟩ := H2mk_surjective (G := Gamma) (M := A) (h2A.symm x)
  have hx : x = h2A (H2mk Gamma A f) := by
    rw [hf, h2A.apply_symm_apply]
  rw [hx, h2A.symm_apply_apply]
  ext lam
  apply h2Scalar.injective
  rw [show h2Scalar
      (sourceCup20 hpair (H2mk Gamma A f) lam) =
        ∑ k, moduleObsFun W gen rho hcompatScalar
          ⟨cup20Fun (dualEval A) f.1 lam.1,
            cup20_mem_Z2 (dualEval A) hpair f lam⟩ k by
      exact htrace _]
  rw [moduleObsFun_cup20 W gen rho hcompatA hcompatScalar hpair]
  change h2Scalar (h2Scalar.symm
      (stokesUC2 (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i)))
        (stokesH2Map
          (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend)
          (h2A (H2mk Gamma A f)))
        (h0Dual lam))) = _
  rw [h2Scalar.apply_symm_apply, h2A_mk]
  change (h0Dual lam : ElemDual A) (∑ k, moduleObsFun W gen rho hcompatA f k) = _
  rw [h0Dual_coe, map_sum]

end EdgeSquares

end

end GQ2.Dyadic.LSquare
