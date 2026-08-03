/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleHeisenberg
import GQ2.Dyadic.Instances.LComparisonSquares

/-!
# The global mixed cup/Heisenberg obstruction identity

The dual-first flipped `(1,1)` cup is the pullback of `moduleKappaHeis` along the graph of its
two `Z¹` representatives.  Reading the global module obstruction at that graph's finite kernel
therefore identifies every intrinsic relator fibre with its Heisenberg central coordinate.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic ContCoh

section GlobalMixed

variable {iota rel : Type*}
  {Gamma C A : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction Gamma A] [ContinuousSMul Gamma A]
  [DistribMulAction C A]
  [TopologicalSpace (ElemDual A)] [IsTopologicalAddGroup (ElemDual A)]
  [DiscreteTopology (ElemDual A)] [ContinuousSMul Gamma (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [DistribMulAction Gamma (ZMod 2)]
  [ContinuousSMul Gamma (ZMod 2)] [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]

local instance mixedScalarAction :
    DistribMulAction (WordLift (A × ElemDual A) C) (ZMod 2) :=
  scalarActionZmodTwo _

local instance mixedHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance mixedHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The graph homomorphism of a primal and dual `1`-cocycle into the base of the
Heisenberg extension. -/
noncomputable def mixedPairHom (rho : ContinuousMonoidHom Gamma C)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (a : Z1 Gamma A) (b : Z1 Gamma (ElemDual A)) :
    ContinuousMonoidHom Gamma (WordLift (A × ElemDual A) C) where
  toFun g := ⟨(a.1 g, b.1 g), rho g⟩
  map_one' := WordLift.ext (Prod.ext (Z1_apply_one a) (Z1_apply_one b)) (map_one rho)
  map_mul' g h := by
    refine WordLift.ext (Prod.ext ?_ ?_) (map_mul rho g h)
    · show a.1 (g * h) = a.1 g + rho g • a.1 h
      rw [(mem_Z1_iff.mp a.2).2 g h, hcompatA]
    · show b.1 (g * h) = b.1 g + rho g • b.1 h
      rw [(mem_Z1_iff.mp b.2).2 g h, hcompatDual]
  continuous_toFun := by
    have hcont : Continuous fun g : Gamma =>
        (((a.1 g, b.1 g), rho g) : (A × ElemDual A) × C) :=
      (((mem_Z1_iff.mp a.2).1).prodMk ((mem_Z1_iff.mp b.2).1)).prodMk
        rho.continuous_toFun
    exact (continuous_of_discreteTopology (f :=
      (WordLift.equivProd (A := A × ElemDual A) (C := C)).symm)).comp hcont

/-- The dual-first flipped cup cocycle is pointwise the Heisenberg cocycle pulled back along
the graph homomorphism. -/
theorem cup11Flip_eq_moduleKappaHeis
    (rho : ContinuousMonoidHom Gamma C)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (a : Z1 Gamma A) (b : Z1 Gamma (ElemDual A)) (g h : Gamma) :
    cup11Fun (dualEval A).flip b.1 a.1 (g, h) =
      (moduleKappaHeis (A := A) (C := C)).κ
        (mixedPairHom rho hcompatA hcompatDual a b g)
        (mixedPairHom rho hcompatA hcompatDual a b h) := by
  change b.1 g (g • a.1 h) = b.1 g (rho g • a.1 h)
  rw [hcompatA]

/-- **Mixed cup/Heisenberg identity.**  The global scalar module obstruction of the
dual-first flipped `(1,1)` cup is the vector of central coordinates of the Heisenberg-evaluated
intrinsic relators. -/
theorem moduleObsFun_cup11Flip (W : rel → PWord iota) (gen : iota → Gamma)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam)
    (a : Z1 Gamma A) (b : Z1 Gamma (ElemDual A)) :
    moduleObsFun W gen rho hcompatScalar
        ⟨cup11Fun (dualEval A).flip b.1 a.1,
          cup11_mem_Z2 (dualEval A).flip (flip_equivariant (dualEval A) hpair) b a⟩ =
      fun k ↦ (PWord.eval
        (heisGen (fun i ↦ rho (gen i)) (fun i ↦ a.1 (gen i))
          (fun i ↦ b.1 (gen i))) (W k)).z := by
  let H := mixedPairHom rho hcompatA hcompatDual a b
  let V := kerON H
  have hV : V.toSubgroup ≤ rho.toMonoidHom.ker := by
    intro g hg
    have hHg : H g = 1 := hg
    exact congrArg WordLift.g hHg
  let rhoV := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) rhoV
  let Hbar : (Gamma ⧸ V.toSubgroup) →* WordLift (A × ElemDual A) C :=
    QuotientGroup.lift V.toSubgroup H.toMonoidHom (by
      intro g hg
      exact hg)
  have hHbarmk : ∀ g : Gamma, Hbar (QuotientGroup.mk' V.toSubgroup g) = H g :=
    fun g ↦ QuotientGroup.lift_mk' _ _ _
  have hsmul : ∀ (g : Gamma ⧸ V.toSubgroup) (s : ZMod 2),
      g • s = Hbar g • s := by
    intro g s
    rw [smul_zmod2, smul_zmod2]
  let z := (moduleKappaHeis (A := A) (C := C)).comap Hbar hsmul
  let f : Z2 Gamma (ZMod 2) :=
    ⟨cup11Fun (dualEval A).flip b.1 a.1,
      cup11_mem_Z2 (dualEval A).flip (flip_equivariant (dualEval A) hpair) b a⟩
  have hf11 : f.1 (1, 1) = 0 := by
    change dualEval A (1 • a.1 1) (b.1 1) = 0
    rw [one_smul, Z1_apply_one a, Z1_apply_one b, dualEval_apply, map_zero]
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := z
      hfact := by
        intro g h
        simp only [z, ModuleTwoCocycle.comap_κ]
        change moduleNormalize f.1 (g, h) =
          (moduleKappaHeis (A := A) (C := C)).κ
            (Hbar (QuotientGroup.mk' V.toSubgroup g))
            (Hbar (QuotientGroup.mk' V.toSubgroup h))
        rw [hHbarmk, hHbarmk, ← cup11Flip_eq_moduleKappaHeis rho hcompatA hcompatDual a b]
        simp only [moduleNormalize]
        rw [smul_zmod2, hf11, sub_zero] }
  rw [moduleObsFun_eq W gen rho hcompatScalar f F]
  funext k
  change moduleRel (W k) (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z = _
  rw [← moduleRel_comap (W k) (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))
    (moduleKappaHeis (A := A) (C := C)) Hbar hsmul]
  have hm : (fun i ↦ Hbar (QuotientGroup.mk' V.toSubgroup (gen i))) =
      heisBase (fun i ↦ rho (gen i)) (fun i ↦ a.1 (gen i))
        (fun i ↦ b.1 (gen i)) := by
    funext i
    rw [hHbarmk]
    rfl
  rw [hm, moduleRel_moduleKappaHeis]

end GlobalMixed

end

end GQ2.Dyadic.Count

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Count

section MixedSquare

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
  [TopologicalSpace (WordLift (A × ElemDual A) C)]
  [DiscreteTopology (WordLift (A × ElemDual A) C)]
  {iota rel : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]

local instance comparisonHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance comparisonHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The full `(1,1)` comparison square follows from scalar trace compatibility, representative
formulas for the two `H¹` comparisons, and a resolution of the intrinsic relators in the common
Heisenberg target. -/
theorem square11_commutes_of_scalarTrace
    (W : rel → PWord iota) (gen : iota → Gamma)
    (rho : ContinuousMonoidHom Gamma C)
    (w : rel → FreeGroup iota)
    (hcompatA : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hcompatDual : ∀ (g : Gamma) (lam : ElemDual A), g • lam = rho g • lam)
    (hcompatScalar : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hend : IsStokesEndpoint w)
    (hresHeis : ResolvesAt W w (HeisLift A C))
    (hpair : ∀ (g : Gamma) (a : A) (lam : ElemDual A),
      dualEval A (g • a) (g • lam) = g • dualEval A a lam)
    (h1A : H1 Gamma A ≃+ WordH1 (fun i ↦ rho (gen i)) w A)
    (h1Dual : H1 Gamma (ElemDual A) ≃+
      WordH1 (fun i ↦ rho (gen i)) w (ElemDual A))
    (za : Z1 Gamma A →
      ↥(heisD1 (A := A) (fun i ↦ rho (gen i)) w).ker)
    (zb : Z1 Gamma (ElemDual A) →
      ↥(heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w).ker)
    (za_coe : ∀ a, (za a : iota → A) = fun i ↦ a.1 (gen i))
    (zb_coe : ∀ b, (zb b : iota → ElemDual A) = fun i ↦ b.1 (gen i))
    (h1A_mk : ∀ a, h1A (H1mk Gamma A a) =
      stokesH1Mk _ _ (za a))
    (h1Dual_mk : ∀ b, h1Dual (H1mk Gamma (ElemDual A) b) =
      stokesH1Mk _ _ (zb b))
    (h2Scalar : H2 Gamma (ZMod 2) ≃+ ZMod 2)
    (htrace : ScalarTraceCompatible W gen rho hcompatScalar h2Scalar) :
    ∀ x,
      ((AddEquiv.ofBijective
          (stokesUC1
            (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i)))
            (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w))
          (wordH1_target_uc (A := A) (fun i ↦ rho (gen i)) w hr)).trans
        (scalarDualTransport h1Dual h2Scalar))
          (stokesH1Map
            (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend)
            (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend) x)
        = sourceCup11 hpair (h1A.symm x) := by
  intro x
  obtain ⟨a, ha⟩ := H1mk_surjective (G := Gamma) (M := A) (h1A.symm x)
  have hx : x = h1A (H1mk Gamma A a) := by
    rw [ha, h1A.apply_symm_apply]
  rw [hx, h1A.symm_apply_apply]
  ext u
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := Gamma) (M := ElemDual A) u
  apply h2Scalar.injective
  rw [show sourceCup11 hpair (H1mk Gamma A a) (H1mk Gamma (ElemDual A) b) =
      cup11 (dualEval A).flip (flip_equivariant (dualEval A) hpair)
        (H1mk Gamma (ElemDual A) b) (H1mk Gamma A a) by
    exact cup11_comm (dualEval A) hpair (fun s : ZMod 2 ↦ CharTwo.add_self_eq_zero s)
      (H1mk Gamma A a) (H1mk Gamma (ElemDual A) b)]
  rw [cup11_mk_mk]
  rw [show h2Scalar
      (H2mk Gamma (ZMod 2)
        ⟨cup11Fun (dualEval A).flip b.1 a.1,
          cup11_mem_Z2 (dualEval A).flip (flip_equivariant (dualEval A) hpair) b a⟩) =
        ∑ k, moduleObsFun W gen rho hcompatScalar
          ⟨cup11Fun (dualEval A).flip b.1 a.1,
            cup11_mem_Z2 (dualEval A).flip (flip_equivariant (dualEval A) hpair) b a⟩ k by
      exact htrace _]
  rw [moduleObsFun_cup11Flip W gen rho hcompatA hcompatDual hcompatScalar hpair]
  change h2Scalar (h2Scalar.symm
      (stokesUC1
        (heisD0 (A := ElemDual A) (fun i ↦ rho (gen i)))
        (heisD1 (A := ElemDual A) (fun i ↦ rho (gen i)) w)
        (stokesH1Map
          (stokes_square₀ (A := A) (fun i ↦ rho (gen i)) w hr hend)
          (stokes_square₁ (A := A) (fun i ↦ rho (gen i)) w hr hend)
          (h1A (H1mk Gamma A a)))
        (h1Dual (H1mk Gamma (ElemDual A) b)))) = _
  rw [h2Scalar.apply_symm_apply, h1A_mk, h1Dual_mk]
  change heisEta1 (fun i ↦ rho (gen i)) w (za a).1 (zb b).1 = _
  rw [za_coe, zb_coe]
  simp only [heisEta1_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg HeisLift.z
    (hresHeis
      (heisGen (fun i ↦ rho (gen i)) (fun i ↦ a.1 (gen i))
        (fun i ↦ b.1 (gen i))) k)

end MixedSquare

end

end GQ2.Dyadic.LSquare
