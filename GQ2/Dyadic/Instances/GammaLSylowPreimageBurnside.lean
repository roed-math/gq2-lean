/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageSchreier
import Mathlib.GroupTheory.Transfer

/-!
# A finite Burnside-transfer criterion for the GammaL Sylow-preimage kernel

The normal-core reduction leaves a finite `2`-residual separation theorem.  This file gives a
strictly more concrete sufficient condition at each `V ◁ₒ U`.

Embed `V` in `GammaL` and take its *normal closure* `N`.  Three finite checks suffice:

1. `N ∩ U = V`, so ambient normal closure introduces no extra relation in `U/V`;
2. the image of `U` in `GammaL/N` is a Sylow `2`-subgroup;
3. that Sylow subgroup controls fusion: its normalizer lies in its centralizer.

Burnside transfer then gives a finite `2`-group quotient of `GammaL/N` which is injective on the
Sylow image.  Its pullback separates every nontrivial class of `U/V`, proving the missing reverse
pro-`2` kernel inclusion.

The improved GammaL word supplies the ambient maximal pro-`2` quotient, but the existing relator
API does not prove checks (1)--(3) for arbitrary `V`.  In particular, odd index proves neither
normal-closure separation nor fusion control.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma h q : Type) A]
  [ContinuousSMul (gamma h q : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma h q : Type) B]
  [ContinuousSMul (gamma h q : Type) B]

local notation "rhoAB" =>
  pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)

local notation "U" P => sylowTwoPreimage rhoAB P

/-! ## The finite quotient by the ambient normal closure -/

/-- The normal closure in `GammaL` of `V ◁ₒ U`, bundled as an open normal subgroup.  It is open
because the image of `V` is already open in `GammaL` and every overgroup of an open subgroup is
open. -/
noncomputable def gammaLSylowPreimageAmbientNormalClosure
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) : OpenNormalSubgroup (gamma h q : Type) := by
  let i := subgroupIncl (gamma h q : Type) (U P)
  let W : Subgroup (gamma h q : Type) := V.toSubgroup.map i.toMonoidHom
  have hUopen : IsOpen ((U P : Subgroup (gamma h q : Type)) : Set (gamma h q : Type)) :=
    isOpen_sylowTwoPreimage rhoAB P
  have hWopen : IsOpen (W : Set (gamma h q : Type)) := by
    rw [Subgroup.coe_map]
    exact hUopen.isOpenMap_subtype_val _ V.isOpen'
  exact
    { toSubgroup := Subgroup.normalClosure (W : Set (gamma h q : Type))
      isOpen' := Subgroup.isOpen_mono Subgroup.le_normalClosure hWopen }

/-- The normal closure contains the original image of `V`. -/
theorem gammaLSylowPreimage_map_le_ambientNormalClosure
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) :
    V.toSubgroup.map
        (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom ≤
      (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup := by
  change V.toSubgroup.map
      (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom ≤
    Subgroup.normalClosure
      (V.toSubgroup.map
        (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom :
          Set (gamma h q : Type))
  exact Subgroup.le_normalClosure

/-! ## The three finite Burnside checks -/

/-- A finite Burnside witness at `V`.

The quotient carrier is definitionally `GammaL / normalClosure(V)`.  `kernel_on_U` is the first
genuine obstruction: the normal closure must meet `U` in exactly `V`.  The remaining two fields
say that the resulting image is Sylow and satisfies Burnside's fusion-control hypothesis. -/
structure GammaLSylowPreimageNormalClosureBurnsideWitness
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) where
  sylow : Sylow 2
    ((gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup)
  kernel_on_U :
    Subgroup.comap (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom
        (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup = V.toSubgroup
  range_on_U :
    ((quotientMk (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup).comp
      (subgroupIncl (gamma h q : Type) (U P))).toMonoidHom.range = sylow.1
  fusion_control : Subgroup.normalizer sylow.1 ≤ Subgroup.centralizer
    (sylow.1 : Set
      ((gamma h q : Type) ⧸
        (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup))

/-- The finite Burnside condition at every intrinsic finite `2`-quotient of `U`. -/
def GammaLSylowPreimageNormalClosureBurnsideSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  ∀ (V : OpenNormalSubgroup (U P))
      (_hV : IsPGroup 2 ((U P) ⧸ V.toSubgroup)),
    Nonempty (GammaLSylowPreimageNormalClosureBurnsideWitness P V)

/-! ## A cyclic-Sylow subclass -/

/-- A more directly checkable specialization of the Burnside witness: the Sylow image is
cyclic, and `2` is the smallest prime divisor of the finite ambient quotient.  Burnside's cyclic
Sylow theorem then supplies `fusion_control`. -/
structure GammaLSylowPreimageNormalClosureCyclicSylowWitness
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) where
  sylow : Sylow 2
    ((gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup)
  kernel_on_U :
    Subgroup.comap (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom
        (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup = V.toSubgroup
  range_on_U :
    ((quotientMk (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup).comp
      (subgroupIncl (gamma h q : Type) (U P))).toMonoidHom.range = sylow.1
  cyclic : IsCyclic sylow
  minFac_eq_two :
    (Nat.card
      ((gamma h q : Type) ⧸
        (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup)).minFac = 2

/-- Cyclic Sylow data supplies the finite Burnside witness by the normal-complement theorem. -/
noncomputable def GammaLSylowPreimageNormalClosureCyclicSylowWitness.toBurnside
    {P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))}
    {V : OpenNormalSubgroup (U P)}
    (D : GammaLSylowPreimageNormalClosureCyclicSylowWitness P V) :
    GammaLSylowPreimageNormalClosureBurnsideWitness P V where
  sylow := D.sylow
  kernel_on_U := D.kernel_on_U
  range_on_U := D.range_on_U
  fusion_control := D.cyclic.normalizer_le_centralizer D.minFac_eq_two

/-- Cyclic-Sylow data at every finite `2`-quotient. -/
def GammaLSylowPreimageNormalClosureCyclicSylowSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  ∀ (V : OpenNormalSubgroup (U P))
      (_hV : IsPGroup 2 ((U P) ⧸ V.toSubgroup)),
    Nonempty (GammaLSylowPreimageNormalClosureCyclicSylowWitness P V)

/-- The cyclic-Sylow supply is an important automatic fusion-control subclass of the general
Burnside supply. -/
theorem gammaLSylowPreimageNormalClosureBurnsideSupply_of_cyclicSylow
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (S : GammaLSylowPreimageNormalClosureCyclicSylowSupply P) :
    GammaLSylowPreimageNormalClosureBurnsideSupply P := by
  intro V hV
  exact ⟨(S V hV).some.toBurnside⟩

/-! ## Burnside transfer separates `U/V` -/

/-- A Burnside witness gives an ambient finite `2`-group homomorphism whose restriction kernel
to `U` is contained in `V`. -/
theorem gammaLSylowPreimage_burnside_restrictionKernel_le
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P))
    (D : GammaLSylowPreimageNormalClosureBurnsideWitness P V) :
    let H :=
      (gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup
    let transfer : ContinuousMonoidHom H D.sylow :=
      { toMonoidHom := MonoidHom.transferSylow D.sylow D.fusion_control
        continuous_toFun := continuous_of_discreteTopology }
    (transfer.comp
      ((quotientMk (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup).comp
        (subgroupIncl (gamma h q : Type) (U P)))).toMonoidHom.ker ≤ V.toSubgroup := by
  dsimp only
  intro u hu
  let qU : ContinuousMonoidHom (U P)
      ((gamma h q : Type) ⧸
        (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup) :=
    (quotientMk (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup).comp
      (subgroupIncl (gamma h q : Type) (U P))
  have hmem : qU u ∈ D.sylow.1 := by
    rw [← D.range_on_U]
    exact ⟨u, rfl⟩
  let s : D.sylow := ⟨qU u, hmem⟩
  have htransfer : MonoidHom.transferSylow D.sylow D.fusion_control s = 1 := by
    exact MonoidHom.mem_ker.mp hu
  have hinj : Function.Injective
      ((MonoidHom.transferSylow D.sylow D.fusion_control).restrict D.sylow) := by
    rw [MonoidHom.transferSylow_restrict_eq_pow]
    exact (D.sylow.2.powEquiv' D.sylow.not_dvd_index).injective
  have hs : s = 1 := by
    apply hinj
    exact htransfer.trans (map_one _).symm
  have hq : qU u = 1 := congrArg Subtype.val hs
  have hW : u ∈ Subgroup.comap
      (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom
      (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup := by
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff u.1).mp hq
  rw [D.kernel_on_U] at hW
  exact hW

/-- The three finite Burnside checks prove the full Sylow-preimage pro-`2` kernel equality. -/
theorem gammaLSylowPreimageProTwoKernelEquality_of_normalClosureBurnside
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (S : GammaLSylowPreimageNormalClosureBurnsideSupply P) :
    GammaLSylowPreimageProTwoKernelEquality P := by
  apply (gammaLSylowPreimageProTwoKernelEquality_iff_reverse P).2
  intro u hu
  rw [proPKernel, Subgroup.mem_iInf]
  rintro ⟨V, hV⟩
  let D := (S V hV).some
  let H :=
    (gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup
  let transfer : ContinuousMonoidHom H D.sylow :=
    { toMonoidHom := MonoidHom.transferSylow D.sylow D.fusion_control
      continuous_toFun := continuous_of_discreteTopology }
  apply gammaLSylowPreimage_burnside_restrictionKernel_le P V D
  rw [MonoidHom.mem_ker]
  apply MonoidHom.mem_ker.mp
  apply proPKernel_le_ker (isProP_of_isPGroup D.sylow.2)
    (transfer.comp
      (quotientMk (gammaLSylowPreimageAmbientNormalClosure P V).toSubgroup))
  rw [Subgroup.mem_comap] at hu
  exact hu

/-- Cyclic Sylow images satisfying normal-closure separation prove the kernel equality. -/
theorem gammaLSylowPreimageProTwoKernelEquality_of_normalClosureCyclicSylow
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (S : GammaLSylowPreimageNormalClosureCyclicSylowSupply P) :
    GammaLSylowPreimageProTwoKernelEquality P :=
  gammaLSylowPreimageProTwoKernelEquality_of_normalClosureBurnside P
    (gammaLSylowPreimageNormalClosureBurnsideSupply_of_cyclicSylow P S)

/-- Consequently, the Burnside checks discharge the exact finite normal-core `2`-residual
condition from `GammaLSylowPreimageSchreier`. -/
theorem gammaLSylowPreimageNormalCoreTwoResidualSeparation_of_normalClosureBurnside
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (S : GammaLSylowPreimageNormalClosureBurnsideSupply P) :
    GammaLSylowPreimageNormalCoreTwoResidualSeparation P :=
  gammaLSylowPreimageNormalCoreTwoResidualSeparation_of_kernelEquality hq2 hqe P
    (gammaLSylowPreimageProTwoKernelEquality_of_normalClosureBurnside P S)

end

end GQ2.Dyadic.LSquare
