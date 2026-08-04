/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.MaxProTwoSubgroupCriterion
import GQ2.Dyadic.Instances.GammaLH2RightExact
import GQ2.Dyadic.Instances.GammaLSylowPreimageProTwo

/-!
# The exact Reidemeister--Schreier boundary for the improved L presentation

Let `U` be the preimage of a Sylow `2`-subgroup of a finite coefficient-action image.  The
improved L presentation identifies `GammaL(2)` with the square-commutator core `DSq h`, and odd
index gives a surjection `U(2) → DSq h`.  This file identifies, without a hidden presentation
hypothesis, exactly when that surjection is an isomorphism.

The answer is the expected subgroup kernel equality

`K₂(U) = U ∩ K₂(GammaL)`.

Thus a quotient-dependent Reidemeister--Schreier theorem need not rebuild the entire improved
presentation: it must prove this equality.  Conversely, the equality immediately constructs a
continuous isomorphism with the existing improved core.  Odd index alone supplies only the
opposite inclusion and surjectivity, so no unconditional isomorphism is claimed.
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

/-- The exact condition missing from the current odd-index argument: the Sylow preimage has no
new pro-`2` kernel beyond the restriction of the ambient one. -/
def GammaLSylowPreimageProTwoKernelEquality
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  proPKernel 2 (U P) =
    Subgroup.comap (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom
      (proPKernel 2 (gamma h q : Type))

/-- Naturality supplies one containment in the kernel equality automatically.  Consequently the
entire Reidemeister--Schreier burden is the displayed reverse containment: every ambient
pro-`2`-invisible element lying in `U` must already be pro-`2`-invisible intrinsically in `U`. -/
theorem gammaLSylowPreimageProTwoKernelEquality_iff_reverse
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageProTwoKernelEquality P ↔
      Subgroup.comap (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom
          (proPKernel 2 (gamma h q : Type)) ≤
        proPKernel 2 (U P) := by
  constructor
  · intro heq
    rw [heq]
  · intro hreverse
    exact le_antisymm
      (proPKernel_le_comap (p := 2)
        (subgroupIncl (gamma h q : Type) (U P))) hreverse

/-- **Sharp presentation criterion.**  The already-constructed epimorphism from the Sylow
preimage's maximal pro-`2` quotient to the improved L core is injective if and only if the
subgroup pro-`2` kernel is exactly the pullback of the ambient pro-`2` kernel.

This rules out treating odd index as an automatic Reidemeister--Schreier isomorphism: the right
side is a genuine additional theorem, not a consequence of the Sylow index calculation. -/
theorem gammaLSylowPreimageMaxProTwoToLCore_injective_iff_kernelEquality
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    Function.Injective (gammaLSylowPreimageMaxProTwoToLCore hq2 hqe P) ↔
      GammaLSylowPreimageProTwoKernelEquality P := by
  change Function.Injective
      ((maxProPHomEquiv (SqCore.isProP_DSq h)).symm
        ((lCanonicalPro2 h q hq2 hqe).comp
          (subgroupIncl (gamma h q : Type) (U P)))) ↔ _
  exact subgroupMaxProPFactor_injective_iff_proPKernel
    (p := 2) (U P) (SqCore.isProP_DSq h) (lCanonicalPro2 h q hq2 hqe)
    (Count.CorePresentation.ker_coreHom
      (Instances.LSquareCore.lCorePresentation h) (q_ne_zero_of_two_le hq2) hqe)

/-- The kernel equality constructs the desired topological presentation model
`U(2) ≅ DSq h`, using the canonical map already tied to the improved L relator. -/
noncomputable def gammaLSylowPreimageMaxProTwoCoreEquiv
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    ContinuousMulEquiv
      (maxProPQuotient 2 (U P)) (SqCore.DSq h) :=
  continuousMulEquivOfBijective
    (gammaLSylowPreimageMaxProTwoToLCore hq2 hqe P)
    ⟨(gammaLSylowPreimageMaxProTwoToLCore_injective_iff_kernelEquality hq2 hqe P).2 hker,
      gammaLSylowPreimageMaxProTwoToLCore_surjective hq2 hqe P⟩

/-- The conditional core equivalence is the canonical improved-presentation map on every
element of the Sylow preimage. -/
@[simp] theorem gammaLSylowPreimageMaxProTwoCoreEquiv_mk
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) (u : U P) :
    gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker
        (maxProPMk 2 (U P) u) =
      lCanonicalPro2 h q hq2 hqe u.1 := by
  exact sylowPreimageMaxProTwoLift_mk rhoAB P (SqCore.isProP_DSq h)
    (lCanonicalPro2 h q hq2 hqe) u

/-! ## The quotient-dependent action retained on the improved core -/

/-- Once the exact kernel equality is proved, transport the Sylow action quotient from `U(2)`
to the *same improved square core*.  This is the quotient-dependent part of the
Reidemeister--Schreier model: the core presentation is fixed, while its epimorphism to `P`
depends on the coefficient-action image. -/
noncomputable def gammaLSylowPreimageCoreActionHom
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    ContinuousMonoidHom (SqCore.DSq h) P :=
  (sylowPreimageMaxProTwoHom rhoAB P).comp
    (gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker).symm

/-- The transported quotient-dependent action map remains onto. -/
theorem gammaLSylowPreimageCoreActionHom_surjective
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    Function.Surjective (gammaLSylowPreimageCoreActionHom hq2 hqe P hker) :=
  (sylowPreimageMaxProTwoHom_surjective rhoAB
      pairFiniteActionImageHom_surjective P).comp
    (gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker).symm.surjective

/-- Compatibility with the original coefficient action: passing from `u : U` to its canonical
point in the improved core and then to `P` recovers the Sylow-preimage action exactly. -/
@[simp] theorem gammaLSylowPreimageCoreActionHom_coreEquiv_mk
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) (u : U P) :
    gammaLSylowPreimageCoreActionHom hq2 hqe P hker
        (gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker
          (maxProPMk 2 (U P) u)) =
      sylowTwoPreimageHom rhoAB P u := by
  rw [gammaLSylowPreimageCoreActionHom]
  change sylowPreimageMaxProTwoHom rhoAB P
      ((gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker).symm
        (gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker
          (maxProPMk 2 (U P) u))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, sylowPreimageMaxProTwoHom_mk]

/-! ## Feeding the exact presentation criterion back into the CD-2 package -/

/-- Once the kernel equality identifies `U(2)` with the improved square core, the genuine
finite-elementary CD-2 tail on that core supplies the `cdTwo` field for `U(2)`.  This is honest
transport along the constructed topological equivalence, not an inference from scalar
Demushkin data. -/
theorem gammaLSylowPreimageMaxProTwoCDTwo_of_kernelEquality
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P)
    (hcore : FiniteElementaryH2RightExactSupply (SqCore.DSq h)) :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 (U P)) :=
  finiteTwoH2RightExactSupply_congr
    (gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker) hcore

/-- Constructor for the exact two-field maximal-pro-`2` package.  The improved presentation
now discharges its `cdTwo` field from a core theorem once the sharp kernel equality is known;
degree-two inflation `U(2) → U` remains the independent comparison input. -/
theorem sylowPreimageMaxProTwoCDTwoPackage_of_kernelEquality
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hinf : FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P)
    (hcore : FiniteElementaryH2RightExactSupply (SqCore.DSq h)) :
    SylowPreimageMaxProTwoCDTwoPackage rhoAB P where
  inflation := hinf
  cdTwo := gammaLSylowPreimageMaxProTwoCDTwo_of_kernelEquality
    hq2 hqe P hker hcore

end

end GQ2.Dyadic.LSquare
