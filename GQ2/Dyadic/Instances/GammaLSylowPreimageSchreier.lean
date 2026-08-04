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

/-! ## Finite-quotient extension criterion

The reverse containment can be tested without mentioning elements of either pro-`2` kernel.
The following condition says that every finite `2`-quotient of the Sylow preimage extends across
the canonical improved-L pro-`2` core.  Composing the supplied map with `lCanonicalPro2` gives an
ambient homomorphism from `GammaL` whose restriction is the original quotient map.

This is stronger and more useful than odd-index surjectivity: it controls *all* intrinsic finite
`2`-quotients of `U`, including ones not visibly induced by the coefficient-action quotient. -/

/-- Every intrinsic finite `2`-quotient of the Sylow preimage factors through the canonical
improved square core.  This is the finite Reidemeister--Schreier extension property needed for
the reverse pro-`2` kernel inclusion. -/
def GammaLSylowPreimageFiniteTwoQuotientExtension
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  ∀ (V : OpenNormalSubgroup (U P))
      (_hV : IsPGroup 2 ((U P) ⧸ V.toSubgroup)),
    ∃ f : ContinuousMonoidHom (SqCore.DSq h) ((U P) ⧸ V.toSubgroup),
      (f.comp (lCanonicalPro2 h q hq2 hqe)).comp
          (subgroupIncl (gamma h q : Type) (U P)) =
        quotientMk V.toSubgroup

/-- Finite-quotient extension supplies the missing reverse kernel containment.  Indeed, an
ambient-pro-`2`-invisible element is killed by `lCanonicalPro2`, hence by every extended finite
quotient of `U`; intersecting those quotient kernels is exactly `proPKernel 2 U`. -/
theorem gammaLSylowPreimageProTwoKernelEquality_of_finiteTwoQuotientExtension
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hext : GammaLSylowPreimageFiniteTwoQuotientExtension hq2 hqe P) :
    GammaLSylowPreimageProTwoKernelEquality P := by
  apply (gammaLSylowPreimageProTwoKernelEquality_iff_reverse P).2
  intro u hu
  rw [proPKernel, Subgroup.mem_iInf]
  rintro ⟨V, hV⟩
  obtain ⟨f, hf⟩ := hext V hV
  have hcore : lCanonicalPro2 h q hq2 hqe u.1 = 1 := by
    rw [Subgroup.mem_comap] at hu
    apply MonoidHom.mem_ker.mp
    have hu' : u.1 ∈ (lCanonicalPro2 h q hq2 hqe).toMonoidHom.ker := by
      change u.1 ∈ (Count.CorePresentation.coreHom
        (Instances.LSquareCore.lCorePresentation h)
        (q_ne_zero_of_two_le hq2) hqe).toMonoidHom.ker
      rw [Count.CorePresentation.ker_coreHom
        (Instances.LSquareCore.lCorePresentation h) (q_ne_zero_of_two_le hq2) hqe]
      exact hu
    exact hu'
  have hquot : quotientMk V.toSubgroup u = 1 := by
    have happ := DFunLike.congr_fun hf u
    change f (lCanonicalPro2 h q hq2 hqe u.1) = quotientMk V.toSubgroup u at happ
    calc
      quotientMk V.toSubgroup u = f (lCanonicalPro2 h q hq2 hqe u.1) := happ.symm
      _ = f 1 := congrArg f hcore
      _ = 1 := map_one f
  exact (QuotientGroup.eq_one_iff u).mp hquot

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

/-- Conversely, the kernel equality extends every finite `2`-quotient of `U` through the
improved square core.  First factor the quotient map through `U(2)` by the maximal-pro-`2`
universal property, then transport that factor across the canonical core equivalence. -/
theorem gammaLSylowPreimageFiniteTwoQuotientExtension_of_kernelEquality
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    GammaLSylowPreimageFiniteTwoQuotientExtension hq2 hqe P := by
  intro V hV
  let qV : ContinuousMonoidHom (U P) ((U P) ⧸ V.toSubgroup) :=
    quotientMk V.toSubgroup
  let liftV : ContinuousMonoidHom
      (maxProPQuotient 2 (U P)) ((U P) ⧸ V.toSubgroup) :=
    (maxProPHomEquiv (isProP_of_isPGroup hV)).symm qV
  let e := gammaLSylowPreimageMaxProTwoCoreEquiv hq2 hqe P hker
  refine ⟨liftV.comp (e.symm : ContinuousMonoidHom (SqCore.DSq h)
    (maxProPQuotient 2 (U P))), ?_⟩
  ext u
  change liftV (e.symm (lCanonicalPro2 h q hq2 hqe u.1)) = qV u
  rw [← gammaLSylowPreimageMaxProTwoCoreEquiv_mk hq2 hqe P hker u,
    ContinuousMulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun ((maxProPHomEquiv (isProP_of_isPGroup hV)).apply_symm_apply qV) u

/-- **Exact finite-quotient form of the Reidemeister--Schreier boundary.**  For the improved
`GammaL` presentation, the subgroup pro-`2` kernel equality is equivalent to extending every
finite `2`-quotient of the Sylow preimage through the already-constructed square core.

Thus the unresolved theorem is now a concrete quotient-extension problem: given
`V ◁ₒ U`, construct the displayed map from `DSq h`. -/
theorem gammaLSylowPreimageProTwoKernelEquality_iff_finiteTwoQuotientExtension
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageProTwoKernelEquality P ↔
      GammaLSylowPreimageFiniteTwoQuotientExtension hq2 hqe P := by
  constructor
  · exact gammaLSylowPreimageFiniteTwoQuotientExtension_of_kernelEquality hq2 hqe P
  · exact gammaLSylowPreimageProTwoKernelEquality_of_finiteTwoQuotientExtension hq2 hqe P

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
