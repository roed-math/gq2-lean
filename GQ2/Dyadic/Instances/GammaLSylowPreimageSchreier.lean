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

/-! ## The normal-core finite quotient and its exact `2`-residual obstruction

For `V ◁ₒ U`, regard `V` as an open subgroup of `GammaL` and take its normal core there.  The
normal core is again open, so the resulting ambient quotient is finite.  Its pro-`2` kernel is
the ordinary finite-group `2`-residual.  The only possible obstruction is that this residual
may meet the image of `U` outside `V`.

This is precisely where a naive normal-core argument can fail: passing from `V` to its ambient
normal core introduces a finite quotient which need not itself be a `2`-group.  One must still
show that taking its maximal `2`-quotient does not collapse any additional class of `U/V`. -/

/-- The ambient normal core of an intrinsic open normal subgroup `V ◁ₒ U`, bundled as an open
normal subgroup of `GammaL`. -/
noncomputable def gammaLSylowPreimageAmbientNormalCore
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) : OpenNormalSubgroup (gamma h q : Type) := by
  let i := subgroupIncl (gamma h q : Type) (U P)
  let W : Subgroup (gamma h q : Type) := V.toSubgroup.map i.toMonoidHom
  have hUopen : IsOpen ((U P : Subgroup (gamma h q : Type)) : Set (gamma h q : Type)) :=
    isOpen_sylowTwoPreimage rhoAB P
  have hWopen : IsOpen (W : Set (gamma h q : Type)) := by
    rw [Subgroup.coe_map]
    exact hUopen.isOpenMap_subtype_val _ V.isOpen'
  haveI : Finite ((gamma h q : Type) ⧸ W) :=
    W.quotient_finite_of_isOpen hWopen
  haveI : W.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact
    { toSubgroup := W.normalCore
      isOpen' := W.normalCore.isOpen_of_isClosed_of_finiteIndex
        (W.normalCore_isClosed (W.isClosed_of_isOpen hWopen)) }

/-- The ambient normal core really lies in the image of `V`; this is the algebraic input that
allows any extension of `U/V` to descend to the finite normal-core quotient. -/
theorem gammaLSylowPreimageAmbientNormalCore_le_map
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) :
    (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup ≤
      V.toSubgroup.map
        (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom := by
  change (V.toSubgroup.map
    (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom).normalCore ≤ _
  exact Subgroup.normalCore_le _

/-- The finite ambient quotient by the normal core of `V`. -/
noncomputable def gammaLSylowPreimageNormalCoreQuotientHom
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (V : OpenNormalSubgroup (U P)) :
    ContinuousMonoidHom (gamma h q : Type)
      ((gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup) :=
  quotientMk (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup

/-- The exact normal-core obstruction: the `2`-residual of the finite ambient normal-core
quotient must pull back to `U` inside `V`.

Equivalently, the maximal `2`-quotient of that finite ambient quotient must still separate all
nontrivial classes of `U/V`. -/
def GammaLSylowPreimageNormalCoreTwoResidualSeparation
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  ∀ (V : OpenNormalSubgroup (U P))
      (_hV : IsPGroup 2 ((U P) ⧸ V.toSubgroup)),
    Subgroup.comap
        ((gammaLSylowPreimageNormalCoreQuotientHom P V).comp
          (subgroupIncl (gamma h q : Type) (U P))).toMonoidHom
        (proPKernel 2
          ((gamma h q : Type) ⧸
            (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup)) ≤
      V.toSubgroup

/-- Normal-core `2`-residual separation implies the reverse pro-`2` kernel inclusion.  This is
just naturality of `proPKernel` into each finite normal-core quotient, followed by the assumed
separation inside `U`. -/
theorem gammaLSylowPreimageProTwoKernelEquality_of_normalCoreTwoResidualSeparation
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hsep : GammaLSylowPreimageNormalCoreTwoResidualSeparation P) :
    GammaLSylowPreimageProTwoKernelEquality P := by
  apply (gammaLSylowPreimageProTwoKernelEquality_iff_reverse P).2
  intro u hu
  rw [proPKernel, Subgroup.mem_iInf]
  rintro ⟨V, hV⟩
  apply hsep V hV
  rw [Subgroup.mem_comap]
  apply proPKernel_le_comap
    (p := 2) (gammaLSylowPreimageNormalCoreQuotientHom P V)
  exact hu

/-- Kernel equality forces normal-core `2`-residual separation.  Extend `U/V` through the
improved core, observe that the resulting ambient map kills the normal core of `V`, descend it
to the finite normal-core quotient, and use naturality of its pro-`2` kernel. -/
theorem gammaLSylowPreimageNormalCoreTwoResidualSeparation_of_kernelEquality
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    GammaLSylowPreimageNormalCoreTwoResidualSeparation P := by
  intro V hV u hu
  obtain ⟨f, hf⟩ :=
    gammaLSylowPreimageFiniteTwoQuotientExtension_of_kernelEquality hq2 hqe P hker V hV
  let a : ContinuousMonoidHom (gamma h q : Type) ((U P) ⧸ V.toSubgroup) :=
    f.comp (lCanonicalPro2 h q hq2 hqe)
  have hmap : V.toSubgroup.map
      (subgroupIncl (gamma h q : Type) (U P)).toMonoidHom ≤ a.toMonoidHom.ker := by
    rintro g ⟨v, hv, rfl⟩
    rw [MonoidHom.mem_ker]
    have happ := DFunLike.congr_fun hf v
    change a v.1 = quotientMk V.toSubgroup v at happ
    change a v.1 = 1
    rw [happ]
    exact (QuotientGroup.eq_one_iff v).mpr hv
  have hcore : (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup ≤
      a.toMonoidHom.ker :=
    (gammaLSylowPreimageAmbientNormalCore_le_map P V).trans hmap
  let aCore : ContinuousMonoidHom
      ((gamma h q : Type) ⧸ (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup)
      ((U P) ⧸ V.toSubgroup) :=
    quotientLift (gammaLSylowPreimageAmbientNormalCore P V).toSubgroup a hcore
  have hres : aCore
      (gammaLSylowPreimageNormalCoreQuotientHom P V u.1) = 1 := by
    apply MonoidHom.mem_ker.mp
    apply proPKernel_le_ker (isProP_of_isPGroup hV) aCore
    rw [Subgroup.mem_comap] at hu
    exact hu
  have ha : a u.1 = 1 := by
    exact hres
  have happ := DFunLike.congr_fun hf u
  change a u.1 = quotientMk V.toSubgroup u at happ
  exact (QuotientGroup.eq_one_iff u).mp (happ.symm.trans ha)

/-- **Exact normal-core reduction.**  The desired Sylow-preimage kernel equality is equivalent
to one explicit finite-group statement at every intrinsic finite `2`-quotient: after taking the
ambient normal core, its finite quotient's `2`-residual must not kill any extra class of `U/V`.

The forward direction uses the improved presentation through the finite-quotient extension
equivalence above; the reverse direction is pure pro-`2` kernel naturality. -/
theorem gammaLSylowPreimageProTwoKernelEquality_iff_normalCoreTwoResidualSeparation
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageProTwoKernelEquality P ↔
      GammaLSylowPreimageNormalCoreTwoResidualSeparation P := by
  constructor
  · exact gammaLSylowPreimageNormalCoreTwoResidualSeparation_of_kernelEquality hq2 hqe P
  · exact gammaLSylowPreimageProTwoKernelEquality_of_normalCoreTwoResidualSeparation P

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
