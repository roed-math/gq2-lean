/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.ProTwoReciprocity

/-!
# The finite local-CFT input for completed pro-2 reciprocity

`MarkedRecip` gives a continuous dense map `Kˣ → G_K^ab`, but deliberately omits the finite
norm-residue theorem.  This file isolates the smallest conventional finite local-CFT supply
that repairs that omission: every homomorphism from `Kˣ` to a finite `2`-group factors through
the finite pro-`2` reciprocity target.

This is genuinely missing from the existing interfaces:

* `LocalReciprocity.norm_reciprocity` is only over `ℚ₂`; its source is `ℚ₂ˣ` and its layers are
  finite abelian extensions of `ℚ₂`.
* `MarkedRecip.norm_compat` only identifies the composite
  `Kˣ → G_K^ab → G_ℚ₂^ab` with the field norm followed by base reciprocity.  It gives no kernel
  theorem for a relative finite layer over `K`, and composing with a norm loses precisely that
  information.
* there is no arbitrary-`K` norm-subgroup/restriction bundle or existence theorem in the
  repository that realizes every finite abelian quotient of `Kˣ` by a finite extension of `K`.

The one-field supply below is therefore a proposed landing point for finite local class field
theory, not a new axiom.  It is proved equivalent to the exact kernel-agreement criterion in
`ProTwoReciprocity`, and hence implies completed injectivity with no further arithmetic input.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

noncomputable local instance instT2SpaceTopAbFiniteRecip {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **Finite pro-`2` local reciprocity supply.**  Every finite `2`-group quotient of `Kˣ`
factors through the pro-`2` abelianized Galois target, compatibly with the marked reciprocity
map.  Since `Kˣ` is commutative, the image of `f` is automatically abelian even though allowing
an arbitrary finite `2`-group target makes the universal property easier to consume.

This is the quotient-map form of finite local CFT.  The usual norm-residue statement produces
it by taking the finite abelian extension whose norm subgroup is `ker f`. -/
structure FiniteTwoLocalReciprocitySupply (B : MarkedRecip R K) : Prop where
  factor : ∀ (P : Type) [Group P] [TopologicalSpace P] [Finite P] [DiscreteTopology P],
    IsPGroup 2 P → ∀ f : (↥K)ˣ →* P,
      ∃ phi : ContinuousMonoidHom
          (topAbelianization (maxProPQuotient 2 (GalK K))) P,
        ∀ a : (↥K)ˣ,
          phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a

namespace FiniteTwoLocalReciprocitySupply

variable {B : MarkedRecip R K}

/-- Quotients by open normal subgroups of a profinite group have discrete quotient topology. -/
private theorem quotient_discrete
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ U.toSubgroup) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hpre : (QuotientGroup.mk : G → G ⧸ U.toSubgroup) ⁻¹' {1} =
      (U.toSubgroup : Set G) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      QuotientGroup.eq_one_iff]
  rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
  exact U.isOpen'

/-- The finite local-CFT factorization supply gives exact finite-layer kernel agreement. -/
theorem kernelAgreement (S : FiniteTwoLocalReciprocitySupply B) :
    ReciprocityFiniteTwoKernelAgreement B := by
  intro U
  let P := proPCompletion 2 ((↥K)ˣ) ⧸ U.toSubgroup
  letI : Finite P := Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  letI : DiscreteTopology P := quotient_discrete U
  let f : (↥K)ˣ →* P :=
    (QuotientGroup.mk' U.toSubgroup).comp (proPCompletionMk 2 ((↥K)ˣ))
  have hP : IsPGroup 2 P := by
    exact isProP_maxProPQuotient U
  obtain ⟨phi, hphi⟩ := S.factor P hP f
  let V : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 (GalK K))) :=
    { toSubgroup := phi.ker
      isOpen' := by
        change IsOpen (phi ⁻¹' {1})
        exact (isOpen_discrete ({1} : Set P)).preimage phi.continuous_toFun }
  refine ⟨V, fun a ↦ ?_⟩
  change phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = 1 ↔
    proPCompletionMk 2 ((↥K)ˣ) a ∈ U
  rw [hphi a]
  change QuotientGroup.mk' U.toSubgroup (proPCompletionMk 2 ((↥K)ˣ) a) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

/-- A finite local-CFT supply implies injectivity of completed pro-`2` reciprocity. -/
theorem completed_injective (S : FiniteTwoLocalReciprocitySupply B) :
    Function.Injective (proTwoReciprocityToTopAb B) :=
  (reciprocityFiniteTwoKernelAgreement_iff_injective B).mp S.kernelAgreement

/-- Kernel agreement constructs the finite-quotient factorization supply.  The exact kernel
criterion first makes completed reciprocity a topological isomorphism; the universal property
of the pro-`2` completion extends `f`, and transport across that isomorphism supplies `phi`. -/
def ofKernelAgreement (hker : ReciprocityFiniteTwoKernelAgreement B) :
    FiniteTwoLocalReciprocitySupply B where
  factor := by
    intro P _ _ _ _ hP f
    let E : ContinuousMulEquiv (proPCompletion 2 ((↥K)ˣ))
        (topAbelianization (maxProPQuotient 2 (GalK K))) :=
      continuousMulEquivOfBijective (proTwoReciprocityToTopAb B)
        ⟨(reciprocityFiniteTwoKernelAgreement_iff_injective B).mp hker,
          proTwoReciprocityToTopAb_surjective B⟩
    let liftF : ContinuousMonoidHom (proPCompletion 2 ((↥K)ˣ)) P :=
      proPCompletionLift (isProP_of_isPGroup hP) f
    let phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K))) P :=
      liftF.comp ⟨E.symm.toMonoidHom, E.symm.continuous⟩
    refine ⟨phi, fun a ↦ ?_⟩
    change liftF (E.symm
      (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a))) = f a
    rw [← proTwoReciprocityToTopAb_mk B a]
    have hE : E (proPCompletionMk 2 ((↥K)ˣ) a) =
        proTwoReciprocityToTopAb B (proPCompletionMk 2 ((↥K)ˣ) a) := rfl
    rw [← hE, E.symm_apply_apply]
    exact proPCompletionLift_mk (isProP_of_isPGroup hP) f a

/-- **Regression: the finite local-CFT supply is exactly kernel agreement.**  The proposed
one-field interface neither hides extra arithmetic strength nor loses anything needed by the
completed reciprocity theorem. -/
theorem iff_kernelAgreement :
    FiniteTwoLocalReciprocitySupply B ↔ ReciprocityFiniteTwoKernelAgreement B :=
  ⟨kernelAgreement, ofKernelAgreement⟩

end FiniteTwoLocalReciprocitySupply

end

end GQ2.Dyadic
