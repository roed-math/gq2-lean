/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.ProPCompletionFunctor
import GQ2.Dyadic.MarkedRecipBundle

/-!
# Completed pro-2 reciprocity for a dyadic field

This file extracts the completion-theoretic content that is honestly available from
`MarkedRecip`: the dense reciprocity map induces a continuous **surjection**

`(Kˣ)^(2) →ₜ* (G_K(2))^ab`.

The source is `proPCompletion 2 ((↥K)ˣ)`, defined as the maximal pro-2 quotient of the
profinite completion.  No injectivity statement is made: density of reciprocity alone cannot
identify its completed kernel.  That arithmetic kernel calculation, followed by the torsion
calculation, remains the missing input to `demushkinQ = 2`.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

/- The topological abelianization is a quotient by a closed subgroup, hence Hausdorff.  As in
`ProPAbelianization`, keep this generic quotient instance local so it does not perturb the
global quotient instance graph. -/
noncomputable local instance instT2SpaceTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The `MarkedRecip` reciprocity map, bundled with its continuity proof. -/
def MarkedRecip.continuousRecip (B : MarkedRecip R K) :
    ContinuousMonoidHom ((↥K)ˣ) (GalKab K) :=
  ⟨B.recip, B.continuous_recip⟩

/-- The purely group-theoretic identification `(G_K^ab)(2) ≃ (G_K(2))^ab`.

The inferred source type carries the deliberately local quotient instances from
`GQ2.ProPAbelianization`; keeping those instances out of the global instance graph avoids the
topological-quotient conflicts documented in `SectionThree.lean`. -/
def maxProTwoGalKabEquivTopAbMaxProTwoGalK :=
  maxProPTopAbEquiv (p := 2) (GalK K)

/-- Completed pro-2 local reciprocity, from the pro-2 completion of `Kˣ` to the topological
abelianization of `G_K(2)`. -/
def proTwoReciprocityToTopAb (B : MarkedRecip R K) :
    ContinuousMonoidHom (proPCompletion 2 ((↥K)ˣ))
      (topAbelianization (maxProPQuotient 2 (GalK K))) :=
  proPCompletionToTopAbMaxProP (p := 2) (GalK K) B.continuousRecip

@[simp] theorem proTwoReciprocityToTopAb_mk (B : MarkedRecip R K) (x : (↥K)ˣ) :
    proTwoReciprocityToTopAb B (proPCompletionMk 2 ((↥K)ˣ) x) =
      topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip x) :=
  proPCompletionToTopAbMaxProP_mk (p := 2) (GalK K) B.continuousRecip x

/-- **Completed pro-2 reciprocity is surjective.**  This is the strongest completion-level
conclusion supplied by the present `MarkedRecip` interface: compactness makes the range of the
extended map closed, while the original reciprocity image is dense. -/
theorem proTwoReciprocityToTopAb_surjective (B : MarkedRecip R K) :
    Function.Surjective (proTwoReciprocityToTopAb B) :=
  proPCompletionToTopAbMaxProP_surjective_of_denseRange (p := 2) (GalK K)
    B.continuousRecip B.denseRange_recip

/-! ## The exact finite-layer kernel interface

The fields of `MarkedRecip` do not contain the finite-layer norm-residue theorem.  The following
predicate records precisely the part of that theorem needed for completed injectivity: the
finite quotients pulled back from the reciprocity target are cofinal among all finite `2`-group
quotients of the source completion.  Since open normal subgroups of a profinite pro-`2` group
are exactly the kernels of its finite continuous `2`-group quotients, this is the
completion-level form of the missing finite-layer kernel calculation.
-/

/-- **Finite-layer norm-reciprocity kernel agreement.**  Pulling back a sufficiently fine
finite quotient of `(G_K(2))^ab` along reciprocity gives exactly the kernel of any prescribed
finite `2`-group quotient of `Kˣ`.

The right side is the kernel condition on `Kˣ` defined by an open normal subgroup of its
pro-`2` completion.  The left side is the kernel of the finite Galois-side quotient defined by
`V`.  In a conventional local-CFT development, equality of these two subgroups is supplied by
`Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)` as `L/K` ranges over finite abelian `2`-extensions.  The present
`MarkedRecip` bundle has no such field, so this predicate names the exact omitted input without
asserting it. -/
def ReciprocityFiniteTwoKernelAgreement (B : MarkedRecip R K) : Prop :=
  ∀ U : OpenNormalSubgroup (proPCompletion 2 ((↥K)ˣ)),
    ∃ V : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 (GalK K))),
      ∀ a : (↥K)ˣ,
        topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a) ∈ V ↔
          proPCompletionMk 2 ((↥K)ˣ) a ∈ U

/-- **Finite-layer reciprocity kernels are cofinal.**  For every finite continuous quotient of
the pro-`2` completion of `Kˣ`, there is a finite continuous quotient of `(G_K(2))^ab` whose
reciprocity kernel is smaller.  This is deliberately a separate premise rather than a field of
`MarkedRecip`: the current general-`K` bundle omits finite-layer norm reciprocity. -/
def CompletedReciprocityFiniteLayerCofinal (B : MarkedRecip R K) : Prop :=
  ∀ U : OpenNormalSubgroup (proPCompletion 2 ((↥K)ˣ)),
    ∃ V : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 (GalK K))),
      V.toSubgroup.comap (proTwoReciprocityToTopAb B).toMonoidHom ≤ U.toSubgroup

/-- Finite-layer kernel agreement on the dense copy of `Kˣ` implies cofinality on its pro-`2`
completion.  The point is topological but elementary: if the containment failed, the nonempty
open difference would meet the dense canonical image of `Kˣ`, contradicting kernel agreement. -/
theorem completedFiniteLayerCofinal_of_kernelAgreement (B : MarkedRecip R K)
    (hker : ReciprocityFiniteTwoKernelAgreement B) :
    CompletedReciprocityFiniteLayerCofinal B := by
  intro U
  obtain ⟨V, hV⟩ := hker U
  refine ⟨V, ?_⟩
  intro x hx
  by_contra hxU
  let W : Set (proPCompletion 2 ((↥K)ˣ)) :=
    (proTwoReciprocityToTopAb B) ⁻¹' (V : Set _) ∩ (U : Set _)ᶜ
  have hWopen : IsOpen W :=
    (V.isOpen'.preimage (proTwoReciprocityToTopAb B).continuous_toFun).inter
      U.toOpenSubgroup.isClosed.isOpen_compl
  have hWnonempty : W.Nonempty := by
    refine ⟨x, hx, ?_⟩
    exact Set.mem_compl hxU
  obtain ⟨a, ha⟩ :=
    (denseRange_proPCompletionMk (p := 2) (A := (↥K)ˣ)).exists_mem_open hWopen hWnonempty
  have haTarget : topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a) ∈ V := by
    rw [← proTwoReciprocityToTopAb_mk B a]
    exact ha.1
  exact ha.2 ((hV a).mp haTarget)

/-- Cofinality of finite-layer reciprocity kernels implies completed injectivity. -/
theorem proTwoReciprocityToTopAb_injective_of_finiteLayerCofinal
    (B : MarkedRecip R K) (hfin : CompletedReciprocityFiniteLayerCofinal B) :
    Function.Injective (proTwoReciprocityToTopAb B) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro U
  obtain ⟨V, hVU⟩ := hfin U
  apply hVU
  change proTwoReciprocityToTopAb B x ∈ V
  rw [hx]
  exact V.one_mem

/-- Completed injectivity makes finite-layer reciprocity kernels cofinal.  Surjectivity of
completed reciprocity, already proved from the dense image in `MarkedRecip`, turns an injective
map into a topological isomorphism; transport an arbitrary source finite quotient across its
inverse. -/
theorem finiteLayerCofinal_of_proTwoReciprocityToTopAb_injective
    (B : MarkedRecip R K) (hinj : Function.Injective (proTwoReciprocityToTopAb B)) :
    CompletedReciprocityFiniteLayerCofinal B := by
  let E : ContinuousMulEquiv (proPCompletion 2 ((↥K)ˣ))
      (topAbelianization (maxProPQuotient 2 (GalK K))) :=
    continuousMulEquivOfBijective (proTwoReciprocityToTopAb B)
      ⟨hinj, proTwoReciprocityToTopAb_surjective B⟩
  intro U
  let V : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 (GalK K))) :=
    { toSubgroup := U.toSubgroup.comap E.symm.toMonoidHom
      isOpen' := U.isOpen'.preimage E.symm.continuous }
  refine ⟨V, ?_⟩
  intro x hx
  change E.symm (proTwoReciprocityToTopAb B x) ∈ U at hx
  change x ∈ U
  have hE : E x = proTwoReciprocityToTopAb B x := rfl
  rw [← hE] at hx
  simpa using hx

/-- **Exact completed-reciprocity reduction.**  Completed pro-`2` reciprocity is injective if
and only if its finite-layer kernels are cofinal.  Thus the remaining input is neither a
topological-completion lemma nor an abelianization lemma: it is exactly the omitted finite-layer
norm-reciprocity/kernel theorem. -/
theorem completedReciprocityFiniteLayerCofinal_iff_injective (B : MarkedRecip R K) :
    CompletedReciprocityFiniteLayerCofinal B ↔
      Function.Injective (proTwoReciprocityToTopAb B) :=
  ⟨proTwoReciprocityToTopAb_injective_of_finiteLayerCofinal B,
    finiteLayerCofinal_of_proTwoReciprocityToTopAb_injective B⟩

/-- Completed injectivity also recovers exact finite-layer kernel agreement: transport each
source quotient across the resulting topological isomorphism. -/
theorem kernelAgreement_of_proTwoReciprocityToTopAb_injective
    (B : MarkedRecip R K) (hinj : Function.Injective (proTwoReciprocityToTopAb B)) :
    ReciprocityFiniteTwoKernelAgreement B := by
  let E : ContinuousMulEquiv (proPCompletion 2 ((↥K)ˣ))
      (topAbelianization (maxProPQuotient 2 (GalK K))) :=
    continuousMulEquivOfBijective (proTwoReciprocityToTopAb B)
      ⟨hinj, proTwoReciprocityToTopAb_surjective B⟩
  intro U
  let V : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 (GalK K))) :=
    { toSubgroup := U.toSubgroup.comap E.symm.toMonoidHom
      isOpen' := U.isOpen'.preimage E.symm.continuous }
  refine ⟨V, fun a ↦ ?_⟩
  change E.symm (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) ∈ U ↔
    proPCompletionMk 2 ((↥K)ˣ) a ∈ U
  rw [← proTwoReciprocityToTopAb_mk B a]
  have hE : E (proPCompletionMk 2 ((↥K)ˣ) a) =
      proTwoReciprocityToTopAb B (proPCompletionMk 2 ((↥K)ˣ) a) := rfl
  rw [← hE]
  simp

/-- **Exact finite-layer norm-kernel criterion for completed reciprocity.**  The completed map
is injective exactly when finite `2`-layer reciprocity kernels agree with the finite quotient
kernels defining the pro-`2` topology on `Kˣ`.  For a future local-CFT implementation, the
forward premise is the direct landing point of the finite norm-residue isomorphisms. -/
theorem reciprocityFiniteTwoKernelAgreement_iff_injective (B : MarkedRecip R K) :
    ReciprocityFiniteTwoKernelAgreement B ↔
      Function.Injective (proTwoReciprocityToTopAb B) :=
  ⟨fun h ↦ proTwoReciprocityToTopAb_injective_of_finiteLayerCofinal B
      (completedFiniteLayerCofinal_of_kernelAgreement B h),
    kernelAgreement_of_proTwoReciprocityToTopAb_injective B⟩

end

end GQ2.Dyadic
