/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLRelationCharacterTrivialAction
import GQ2.Dyadic.Instances.GammaLAsphericityRightExact
import GQ2.Dyadic.Count.H2SylowPreimageDevissage

/-!
# The scalar-kernel relation-character step for the improved L presentation

This file isolates the first genuinely nonsplit unipotent coefficient extension.  For a
surjective coefficient map `g : A → B` with two-element kernel, the simple-kernel comparison
is already bijective by the direct L theorem.  If the quotient coefficient `B` has relator
realization, the four-term coefficient comparison therefore shows that relator realization
for `A` is equivalent to surjectivity of

`H²(GammaL, A) → H²(GammaL, B)`.

Via the exact cocycle/character inverse, this is also equivalent to constructing the requested
quotient-dependent refined relation character for `A`.  Thus passing to the deeper quotient
allowed by the improved presentation does not remove the nonsplit obstruction: it is exactly
the scalar-kernel `H²` right-exactness/CD-2 tail.

The first section proves a reusable one-step coefficient theorem.  The second specializes it
to a two-element kernel and records the exact equivalences and the split constructor.  The
final section packages the finite `2`-group induction endpoint.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

private theorem continuousSMul_comp_scalarKernel
    {G C M : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace M] [DiscreteTopology M] [SMul C M]
    (rho : ContinuousMonoidHom G C) [SMul G M]
    (hcompat : ∀ (g : G) (m : M), g • m = rho g • m) : ContinuousSMul G M := by
  constructor
  have hfac : (fun p : G × M ↦ p.1 • p.2) =
      (fun p : C × M ↦ p.1 • p.2) ∘ (fun p : G × M ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-! ## A reusable coefficient-extension step -/

section CoefficientExtensionStep

variable {h q : ℕ} {C K A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
  [DiscreteTopology K] [Finite K]
  [DistribMulAction ((gamma h q : Type)) K]
  [ContinuousSMul ((gamma h q : Type)) K] [DistribMulAction C K]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A] [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B] [DistribMulAction C B]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

set_option maxHeartbeats 2400000 in
/-- Relator realization is closed under one finite coefficient extension once the continuous
`H²` map to the quotient is onto.

Both endpoint comparisons are obtained from their relator-realization hypotheses.  The finite
coefficient snake and the word snake then differ in only the middle comparison; the explicit
`H2RightExactAt` input closes the four-term chase. -/
theorem lModuleRelatorRealization_of_coeffExtension
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatK : ∀ (x : GammaL) (k : K), x • k = rho x • k)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b)
    (hK₂ : ∀ k : K, k + k = 0) (hA₂ : ∀ a : A, a + a = 0)
    (hB₂ : ∀ b : B, b + b = 0)
    (f : K →+ A) (g : A →+ B)
    (hfG : ∀ (x : GammaL) (k : K), f (x • k) = x • f k)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hfC : ∀ (c : C) (k : K), f (c • k) = c • f k)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hfinj : Function.Injective f) (hgsurj : Function.Surjective g)
    (hrange : f.range = g.ker)
    (hrealK : LModuleRelatorRealization (A := K) (e := eC) rho)
    (hrealB : LModuleRelatorRealization (A := B) (e := eC) rho)
    (hright : H2RightExactAt g continuous_of_discreteTopology hgG) :
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  let S : FiniteDiscreteCoeffSES (G := GammaL) (A' := K) (A := A) (A'' := B) := {
    f := f
    g := g
    f_equivariant := hfG
    g_equivariant := hgG
    f_injective := hfinj
    g_surjective := hgsurj
    range_eq_ker := hrange
  }
  let hresK := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hK₂
  let hresA := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hA₂
  let hresB := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hB₂
  let c := fun i ↦ rho (genL i)
  have hr : ∀ k, FreeGroup.lift c (wC k) = 1 := fun k ↦
    lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 * h + 1) q (Words.LSq.lSqW h)) hresA k
  have hbijK : Function.Bijective
      (lModuleH2WordFlexible rho hcompatK hK₂ hresK) :=
    lModuleH2WordFlexible_bijective_of_surjective rho hcompatK hK₂ hresK
      (lModuleH2WordFlexible_surjective_of_relatorRealization
        rho hcompatK hK₂ hresK hrealK)
  have hbijB : Function.Bijective
      (lModuleH2WordFlexible rho hcompatB hB₂ hresB) :=
    lModuleH2WordFlexible_bijective_of_surjective rho hcompatB hB₂ hresB
      (lModuleH2WordFlexible_surjective_of_relatorRealization
        rho hcompatB hB₂ hresB hrealB)
  have hbijA : Function.Bijective
      (lModuleH2WordFlexible rho hcompatA hA₂ hresA) :=
    ContCoh.fourTermComparison_bijective
      S.delta1
      (mapCoeff2 S.f S.continuous_f S.f_equivariant)
      (mapCoeff2 S.g S.continuous_g S.g_equivariant)
      (S.wordDelta1 c wC hfC hgC hr)
      (S.wordH2MapF c wC hfC)
      (S.wordH2MapG c wC hgC)
      (lSourceH1Equiv rho hcompatB hB₂ hresB)
      (lModuleH2WordFlexible rho hcompatK hK₂ hresK)
      (lModuleH2WordFlexible rho hcompatA hA₂ hresA)
      (lModuleH2WordFlexible rho hcompatB hB₂ hresB)
      (fun x ↦ (l_delta1_comparison S rho hcompatK hcompatA hcompatB
        hK₂ hB₂ hresK hresA hresB hfC hgC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho hcompatK hcompatA
        hK₂ hA₂ hresK hresA S.f S.f_equivariant hfC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho hcompatA hcompatB
        hA₂ hB₂ hresA hresB S.g S.g_equivariant hgC x).symm)
      S.exact_left S.exact_middle
      (S.wordH2_exact_left c wC hfC hgC hr)
      (S.wordH2_exact_middle c wC hfC hgC)
      hright (lSourceH1Equiv rho hcompatB hB₂ hresB).bijective hbijK hbijB
  exact moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompatA (fun V ↦ hwildLevel_gammaR V) hA₂
      (lFlexibleResolverSystem rho hresA) hbijA.2

end CoefficientExtensionStep

/-! ## The exact scalar-kernel obstruction -/

section ScalarKernel

variable {h q : ℕ} {C A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A] [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B] [DistribMulAction C B]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

/-- A two-element coefficient kernel has the direct improved-L relator-realization property.
This is the simple-coefficient theorem, packaged in the exact shape needed by the extension
step below. -/
theorem lModuleRelatorRealization_kernel_of_natCard_eq_two
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (g : A →+ B)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hcard : Nat.card ↑g.ker = 2) :
    letI : DistribMulAction GammaL ↑g.ker :=
      stableSubAction g.ker (fun x a ha ↦ by
        rw [AddMonoidHom.mem_ker, hgG, AddMonoidHom.mem_ker.mp ha, smul_zero])
    letI : DistribMulAction C ↑g.ker :=
      stableSubAction g.ker (fun c a ha ↦ by
        rw [AddMonoidHom.mem_ker, hgC, AddMonoidHom.mem_ker.mp ha, smul_zero])
    letI : ContinuousSMul GammaL ↑g.ker :=
      continuousSMul_comp_scalarKernel rho
        (fun x k ↦ Subtype.ext (hcompatA x k.1))
    LModuleRelatorRealization (A := ↑g.ker) (e := eC) rho := by
  let hKstableG : ∀ (x : GammaL) (a : A), a ∈ g.ker → x • a ∈ g.ker := by
    intro x a ha
    rw [AddMonoidHom.mem_ker, hgG, AddMonoidHom.mem_ker.mp ha, smul_zero]
  let hKstableC : ∀ (c : C) (a : A), a ∈ g.ker → c • a ∈ g.ker := by
    intro c a ha
    rw [AddMonoidHom.mem_ker, hgC, AddMonoidHom.mem_ker.mp ha, smul_zero]
  letI : DistribMulAction GammaL ↑g.ker := stableSubAction g.ker hKstableG
  letI : DistribMulAction C ↑g.ker := stableSubAction g.ker hKstableC
  have hcompatK : ∀ (x : GammaL) (k : ↑g.ker), x • k = rho x • k := by
    intro x k
    exact Subtype.ext (hcompatA x k.1)
  letI : ContinuousSMul GammaL ↑g.ker :=
    continuousSMul_comp_scalarKernel rho hcompatK
  have hK₂ : ∀ k : ↑g.ker, k + k = 0 := fun k ↦ Subtype.ext (hA₂ k.1)
  have hsimpleK : IsSimpleModTwo C ↑g.ker := isSimpleModTwo_of_natCard_eq_two hcard
  apply moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompatK (fun V ↦ hwildLevel_gammaR V) hK₂
      (lFlexibleResolverSystem rho (lUniform_wordLift_resolver hK₂))
  exact lUniform_simpleH2WordFlexible_surjective_of_surjective
    rho hrho hcompatK hK₂ hsimpleK hq

/-- The backward scalar-kernel step: if the quotient coefficient is already realized, the
only additional input required for the middle coefficient is right exactness on `H²`. -/
theorem lModuleRelatorRealization_of_scalarKernel_rightExact
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (g : A →+ B)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hgsurj : Function.Surjective g) (hcard : Nat.card ↑g.ker = 2)
    (hrealB : LModuleRelatorRealization (A := B) (e := eC) rho)
    (hright : H2RightExactAt g continuous_of_discreteTopology hgG) :
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  have hKstableG : ∀ (x : GammaL) (a : A), a ∈ g.ker → x • a ∈ g.ker := by
    intro x a ha
    rw [AddMonoidHom.mem_ker, hgG, AddMonoidHom.mem_ker.mp ha, smul_zero]
  have hKstableC : ∀ (c : C) (a : A), a ∈ g.ker → c • a ∈ g.ker := by
    intro c a ha
    rw [AddMonoidHom.mem_ker, hgC, AddMonoidHom.mem_ker.mp ha, smul_zero]
  letI : DistribMulAction GammaL ↑g.ker := stableSubAction g.ker hKstableG
  letI : DistribMulAction C ↑g.ker := stableSubAction g.ker hKstableC
  have hcompatK : ∀ (x : GammaL) (k : ↑g.ker), x • k = rho x • k := by
    intro x k
    exact Subtype.ext (hcompatA x k.1)
  letI : ContinuousSMul GammaL ↑g.ker :=
    continuousSMul_comp_scalarKernel rho hcompatK
  have hK₂ : ∀ k : ↑g.ker, k + k = 0 := fun k ↦ Subtype.ext (hA₂ k.1)
  let incl : ↑g.ker →+ A := g.ker.subtype
  have hinclG : ∀ (x : GammaL) (k : ↑g.ker), incl (x • k) = x • incl k := fun _ _ ↦ rfl
  have hinclC : ∀ (c : C) (k : ↑g.ker), incl (c • k) = c • incl k := fun _ _ ↦ rfl
  have hrange : incl.range = g.ker := by
    ext a
    simp [incl]
  apply lModuleRelatorRealization_of_coeffExtension rho hcompatK hcompatA hcompatB
    hK₂ hA₂ hB₂ incl g hinclG hgG hinclC hgC Subtype.val_injective
    hgsurj hrange
  · exact lModuleRelatorRealization_kernel_of_natCard_eq_two
      rho hrho hq g hgG hgC hcompatA hA₂ hcard
  · exact hrealB
  · exact hright

/-- Exact presentation obstruction for a scalar-kernel coefficient extension.

Once the quotient coefficient is realized, realization for the middle coefficient is not a
weaker presentation-theoretic substitute for the scalar-kernel CD-2 tail: it is equivalent to
that tail. -/
theorem lModuleRelatorRealization_iff_h2RightExactAt_scalarKernel
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (g : A →+ B)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hgsurj : Function.Surjective g) (hcard : Nat.card ↑g.ker = 2)
    (hrealB : LModuleRelatorRealization (A := B) (e := eC) rho) :
    LModuleRelatorRealization (A := A) (e := eC) rho ↔
      H2RightExactAt g continuous_of_discreteTopology hgG := by
  constructor
  · intro hrealA
    exact H2RightExactAt.of_lModuleRelatorRealization rho hcompatA hcompatB
      hA₂ hB₂ (lUniform_wordLift_resolver hA₂)
      (lUniform_wordLift_resolver hB₂) g hgG hgC hgsurj hrealA
  · exact lModuleRelatorRealization_of_scalarKernel_rightExact
      rho hrho hq hcompatA hcompatB hA₂ hB₂ g hgG hgC hgsurj hcard hrealB

/-- Exact refined-character form of the scalar-kernel obstruction.

The left side includes the deeper quotient, its quotient-specific improved L word, and the
`ModuleExt`-derived relation character.  The equivalence says that constructing those data for
every requested vector is exactly the missing `H²` coefficient lift. -/
theorem vectorwiseRefinedRelationCharacters_iff_h2RightExactAt_scalarKernel
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (g : A →+ B)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hgsurj : Function.Surjective g) (hcard : Nat.card ↑g.ker = 2)
    (hrealB : LModuleRelatorRealization (A := B) (e := eC) rho) :
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
        rho (fun i ↦ rho (genL i)) wC ↔
      H2RightExactAt g continuous_of_discreteTopology hgG := by
  rw [vectorwiseRefinedRelationCharacters_iff_lModuleRelatorRealization rho hA₂]
  exact lModuleRelatorRealization_iff_h2RightExactAt_scalarKernel
    rho hrho hq hcompatA hcompatB hA₂ hB₂ g hgG hgC hgsurj hcard hrealB

/-- The equivariantly split scalar-kernel case constructs the refined relation characters.
Consequently the equivalence above isolates only genuinely nonsplit unipotent extensions. -/
theorem vectorwiseRefinedRelationCharacters_of_scalarKernel_equivariantAddSection
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q)
    (hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (g : A →+ B)
    (hgG : ∀ (x : GammaL) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hgsurj : Function.Surjective g) (hcard : Nat.card ↑g.ker = 2)
    (hrealB : LModuleRelatorRealization (A := B) (e := eC) rho)
    (S : EquivariantAddSection (G := GammaL) g) :
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
      rho (fun i ↦ rho (genL i)) wC :=
  (vectorwiseRefinedRelationCharacters_iff_h2RightExactAt_scalarKernel
    rho hrho hq hcompatA hcompatB hA₂ hB₂ g hgG hgC hgsurj hcard hrealB).2
      (H2RightExactAt.of_equivariantAddSection
        g continuous_of_discreteTopology hgG S)

end ScalarKernel

/-! ## Finite `2`-group target induction -/

section TwoGroupTarget

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

set_option maxHeartbeats 2400000 in
/-- At one surjective finite `2`-group target, scalar-kernel right exactness closes the
presentation theorem for every finite elementary coefficient.

The induction is on a stable composition series.  Simple coefficients are supplied by the
direct L theorem.  At a nonsimple step, the already-proved scalar-kernel devissage upgrades the
tail premise to the actual quotient map, and `lModuleRelatorRealization_of_coeffExtension`
assembles the two endpoint realizations. -/
theorem lModuleRelatorRealization_of_twoGroupActionScalarKernelTail
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) (hC₂ : IsPGroup 2 C)
    (T : TwoGroupActionScalarKernelH2Tail rho)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  let P : ContCoh.FiniteTwoModuleProperty (C := C) := fun M _ _ _ ↦
    LModuleRelatorRealization (A := M) (e := eC) rho
  apply ContCoh.finiteTwoModuleProperty_of_simple P
  · intro M _ _ _ _
    exact lModuleRelatorRealization_of_trivial_action rho hrho hq M
      (fun m ↦ Subsingleton.elim (m + m) 0)
      (fun _ _ ↦ Subsingleton.elim _ _)
  · intro M _ _ _ hM₂ hsimple
    exact lModuleRelatorRealization_of_extensionAsphericity rho
      (lUniform_wordLift_resolver hM₂)
      (uniformSimpleExtensionAsphericitySingleProvider_of_surjective
        rho hrho hq M hM₂ hsimple)
  · intro M _ _ _ hM₂ W hWstable _hWbot _hWtop ihW ihQ
    letI : DistribMulAction C ↑W := stableSubAction W hWstable
    letI : DistribMulAction C (M ⧸ W) := stableQuotAction W hWstable
    letI : TopologicalSpace M := ⊥
    letI : DiscreteTopology M := ⟨rfl⟩
    letI : TopologicalSpace ↑W := ⊥
    letI : DiscreteTopology ↑W := ⟨rfl⟩
    letI : TopologicalSpace (M ⧸ W) := ⊥
    letI : DiscreteTopology (M ⧸ W) := ⟨rfl⟩
    letI : DistribMulAction GammaL M := DistribMulAction.compHom M rho.toMonoidHom
    letI : DistribMulAction GammaL ↑W := DistribMulAction.compHom ↑W rho.toMonoidHom
    letI : DistribMulAction GammaL (M ⧸ W) :=
      DistribMulAction.compHom (M ⧸ W) rho.toMonoidHom
    letI : ContinuousSMul GammaL M :=
      continuousSMul_comp_scalarKernel rho (fun _ _ ↦ rfl)
    letI : ContinuousSMul GammaL ↑W :=
      continuousSMul_comp_scalarKernel rho (fun _ _ ↦ rfl)
    letI : ContinuousSMul GammaL (M ⧸ W) :=
      continuousSMul_comp_scalarKernel rho (fun _ _ ↦ rfl)
    let incl : ↑W →+ M := W.subtype
    let quot : M →+ M ⧸ W := QuotientAddGroup.mk' W
    have hinclG : ∀ (x : GammaL) (w : ↑W), incl (x • w) = x • incl w := fun _ _ ↦ rfl
    have hquotG : ∀ (x : GammaL) (m : M), quot (x • m) = x • quot m := fun _ _ ↦ rfl
    have hinclC : ∀ (c : C) (w : ↑W), incl (c • w) = c • incl w := fun _ _ ↦ rfl
    have hquotC : ∀ (c : C) (m : M), quot (c • m) = c • quot m := fun _ _ ↦ rfl
    have hW₂ : ∀ w : ↑W, w + w = 0 := two_torsion_sub W hM₂
    have hQ₂ : ∀ m : M ⧸ W, m + m = 0 := two_torsion_quot W hM₂
    have hquotSurj : Function.Surjective quot := QuotientAddGroup.mk'_surjective W
    have hrange : incl.range = quot.ker := by
      rw [show incl.range = W by ext m; simp [incl]]
      exact (QuotientAddGroup.ker_mk' W).symm
    have hright : H2RightExactAt quot continuous_of_discreteTopology hquotG :=
      h2RightExactAt_of_twoGroupActionScalarKernelTail rho hrho hC₂ T
        quot hquotG hquotC (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
          hM₂ hQ₂ hquotSurj
    exact lModuleRelatorRealization_of_coeffExtension rho
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hW₂ hM₂ hQ₂ incl quot hinclG hquotG hinclC hquotC
      Subtype.val_injective hquotSurj hrange ihW ihQ hright
  · exact hA₂

/-- Refined-relation-character form of the finite `2`-group induction theorem. -/
theorem vectorwiseRefinedRelationCharacters_of_twoGroupActionScalarKernelTail
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) (hC₂ : IsPGroup 2 C)
    (T : TwoGroupActionScalarKernelH2Tail rho)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction GammaL A := DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul GammaL A :=
      continuousSMul_comp_scalarKernel rho (fun _ _ ↦ rfl)
    VectorwiseRefinedRelationCharacterRealization (A := A) (gen := genL) (W := WL)
      rho (fun i ↦ rho (genL i)) wC := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A := DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_scalarKernel rho (fun _ _ ↦ rfl)
  exact (vectorwiseRefinedRelationCharacters_iff_lModuleRelatorRealization
    rho hA₂).2 (lModuleRelatorRealization_of_twoGroupActionScalarKernelTail
      rho hrho hq hC₂ T A hA₂)

end TwoGroupTarget

/-! ## Direct uniform adapters -/

section UniformAdapters

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- Uniform scalar-kernel right-exactness on surjective finite `2`-group action targets. -/
noncomputable abbrev GammaLTwoGroupScalarKernelH2TailSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho → IsPGroup 2 C →
      TwoGroupActionScalarKernelH2Tail rho

/-- The complementary target-side premise needed by this direct presentation route.  Scalar
kernels close all coefficients for `2`-group targets; targets which are not `2`-groups can have
higher-dimensional simple modules and are kept explicit here. -/
noncomputable abbrev UniformElementaryNonTwoGroupTargetRelatorRealizationSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho → ¬ IsPGroup 2 C →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        LModuleRelatorRealization (A := A)
          (e := omega2Exp (4 * Monoid.exponent C)) rho

/-- Direct Gamma adapter: scalar-kernel tails close every `2`-group target, and the explicit
complementary premise closes the remaining finite targets. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_twoGroupScalarKernelTails
    (hq : Even q) (hscalar : GammaLTwoGroupScalarKernelH2TailSupply (h := h) (q := q))
    (hnon : UniformElementaryNonTwoGroupTargetRelatorRealizationSupply
      (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  by_cases hC₂ : IsPGroup 2 C
  · exact lModuleRelatorRealization_of_twoGroupActionScalarKernelTail
      rho hrho hq hC₂ (hscalar C rho hrho hC₂) A hA₂
  · exact hnon C rho hrho hC₂ A hA₂

/-- Direct refined-character adapter for the preceding target decomposition. -/
theorem uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_twoGroupScalarKernelTails
    (hq : Even q) (hscalar : GammaLTwoGroupScalarKernelH2TailSupply (h := h) (q := q))
    (hnon : UniformElementaryNonTwoGroupTargetRelatorRealizationSupply
      (h := h) (q := q)) :
    UniformElementaryVectorwiseRefinedRelationCharacterSupply (h := h) (q := q) :=
  uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_relatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_twoGroupScalarKernelTails
      hq hscalar hnon)

/-- Direct Tate adapter.  This records honestly that scalar unipotent extensions solve the
finite `2`-group target lane, while the non-`2`-group target lane remains a separate input. -/
noncomputable def tateDualityG_of_twoGroupScalarKernelTails
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hscalar : GammaLTwoGroupScalarKernelH2TailSupply (h := h) (q := q))
    (hnon : UniformElementaryNonTwoGroupTargetRelatorRealizationSupply
      (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_vectorwiseRelationCharacters hq
    (uniformElementaryVectorwiseRefinedRelationCharacterSupply_of_twoGroupScalarKernelTails
      hq hscalar hnon)

/-! ### Q₂ regressions -/

/-- The proved Q₂ all-elementary theorem supplies, in particular, every scalar-kernel tail on
finite `2`-group action targets. -/
theorem gammaLTwoGroupScalarKernelH2TailSupply_zero_two :
    GammaLTwoGroupScalarKernelH2TailSupply (h := 0) (q := 2) := by
  intro C _ _ _ _ rho _hrho _hC₂
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG _hgC _hcompatA _hcompatB
    hA₂ hB₂ hsurj _hcard
  exact (gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    uniformElementaryRelatorRealizationSurjectiveSupply_zero_two)
      A B g continuous_of_discreteTopology hgG hA₂ hB₂ hsurj

/-- The complementary non-`2`-group target premise also follows from the proved Q₂ theorem. -/
theorem uniformElementaryNonTwoGroupTargetRelatorRealizationSupply_zero_two :
    UniformElementaryNonTwoGroupTargetRelatorRealizationSupply (h := 0) (q := 2) := by
  intro C _ _ _ _ rho hrho _hC₂ A _ _ _ hA₂
  exact uniformElementaryRelatorRealizationSurjectiveSupply_zero_two C rho hrho A hA₂

/-- End-to-end regression for the explicit target-decomposed scalar-kernel adapter. -/
noncomputable def tateDualityG_zero_two_via_twoGroupScalarKernelTails
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    [ContinuousSMul (gamma 0 2 : Type) (MuN 2)] :
    TateDualityG (gamma 0 2 : Type) 2 :=
  tateDualityG_of_twoGroupScalarKernelTails (by decide)
    gammaLTwoGroupScalarKernelH2TailSupply_zero_two
    uniformElementaryNonTwoGroupTargetRelatorRealizationSupply_zero_two

end UniformAdapters

end

end GQ2.Dyadic.LSquare
