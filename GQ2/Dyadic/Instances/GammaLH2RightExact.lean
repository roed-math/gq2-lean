/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LH2ComparisonDevissage
import GQ2.Dyadic.Count.Separation
import GQ2.Dyadic.Instances.GammaLDualityBoundary

/-!
# The continuous CD-2 tail: duality and transport boundaries

This file isolates two facts about the remaining continuous right-exactness input for the
improved L presentation.

First, local Tate duality implies surjectivity on `H²` for a surjection of finite elementary
coefficient modules.  The proof uses only the `(0,2)` perfect pairing: if an `H²` class were
outside the image, an elementary functional on the quotient would annihilate the image but not
that class.  Perfectness represents the functional by an invariant dual coefficient; naturality
and injectivity of dualizing a coefficient surjection then force that coefficient, and hence the
functional, to vanish.

Second, the right-exactness supply is invariant under topological group equivalence.  This makes
precise what a carrier identification `GammaL ≃ GalK` would buy: a CD-2 theorem on `GalK`
transports to `GammaL` without using Tate duality on `GammaL`.

The first result is deliberately labelled as a boundary, not as a direct proof of the L Tate
bundle.  Applying it to a supplied `TateDualityG GammaL 2` is circular for that campaign.  The
second result reduces the missing input to the narrower arithmetic statement
`FiniteTwoH2RightExactSupply (GalK K)` (or to the corresponding open-subgroup statement), but the
current repository has no non-Tate constructor for that statement: continuous cohomology is
implemented only through degree two, so there is no formal `H³ = 0`/`cd₂` theorem to invoke.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

/-! ## Dualizing a coefficient map -/

section MuDualMap

variable {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- Contravariant functoriality of the `MuN 2`-dual. -/
def muDualMap (g : A →+ B) : MuDual 2 B →+ MuDual 2 A where
  toFun phi := (phi.comp g : A →+ MuN 2)
  map_zero' := by
    apply MuDual.ext
    intro a
    rfl
  map_add' phi psi := by
    apply MuDual.ext
    intro a
    rfl

@[simp] theorem muDualMap_apply (g : A →+ B) (phi : MuDual 2 B) (a : A) :
    muDualMap g phi a = phi (g a) := rfl

omit [IsTopologicalGroup G] [ContinuousSMul G (MuN 2)]
  [ContinuousSMul G A] [ContinuousSMul G B] in
/-- Precomposition on the Tate dual is equivariant. -/
theorem muDualMap_equivariant (g : A →+ B)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a) (c : G) (phi : MuDual 2 B) :
    muDualMap g (c • phi) = c • muDualMap g phi := by
  apply MuDual.ext
  intro a
  rw [muDualMap_apply, muDual_smul_apply, muDual_smul_apply, muDualMap_apply,
    hg c⁻¹ a]

omit [IsTopologicalGroup G] [ContinuousSMul G (MuN 2)]
  [ContinuousSMul G A] [ContinuousSMul G B] in
/-- Dualizing a surjective coefficient map gives an injection on invariant Tate-dual
coefficients. -/
theorem mapCoeff0_muDualMap_injective (g : A →+ B)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) :
    Function.Injective (mapCoeff0 (muDualMap g) (muDualMap_equivariant g hg)) := by
  intro phi psi h
  apply Subtype.ext
  apply MuDual.ext
  intro b
  obtain ⟨a, rfl⟩ := hsurj b
  exact DFunLike.congr_fun (congrArg Subtype.val h) a

omit [IsTopologicalGroup G] [ContinuousSMul G (MuN 2)] in
/-- Naturality of the Tate `(0,2)` cup under a coefficient map and its contravariant dual. -/
theorem cup02_muDualMap_mapCoeff2 (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (phi : H0 G (MuDual 2 B)) (x : H2 G A) :
    cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A)
        (mapCoeff0 (muDualMap g) (muDualMap_equivariant g hg) phi) x =
      cup02 (muDualPairing 2 B) (muDualPairing_equivariant 2 B) phi
        (mapCoeff2 g hgC hg x) := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := A) x
  rw [mapCoeff2_H2mk_coeff, cup02_mk_mk, cup02_mk_mk]
  apply congrArg (H2mk G (MuN 2))
  apply Subtype.ext
  rfl

end MuDualMap

/-! ## Tate `(0,2)` perfectness implies the CD-2 tail -/

section TateRightExact

variable {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]

/-- The `(0,2)` fragment of local Tate duality.  It is a syntactically smaller data structure
than `TateDualityG`, containing neither `(1,1)` nor `(2,0)` perfectness.  For the improved L
presentation at even `q`, `GammaLTateRightExact` later proves that this data already reconstructs
the full bundle, so it must not be described there as logically weaker. -/
structure H02PerfectDualityG
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)] where
  inv : H2 G (MuN 2) ≃+ ZMod 2
  perfect02 : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M],
    (∀ x : M, (2 : ℕ) • x = 0) →
    Function.Bijective fun c : H0 G (MuDual 2 M) =>
      inv.toAddMonoidHom.comp
        (cup02 (muDualPairing 2 M) (muDualPairing_equivariant 2 M) c)

/-- Forget the two unused perfectness clauses of a full Tate bundle. -/
def h02PerfectDualityG_of_tateDualityG (D : TateDualityG G 2) :
    H02PerfectDualityG G where
  inv := D.inv
  perfect02 := D.perfect02

set_option maxHeartbeats 800000 in
/-- The `(0,2)` perfectness fragment forces surjectivity on `H²` for every surjection of finite
elementary coefficient modules.

This is the smallest duality fragment used by the proof. -/
theorem H2RightExactAt.of_h02PerfectDualityG (D : H02PerfectDualityG G)
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hsurj : Function.Surjective g) : H2RightExactAt g hgC hg := by
  let m : H2 G A →+ H2 G B := mapCoeff2 g hgC hg
  let d : H0 G (MuDual 2 B) →+ H0 G (MuDual 2 A) :=
    mapCoeff0 (muDualMap g) (muDualMap_equivariant g hg)
  have hd_inj : Function.Injective d := mapCoeff0_muDualMap_injective g hg hsurj
  let htorA : ∀ a : A, (2 : ℕ) • a = 0 := fun a => by rw [two_nsmul]; exact hA₂ a
  let htorB : ∀ b : B, (2 : ℕ) • b = 0 := fun b => by rw [two_nsmul]; exact hB₂ b
  let pairA : H0 G (MuDual 2 A) → (H2 G A →+ ZMod 2) := fun phi =>
    D.inv.toAddMonoidHom.comp
      (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) phi)
  let pairB : H0 G (MuDual 2 B) → (H2 G B →+ ZMod 2) := fun phi =>
    D.inv.toAddMonoidHom.comp
      (cup02 (muDualPairing 2 B) (muDualPairing_equivariant 2 B) phi)
  have hpairA : Function.Bijective pairA := D.perfect02 A htorA
  have hpairB : Function.Bijective pairB := D.perfect02 B htorB
  intro y
  by_contra hy
  have hy_range : y ∉ m.range := by
    intro hym
    rcases hym with ⟨x, hx⟩
    exact hy ⟨x, hx⟩
  let Q := H2 G B ⧸ m.range
  let pi : H2 G B →+ Q := QuotientAddGroup.mk' m.range
  have hpiy : pi y ≠ 0 := by
    intro hzero
    apply hy_range
    exact (QuotientAddGroup.eq_zero_iff y).mp hzero
  have hQ₂ : ∀ z : Q, z + z = 0 :=
    two_torsion_quot m.range (H2_two_torsionG hB₂)
  obtain ⟨lambdaQ, hlambdaQ⟩ := elemDual_separates hQ₂ hpiy
  let lambda : H2 G B →+ ZMod 2 := lambdaQ.comp pi
  have hlambda_y : lambda y ≠ 0 := hlambdaQ
  have hlambda_m : ∀ x : H2 G A, lambda (m x) = 0 := by
    intro x
    change lambdaQ (pi (m x)) = 0
    rw [show pi (m x) = 0 from (QuotientAddGroup.eq_zero_iff (m x)).mpr ⟨x, rfl⟩,
      map_zero]
  obtain ⟨phi, hphi⟩ := hpairB.2 lambda
  have hdphi : d phi = 0 := by
    apply hpairA.1
    apply AddMonoidHom.ext
    intro x
    change D.inv
        (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) (d phi) x) =
      D.inv
        (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) 0 x)
    rw [map_zero, AddMonoidHom.zero_apply, map_zero]
    rw [cup02_muDualMap_mapCoeff2 g hgC hg phi x]
    have hx := DFunLike.congr_fun hphi (m x)
    exact hx.trans (hlambda_m x)
  have hphi0 : phi = 0 := hd_inj (hdphi.trans (map_zero d).symm)
  apply hlambda_y
  have hzero : pairB phi = 0 := by
    rw [hphi0]
    apply AddMonoidHom.ext
    intro x
    simp [pairB]
  have hlambda0 : lambda = 0 := hphi.symm.trans hzero
  rw [hlambda0, AddMonoidHom.zero_apply]

/-- Full local Tate duality implies the CD-2 tail through only its `(0,2)` fragment.  This is a
useful generic consequence of B6, but using it with an already supplied
`TateDualityG GammaL 2` is circular in a construction of that same bundle. -/
theorem H2RightExactAt.of_tateDualityG (D : TateDualityG G 2)
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hsurj : Function.Surjective g) : H2RightExactAt g hgC hg :=
  H2RightExactAt.of_h02PerfectDualityG (h02PerfectDualityG_of_tateDualityG D)
    g hgC hg hA₂ hB₂ hsurj

/-- The group-parametric finite elementary CD-2 tail used by the L devissage. -/
noncomputable abbrev FiniteTwoH2RightExactSupply
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction G B] [ContinuousSMul G B]
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective g → H2RightExactAt g hgC hg

/-- Full Tate duality supplies the finite elementary CD-2 tail.  This theorem is a dependency
diagnostic, not a noncircular constructor of Tate duality. -/
theorem finiteTwoH2RightExactSupply_of_tateDualityG (D : TateDualityG G 2) :
    FiniteTwoH2RightExactSupply G := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  exact H2RightExactAt.of_tateDualityG D g hgC hg hA₂ hB₂ hsurj

/-- The syntactically smaller `(0,2)` duality fragment already supplies the tail. -/
theorem finiteTwoH2RightExactSupply_of_h02PerfectDualityG
    (D : H02PerfectDualityG G) : FiniteTwoH2RightExactSupply G := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  exact H2RightExactAt.of_h02PerfectDualityG D g hgC hg hA₂ hB₂ hsurj

/-- At `GammaL`, the generic supply is definitionally the CD-2 tail consumed by the coefficient
devissage.  Its Tate-based proof is intentionally explicit about the circular input. -/
theorem gammaLH2RightExactSupply_of_tateDualityG {h q : ℕ}
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (D : TateDualityG (gamma h q : Type) 2) : GammaLH2RightExactSupply h q :=
  finiteTwoH2RightExactSupply_of_tateDualityG D

end TateRightExact

/-! ## Transport along a topological group equivalence -/

section EquivTransport

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

private theorem continuousSMul_comp_equiv
    {A : Type} [AddCommGroup A] [TopologicalSpace A]
    [DistribMulAction G A] [ContinuousSMul G A]
    (e : G ≃ₜ* G') :
    letI : DistribMulAction G' A := DistribMulAction.compHom A e.symm.toMonoidHom
    ContinuousSMul G' A := by
  have hcontinuous_smul_G : Continuous (fun p : G × A => p.1 • p.2) := continuous_smul
  letI : DistribMulAction G' A := DistribMulAction.compHom A e.symm.toMonoidHom
  constructor
  exact hcontinuous_smul_G.comp
    ((e.symm.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section Naturality

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction G' A] [ContinuousSMul G' A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction G' B] [ContinuousSMul G' B]

/-- Coefficient functoriality commutes with group transport.  This is the naturality square
missing from the pre-existing `H2congrGroup` API and is proved directly on cocycle
representatives. -/
theorem H2congrGroup_mapCoeff2
    (e : G ≃ₜ* G')
    (hcompatA : ∀ (c : G) (a : A), c • a = e c • a)
    (hcompatB : ∀ (c : G) (b : B), c • b = e c • b)
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hg' : ∀ (c : G') (a : A), g (c • a) = c • g a)
    (x : H2 G A) :
    H2congrGroup e (AddEquiv.refl B) continuous_id continuous_id hcompatB
        (mapCoeff2 g hgC hg x) =
      mapCoeff2 g hgC hg'
        (H2congrGroup e (AddEquiv.refl A) continuous_id continuous_id hcompatA x) := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := A) x
  rfl

end Naturality

/-- The finite elementary CD-2 tail is invariant under topological group equivalence. -/
theorem finiteTwoH2RightExactSupply_congr
    (e : G ≃ₜ* G') (hG' : FiniteTwoH2RightExactSupply G') :
    FiniteTwoH2RightExactSupply G := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  letI : DistribMulAction G' A := DistribMulAction.compHom A e.symm.toMonoidHom
  letI : ContinuousSMul G' A := continuousSMul_comp_equiv e
  letI : DistribMulAction G' B := DistribMulAction.compHom B e.symm.toMonoidHom
  letI : ContinuousSMul G' B := continuousSMul_comp_equiv e
  have hcompatA : ∀ (c : G) (a : A), (AddEquiv.refl A) (c • a) = e c • a := by
    intro c a
    change c • a = e.symm (e c) • a
    rw [e.symm_apply_apply]
  have hcompatB : ∀ (c : G) (b : B), (AddEquiv.refl B) (c • b) = e c • b := by
    intro c b
    change c • b = e.symm (e c) • b
    rw [e.symm_apply_apply]
  have hg' : ∀ (c : G') (a : A), g (c • a) = c • g a := by
    intro c a
    exact hg (e.symm c) a
  have hright' : H2RightExactAt (G := G') g hgC hg' :=
    hG' A B g hgC hg' hA₂ hB₂ hsurj
  let EA : H2 G A ≃+ H2 G' A :=
    H2congrGroup e (AddEquiv.refl A) continuous_id continuous_id hcompatA
  let EB : H2 G B ≃+ H2 G' B :=
    H2congrGroup e (AddEquiv.refl B) continuous_id continuous_id hcompatB
  intro y
  obtain ⟨x', hx'⟩ := hright' (EB y)
  refine ⟨EA.symm x', ?_⟩
  apply EB.injective
  rw [H2congrGroup_mapCoeff2 e hcompatA hcompatB g hgC hg hg']
  change mapCoeff2 g hgC hg' (EA (EA.symm x')) = EB y
  rw [EA.apply_symm_apply, hx']

/-- The exact carrier-noncircular boundary for the L source: an equivalence to any group on
which the finite elementary CD-2 tail is known transports that tail to `GammaL`. -/
theorem gammaLH2RightExactSupply_of_equiv {h q : ℕ} {G : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : (gamma h q : Type) ≃ₜ* G) (hG : FiniteTwoH2RightExactSupply G) :
    GammaLH2RightExactSupply h q :=
  finiteTwoH2RightExactSupply_congr e hG

/-- A field realization reduces the L CD-2 tail to the same narrower tail on its open
subgroup.  No Tate bundle is constructed or consumed by this transport theorem. -/
theorem gammaLH2RightExactSupply_of_fieldRealization {h q : ℕ}
    (R : GammaLFieldRealization h q)
    (hsub : FiniteTwoH2RightExactSupply R.subgroup) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_equiv R.equiv hsub

/-! ### The precise arithmetic specialization -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The narrower arithmetic statement needed on the absolute/profinite Galois group of
a finite extension of `ℚ₂`. -/
noncomputable abbrev GalKH2RightExactSupply
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] : Prop :=
  FiniteTwoH2RightExactSupply (GalK K)

/-- The repository can currently construct the GalK CD-2 supply from B6 local Tate duality.
The implication from the bundle is proved above; `FieldData.tateDualityGalK` is the unique
non-standard dependency here. -/
theorem galKH2RightExactSupply_of_B6
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    GalKH2RightExactSupply K := by
  letI dmMu : DistribMulAction (GalK K) (MuN 2) := inferInstance
  haveI csMu : ContinuousSMul (GalK K) (MuN 2) :=
    ⟨Continuous.comp (continuous_smul (M := AbsGalQ2) (X := MuN 2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  let D : TateDualityG (GalK K) 2 := FieldData.tateDualityGalK K
  exact finiteTwoH2RightExactSupply_of_tateDualityG D

/-- An independently obtained presentation equivalence and the arithmetic CD-2 theorem imply
the L tail.  Supplying `galKH2RightExactSupply_of_B6 K` for the second argument uses B6 on
`GalK K`, but never assumes a Tate bundle on `GammaL`. -/
theorem gammaLH2RightExactSupply_of_equiv_galK {h q : ℕ}
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : (gamma h q : Type) ≃ₜ* GalK K) (hK : GalKH2RightExactSupply K) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_equiv e hK

/-- B6-specialized form of the preceding carrier transport.  Its non-standard axiom footprint
is exactly the existing `tateDualityAt` used on `GalK K`. -/
theorem gammaLH2RightExactSupply_of_equiv_galK_B6 {h q : ℕ}
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : (gamma h q : Type) ≃ₜ* GalK K) : GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_equiv_galK K e (galKH2RightExactSupply_of_B6 K)

end EquivTransport

end

end GQ2.Dyadic.LSquare
