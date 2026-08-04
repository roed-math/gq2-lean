/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.LowerTwoCentralJenningsDegreeOneReverse
import GQ2.Dyadic.Count.H3CompletedQuadraticRelation
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteElementaryH2

/-!
# Quadratic moments for the reverse degree-two Jennings containment

This file begins the reverse containment `D_3 <= lambda_3` for the improved square
presentation.  Its first reusable ingredient is independent of that presentation: a central
extension defined by a cup cocycle has trivial third lower two-central subgroup.  Consequently
every admissible quadratic detector of `DSq h` factors through the quotient by `lambda_3`.

The second ingredient converts membership of a group-like difference in the augmentation cube
into vanishing of the detector's fibre coordinate.  The remaining step is the finite quadratic
separation theorem on `lambda_2/lambda_3`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Roe.Labute
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.MarkedCore
open scoped commutatorElement

variable {L : Type} [Group L] {c : GQ2.DRCoh.TwoCocycle L}

/-! ## The elementary first lower-central quotient -/

/-- The quotient by `lambda_2` has exponent two. -/
theorem levelQuot_two_pow_two {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : levelQuot G 2) : q ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G 2 q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (sq_mem_twoCentralSeries_succ G (Subgroup.mem_top g))

/-- The quotient by `lambda_2` is commutative. -/
theorem levelQuot_two_mul_comm {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q r : levelQuot G 2) : q * r = r * q := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G 2 q
  obtain ⟨k, rfl⟩ := levelMk_surjective G 2 r
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (commutator_mem_twoCentralSeries_succ G (Subgroup.mem_top g) k)

/-! ## Central extensions attached to intrinsic quadratic forms -/

section ElementaryQuadraticDetector

variable (V : Type) [CommGroup V] [TopologicalSpace V] [IsTopologicalGroup V]
  [DiscreteTopology V] [Finite V] [Fact (∀ v : V, v ^ 2 = 1)]

local instance : Module (ZMod 2) (Additive V) :=
  GQ2.Dyadic.LSquare.instModuleZModOfNatNatAdditive_gQ2 V

local instance : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite

local instance : DistribMulAction V (ZMod 2) :=
  GQ2.Dyadic.LSquare.instDistribMulActionZModOfNatNat_gQ2_1 V

local instance : ContinuousSMul V (ZMod 2) :=
  GQ2.Dyadic.LSquare.instContinuousSMulZModOfNatNat_gQ2_1 V

/-- The `DRCoh` normalized cocycle obtained from the canonical upper-triangular bilinear
refinement of a quadratic form. -/
def elementaryQuadraticDRCocycle
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    GQ2.DRCoh.TwoCocycle V := by
  let B := Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
  refine
    { κ := fun v w => B (Additive.ofMul v) (Additive.ofMul w)
      norm := by simp [B]
      cocyc := ?_ }
  intro g h k
  change B (Additive.ofMul g) (Additive.ofMul h) +
      B (Additive.ofMul g + Additive.ofMul h) (Additive.ofMul k) =
    B (Additive.ofMul g) (Additive.ofMul h + Additive.ofMul k) +
      B (Additive.ofMul h) (Additive.ofMul k)
  simp only [map_add, LinearMap.add_apply]
  abel

/-- The intrinsic quadratic detector is a cup-cocycle extension when its base is elementary
abelian of exponent two. -/
theorem elementaryQuadraticDRCocycle_isCup
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    IsCupCocycle (elementaryQuadraticDRCocycle V Q) where
  comm v w := mul_comm v w
  expTwo v := by simpa [pow_two] using (Fact.out : ∀ x : V, x ^ 2 = 1) v
  addLeft v w t := by
    change Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
        (Additive.ofMul v + Additive.ofMul w) (Additive.ofMul t) =
      Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
          (Additive.ofMul v) (Additive.ofMul t) +
        Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
          (Additive.ofMul w) (Additive.ofMul t)
    have hadd := congrArg
      (fun f : Additive V →ₗ[ZMod 2] ZMod 2 => f (Additive.ofMul t))
      (map_add (Q.toBilin (Module.finBasis (ZMod 2) (Additive V)))
        (Additive.ofMul v) (Additive.ofMul w))
    simpa using hadd
  addRight v w t := by
    change Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
        (Additive.ofMul v) (Additive.ofMul w + Additive.ofMul t) =
      Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
          (Additive.ofMul v) (Additive.ofMul w) +
        Q.toBilin (Module.finBasis (ZMod 2) (Additive V))
          (Additive.ofMul v) (Additive.ofMul t)
    rw [map_add]

/-- The cohomological and `DRCoh` versions of the intrinsic quadratic cocycle have the same
pointwise cocycle. -/
theorem elementaryQuadraticCocycle_eq_elementaryQuadraticDRCocycle
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) (v w : V) :
    (GQ2.Dyadic.LSquare.elementaryQuadraticCocycle V Q).1 (v, w) =
      (elementaryQuadraticDRCocycle V Q).κ v w :=
  rfl

/-- The canonical quadratic cocycle represents the cohomology class from which its quadratic
form was extracted. -/
theorem H2mk_elementaryQuadraticCocycle_equiv
    (η : H2 V (ZMod 2)) :
    H2mk V (ZMod 2)
        (GQ2.Dyadic.LSquare.elementaryQuadraticCocycle V
          (GQ2.Dyadic.LSquare.elementaryH2EquivQuadratic V η)) = η := by
  apply GQ2.Dyadic.LSquare.elementaryH2ToQuadratic_injective V
  rw [GQ2.Dyadic.LSquare.elementaryH2ToQuadratic_H2mk,
    GQ2.Dyadic.LSquare.elementaryCocycleQuadraticMap_elementaryQuadraticCocycle]
  rfl

end ElementaryQuadraticDetector

/-! ## Quadratic realization of layer characters -/

/-- Every additive character of `lambda_2/lambda_3` is the fibre restriction of a homomorphism
to a cup-cocycle central extension of the elementary first quotient. -/
theorem exists_elementaryQuadraticDetector_of_zLayerCharacter (h : ℕ)
    (chi : Additive (zLayer (DSq h : Type) 2) →+ ZMod 2) :
    ∃ (c : GQ2.DRCoh.TwoCocycle (levelQuot (DSq h : Type) 2))
      (_hc : IsCupCocycle c)
      (φ : (DSq h : Type) →* GQ2.DRCoh.CentExt c),
      ∀ (g : DSq h) (hg : g ∈ twoCentralSeries (DSq h : Type) 2),
        (φ g).fib = chi (Additive.ofMul
          (⟨levelMk (DSq h : Type) 3 g, ⟨g, hg, rfl⟩⟩ :
            zLayer (DSq h : Type) 2)) := by
  let G := (DSq h : Type)
  let Q := levelQuot G 2
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G (dsqFinsetTopGen h) (isProP_DSq h) 2
  letI : Finite Q :=
    finite_levelQuot G (dsqFinsetTopGen h) (isProP_DSq h) 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := levelQuot_two_mul_comm }
  letI : Fact (∀ q : Q, q ^ 2 = 1) := ⟨levelQuot_two_pow_two⟩
  letI : Module (ZMod 2) (Additive Q) :=
    GQ2.Dyadic.LSquare.instModuleZModOfNatNatAdditive_gQ2 Q
  letI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  letI : DistribMulAction Q (ZMod 2) :=
    GQ2.Dyadic.LSquare.instDistribMulActionZModOfNatNat_gQ2_1 Q
  letI : ContinuousSMul Q (ZMod 2) :=
    GQ2.Dyadic.LSquare.instContinuousSMulZModOfNatNat_gQ2_1 Q
  letI : DistribMulAction G (ZMod 2) := GQ2.Dyadic.scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) :=
    GQ2.Dyadic.scalarActionZmodTwo_continuousSMul G
  let z := GQ2.Dyadic.LSquare.lowerTwoCentralTransgressionCocycle G
    (dsqFinsetTopGen h) (isProP_DSq h) chi
  let η := H2mk Q (ZMod 2) z
  let qform := GQ2.Dyadic.LSquare.elementaryH2EquivQuadratic Q η
  let zq := GQ2.Dyadic.LSquare.elementaryQuadraticCocycle Q qform
  let c := elementaryQuadraticDRCocycle Q qform
  have hclass : H2mk Q (ZMod 2) zq = H2mk Q (ZMod 2) z := by
    change H2mk Q (ZMod 2)
      (GQ2.Dyadic.LSquare.elementaryQuadraticCocycle Q
        (GQ2.Dyadic.LSquare.elementaryH2EquivQuadratic Q η)) = η
    exact H2mk_elementaryQuadraticCocycle_equiv Q η
  change (QuotientAddGroup.mk zq : H2 Q (ZMod 2)) =
      QuotientAddGroup.mk z at hclass
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at hclass
  change (zq - z).1 ∈ B2 Q (ZMod 2) at hclass
  obtain ⟨psi, hpsiC, hpsi⟩ := hclass
  let b0 := GQ2.Dyadic.LSquare.lowerTwoCentralKernelPartC1 G
    (dsqFinsetTopGen h) (isProP_DSq h) chi
  let psiInf : G → ZMod 2 := fun g => psi (levelMk G 2 g)
  let b : G → ZMod 2 := fun g => b0.1 g + psiInf g
  have hpsi_one : psi 1 = 0 := by
    have hp := congrFun hpsi (1, 1)
    change (1 : Q) • psi 1 - psi (1 * 1) + psi 1 =
      zq.1 (1, 1) - z.1 (1, 1) at hp
    rw [GQ2.Dyadic.scalarActionZmodTwo_triv Q, one_mul] at hp
    simp only [sub_self, zero_add] at hp
    have hzq : zq.1 (1, 1) = 0 := by
      change c.κ 1 1 = 0
      exact c.norm
    have hz : z.1 (1, 1) = 0 := by
      change chi (Additive.ofMul
        (GQ2.Dyadic.LSquare.lowerTwoCentralSectionDefect G 1 1)) = 0
      rw [GQ2.Dyadic.LSquare.lowerTwoCentralSectionDefect_one_one]
      exact map_zero chi
    rwa [hzq, hz, sub_zero] at hp
  have hb_one : b 1 = 0 := by
    change b0.1 1 + psi 1 = 0
    rw [hpsi_one]
    simp [b0, GQ2.Dyadic.LSquare.lowerTwoCentralKernelPartC1]
  have hb_cocycle (g k : G) :
      b (g * k) = b g + b k + c.κ (levelMk G 2 g) (levelMk G 2 k) := by
    have hb0 := congrFun
      (GQ2.Dyadic.LSquare.lowerTwoCentralTransgression_inflated_eq_dOne G
        (dsqFinsetTopGen h) (isProP_DSq h) chi) (g, k)
    have hp := congrFun hpsi (levelMk G 2 g, levelMk G 2 k)
    change z.1 (levelMk G 2 g, levelMk G 2 k) =
      g • b0.1 k - b0.1 (g * k) + b0.1 g at hb0
    change (levelMk G 2 g) • psi (levelMk G 2 k) -
        psi (levelMk G 2 g * levelMk G 2 k) + psi (levelMk G 2 g) =
      zq.1 (levelMk G 2 g, levelMk G 2 k) -
        z.1 (levelMk G 2 g, levelMk G 2 k) at hp
    rw [GQ2.Dyadic.scalarActionZmodTwo_triv G] at hb0
    rw [GQ2.Dyadic.scalarActionZmodTwo_triv Q] at hp
    change z.1 (levelMk G 2 g, levelMk G 2 k) =
      b0.1 k - b0.1 (g * k) + b0.1 g at hb0
    rw [← map_mul (levelMk G 2) g k] at hp
    change psi (levelMk G 2 k) - psi (levelMk G 2 (g * k)) +
        psi (levelMk G 2 g) =
      zq.1 (levelMk G 2 g, levelMk G 2 k) -
        z.1 (levelMk G 2 g, levelMk G 2 k) at hp
    change b0.1 (g * k) + psi (levelMk G 2 (g * k)) =
      (b0.1 g + psi (levelMk G 2 g)) +
        (b0.1 k + psi (levelMk G 2 k)) +
          c.κ (levelMk G 2 g) (levelMk G 2 k)
    rw [← elementaryQuadraticCocycle_eq_elementaryQuadraticDRCocycle
      Q qform]
    dsimp only [zq] at hp
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -hb0 - hp
  let φ : G →* GQ2.DRCoh.CentExt c :=
    { toFun := fun g => ((levelMk G 2 g, b g) : GQ2.DRCoh.CentExt c)
      map_one' := GQ2.DRCoh.CentExt.ext (map_one (levelMk G 2)) hb_one
      map_mul' := by
        intro g k
        apply GQ2.DRCoh.CentExt.ext
        · exact map_mul (levelMk G 2) g k
        · change b (g * k) = b g + b k +
            c.κ (levelMk G 2 g) (levelMk G 2 k)
          exact hb_cocycle g k }
  refine ⟨c, elementaryQuadraticDRCocycle_isCup Q qform, φ, ?_⟩
  intro g hg
  change b0.1 g + psi (levelMk G 2 g) = _
  have hlevel : levelMk G 2 g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  rw [hlevel, hpsi_one, add_zero]
  change chi (Additive.ofMul
      (GQ2.Dyadic.LSquare.lowerTwoCentralKernelPart G g)) = _
  congr 2
  apply Subtype.ext
  exact GQ2.Dyadic.LSquare.lowerTwoCentralKernelPart_coe_of_mem G hg

/-- The second lower two-central subgroup of a cup-cocycle central extension lies in its
central fibre. -/
theorem twoCentralSeries_two_le_centExtProj_ker (hc : IsCupCocycle c) :
    twoCentralSeries (GQ2.DRCoh.CentExt c) 2 ≤
      (GQ2.DRCoh.CentExt.proj c).ker := by
  rw [twoCentralSeries_succ (GQ2.DRCoh.CentExt c) (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨p, -, rfl⟩
    change (p ^ 2).base = 1
    rw [centExt_pow_base, pow_two]
    exact hc.expTwo p.base
  · rw [Subgroup.commutator_le]
    intro p hp q hq
    change (⁅p, q⁆).base = 1
    change ⁅p.base, q.base⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc.comm p.base q.base)
  · have hset : ((GQ2.DRCoh.CentExt.proj c).ker :
        Set (GQ2.DRCoh.CentExt c)) =
        (GQ2.DRCoh.CentExt.proj c) ⁻¹' {1} := by
      ext p
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_discrete _

/-- The central fibre of a normalized central extension is central. -/
theorem centExtProj_ker_le_center :
    (GQ2.DRCoh.CentExt.proj c).ker ≤
      Subgroup.center (GQ2.DRCoh.CentExt c) := by
  intro p hp
  have hbase := MonoidHom.mem_ker.mp hp
  change p.base = 1 at hbase
  rw [Subgroup.mem_center_iff]
  intro q
  apply GQ2.DRCoh.CentExt.ext
  · change q.base * p.base = p.base * q.base
    rw [hbase, one_mul, mul_one]
  · rw [GQ2.DRCoh.CentExt.mul_fib, GQ2.DRCoh.CentExt.mul_fib]
    rw [hbase, c.κ_one_left, c.κ_one_right]
    abel

/-- Every element of the central fibre has order dividing two. -/
theorem centExtProj_ker_sq_eq_one {p : GQ2.DRCoh.CentExt c}
    (hp : p ∈ (GQ2.DRCoh.CentExt.proj c).ker) : p ^ 2 = 1 := by
  have hbase := MonoidHom.mem_ker.mp hp
  change p.base = 1 at hbase
  apply GQ2.DRCoh.CentExt.ext
  · rw [centExt_pow_base, centExt_one_base, hbase, one_pow]
  · rw [pow_two, GQ2.DRCoh.CentExt.mul_fib]
    change p.fib + p.fib + c.κ p.base p.base = 0
    rw [hbase, c.κ_one_left, add_zero]
    exact CharTwo.add_self_eq_zero p.fib

/-- A central extension by a cup cocycle has lower two-central length at most two. -/
theorem twoCentralSeries_three_centExt_eq_bot (hc : IsCupCocycle c) :
    twoCentralSeries (GQ2.DRCoh.CentExt c) 3 = ⊥ := by
  rw [twoCentralSeries_succ (GQ2.DRCoh.CentExt c) (by omega)]
  apply twoCentralSucc_eq_bot_of_le_center
  · exact (twoCentralSeries_two_le_centExtProj_ker hc).trans
      centExtProj_ker_le_center
  · intro p hp
    exact centExtProj_ker_sq_eq_one
      (twoCentralSeries_two_le_centExtProj_ker hc hp)

/-- Every admissible quadratic detector kills `lambda_3(DSq h)`. -/
theorem twoCentralSeries_three_le_sqQuadraticDetectorHom_ker (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    twoCentralSeries (DSq h : Type) 3 ≤
      (sqQuadraticDetectorHom h κ hκ).toMonoidHom.ker := by
  intro g hg
  have himage : sqQuadraticDetectorHom h κ hκ g ∈
      twoCentralSeries
        (GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)) 3 :=
    map_twoCentralSeries_le
      (sqQuadraticDetectorHom h κ hκ).toMonoidHom
      (sqQuadraticDetectorHom h κ hκ).continuous_toFun 3 ⟨g, hg, rfl⟩
  rw [twoCentralSeries_three_centExt_eq_bot
    (sqQuadraticDetectorCocycle_isCup h κ)] at himage
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp himage)

/-- An admissible quadratic detector factored through `DSq h / lambda_3`. -/
noncomputable def sqQuadraticDetectorLevelThreeHom (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    levelQuot (DSq h : Type) 3 →*
      GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ) :=
  QuotientGroup.lift (twoCentralSeries (DSq h : Type) 3)
    (sqQuadraticDetectorHom h κ hκ).toMonoidHom
    (twoCentralSeries_three_le_sqQuadraticDetectorHom_ker h κ hκ)

@[simp] theorem sqQuadraticDetectorLevelThreeHom_levelMk (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) (g : DSq h) :
    sqQuadraticDetectorLevelThreeHom h κ hκ
        (levelMk (DSq h : Type) 3 g) =
      sqQuadraticDetectorHom h κ hκ g :=
  rfl

/-- A cup-cocycle fibre coordinate vanishes on a group element whose group-like difference
has augmentation order at least three. -/
theorem centExtFib_eq_zero_of_groupDifference_mem_augmentation_cube
    {Q : Type} [Group Q] [Fintype Q]
    (hc : IsCupCocycle c) (φ : Q →* GQ2.DRCoh.CentExt c) (q : Q)
    (hq : modTwoFiniteGroupDifference Q q ∈
      modTwoFiniteAugmentationIdeal Q ^ 3) :
    (φ q).fib = 0 := by
  have hzero :=
    modTwoGroupAlgebraFunctionMoment_eq_zero_of_mem_augmentation_cube
      hc φ (modTwoFiniteGroupDifference Q q) hq
  rw [modTwoFiniteGroupDifference, map_sub,
    ] at hzero
  change modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib)
      (MonoidAlgebra.single q 1) -
      modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib) 1 = 0 at hzero
  rw [modTwoGroupAlgebraFunctionMoment_single, one_mul] at hzero
  have hone : (φ (1 : Q)).fib = 0 := by simp
  rw [MonoidAlgebra.one_def,
    modTwoGroupAlgebraFunctionMoment_single, one_mul, hone, sub_zero] at hzero
  exact hzero

#print axioms twoCentralSeries_three_centExt_eq_bot
#print axioms twoCentralSeries_three_le_sqQuadraticDetectorHom_ker
#print axioms centExtFib_eq_zero_of_groupDifference_mem_augmentation_cube

end

end GQ2.ContCoh
