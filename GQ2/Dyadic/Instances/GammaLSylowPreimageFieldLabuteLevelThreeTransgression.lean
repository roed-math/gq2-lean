/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeSeed
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHigherTransgression
import GQ2.Dyadic.Count.LowerTwoCentralJenningsDegreeTwoReverse
import GQ2.Dyadic.Count.H3SqRowInitialForms
import GQ2.Dyadic.MaxProTwoCohomology
import GQ2.Devissage.ElemDualPack

/-!
# The finite transgression realization theorem

This file proves `OddDegreeSqLevelThreeRelationRealization`, the exact missing transgression
statement of the level-three seed: every cup-adapted Frattini frame kills the literal improved
word `Y²[S,X]·∏ⱼ[Uⱼ,Vⱼ]` modulo `λ₃`.

The proof is a finite duality argument.  Write `G = G_K(2)`, `Q = G/λ₂`, and let `W` be the
improved relator word evaluated at the frame's actual generators.

* `W` lies in `λ₂` (`levelThreeTransgression.sqRelWord_mem_twoCentralSeries_two`): its image in
  the elementary quotient `Q` is `x̄₀⁻⁴·x̄₁² = 1`.
* The class of `W` in `λ₂/λ₃` vanishes iff every mod-two character `χ` of the layer kills it
  (`GQ2.FoxH.elemDual_separates`).
* For each `χ`, the stage-two transgression machinery produces a **cup-cocycle detector**
  (`levelThreeTransgression.exists_cupDetector_of_zLayerCharacter`): a bi-additive normalized
  two-cocycle `c` on `Q` and a continuous homomorphism `φ : G → CentExt c` over `G → Q` whose
  fibre restricted to `λ₂` computes `χ` on the layer.  The bi-additive representative comes from
  the quadratic-map normal form of `H²(Q, 𝔽₂)` (`elementaryH2EquivQuadratic`), and the primitive
  from the transgression coboundary plus the comparison cochain between the two representatives.
* Since central square-one offsets do not move the improved word
  (`levelThreeTransgression.sqRelWord_mul_central`), the fibre of `φ(W)` is the Gram contraction
  `sqRelatorQuadraticInitialGram` of `c` at the generator images
  (`sqRelWord_centLift_fib_eq_quadraticInitialGram`).
* Finally the Gram contraction vanishes: expanding the bi-additive cocycle in a mod-two basis
  of `Q` writes the matrix as a finite sum of rank-one character products; `IsCupAdapted`
  converts each Gram term into a field cup-form value; summing and using naturality of the cup
  product under inflation identifies the total with `inv_K` of the inflation of the class of
  `c` itself — which is zero, because the fibre of `φ` is a continuous primitive for the
  inflated cocycle.

No parity input beyond the statement's hypotheses is used; the argument is uniform in the
handle count.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace levelThreeTransgression

/-! ## Central square-one offsets do not move the improved word -/

section CentralOffsets

variable {H : Type*} [Group H]

/-- Slide a central factor `z` across the right factor of a left-associated product. -/
theorem mul_central_swap {z : H} (hz : ∀ g : H, Commute z g) (a b : H) :
    a * z * b = a * b * z := by
  rw [mul_assoc, (hz b).eq, ← mul_assoc]

/-- Central offsets on both letters shift a conjugate by the central offset of the conjugated
letter only. -/
theorem conjP_mul_central {z w : H} (hz : ∀ g : H, Commute z g) (hw : ∀ g : H, Commute w g)
    (x s : H) : conjP (x * z) (s * w) = conjP x s * z := by
  have hw' : ∀ g : H, Commute w⁻¹ g := fun g => (hw g).inv_left
  simp only [conjP, mul_inv_rev]
  rw [← mul_assoc (w⁻¹ * s⁻¹) x z, ← mul_assoc _ s w,
    mul_central_swap hz (w⁻¹ * s⁻¹ * x) s, mul_central_swap hz (w⁻¹ * s⁻¹ * x * s) w,
    (hw' s⁻¹).eq, mul_central_swap hw' s⁻¹ x, mul_central_swap hw' (s⁻¹ * x) s,
    mul_assoc (s⁻¹ * x * s) w⁻¹ w, inv_mul_cancel, mul_one]

/-- Central offsets cancel inside a commutator. -/
theorem commP_mul_central {z w : H} (hz : ∀ g : H, Commute z g) (hw : ∀ g : H, Commute w g)
    (a b : H) : commP (a * z) (b * w) = commP a b := by
  have hz' : ∀ g : H, Commute z⁻¹ g := fun g => (hz g).inv_left
  have hw' : ∀ g : H, Commute w⁻¹ g := fun g => (hw g).inv_left
  simp only [commP, mul_inv_rev]
  rw [← mul_assoc (z⁻¹ * a⁻¹) w⁻¹ b⁻¹, ← mul_assoc _ a z, ← mul_assoc _ b w,
    mul_central_swap hz (z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ * a) b,
    mul_central_swap hz (z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ * a * b) w,
    mul_central_swap hw' (z⁻¹ * a⁻¹) b⁻¹, mul_central_swap hw' (z⁻¹ * a⁻¹ * b⁻¹) a,
    mul_central_swap hw' (z⁻¹ * a⁻¹ * b⁻¹ * a) b,
    mul_assoc (z⁻¹ * a⁻¹ * b⁻¹ * a * b) w⁻¹ w, inv_mul_cancel, mul_one,
    (hz' a⁻¹).eq, mul_central_swap hz' a⁻¹ b⁻¹, mul_central_swap hz' (a⁻¹ * b⁻¹) a,
    mul_central_swap hz' (a⁻¹ * b⁻¹ * a) b,
    mul_assoc (a⁻¹ * b⁻¹ * a * b) z⁻¹ z, inv_mul_cancel, mul_one]

/-- Central square-one offsets do not move the core word. -/
theorem sqWord_mul_central {z₀ z₁ z₂ : H} (h₀ : ∀ g : H, Commute z₀ g)
    (h₁ : ∀ g : H, Commute z₁ g) (h₂ : ∀ g : H, Commute z₂ g)
    (hz₁ : z₁ ^ 2 = 1) (hz₂ : z₂ ^ 2 = 1) (s x y : H) :
    SqCore.sqWord (s * z₀) (x * z₁) (y * z₂) = SqCore.sqWord s x y := by
  have h₁' : ∀ g : H, Commute z₁⁻¹ g := fun g => (h₁ g).inv_left
  have hz₁inv : z₁⁻¹ * z₁⁻¹ = 1 := by rw [← mul_inv_rev, ← pow_two, hz₁, inv_one]
  have e₁ : conjP (x * z₁) (s * z₀) = conjP x s * z₁ := conjP_mul_central h₁ h₀ x s
  have e₂ : conjP (y * z₂) (s * z₀) = conjP y s * z₂ := conjP_mul_central h₂ h₀ y s
  have e₃ : commP (y * z₂) (conjP y s * z₂) = commP y (conjP y s) :=
    commP_mul_central h₂ h₂ y (conjP y s)
  have e₄ : (y * z₂) ^ 2 = y ^ 2 := by rw [((h₂ y).symm).mul_pow, hz₂, mul_one]
  have e₅ : (x * z₁) ^ 3 = x ^ 3 * z₁ := by
    rw [((h₁ x).symm).mul_pow]
    congr 1
    rw [pow_succ, hz₁, one_mul]
  simp only [SqCore.sqWord]
  rw [e₂, e₁, e₅, e₄, e₃]
  have hcore : (conjP x s * z₁)⁻¹ * (x ^ 3 * z₁)⁻¹ = (conjP x s)⁻¹ * (x ^ 3)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (z₁⁻¹ * (conjP x s)⁻¹) z₁⁻¹ (x ^ 3)⁻¹,
      ← mul_central_swap h₁' z₁⁻¹ (conjP x s)⁻¹, hz₁inv, one_mul]
  rw [hcore]

/-- Central offsets do not move the handle word. -/
theorem handleWord_mul_central {k : ℕ} (u v ζu ζv : Fin k → H)
    (hu : ∀ (j : Fin k) (g : H), Commute (ζu j) g)
    (hv : ∀ (j : Fin k) (g : H), Commute (ζv j) g) :
    MarkedCore.handleWord (fun j => u j * ζu j) (fun j => v j * ζv j) =
      MarkedCore.handleWord u v := by
  unfold MarkedCore.handleWord
  congr 1
  refine List.map_congr_left fun j _ => ?_
  exact commP_mul_central (hu j) (hv j) (u j) (v j)

/-- **Central square-one offsets do not move the improved relator word.**  This is the exact
letter-degree count of `Y²[S,X]·∏ⱼ[Uⱼ,Vⱼ]`: every letter has even total degree. -/
theorem sqRelWord_mul_central {h : ℕ} (m ζ : Fin (SqCore.sqRank h) → H)
    (hζ : ∀ (i : Fin (SqCore.sqRank h)) (g : H), Commute (ζ i) g)
    (hsq : ∀ i : Fin (SqCore.sqRank h), ζ i ^ 2 = 1) :
    SqCore.sqRelWord (fun i => m i * ζ i) = SqCore.sqRelWord m := by
  have e₁ : SqCore.sqWord (m 0 * ζ 0) (m 1 * ζ 1) (m 2 * ζ 2) =
      SqCore.sqWord (m 0) (m 1) (m 2) :=
    sqWord_mul_central (hζ 0) (hζ 1) (hζ 2) (hsq 1) (hsq 2) (m 0) (m 1) (m 2)
  have e₂ : MarkedCore.handleWord
      (fun j => m (SqCore.sqHandleIdxU j) * ζ (SqCore.sqHandleIdxU j))
      (fun j => m (SqCore.sqHandleIdxV j) * ζ (SqCore.sqHandleIdxV j)) =
      MarkedCore.handleWord (fun j => m (SqCore.sqHandleIdxU j))
        (fun j => m (SqCore.sqHandleIdxV j)) :=
    handleWord_mul_central _ _ _ _ (fun j => hζ (SqCore.sqHandleIdxU j))
      (fun j => hζ (SqCore.sqHandleIdxV j))
  change SqCore.sqWord (m 0 * ζ 0) (m 1 * ζ 1) (m 2 * ζ 2) *
      MarkedCore.handleWord
        (fun j => m (SqCore.sqHandleIdxU j) * ζ (SqCore.sqHandleIdxU j))
        (fun j => m (SqCore.sqHandleIdxV j) * ζ (SqCore.sqHandleIdxV j)) =
    SqCore.sqWord (m 0) (m 1) (m 2) *
      MarkedCore.handleWord (fun j => m (SqCore.sqHandleIdxU j))
        (fun j => m (SqCore.sqHandleIdxV j))
  rw [e₁, e₂]

end CentralOffsets

/-! ## The improved word lies in `λ₂` -/

/-- The improved relator word lies in `λ₂` for any marking: its image in the elementary
quotient is `x̄₀⁻⁴·x̄₁² = 1`. -/
theorem sqRelWord_mem_twoCentralSeries_two (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {h : ℕ} (m : Fin (SqCore.sqRank h) → G) :
    SqCore.sqRelWord m ∈ twoCentralSeries G 2 := by
  apply (QuotientGroup.eq_one_iff (SqCore.sqRelWord m)).mp
  change levelMk G 2 (SqCore.sqRelWord m) = 1
  rw [SqCore.map_sqRelWord (levelMk G 2) m]
  letI : CommGroup (levelQuot G 2) :=
    { (inferInstance : Group (levelQuot G 2)) with mul_comm := levelQuot_two_mul_comm }
  rw [SqCore.sqRelWord_comm]
  have hpow : ∀ q : levelQuot G 2, q ^ 2 = 1 := levelQuot_two_pow_two
  have h4 : levelMk G 2 (m 1) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hpow]
  rw [h4, hpow, inv_one, one_mul]

/-! ## Additivity of the Gram contraction -/

/-- The Gram contraction of the zero matrix vanishes. -/
theorem gram_zero (h : ℕ) :
    sqRelatorQuadraticInitialGram h (fun _ _ => (0 : ZMod 2)) = 0 := by
  simp [sqRelatorQuadraticInitialGram]

/-- The Gram contraction is additive in the matrix. -/
theorem gram_add {h : ℕ} (κ κ' : Fin (SqCore.sqRank h) → Fin (SqCore.sqRank h) → ZMod 2) :
    sqRelatorQuadraticInitialGram h (fun i j => κ i j + κ' i j) =
      sqRelatorQuadraticInitialGram h κ + sqRelatorQuadraticInitialGram h κ' := by
  simp only [sqRelatorQuadraticInitialGram, Finset.sum_add_distrib]
  abel

/-- The Gram contraction commutes with finite sums of matrices. -/
theorem gram_sum {h : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → Fin (SqCore.sqRank h) → Fin (SqCore.sqRank h) → ZMod 2) :
    sqRelatorQuadraticInitialGram h (fun i j => ∑ x ∈ S, f x i j) =
      ∑ x ∈ S, sqRelatorQuadraticInitialGram h (f x) := by
  induction S using Finset.induction_on with
  | empty => simpa using gram_zero h
  | insert a S ha ih =>
      rw [Finset.sum_insert ha,
        show (fun i j => ∑ x ∈ insert a S, f x i j) =
          fun i j => f a i j + ∑ x ∈ S, f x i j from
            funext fun i => funext fun j => Finset.sum_insert ha,
        gram_add, ih]

/-! ## The cup-cocycle detector attached to a layer character -/

/-- Every additive character of `λ₂/λ₃` of a finitely generated pro-2 group is computed, on
`λ₂`, by the fibre of a continuous homomorphism into the central extension of the elementary
quotient by a **bi-additive** normalized two-cocycle, lying over the canonical projection.

This is the generic-group form of
`GQ2.ContCoh.exists_elementaryQuadraticDetector_of_zLayerCharacter`, with the base identity of
the detector exposed: the stage-two transgression cocycle of the character is replaced by the
bi-additive representative of its class supplied by the quadratic normal form of `H²` of the
finite elementary quotient, and the comparison coboundary is absorbed into the primitive. -/
theorem exists_cupDetector_of_zLayerCharacter
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (chi : Additive (zLayer G 2) →+ ZMod 2) :
    ∃ (c : GQ2.DRCoh.TwoCocycle (levelQuot G 2))
      (φ : ContinuousMonoidHom G (GQ2.DRCoh.CentExt c)),
      MarkedCore.IsCupCocycle c ∧
      (∀ g : G, (φ g).base = levelMk G 2 g) ∧
      ∀ (g : G) (hg : g ∈ twoCentralSeries G 2),
        (φ g).fib = chi (Additive.ofMul
          (⟨levelMk G 3 g, ⟨g, hg, rfl⟩⟩ : zLayer G 2)) := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : Finite Q := finite_levelQuot G hfg hpro 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with mul_comm := levelQuot_two_mul_comm }
  letI : Fact (∀ q : Q, q ^ 2 = 1) := ⟨levelQuot_two_pow_two⟩
  letI : Module (ZMod 2) (Additive Q) := instModuleZModOfNatNatAdditive_gQ2 Q
  letI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  letI : DistribMulAction Q (ZMod 2) := instDistribMulActionZModOfNatNat_gQ2_1 Q
  letI : ContinuousSMul Q (ZMod 2) := instContinuousSMulZModOfNatNat_gQ2_1 Q
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let z := lowerTwoCentralTransgressionCocycleAt G 2 hfg hpro chi
  let η := H2mk Q (ZMod 2) z
  let qform := elementaryH2EquivQuadratic Q η
  let zq := elementaryQuadraticCocycle Q qform
  let c := elementaryQuadraticDRCocycle Q qform
  have hclass : H2mk Q (ZMod 2) zq = H2mk Q (ZMod 2) z :=
    H2mk_elementaryQuadraticCocycle_equiv Q η
  change (QuotientAddGroup.mk zq : H2 Q (ZMod 2)) = QuotientAddGroup.mk z at hclass
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at hclass
  change (zq - z).1 ∈ B2 Q (ZMod 2) at hclass
  obtain ⟨psi, hpsiC, hpsi⟩ := hclass
  let b0 := lowerTwoCentralKernelPartC1At G 2 hfg hpro chi
  let b : G → ZMod 2 := fun g => b0.1 g + psi (levelMk G 2 g)
  have hpsi_one : psi 1 = 0 := by
    have hp := congrFun hpsi (1, 1)
    change (1 : Q) • psi 1 - psi (1 * 1) + psi 1 = zq.1 (1, 1) - z.1 (1, 1) at hp
    rw [scalarActionZmodTwo_triv Q, one_mul] at hp
    simp only [sub_self, zero_add] at hp
    have hzq : zq.1 (1, 1) = 0 := by
      change c.κ 1 1 = 0
      exact c.norm
    have hz : z.1 (1, 1) = 0 := by
      change chi (Additive.ofMul (lowerTwoCentralSectionDefectAt G 2 1 1)) = 0
      rw [lowerTwoCentralSectionDefectAt_one_one G 2]
      exact map_zero chi
    rwa [hzq, hz, sub_zero] at hp
  have hb_one : b 1 = 0 := by
    change b0.1 1 + psi (levelMk G 2 1) = 0
    rw [map_one, hpsi_one, add_zero]
    change chi (Additive.ofMul (lowerTwoCentralKernelPartAt G 2 1)) = 0
    rw [lowerTwoCentralKernelPartAt_one G 2]
    exact map_zero chi
  have hb_cocycle : ∀ g l : G,
      b (g * l) = b g + b l + c.κ (levelMk G 2 g) (levelMk G 2 l) := by
    intro g l
    have hb0 := congrFun
      (lowerTwoCentralTransgressionAt_inflated_eq_dOne G 2 hfg hpro chi) (g, l)
    change z.1 (levelMk G 2 g, levelMk G 2 l) =
      g • b0.1 l - b0.1 (g * l) + b0.1 g at hb0
    rw [scalarActionZmodTwo_triv G] at hb0
    have hp := congrFun hpsi (levelMk G 2 g, levelMk G 2 l)
    change (levelMk G 2 g) • psi (levelMk G 2 l) -
        psi (levelMk G 2 g * levelMk G 2 l) + psi (levelMk G 2 g) =
      zq.1 (levelMk G 2 g, levelMk G 2 l) - z.1 (levelMk G 2 g, levelMk G 2 l) at hp
    rw [scalarActionZmodTwo_triv Q, ← map_mul (levelMk G 2) g l] at hp
    change b0.1 (g * l) + psi (levelMk G 2 (g * l)) =
      (b0.1 g + psi (levelMk G 2 g)) + (b0.1 l + psi (levelMk G 2 l)) +
        c.κ (levelMk G 2 g) (levelMk G 2 l)
    have hcz : c.κ (levelMk G 2 g) (levelMk G 2 l) =
        zq.1 (levelMk G 2 g, levelMk G 2 l) := rfl
    rw [hcz]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -hb0 - hp
  let φ : ContinuousMonoidHom G (GQ2.DRCoh.CentExt c) :=
    { toMonoidHom :=
        { toFun := fun g => ((levelMk G 2 g, b g) : GQ2.DRCoh.CentExt c)
          map_one' := GQ2.DRCoh.CentExt.ext (map_one (levelMk G 2)) hb_one
          map_mul' := by
            intro g l
            apply GQ2.DRCoh.CentExt.ext
            · exact map_mul (levelMk G 2) g l
            · change b (g * l) = b g + b l + c.κ (levelMk G 2 g) (levelMk G 2 l)
              exact hb_cocycle g l }
      continuous_toFun := by
        have hpair : Continuous fun g : G =>
            (levelMk G 2 g, b0.1 g + psi (levelMk G 2 g)) :=
          (continuous_levelMk G 2).prodMk
            (b0.2.add (hpsiC.comp (continuous_levelMk G 2)))
        rw [DiscreteTopology.eq_bot (α := Q × ZMod 2)] at hpair
        change @Continuous G (Q × ZMod 2) _ ⊥
          (fun g => (levelMk G 2 g, b0.1 g + psi (levelMk G 2 g)))
        exact hpair }
  refine ⟨c, φ, elementaryQuadraticDRCocycle_isCup Q qform, fun g => rfl, ?_⟩
  intro g hg
  change b0.1 g + psi (levelMk G 2 g) = _
  have hlevel : levelMk G 2 g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  rw [hlevel, hpsi_one, add_zero]
  change chi (Additive.ofMul (lowerTwoCentralKernelPartAt G 2 g)) = _
  congr 2
  apply Subtype.ext
  exact lowerTwoCentralKernelPartAt_coe_of_mem G 2 hg

/-! ## Vanishing of the Gram contraction -/

/-- **The generic heart of the finite transgression realization.**  Let `G` be a finitely
generated pro-2 group, `c` a bi-additive normalized two-cocycle on its elementary quotient
that becomes a coboundary over `G` through a continuous homomorphism `φ` lying over the
projection, and `ℓ` an additive functional on `H²(G, 𝔽₂)` whose values on cup products of
character classes realize the improved relator's Gram contraction at a marking `gens`.  Then
the Gram contraction of `c` at the images of the marking vanishes.

Expanding `c` in a mod-two basis of the elementary quotient writes the contraction matrix as a
finite sum of rank-one products of inflated coordinate characters; the pairing hypothesis
turns each Gram term into an `ℓ`-value; naturality of the cup product under inflation
recombines the sum into `ℓ` of the inflation of the class of `c`, which dies because the fibre
of `φ` is a continuous primitive of the inflated cocycle. -/
theorem gram_vanishes_aux
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) {h : ℕ}
    (gens : Fin (SqCore.sqRank h) → G)
    (c : GQ2.DRCoh.TwoCocycle (levelQuot G 2)) (hc : MarkedCore.IsCupCocycle c)
    (φ : ContinuousMonoidHom G (GQ2.DRCoh.CentExt c))
    (hbase : ∀ g : G, (φ g).base = levelMk G 2 g)
    (ℓ :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      H2 G (ZMod 2) →+ ZMod 2)
    (hpair :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      ∀ cG dG : ContinuousMonoidHom G (Multiplicative (ZMod 2)),
        ℓ (trivialCupPairing 2 G (fun _ _ => rfl)
            (H1mk G (ZMod 2) (Count.homEquivZ1 cG))
            (H1mk G (ZMod 2) (Count.homEquivZ1 dG))) =
          sqRelatorQuadraticInitialGram h (fun i j =>
            Multiplicative.toAdd (cG (gens i)) * Multiplicative.toAdd (dG (gens j)))) :
    sqRelatorQuadraticInitialGram h
      (fun i j => c.κ (levelMk G 2 (gens i)) (levelMk G 2 (gens j))) = 0 := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : Finite Q := finite_levelQuot G hfg hpro 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with mul_comm := levelQuot_two_mul_comm }
  letI : Fact (∀ q : Q, q ^ 2 = 1) := ⟨levelQuot_two_pow_two⟩
  letI : Module (ZMod 2) (Additive Q) := instModuleZModOfNatNatAdditive_gQ2 Q
  letI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  letI : DistribMulAction Q (ZMod 2) := instDistribMulActionZModOfNatNat_gQ2_1 Q
  letI : ContinuousSMul Q (ZMod 2) := instContinuousSMulZModOfNatNat_gQ2_1 Q
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  -- The bi-additive cocycle as a bilinear form on the additive elementary quotient.
  let Bform : LinearMap.BilinForm (ZMod 2) (Additive Q) :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w => c.κ v.toMul w.toMul)
            (fun w w' => hc.addRight v.toMul w.toMul w'.toMul)))
        (fun v v' => by
          apply LinearMap.ext
          intro w
          exact hc.addLeft v.toMul v'.toMul w.toMul))
  have hB : ∀ v w : Q, c.κ v w = Bform (Additive.ofMul v) (Additive.ofMul w) :=
    fun v w => rfl
  let bas := Module.finBasis (ZMod 2) (Additive Q)
  let d := Module.finrank (ZMod 2) (Additive Q)
  -- Basis expansion of the bilinear form.
  have hrow : ∀ x w : Additive Q,
      Bform x w = ∑ t : Fin d, bas.repr w t * Bform x (bas t) := by
    intro x w
    conv_lhs => rw [← bas.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, smul_eq_mul]
  have hcol : ∀ u y : Additive Q,
      Bform u y = ∑ s : Fin d, bas.repr u s * Bform (bas s) y := by
    intro u y
    conv_lhs => rw [← bas.sum_repr u]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hexp : ∀ u w : Additive Q, Bform u w =
      ∑ p : Fin d × Fin d,
        bas.repr u p.1 * bas.repr w p.2 * Bform (bas p.1) (bas p.2) := by
    intro u w
    rw [Fintype.sum_prod_type, hcol u w]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrow (bas s) w, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show bas.repr u s * (bas.repr w t * Bform (bas s) (bas t)) =
      bas.repr u s * bas.repr w t * Bform (bas s) (bas t)
    ring
  -- Coordinate characters of the elementary quotient and their inflations.
  let qChar : (Additive Q →+ ZMod 2) → ContinuousMonoidHom Q (Multiplicative (ZMod 2)) :=
    fun f =>
      { toFun := fun v => Multiplicative.ofAdd (f (Additive.ofMul v))
        map_one' := by simp
        map_mul' := fun v w => by simp
        continuous_toFun := continuous_of_discreteTopology }
  let lmHom : ContinuousMonoidHom G Q := ⟨levelMk G 2, continuous_levelMk G 2⟩
  let gChar : (Additive Q →+ ZMod 2) →
      ContinuousMonoidHom G (Multiplicative (ZMod 2)) :=
    fun f => (qChar f).comp lmHom
  let cFn : Fin d → Additive Q →+ ZMod 2 := fun s =>
    AddMonoidHom.mk' (fun u => bas.repr u s)
      (fun u u' => by rw [map_add, Finsupp.add_apply])
  let wFn : Fin d × Fin d → Additive Q →+ ZMod 2 := fun p =>
    AddMonoidHom.mk' (fun u => Bform (bas p.1) (bas p.2) * bas.repr u p.1)
      (fun u u' => by rw [map_add, Finsupp.add_apply, mul_add])
  -- The contraction matrix as a finite sum of rank-one character products.
  have hmatrix : (fun i j => c.κ (levelMk G 2 (gens i)) (levelMk G 2 (gens j))) =
      fun i j => ∑ p : Fin d × Fin d,
        Multiplicative.toAdd (gChar (wFn p) (gens i)) *
          Multiplicative.toAdd (gChar (cFn p.2) (gens j)) := by
    funext i j
    rw [hB, hexp]
    refine Finset.sum_congr rfl fun p _ => ?_
    show bas.repr (Additive.ofMul (levelMk G 2 (gens i))) p.1 *
        bas.repr (Additive.ofMul (levelMk G 2 (gens j))) p.2 *
        Bform (bas p.1) (bas p.2) =
      Bform (bas p.1) (bas p.2) *
          bas.repr (Additive.ofMul (levelMk G 2 (gens i))) p.1 *
        bas.repr (Additive.ofMul (levelMk G 2 (gens j))) p.2
    ring
  -- Inflated character classes are inflations of the quotient-level classes.
  have hinfl : ∀ f : Additive Q →+ ZMod 2,
      H1mk G (ZMod 2) (Count.homEquivZ1 (gChar f)) =
        lowerTwoCentralH1InflationAt G 2
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar f))) := by
    intro f
    rfl
  -- The bi-additive cocycle as a continuous two-cocycle on the elementary quotient.
  let zc : ↥(Z2 Q (ZMod 2)) :=
    ⟨fun pr => c.κ pr.1 pr.2, by
      apply mem_Z2_iff.mpr
      refine ⟨continuous_of_discreteTopology, ?_⟩
      intro g h' k
      change c.κ h' k + c.κ g (h' * k) = c.κ (g * h') k + c.κ g h'
      linear_combination -c.cocyc g h' k⟩
  -- The sum of quotient-level cup classes is the class of the cocycle itself.
  have hsumQ : ∑ p : Fin d × Fin d,
      trivialCupPairing 2 Q (fun _ _ => rfl)
        (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
        (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2)))) =
      H2mk Q (ZMod 2) zc := by
    have hterm : ∀ p : Fin d × Fin d,
        trivialCupPairing 2 Q (fun _ _ => rfl)
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
          (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2)))) =
        H2mk Q (ZMod 2)
          ⟨cup11Fun AddMonoidHom.mul (Count.homEquivZ1 (qChar (wFn p))).1
              (Count.homEquivZ1 (qChar (cFn p.2))).1,
            cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
              (Count.homEquivZ1 (qChar (wFn p)))
              (Count.homEquivZ1 (qChar (cFn p.2)))⟩ :=
      fun p => rfl
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← map_sum]
    congr 1
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    funext pr
    rw [Finset.sum_apply]
    show ∑ p : Fin d × Fin d,
        Bform (bas p.1) (bas p.2) * bas.repr (Additive.ofMul pr.1) p.1 *
          bas.repr (Additive.ofMul pr.2) p.2 = c.κ pr.1 pr.2
    rw [hB pr.1 pr.2, hexp]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  -- The class of the cocycle dies under inflation: the fibre of `φ` is a primitive.
  have hker : lowerTwoCentralH2InflationAt G 2 (H2mk Q (ZMod 2) zc) = 0 := by
    rw [show lowerTwoCentralH2InflationAt G 2 =
        inf2 lmHom (fun _ _ => rfl) from rfl, inf2_H2mk]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨fun g => (φ g).fib,
      (continuous_of_discreteTopology :
        Continuous fun p : GQ2.DRCoh.CentExt c => p.fib).comp φ.continuous_toFun, ?_⟩
    funext pr
    obtain ⟨g, l⟩ := pr
    show g • (φ l).fib - (φ (g * l)).fib + (φ g).fib =
      c.κ (levelMk G 2 g) (levelMk G 2 l)
    rw [scalarActionZmodTwo_triv G, map_mul φ g l, GQ2.DRCoh.CentExt.mul_fib,
      hbase g, hbase l]
    calc (φ l).fib - ((φ g).fib + (φ l).fib +
          c.κ (levelMk G 2 g) (levelMk G 2 l)) + (φ g).fib
        = -c.κ (levelMk G 2 g) (levelMk G 2 l) := by ring
      _ = c.κ (levelMk G 2 g) (levelMk G 2 l) := CharTwo.neg_eq _
  -- The `G`-level cup sum vanishes.
  have hGsum : ∑ p : Fin d × Fin d,
      trivialCupPairing 2 G (fun _ _ => rfl)
        (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
        (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2)))) = 0 := by
    have hstep : ∀ p : Fin d × Fin d,
        trivialCupPairing 2 G (fun _ _ => rfl)
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2)))) =
        lowerTwoCentralH2InflationAt G 2
          (trivialCupPairing 2 Q (fun _ _ => rfl)
            (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (wFn p))))
            (H1mk Q (ZMod 2) (Count.homEquivZ1 (qChar (cFn p.2))))) := by
      intro p
      rw [hinfl (wFn p), hinfl (cFn p.2),
        ← lowerTwoCentralH2InflationAt_trivialCupPairing]
    rw [Finset.sum_congr rfl fun p _ => hstep p, ← map_sum, hsumQ, hker]
  -- Assemble.
  rw [hmatrix, gram_sum Finset.univ]
  have hcup : ∀ p : Fin d × Fin d,
      sqRelatorQuadraticInitialGram h
        (fun i j => Multiplicative.toAdd (gChar (wFn p) (gens i)) *
          Multiplicative.toAdd (gChar (cFn p.2) (gens j))) =
      ℓ (trivialCupPairing 2 G (fun _ _ => rfl)
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (wFn p))))
          (H1mk G (ZMod 2) (Count.homEquivZ1 (gChar (cFn p.2))))) :=
    fun p => (hpair (gChar (wFn p)) (gChar (cFn p.2))).symm
  rw [Finset.sum_congr rfl fun p _ => hcup p, ← map_sum, hGsum, map_zero]

local notation "GK2" K => maxProPQuotient 2 (GalK K)

/-- **Vanishing of the Gram contraction on a cup-adapted frame.**  The field-level wrapper of
`gram_vanishes_aux`: the functional is `inv_K` composed with inflation to `G_K`, and the
pairing hypothesis is exactly `IsCupAdapted` read through the compatibility of the mod-two cup
product with inflation along `G_K → G_K(2)`. -/
theorem gram_vanishes
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (c : GQ2.DRCoh.TwoCocycle (levelQuot (GK2 K) 2))
    (hc : MarkedCore.IsCupCocycle c)
    (φ : ContinuousMonoidHom (GK2 K) (GQ2.DRCoh.CentExt c))
    (hbase : ∀ g : GK2 K, (φ g).base = levelMk (GK2 K) 2 g) :
    sqRelatorQuadraticInitialGram h
      (fun i j => c.κ (levelMk (GK2 K) 2 (F.generators i))
        (levelMk (GK2 K) 2 (F.generators j))) = 0 := by
  letI : DistribMulAction (GK2 K) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (GK2 K) (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  refine gram_vanishes_aux (GK2 K) (maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient F.generators c hc φ hbase
    ((FieldData.invGalK K).toAddMonoidHom.comp (h2InflationGalK (K := K))) ?_
  intro cG dG
  rw [← hcup cG dG]
  exact congrArg (FieldData.invGalK K)
    (inf2_trivialCupPairing_maxProPMk_galK
      (SqCyclotomicFrattiniFrame.characterClass (K := K) cG)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) dG))

end levelThreeTransgression

/-! ## The finite transgression realization theorem -/

/-- **The finite transgression realization theorem**: every cup-adapted odd-degree Frattini
frame kills the literal improved word `Y²[S,X]·∏ⱼ[Uⱼ,Vⱼ]` modulo `λ₃`.  This discharges the
second finite supply of the level-three seed.  The parity hypothesis is carried but not
consumed: the argument is uniform in the handle count. -/
theorem oddDegreeSqLevelThreeRelationRealization :
    OddDegreeSqLevelThreeRelationRealization := by
  intro K _ _ _ _ _hodd F hcup
  have hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)) :=
    maxProTwoGalK_isTopologicallyFinGen K
  have hpro : IsProP 2 (maxProPQuotient 2 (GalK K)) := isProP_maxProPQuotient
  change SqCore.sqRelWord
    (fun i => levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i)) = 1
  rw [← SqCore.map_sqRelWord (levelMk (maxProPQuotient 2 (GalK K)) 3) F.generators]
  have hW : SqCore.sqRelWord F.generators ∈
      twoCentralSeries (maxProPQuotient 2 (GalK K)) 2 :=
    levelThreeTransgression.sqRelWord_mem_twoCentralSeries_two _ F.generators
  -- The class of the word in the second layer.
  let zW : zLayer (maxProPQuotient 2 (GalK K)) 2 :=
    ⟨levelMk (maxProPQuotient 2 (GalK K)) 3 (SqCore.sqRelWord F.generators),
      ⟨SqCore.sqRelWord F.generators, hW, rfl⟩⟩
  suffices hz1 : zW = 1 from congrArg Subtype.val hz1
  by_contra hzne
  -- Separation by mod-two characters of the layer.
  letI : CommGroup ↥(zLayer (maxProPQuotient 2 (GalK K)) 2) :=
    { (inferInstance : Group ↥(zLayer (maxProPQuotient 2 (GalK K)) 2)) with
      mul_comm := fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp
          (zLayer_le_center (maxProPQuotient 2 (GalK K)) 2 a.2) b.1).symm }
  have htwo : ∀ a : Additive ↥(zLayer (maxProPQuotient 2 (GalK K)) 2), a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    apply Subtype.ext
    simpa [pow_two] using zLayer_sq (maxProPQuotient 2 (GalK K)) a.toMul.2
  have hzneAdd : Additive.ofMul zW ≠ 0 := by
    intro hz0
    exact hzne (congrArg Additive.toMul hz0)
  obtain ⟨chi, hchi⟩ := GQ2.FoxH.elemDual_separates htwo hzneAdd
  obtain ⟨c, φ, hc, hbase, hfib⟩ :=
    levelThreeTransgression.exists_cupDetector_of_zLayerCharacter
      (maxProPQuotient 2 (GalK K)) hfg hpro chi
  -- The character's value on the class of the word …
  have hval : (φ (SqCore.sqRelWord F.generators)).fib = chi (Additive.ofMul zW) :=
    hfib _ hW
  -- … is a Gram contraction, because the detector's offsets are central and square one …
  have hker : ∀ i, (MarkedCore.centLift c
      (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)))⁻¹ * φ (F.generators i) ∈
      (GQ2.DRCoh.CentExt.proj c).ker := by
    intro i
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change ((MarkedCore.centLift c
      (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i))).base)⁻¹ *
        (φ (F.generators i)).base = 1
    rw [MarkedCore.centLift_base, hbase]
    exact inv_mul_cancel _
  have hcent : ∀ i, ∀ g' : GQ2.DRCoh.CentExt c,
      Commute ((MarkedCore.centLift c
        (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)))⁻¹ *
          φ (F.generators i)) g' := by
    intro i g'
    exact ((Subgroup.mem_center_iff.mp (centExtProj_ker_le_center (hker i))) g').symm
  have hsq1 : ∀ i, ((MarkedCore.centLift c
      (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)))⁻¹ *
        φ (F.generators i)) ^ 2 = 1 :=
    fun i => centExtProj_ker_sq_eq_one (hker i)
  have hword : φ (SqCore.sqRelWord F.generators) =
      SqCore.sqRelWord (fun i => MarkedCore.centLift c
        (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i))) := by
    rw [SqCore.map_sqRelWord φ F.generators]
    calc SqCore.sqRelWord (fun i => φ (F.generators i))
        = SqCore.sqRelWord (fun i =>
            MarkedCore.centLift c
              (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)) *
              ((MarkedCore.centLift c
                (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)))⁻¹ *
                φ (F.generators i))) := by
          congr 1
          funext i
          rw [mul_inv_cancel_left]
      _ = SqCore.sqRelWord (fun i => MarkedCore.centLift c
            (levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i))) :=
          levelThreeTransgression.sqRelWord_mul_central _ _ hcent hsq1
  -- … and the Gram contraction vanishes on a cup-adapted frame.
  have hzero : chi (Additive.ofMul zW) = 0 := by
    rw [← hval, hword, sqRelWord_centLift_fib_eq_quadraticInitialGram hc]
    exact levelThreeTransgression.gram_vanishes K F hcup c hc φ hbase
  exact hchi hzero

#print axioms levelThreeTransgression.exists_cupDetector_of_zLayerCharacter
#print axioms levelThreeTransgression.gram_vanishes
#print axioms oddDegreeSqLevelThreeRelationRealization

end

end GQ2.Dyadic.LSquare
