/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteBracketSpan
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHigherTransgression

/-!
# Literal Labute atoms as values of the transgression cocycle

This file identifies the two elementary operations in the improved square-presentation
atoms with the corresponding operations on the normalized factor-set cocycle:

* a commutator of lifts is the polarization `c(q,r) + c(r,q)` when `q` and `r` commute;
* the square of a lift is the diagonal value `c(q,q)` when `q ^ 2 = 1`.

The hypotheses are exactly the ones enjoyed by the image of `lambda_(k-1)` in `Q_k`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh
open scoped commutatorElement

section FactorSetIdentities

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The stage-`k` section, viewed one floor higher in the two-central tower. -/
def lowerTwoCentralSectionLiftAt (k : ℕ) (q : levelQuot G k) : levelQuot G (k + 1) :=
  levelMk G (k + 1) (lowerTwoCentralSectionAt G k q)

@[simp] theorem levelProj_lowerTwoCentralSectionLiftAt (k : ℕ) (q : levelQuot G k) :
    levelProj G k (lowerTwoCentralSectionLiftAt G k q) = q := by
  simp [lowerTwoCentralSectionLiftAt]

/-- If two base classes commute, the commutator of their chosen lifts is the product of
the two factor-set values with reversed arguments.  Since the kernel layer has exponent
two, no inverse occurs in this formula. -/
theorem commP_lowerTwoCentralSectionLiftAt (k : ℕ) (q r : levelQuot G k)
    (hqr : q * r = r * q) :
    commP (lowerTwoCentralSectionLiftAt G k q)
        (lowerTwoCentralSectionLiftAt G k r) =
      (lowerTwoCentralSectionDefectAt G k q r).1 *
        (lowerTwoCentralSectionDefectAt G k r q).1 := by
  let sq := lowerTwoCentralSectionLiftAt G k q
  let sr := lowerTwoCentralSectionLiftAt G k r
  let sqr := lowerTwoCentralSectionLiftAt G k (q * r)
  let dqr : levelQuot G (k + 1) := (lowerTwoCentralSectionDefectAt G k q r).1
  let drq : levelQuot G (k + 1) := (lowerTwoCentralSectionDefectAt G k r q).1
  have hdqr : dqr = sq * sr * sqr⁻¹ := by
    simp [dqr, sq, sr, sqr, lowerTwoCentralSectionLiftAt,
      lowerTwoCentralSectionDefectAt, map_mul, map_inv]
  have hdrq : drq = sr * sq * sqr⁻¹ := by
    simp [drq, sq, sr, sqr, lowerTwoCentralSectionLiftAt,
      lowerTwoCentralSectionDefectAt, map_mul, map_inv, hqr]
  have hdqr_central : ∀ w, Commute dqr w :=
    zLayer_commute (lowerTwoCentralSectionDefectAt G k q r).2
  have hdrq_central : ∀ w, Commute drq w :=
    zLayer_commute (lowerTwoCentralSectionDefectAt G k r q).2
  have hdrq_inv : drq⁻¹ = drq :=
    zLayer_inv_self (lowerTwoCentralSectionDefectAt G k r q).2
  have hdqr_drq : Commute dqr drq := hdqr_central drq
  have hsqsr : sq * sr = dqr * sqr := by
    rw [hdqr]
    group
  have hsrsq : sr * sq = drq * sqr := by
    rw [hdrq]
    group
  change commP sq sr = dqr * drq
  calc
    commP sq sr = (sr * sq)⁻¹ * (sq * sr) := by simp only [commP]; group
    _ = (drq * sqr)⁻¹ * (dqr * sqr) := by rw [hsrsq, hsqsr]
    _ = sqr⁻¹ * drq⁻¹ * dqr * sqr := by group
    _ = drq⁻¹ * sqr⁻¹ * dqr * sqr := by
      rw [← (hdrq_central sqr).inv_inv.eq]
    _ = drq⁻¹ * (sqr⁻¹ * dqr) * sqr := by group
    _ = drq⁻¹ * (dqr * sqr⁻¹) * sqr := by
      rw [← (hdqr_central sqr).inv_right.eq]
    _ = drq⁻¹ * dqr * sqr⁻¹ * sqr := by group
    _ = drq⁻¹ * dqr := by group
    _ = drq * dqr := by rw [hdrq_inv]
    _ = dqr * drq := hdqr_drq.eq.symm

/-- If a base class has order at most two, the square of its chosen lift is the diagonal
factor-set value. -/
theorem sq_lowerTwoCentralSectionLiftAt (k : ℕ) (q : levelQuot G k)
    (hq : q ^ 2 = 1) :
    lowerTwoCentralSectionLiftAt G k q ^ 2 =
      (lowerTwoCentralSectionDefectAt G k q q).1 := by
  change levelMk G (k + 1) (lowerTwoCentralSectionAt G k q) ^ 2 =
    levelMk G (k + 1) (lowerTwoCentralSectionAt G k q *
      lowerTwoCentralSectionAt G k q *
        (lowerTwoCentralSectionAt G k (q * q))⁻¹)
  rw [← map_pow]
  rw [pow_two] at hq
  rw [hq, lowerTwoCentralSectionAt_one]
  simp [pow_two]

end FactorSetIdentities

section LiftIdentities

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The commutator of arbitrary lifts of commuting base classes is independent of the lifts. -/
theorem commP_eq_commP_lowerTwoCentralSectionLiftAt (k : ℕ)
    (x y : levelQuot G (k + 1)) :
    commP x y =
      commP (lowerTwoCentralSectionLiftAt G k (levelProj G k x))
        (lowerTwoCentralSectionLiftAt G k (levelProj G k y)) := by
  let q := levelProj G k x
  let r := levelProj G k y
  change commP x y =
    commP (lowerTwoCentralSectionLiftAt G k q) (lowerTwoCentralSectionLiftAt G k r)
  obtain ⟨zx, hzx, hx⟩ := exists_zLayer_mul (G := G) (k := k) (x := x)
    (y := lowerTwoCentralSectionLiftAt G k q) (by simp [q])
  obtain ⟨zy, hzy, hy⟩ := exists_zLayer_mul (G := G) (k := k) (x := y)
    (y := lowerTwoCentralSectionLiftAt G k r) (by simp [r])
  rw [hx, hy, commP_central_left (zLayer_commute hzx),
    commP_central_right (zLayer_commute hzy)]

/-- A commutator of lifts of commuting base classes belongs to the kernel layer. -/
theorem commP_mem_zLayer_of_levelProj_mul_comm (k : ℕ)
    (x y : levelQuot G (k + 1))
    (hxy : levelProj G k x * levelProj G k y =
      levelProj G k y * levelProj G k x) :
    commP x y ∈ zLayer G k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker]
  rw [show levelProj G k (commP x y) =
    commP (levelProj G k x) (levelProj G k y) by simp only [commP, map_mul, map_inv]]
  exact commP_eq_one_of_mul_comm hxy

/-- The square of an arbitrary lift of an order-two base class is independent of the lift. -/
theorem sq_eq_sq_lowerTwoCentralSectionLiftAt (k : ℕ)
    (x : levelQuot G (k + 1)) :
    x ^ 2 = lowerTwoCentralSectionLiftAt G k (levelProj G k x) ^ 2 := by
  let q := levelProj G k x
  change x ^ 2 = lowerTwoCentralSectionLiftAt G k q ^ 2
  obtain ⟨z, hz, hxz⟩ := exists_zLayer_mul (G := G) (k := k) (x := x)
    (y := lowerTwoCentralSectionLiftAt G k q) (by simp [q])
  rw [hxz, (zLayer_commute hz _).mul_pow, zLayer_sq G hz, one_mul]

/-- A square of a lift of an order-two base class belongs to the kernel layer. -/
theorem sq_mem_zLayer_of_levelProj_sq (k : ℕ) (x : levelQuot G (k + 1))
    (hx : levelProj G k x ^ 2 = 1) : x ^ 2 ∈ zLayer G k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_pow, hx]

end LiftIdentities

section CocycleEvaluations

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The transgression cocycle polarizes to the value of the layer character on a
commutator of arbitrary lifts. -/
theorem lowerTwoCentralTransgressionCocycleAt_commP_apply (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (phi : Additive (zLayer G k) →+ ZMod 2)
    (x y : levelQuot G (k + 1))
    (hxy : levelProj G k x * levelProj G k y =
      levelProj G k y * levelProj G k x) :
    phi (Additive.ofMul
      (⟨commP x y, commP_mem_zLayer_of_levelProj_mul_comm G k x y hxy⟩ : zLayer G k)) =
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k x, levelProj G k y) +
        (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k y, levelProj G k x) := by
  change phi (Additive.ofMul
      (⟨commP x y, commP_mem_zLayer_of_levelProj_mul_comm G k x y hxy⟩ : zLayer G k)) =
    phi (Additive.ofMul
      (lowerTwoCentralSectionDefectAt G k (levelProj G k x) (levelProj G k y))) +
    phi (Additive.ofMul
      (lowerTwoCentralSectionDefectAt G k (levelProj G k y) (levelProj G k x)))
  rw [← map_add]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change commP x y =
    (lowerTwoCentralSectionDefectAt G k (levelProj G k x) (levelProj G k y)).1 *
      (lowerTwoCentralSectionDefectAt G k (levelProj G k y) (levelProj G k x)).1
  rw [commP_eq_commP_lowerTwoCentralSectionLiftAt G k x y,
    commP_lowerTwoCentralSectionLiftAt G k _ _ hxy]

/-- The diagonal value of the transgression cocycle is the layer-character value on the
square of any lift of an order-two base class. -/
theorem lowerTwoCentralTransgressionCocycleAt_sq_apply (k : ℕ)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (phi : Additive (zLayer G k) →+ ZMod 2)
    (x : levelQuot G (k + 1)) (hx : levelProj G k x ^ 2 = 1) :
    phi (Additive.ofMul
      (⟨x ^ 2, sq_mem_zLayer_of_levelProj_sq G k x hx⟩ : zLayer G k)) =
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
        (levelProj G k x, levelProj G k x) := by
  change phi (Additive.ofMul
      (⟨x ^ 2, sq_mem_zLayer_of_levelProj_sq G k x hx⟩ : zLayer G k)) =
    phi (Additive.ofMul
      (lowerTwoCentralSectionDefectAt G k (levelProj G k x) (levelProj G k x)))
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change x ^ 2 =
    (lowerTwoCentralSectionDefectAt G k (levelProj G k x) (levelProj G k x)).1
  rw [sq_eq_sq_lowerTwoCentralSectionLiftAt G k x,
    sq_lowerTwoCentralSectionLiftAt G k _ hx]

end CocycleEvaluations

section DepthEvaluations

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A depth-`k-1` modification has central image in `Q_k`. -/
theorem levelProj_mul_comm_of_mem_lambdaImage_pred (k : ℕ) (hk : 3 ≤ k)
    (p g : levelQuot G (k + 1)) (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    levelProj G k p * levelProj G k g = levelProj G k g * levelProj G k p := by
  have hz := commP_mem_zLayer (G := G) k hk hp g
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker] at hz
  have hc : commP (levelProj G k p) (levelProj G k g) = 1 := by
    simpa only [commP, map_mul, map_inv] using hz
  calc
    levelProj G k p * levelProj G k g =
        levelProj G k g * levelProj G k p *
          commP (levelProj G k p) (levelProj G k g) := by simp only [commP]; group
    _ = levelProj G k g * levelProj G k p := by rw [hc, mul_one]

/-- A depth-`k-1` modification has order at most two after projection to `Q_k`. -/
theorem levelProj_sq_of_mem_lambdaImage_pred (k : ℕ) (hk : 3 ≤ k)
    (p : levelQuot G (k + 1)) (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    levelProj G k p ^ 2 = 1 := by
  have hz := sq_mem_zLayer (G := G) k hk hp
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_pow] at hz
  exact hz

/-- Cocycle polarization on the literal bracket atom `[p,g]`, for a depth-`k-1`
modification `p`. -/
theorem lowerTwoCentralTransgressionCocycleAt_depth_commP_apply (k : ℕ) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (phi : Additive (zLayer G k) →+ ZMod 2)
    (p g : levelQuot G (k + 1)) (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    phi (Additive.ofMul
      (⟨commP p g, commP_mem_zLayer (G := G) k hk hp g⟩ : zLayer G k)) =
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k p, levelProj G k g) +
        (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k g, levelProj G k p) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_commP_apply G k hfg hpro phi p g
    (levelProj_mul_comm_of_mem_lambdaImage_pred G k hk p g hp)

/-- Cocycle diagonal evaluation on the literal square atom `p²`, for a depth-`k-1`
modification `p`. -/
theorem lowerTwoCentralTransgressionCocycleAt_depth_sq_apply (k : ℕ) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (phi : Additive (zLayer G k) →+ ZMod 2)
    (p : levelQuot G (k + 1)) (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    phi (Additive.ofMul
      (⟨p ^ 2, sq_mem_zLayer (G := G) k hk hp⟩ : zLayer G k)) =
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
        (levelProj G k p, levelProj G k p) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_sq_apply G k hfg hpro phi p
    (levelProj_sq_of_mem_lambdaImage_pred G k hk p hp)

/-- The mixed literal atom `p²[p,g]` evaluates as the sum of the diagonal and
polarization terms of the factor-set cocycle. -/
theorem lowerTwoCentralTransgressionCocycleAt_depth_sq_mul_commP_apply
    (k : ℕ) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (phi : Additive (zLayer G k) →+ ZMod 2)
    (p g : levelQuot G (k + 1)) (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    phi (Additive.ofMul
      (⟨p ^ 2 * commP p g,
        Subgroup.mul_mem (zLayer G k) (sq_mem_zLayer (G := G) k hk hp)
          (commP_mem_zLayer (G := G) k hk hp g)⟩ : zLayer G k)) =
      (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k p, levelProj G k p) +
        (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k p, levelProj G k g) +
        (lowerTwoCentralTransgressionCocycleAt G k hfg hpro phi).1
          (levelProj G k g, levelProj G k p) := by
  change phi (Additive.ofMul
      (⟨p ^ 2, sq_mem_zLayer (G := G) k hk hp⟩ : zLayer G k) +
    Additive.ofMul
      (⟨commP p g, commP_mem_zLayer (G := G) k hk hp g⟩ : zLayer G k)) = _
  rw [map_add,
    lowerTwoCentralTransgressionCocycleAt_depth_sq_apply G k hk hfg hpro phi p hp,
    lowerTwoCentralTransgressionCocycleAt_depth_commP_apply G k hk hfg hpro phi p g hp,
    add_assoc]

end DepthEvaluations

namespace SqCyclotomicStageTuple

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The first improved core atom `[p,x₁]` is cocycle polarization against generator `1`. -/
theorem sharpNeutralCoreOneTransgressionCocycle_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (phi : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2)
    (p : sharpNeutralCoordinateSubgroup (K := K) (by omega)) :
    phi (Additive.ofMul
      (⟨commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)),
        commP_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1 _⟩ :
          zLayer (maxProPQuotient 2 (GalK K)) k)) =
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1, T.generators 1) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (T.generators 1, GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_depth_commP_apply
    (maxProPQuotient 2 (GalK K)) k hk hfg isProP_maxProPQuotient phi p.1
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)) p.2.1

/-- The second improved core atom `[p,x₀]` is cocycle polarization against generator `0`. -/
theorem sharpNeutralCoreZeroTransgressionCocycle_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (phi : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2)
    (p : sharpNeutralCoordinateSubgroup (K := K) (by omega)) :
    phi (Additive.ofMul
      (⟨commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)),
        commP_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1 _⟩ :
          zLayer (maxProPQuotient 2 (GalK K)) k)) =
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1, T.generators 0) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (T.generators 0, GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_depth_commP_apply
    (maxProPQuotient 2 (GalK K)) k hk hfg isProP_maxProPQuotient phi p.1
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) p.2.1

/-- The mixed improved core atom `p²[p,x₂]` is the diagonal plus polarization against
generator `2`. -/
theorem sharpNeutralCoreTwoTransgressionCocycle_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (phi : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2)
    (p : sharpNeutralCoordinateSubgroup (K := K) (by omega)) :
    phi (Additive.ofMul
      (⟨p.1 ^ 2 * commP p.1
          (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 2)),
        Subgroup.mul_mem _ (sq_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1)
          (commP_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1 _)⟩ :
          zLayer (maxProPQuotient 2 (GalK K)) k)) =
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1,
          GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1, T.generators 2) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (T.generators 2, GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_depth_sq_mul_commP_apply
    (maxProPQuotient 2 (GalK K)) k hk hfg isProP_maxProPQuotient phi p.1
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 2)) p.2.1

/-- The improved `V_j` handle atom `[p,V_j]` is cocycle polarization against its marked
generator. -/
theorem sharpNeutralHandleVTransgressionCocycle_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (phi : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2)
    (j : Fin h) (p : sharpNeutralCoordinateSubgroup (K := K) (by omega)) :
    phi (Additive.ofMul
      (⟨commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxV j))),
        commP_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1 _⟩ :
          zLayer (maxProPQuotient 2 (GalK K)) k)) =
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1,
          T.generators (SqCore.sqHandleIdxV j)) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (T.generators (SqCore.sqHandleIdxV j),
          GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_depth_commP_apply
    (maxProPQuotient 2 (GalK K)) k hk hfg isProP_maxProPQuotient phi p.1
      (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxV j))) p.2.1

/-- The improved `U_j` handle atom `[p,U_j]` is cocycle polarization against its marked
generator. -/
theorem sharpNeutralHandleUTransgressionCocycle_apply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (phi : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2)
    (j : Fin h) (p : sharpNeutralCoordinateSubgroup (K := K) (by omega)) :
    phi (Additive.ofMul
      (⟨commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxU j))),
        commP_mem_zLayer (G := maxProPQuotient 2 (GalK K)) k hk p.2.1 _⟩ :
          zLayer (maxProPQuotient 2 (GalK K)) k)) =
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1,
          T.generators (SqCore.sqHandleIdxU j)) +
      (lowerTwoCentralTransgressionCocycleAt (maxProPQuotient 2 (GalK K)) k hfg
          isProP_maxProPQuotient phi).1
        (T.generators (SqCore.sqHandleIdxU j),
          GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k p.1) := by
  simpa using lowerTwoCentralTransgressionCocycleAt_depth_commP_apply
    (maxProPQuotient 2 (GalK K)) k hk hfg isProP_maxProPQuotient phi p.1
      (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxU j))) p.2.1

end SqCyclotomicStageTuple

end

end GQ2.Dyadic.LSquare
