/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteRawSpanStep
import GQ2.Roe.Labute.StageLemma.StageOne

/-!
# The residual tail obstruction for the literal square relator

The augmented span theorem cannot be sharpened by simply deleting its tails.  This file
packages the crossed-derivation obstruction at the first relevant layer.  The construction
uses the actual improved square presentation, including all hyperbolic handles.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

local instance (N : ℕ) : TopologicalSpace (WL N) := ⊥
local instance (N : ℕ) : DiscreteTopology (WL N) := ⟨rfl⟩
local instance (N : ℕ) : TopologicalSpace ((ZMod (2 ^ N))ˣ) := ⊥
local instance (N : ℕ) : DiscreteTopology ((ZMod (2 ^ N))ˣ) := ⟨rfl⟩

private theorem isPGroup_WL_four : IsPGroup 2 (WL 4) := by
  have hcard : Nat.card (WL 4) = 2 ^ (4 + (4 - 1)) := by
    have h1 : Nat.card (WL 4) = Nat.card (ZMod (2 ^ 4)) * Nat.card ((ZMod (2 ^ 4))ˣ) := by
      rw [Nat.card_congr (WordLift.equivProd (A := ZMod (2 ^ 4)) (C := (ZMod (2 ^ 4))ˣ)),
        Nat.card_prod]
    have h2 : Nat.card (ZMod (2 ^ 4)) = 2 ^ 4 := by
      haveI : NeZero (2 ^ 4) := ⟨by positivity⟩
      simp [Nat.card_eq_fintype_card]
    have h3 : Nat.card ((ZMod (2 ^ 4))ˣ) = 2 ^ (4 - 1) := by
      haveI : NeZero (2 ^ 4) := ⟨by positivity⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [h1, h2, h3, ← pow_add]
  exact IsPGroup.of_card hcard

private theorem isProP_WL_four : IsProP 2 (WL 4) :=
  isProP_of_isPGroup isPGroup_WL_four

/-! ## Coordinate derivations of the improved presentation -/

/-- The full `ℤ₂` WordLift marking with arbitrary offset coordinates and the
presentation's canonical orientation as base component. -/
private def sqDerivMark (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    (i : Fin (SqCore.sqRank h)) : WordLift ℤ_[2] ℤ_[2]ˣ :=
  ⟨v i, SqCore.chiSq h (SqCore.sqGen h i)⟩

private theorem sqDerivMark_zero (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    sqDerivMark h v 0 = ⟨v 0, GQ2.Roe.SvalUnit⟩ := by
  ext
  · rfl
  · exact congrArg Units.val (SqCore.chiSq_sigma h)

private theorem sqDerivMark_one (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    sqDerivMark h v 1 = ⟨v 1, GQ2.Roe.rootXUnit⟩ := by
  ext
  · rfl
  · exact congrArg Units.val (SqCore.chiSq_x0 h)

private theorem sqDerivMark_two (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    sqDerivMark h v 2 = ⟨v 2, GQ2.Roe.YvalUnit⟩ := by
  ext
  · rfl
  · exact congrArg Units.val (SqCore.chiSq_x1 h)

private theorem commP_sqDerivMark_handle_eq_one
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) (j : Fin h) :
    commP (sqDerivMark h v (SqCore.sqHandleIdxU j))
      (sqDerivMark h v (SqCore.sqHandleIdxV j)) = 1 := by
  apply commP_eq_one_of_mul_comm
  ext
  · simp only [sqDerivMark, WordLift.mul_u, SqCore.chiSq_handleU,
      SqCore.chiSq_handleV]
    simp [add_comm]
  · simp only [sqDerivMark, WordLift.mul_g, SqCore.chiSq_handleU,
      SqCore.chiSq_handleV, mul_one]

private theorem sqRelWord_sqDerivMark
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    SqCore.sqRelWord (sqDerivMark h v) = 1 := by
  have hcore :
      drWord (⟨v 0, GQ2.Roe.SvalUnit⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)
        ⟨v 1, GQ2.Roe.rootXUnit⟩ ⟨v 2, GQ2.Roe.YvalUnit⟩ = 1 := by
    convert GQ2.Roe.isLabuteOrientation_chiR (v 0) (v 1) (v 2) using 1
    all_goals simp
  rw [SqCore.sqRelWord, sqDerivMark_zero, sqDerivMark_one, sqDerivMark_two,
    SqCore.sqWord_eq_drWord, hcore, one_mul]
  rw [MarkedCore.handleWord]
  apply List.prod_eq_one
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨j, _, rfl⟩ := hz
  exact commP_sqDerivMark_handle_eq_one h v j

/-- The coordinate crossed derivations of `D_sq(h)` at precision `2⁴`.  The handle
coordinates are genuine independent coordinates: their base component is `1`, so their
commutator block vanishes in WordLift while their offsets remain free. -/
noncomputable def sqDerivFour (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    ContinuousMonoidHom (SqCore.DSq h : Type) (WL 4) :=
  SqCore.sqLiftHom h isProP_WL_four
    (fun i ↦ redWL 4 (sqDerivMark h v i)) (by
      rw [← SqCore.map_sqRelWord, sqRelWord_sqDerivMark, map_one])

@[simp] theorem sqDerivFour_sqGen
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    (i : Fin (SqCore.sqRank h)) :
    sqDerivFour h v (SqCore.sqGen h i) = redWL 4 (sqDerivMark h v i) :=
  SqCore.sqLiftHom_gen _ _ _ _ i

/-! ## The cubic vanishing functional -/

/-- The base projection of the coordinate derivation is the canonical orientation,
reduced modulo `16`. -/
private theorem sqDerivFour_base
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) (a : (SqCore.DSq h : Type)) :
    (sqDerivFour h v a).g =
      Units.map (PadicInt.toZModPow 4).toMonoidHom (SqCore.chiSq h a) := by
  let baseMap : ContinuousMonoidHom (WL 4) ((ZMod (2 ^ 4))ˣ) :=
    { toFun := fun p ↦ p.g
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_of_discreteTopology }
  haveI := discreteTopology_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
    (SqCore.isProP_DSq h) 4
  let targetMap : ContinuousMonoidHom (SqCore.DSq h : Type) ((ZMod (2 ^ 4))ˣ) :=
    { toMonoidHom := (chiLevel (SqCore.chiSq h) 4).comp (levelMk (SqCore.DSq h : Type) 4)
      continuous_toFun := (continuous_of_discreteTopology
        (f := ⇑(chiLevel (SqCore.chiSq h) 4))).comp
          (continuous_levelMk (SqCore.DSq h : Type) 4) }
  have heq : baseMap.comp (sqDerivFour h v) = targetMap := by
    apply SqCore.dsq_hom_ext
    intro i
    change (sqDerivFour h v (SqCore.sqGen h i)).g =
      chiLevel (SqCore.chiSq h) 4
        (levelMk (SqCore.DSq h : Type) 4 (SqCore.sqGen h i))
    rw [sqDerivFour_sqGen, chiLevel_levelMk]
    rfl
  have htarget : targetMap a =
      Units.map (PadicInt.toZModPow 4).toMonoidHom (SqCore.chiSq h a) := by
    show chiLevel (SqCore.chiSq h) 4 (levelMk (SqCore.DSq h : Type) 4 a) = _
    rw [chiLevel_levelMk]
  rw [← htarget]
  exact DFunLike.congr_fun heq a

/-- The offset of the repository commutator in a WordLift. -/
private theorem commP_wl_u {R : Type*} [CommRing R]
    (p q : WordLift R Rˣ) :
    (commP p q).u = ((p.g⁻¹ : Rˣ) : R) * (((q.g⁻¹ : Rˣ) : R) - 1) * p.u +
      ((q.g⁻¹ : Rˣ) : R) * (1 - ((p.g⁻¹ : Rˣ) : R)) * q.u := by
  have hp : ((p.g⁻¹ : Rˣ) : R) * (p.g : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [commP, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g,
    Units.smul_def, smul_eq_mul, Units.val_mul]
  linear_combination (((q.g⁻¹ : Rˣ) : R) * q.u) * hp

/-- Membership in `derivKer` forces the divisibility condition on every representative. -/
private theorem derivKer_dvd_four
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Φ : ContinuousMonoidHom G (WL 4)) {k : ℕ} {b : G}
    (hb : levelMk G (k + 1) b ∈ derivKer Φ k) :
    (2 : ZMod (2 ^ 4)) ^ k ∣ (Φ b).u := by
  obtain ⟨a, ha, hab, hda⟩ := hb
  have hmem : a⁻¹ * b ∈ twoCentralSeries G (k + 1) := QuotientGroup.eq.mp hab
  have hcong := (deriv_mem_wlCong (N := 4) (by omega) Φ (by omega) hmem).1
  rw [show b = a * (a⁻¹ * b) by group, map_mul, WordLift.mul_u,
    Units.smul_def, smul_eq_mul]
  exact dvd_add hda (Dvd.dvd.mul_left hcong _)

/-- Inversion preserves a `2^j` congruence to `1` in a commutative ring. -/
private theorem pow_two_dvd_unit_inv_sub_one {R : Type*} [CommRing R]
    (g : Rˣ) (j : ℕ) (hg : (2 : R) ^ j ∣ (g : R) - 1) :
    (2 : R) ^ j ∣ ((g⁻¹ : Rˣ) : R) - 1 := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨-((g⁻¹ : Rˣ) : R) * c, ?_⟩
  have hunit : (g : R) * ((g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination -((g⁻¹ : Rˣ) : R) * hc + hunit

/-- Every ordinary bracket row of the improved constructor table is killed by the cubic
functional as soon as the displayed base has orientation `1 mod 4`. -/
private theorem commP_depthTwo_mem_derivKer
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    {a : (SqCore.DSq h : Type)} (ha : a ∈ twoCentralSeries (SqCore.DSq h : Type) 2)
    (b : SqCore.DSq h)
    (hgb : (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v b).g : ZMod (2 ^ 4)) - 1) :
    levelMk (SqCore.DSq h : Type) 4 (commP a b) ∈ derivKer (sqDerivFour h v) 3 := by
  refine ⟨commP a b, ?_, rfl, ?_⟩
  · have hm := commP_mem_twoCentralSucc ha b
    rwa [← twoCentralSeries_succ (SqCore.DSq h : Type) (by omega : 1 ≤ 2)] at hm
  · have hdu := (deriv_mem_wlCong (N := 4) (by omega) (sqDerivFour h v)
        (by omega : 1 ≤ 2) ha).1
    have hgaPadic := dvd_chi_of_mem_twoCentralSeries (SqCore.chiSq h)
      (by omega : 2 ≤ 2) ha
    have hga := (two_pow_dvd_toZModPow_iff (N := 4) (j := 3) (by omega)).mpr hgaPadic
    rw [map_sub, map_one] at hga
    change (2 : ZMod (2 ^ 4)) ^ 3 ∣
      ((Units.map (PadicInt.toZModPow 4).toMonoidHom (SqCore.chiSq h a) :
        (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) - 1 at hga
    rw [← sqDerivFour_base h v a] at hga
    have hgbInv := pow_two_dvd_unit_inv_sub_one (sqDerivFour h v b).g 2 hgb
    have hgaInv := pow_two_dvd_unit_inv_sub_one (sqDerivFour h v a).g 3 hga
    rw [show sqDerivFour h v (commP a b) =
      commP (sqDerivFour h v a) (sqDerivFour h v b) from
        Marking.map_commP (sqDerivFour h v).toMonoidHom a b, commP_wl_u]
    apply dvd_add
    · have hm := mul_dvd_mul hgbInv hdu
      rw [← pow_add] at hm
      have hm' : (2 : ZMod (2 ^ 4)) ^ 3 ∣
          ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) - 1) *
            (sqDerivFour h v a).u := by simpa using hm
      simpa [mul_assoc] using hm'.mul_left
        ((((sqDerivFour h v a).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)))
    · have hneg : (2 : ZMod (2 ^ 4)) ^ 3 ∣
          1 - (((sqDerivFour h v a).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) := by
        simpa [sub_eq_add_neg, add_comm] using hgaInv.neg_right
      exact (hneg.mul_left
        ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)))).mul_right _

/-- Closed offset formula for the twisted diagonal row `p²[p,b]`. -/
private theorem sq_mul_commP_wl_u {R : Type*} [CommRing R]
    (p q : WordLift R Rˣ) :
    (p ^ 2 * commP p q).u =
      (1 + (p.g : R) * ((q.g⁻¹ : Rˣ) : R)) * p.u +
        (p.g : R) ^ 2 * ((q.g⁻¹ : Rˣ) : R) *
          (1 - ((p.g⁻¹ : Rˣ) : R)) * q.u := by
  have hp : (p.g : R) * ((p.g⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [pow_two, WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul,
    Units.val_mul, commP_wl_u]
  linear_combination
    -(p.u * (p.g : R)) * hp +
      (p.u * (p.g : R) * ((q.g⁻¹ : Rˣ) : R)) * hp

/-- The twisted `x₁` row is also killed: its square term is essential and cancels the
otherwise surviving bracket digit. -/
private theorem diagonal_depthTwo_mem_derivKer
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    {a : (SqCore.DSq h : Type)} (ha : a ∈ twoCentralSeries (SqCore.DSq h : Type) 2)
    (b : SqCore.DSq h)
    (hgbPlus : (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v b).g : ZMod (2 ^ 4)) + 1) :
    levelMk (SqCore.DSq h : Type) 4 (a ^ 2 * commP a b) ∈
      derivKer (sqDerivFour h v) 3 := by
  refine ⟨a ^ 2 * commP a b, ?_, rfl, ?_⟩
  · apply Subgroup.mul_mem
    · have hm := sq_mem_twoCentralSeries_succ (SqCore.DSq h : Type) ha
      simpa using hm
    · have hm := commP_mem_twoCentralSucc ha b
      rwa [← twoCentralSeries_succ (SqCore.DSq h : Type) (by omega : 1 ≤ 2)] at hm
  · have hdu := (deriv_mem_wlCong (N := 4) (by omega) (sqDerivFour h v)
        (by omega : 1 ≤ 2) ha).1
    have hgaPadic := dvd_chi_of_mem_twoCentralSeries (SqCore.chiSq h)
      (by omega : 2 ≤ 2) ha
    have hga := (two_pow_dvd_toZModPow_iff (N := 4) (j := 3) (by omega)).mpr hgaPadic
    rw [map_sub, map_one] at hga
    change (2 : ZMod (2 ^ 4)) ^ 3 ∣
      ((Units.map (PadicInt.toZModPow 4).toMonoidHom (SqCore.chiSq h a) :
        (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) - 1 at hga
    rw [← sqDerivFour_base h v a] at hga
    have hgaInv := pow_two_dvd_unit_inv_sub_one (sqDerivFour h v a).g 3 hga
    have hgbInvPlus : (2 : ZMod (2 ^ 4)) ^ 2 ∣
        ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) + 1) := by
      obtain ⟨c, hc⟩ := hgbPlus
      refine ⟨((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4))) * c, ?_⟩
      have hunit : ((sqDerivFour h v b).g : ZMod (2 ^ 4)) *
          (((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      linear_combination
        ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4))) * hc - hunit
    have hgaFour : (2 : ZMod (2 ^ 4)) ^ 2 ∣
        ((sqDerivFour h v a).g : ZMod (2 ^ 4)) - 1 :=
      dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ 3)) hga
    have hcoef : (2 : ZMod (2 ^ 4)) ^ 2 ∣
        1 + ((sqDerivFour h v a).g : ZMod (2 ^ 4)) *
          (((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) := by
      have hs := dvd_add hgbInvPlus (hgaFour.mul_right
        ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4))))
      convert hs using 1
      all_goals ring
    rw [map_mul, map_pow, show sqDerivFour h v (commP a b) =
      commP (sqDerivFour h v a) (sqDerivFour h v b) from
        Marking.map_commP (sqDerivFour h v).toMonoidHom a b, sq_mul_commP_wl_u]
    apply dvd_add
    · have hm := mul_dvd_mul hcoef hdu
      rw [← pow_add] at hm
      simpa using hm
    · have hneg : (2 : ZMod (2 ^ 4)) ^ 3 ∣
          1 - (((sqDerivFour h v a).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) := by
        simpa [sub_eq_add_neg, add_comm] using hgaInv.neg_right
      have hm := hneg.mul_left (((sqDerivFour h v a).g : ZMod (2 ^ 4)) ^ 2)
      have hm' := hm.mul_left
        ((((sqDerivFour h v b).g⁻¹ : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)))
      have hx := hm'.mul_right (sqDerivFour h v b).u
      convert hx using 1
      all_goals ring

private theorem sqDerivFour_sigma_base_sub_one_dvd_four
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v (SqCore.sqGen h 0)).g : ZMod (2 ^ 4)) - 1 := by
  simp only [sqDerivFour_sqGen, redWL_g, sqDerivMark]
  rw [show SqCore.sqGen h 0 = SqCore.dsqSigma h from rfl, SqCore.chiSq_sigma]
  change (2 : ZMod (2 ^ 4)) ^ 2 ∣
    PadicInt.toZModPow 4 (GQ2.Roe.SvalUnit : ℤ_[2]) - 1
  rw [GQ2.Roe.val_SvalUnit]
  rw [GQ2.Roe.Sval_toZModPow_four]
  exact ⟨3, by decide⟩

private theorem sqDerivFour_x0_base_sub_one_dvd_four
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v (SqCore.sqGen h 1)).g : ZMod (2 ^ 4)) - 1 := by
  simp only [sqDerivFour_sqGen, redWL_g, sqDerivMark]
  rw [show SqCore.sqGen h 1 = SqCore.dsqX0 h from rfl, SqCore.chiSq_x0]
  change (2 : ZMod (2 ^ 4)) ^ 2 ∣
    PadicInt.toZModPow 4 (GQ2.Roe.rootXUnit : ℤ_[2]) - 1
  rw [GQ2.Roe.val_rootXUnit]
  rw [GQ2.Roe.rootX_toZModPow_four]
  exact ⟨1, by decide⟩

private theorem sqDerivFour_x1_base_add_one_dvd_four
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v (SqCore.sqGen h 2)).g : ZMod (2 ^ 4)) + 1 := by
  simp only [sqDerivFour_sqGen, redWL_g, sqDerivMark]
  rw [show SqCore.sqGen h 2 = SqCore.dsqX1 h from rfl, SqCore.chiSq_x1]
  change (2 : ZMod (2 ^ 4)) ^ 2 ∣
    PadicInt.toZModPow 4 (GQ2.Roe.YvalUnit : ℤ_[2]) + 1
  rw [GQ2.Roe.val_YvalUnit]
  rw [GQ2.Roe.Yval_toZModPow_four]
  exact ⟨2, by decide⟩

private theorem sqDerivFour_handleU_base_sub_one_dvd_four
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) (j : Fin h) :
    (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v (SqCore.sqGen h (SqCore.sqHandleIdxU j))).g :
        ZMod (2 ^ 4)) - 1 := by
  rw [sqDerivFour_sqGen]
  simp [sqDerivMark, SqCore.chiSq_handleU]

private theorem sqDerivFour_handleV_base_sub_one_dvd_four
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) (j : Fin h) :
    (2 : ZMod (2 ^ 4)) ^ 2 ∣
      ((sqDerivFour h v (SqCore.sqGen h (SqCore.sqHandleIdxV j))).g :
        ZMod (2 ^ 4)) - 1 := by
  rw [sqDerivFour_sqGen]
  simp [sqDerivMark, SqCore.chiSq_handleV]

/-- Every one-coordinate row in the literal improved constructor table belongs to every
coordinate derivation kernel at the cubic layer. -/
private theorem rawDepthCoordinateShift_mem_derivKer
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    (i : Fin (SqCore.sqRank h))
    (p : lambdaImage (SqCore.DSq h : Type) 2 4) :
    ((rawDepthShiftHom (rawMarkedBase (SqCore.sqGen h) 3) (by omega))
        (rawDepthCoordinateCorrection i p)).1 ∈ derivKer (sqDerivFour h v) 3 := by
  obtain ⟨a, ha, hpa⟩ := p.2
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [rawDepthShiftHom_zero_apply]
    rw [← hpa, rawMarkedBase, ← Marking.map_commP]
    exact commP_depthTwo_mem_derivKer h v ha (SqCore.sqGen h 1)
      (sqDerivFour_x0_base_sub_one_dvd_four h v)
  · rw [rawDepthShiftHom_one_apply]
    rw [← hpa, rawMarkedBase, ← Marking.map_commP]
    exact commP_depthTwo_mem_derivKer h v ha (SqCore.sqGen h 0)
      (sqDerivFour_sigma_base_sub_one_dvd_four h v)
  · rw [rawDepthShiftHom_two_apply]
    rw [← hpa, rawMarkedBase, ← map_pow, ← Marking.map_commP, ← map_mul]
    exact diagonal_depthTwo_mem_derivKer h v ha (SqCore.sqGen h 2)
      (sqDerivFour_x1_base_add_one_dvd_four h v)
  · rw [rawDepthShiftHom_handleU_apply]
    rw [← hpa, rawMarkedBase, ← Marking.map_commP]
    exact commP_depthTwo_mem_derivKer h v ha
      (SqCore.sqGen h (SqCore.sqHandleIdxV j))
      (sqDerivFour_handleV_base_sub_one_dvd_four h v j)
  · rw [rawDepthShiftHom_handleV_apply]
    rw [← hpa, rawMarkedBase, ← Marking.map_commP]
    exact commP_depthTwo_mem_derivKer h v ha
      (SqCore.sqGen h (SqCore.sqHandleIdxU j))
      (sqDerivFour_handleU_base_sub_one_dvd_four h v j)

private theorem list_map_prod_eq_single_of_nodup_obstruction
    {H I : Type*} [Monoid H] (l : List I) (j : I) (f : I → H)
    (hj : j ∈ l) (hnodup : l.Nodup)
    (hf : ∀ i ∈ l, i ≠ j → f i = 1) :
    (l.map f).prod = f j := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hj with hij | hj
      · subst i
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hf b (List.mem_cons_of_mem _ hb) (fun hbj ↦ hnd.1 (hbj ▸ hb))
        simp [htail]
      · have hij : i ≠ j := by
          intro h
          exact hnd.1 (h ▸ hj)
        rw [List.map_cons, List.prod_cons, hf i (by simp) hij, one_mul,
          ih hj hnd.2 (fun b hb hbj ↦ hf b (List.mem_cons_of_mem _ hb) hbj)]

/-- A raw depth correction is the ordered product of its one-coordinate corrections. -/
private theorem rawDepthCorrection_eq_prod_coordinate
    (h : ℕ) (V : RawDepthCorrection (SqCore.DSq h : Type) h 3) :
    V = ((List.finRange (SqCore.sqRank h)).map fun i ↦
      rawDepthCoordinateCorrection i
        (⟨V.correction i, V.depth i⟩ : lambdaImage (SqCore.DSq h : Type) 2 4)).prod := by
  classical
  ext j
  let ev : RawDepthCorrection (SqCore.DSq h : Type) h 3 →*
      levelQuot (SqCore.DSq h : Type) 4 :=
    { toFun := fun W ↦ W.correction j
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  change ev V = ev (((List.finRange (SqCore.sqRank h)).map fun i ↦
    rawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage (SqCore.DSq h : Type) 2 4)).prod)
  rw [map_list_prod]
  have hsingle := list_map_prod_eq_single_of_nodup_obstruction
    (List.finRange (SqCore.sqRank h)) j
    (fun i ↦ ev (rawDepthCoordinateCorrection i
      (⟨V.correction i, V.depth i⟩ : lambdaImage (SqCore.DSq h : Type) 2 4)))
    (by simp) (List.nodup_finRange _) (by
      intro i _ hij
      simp [ev, rawDepthCoordinateCorrection_apply, Ne.symm hij])
  simpa [List.map_map, Function.comp_def, ev, rawDepthCoordinateCorrection_apply] using
    hsingle.symm

/-- The whole literal raw shift image is annihilated by every coordinate derivation
functional at the cubic layer. -/
theorem sqCore_rawShiftSpan_le_derivKer
    (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    rawShiftSpan (rawMarkedBase (SqCore.sqGen h) 3) (by omega) ≤
      derivKer (sqDerivFour h v) 3 := by
  rintro z ⟨q, hq, rfl⟩
  obtain ⟨V, rfl⟩ := hq
  rw [rawDepthCorrection_eq_prod_coordinate h V, map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  exact rawDepthCoordinateShift_mem_derivKer h v i ⟨V.correction i, V.depth i⟩

/-! ## A surviving non-twisted tail -/

private def sigmaCoordinate (h : ℕ) : Fin (SqCore.sqRank h) → ℤ_[2] :=
  Pi.single 0 1

private theorem wl_pow_four_u {R : Type*} [CommRing R] (p : WordLift R Rˣ) :
    (p ^ 4).u = (1 + (p.g : R) + (p.g : R) ^ 2 + (p.g : R) ^ 3) * p.u := by
  norm_num [pow_succ, WordLift.mul_u, WordLift.mul_g, Units.smul_def, smul_eq_mul,
    Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem sqDerivFour_sigma_pow_four_u (h : ℕ) :
    (sqDerivFour h (sigmaCoordinate h) ((SqCore.sqGen h 0) ^ 4)).u =
      (12 : ZMod (2 ^ 4)) := by
  rw [map_pow, sqDerivFour_sqGen]
  rw [wl_pow_four_u]
  change (1 + PadicInt.toZModPow 4
      ((SqCore.chiSq h (SqCore.sqGen h 0) : ℤ_[2])) +
        (PadicInt.toZModPow 4 ((SqCore.chiSq h (SqCore.sqGen h 0) : ℤ_[2]))) ^ 2 +
        (PadicInt.toZModPow 4 ((SqCore.chiSq h (SqCore.sqGen h 0) : ℤ_[2]))) ^ 3) *
      PadicInt.toZModPow 4 ((sigmaCoordinate h) 0) = _
  rw [show SqCore.sqGen h 0 = SqCore.dsqSigma h from rfl, SqCore.chiSq_sigma,
    GQ2.Roe.val_SvalUnit, GQ2.Roe.Sval_toZModPow_four]
  simp [sigmaCoordinate]
  decide

private theorem eight_not_dvd_twelve_mod_sixteen :
    ¬(2 : ZMod (2 ^ 4)) ^ 3 ∣ (12 : ZMod (2 ^ 4)) := by
  rintro ⟨c, hc⟩
  have hc' := congrArg (ZMod.castHom (by norm_num : 2 ^ 3 ∣ 2 ^ 4) (ZMod (2 ^ 3))) hc
  rw [map_mul, map_pow, map_ofNat, ZMod.castHom_apply] at hc'
  change (12 : ZMod 8) = (8 : ZMod 8) * ZMod.cast c at hc'
  rw [show (12 : ZMod 8) = 4 by decide, show (8 : ZMod 8) = 0 by decide, zero_mul] at hc'
  exact (by decide : (4 : ZMod 8) ≠ 0) hc'

/-- The `σ⁴` tail is a genuine cokernel class: it is one of the non-twisted tails in the
augmented theorem, but it does not belong to the literal raw shift span. -/
theorem sqCore_sigma_rawTail_not_mem_rawShiftSpan (h : ℕ) :
    rawMarkedBase (SqCore.sqGen h) 3 0 ^ 2 ^ (3 - 1) ∉
      rawShiftSpan (rawMarkedBase (SqCore.sqGen h) 3) (by omega) := by
  intro hmem
  have hker := sqCore_rawShiftSpan_le_derivKer h (sigmaCoordinate h) hmem
  have hker' : levelMk (SqCore.DSq h : Type) 4 ((SqCore.sqGen h 0) ^ 4) ∈
      derivKer (sqDerivFour h (sigmaCoordinate h)) 3 := by
    simpa [rawMarkedBase, ← map_pow] using hker
  have hdvd := derivKer_dvd_four (sqDerivFour h (sigmaCoordinate h)) hker'
  rw [sqDerivFour_sigma_pow_four_u] at hdvd
  exact eight_not_dvd_twelve_mod_sixteen hdvd

/-! ## Public cubic regressions -/

/-- The literal improved-relator shift is not onto the cubic central layer. -/
theorem sqCore_rawShiftSpan_ne_zLayer (h : ℕ) :
    rawShiftSpan (rawMarkedBase (SqCore.sqGen h) 3) (by omega) ≠
      zLayer (SqCore.DSq h : Type) 3 := by
  intro heq
  apply sqCore_sigma_rawTail_not_mem_rawShiftSpan h
  rw [heq]
  simpa using pow_two_pow_mem_lambdaImage
    (rawMarkedBase (SqCore.sqGen h) 3 0) 2

/-- The non-twisted tails enlarge the literal raw shift span already at the cubic layer. -/
theorem sqCore_rawAugmentedSpan_ne_rawShiftSpan (h : ℕ) :
    rawAugmentedSpan (SqCore.sqGen h) 3 (by omega) ≠
      rawShiftSpan (rawMarkedBase (SqCore.sqGen h) 3) (by omega) := by
  intro heq
  apply sqCore_sigma_rawTail_not_mem_rawShiftSpan h
  rw [← heq]
  exact rawTail_mem_rawAugmentedSpan (SqCore.sqGen h) (by omega) 0 (by
    intro heq
    have hv := congrArg Fin.val heq
    rw [SqCore.sqVal_zero, SqCore.sqVal_two] at hv
    omega)

/-- Consequently the cubic pure-square supply isolated by the raw-span analysis is false
for the actual improved square presentation. -/
theorem sqCore_not_rawPureSquareSpanSupply_three (h : ℕ) :
    ¬RawPureSquareSpanSupply (rawMarkedBase (SqCore.sqGen h) 3) (by omega) := by
  intro hsupply
  apply sqCore_rawShiftSpan_ne_zLayer h
  exact (rawPureSquareSpanSupply_iff_rawShiftSpan_eq_zLayer
    (rawMarkedBase (SqCore.sqGen h) 3) (by omega)
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
    (closure_rawMarkedBase_eq_top (SqCore.sqGen h)
      (dsqFinsetTopGen h) (SqCore.isProP_DSq h) (SqCore.dsq_topGen h) 3)).mp hsupply

#print axioms sqCore_rawShiftSpan_le_derivKer
#print axioms sqCore_sigma_rawTail_not_mem_rawShiftSpan
#print axioms sqCore_rawShiftSpan_ne_zLayer
#print axioms sqCore_rawAugmentedSpan_ne_rawShiftSpan
#print axioms sqCore_not_rawPureSquareSpanSupply_three

end

end GQ2.Dyadic.LSquare
