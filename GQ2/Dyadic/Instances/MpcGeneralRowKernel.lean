/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralChiCorrection
import GQ2.Dyadic.MarkedCore.MFrameExists

/-!
# The general additive row kernel

For every degree and handle count, universal `Z_2`-row neutrality is exactly order at most two
in the topological abelianization.  On the second two-central subgroup the torsion coordinate
also vanishes, so row neutrality is simply trivial abelianization.  This removes the apparent
infinite family of row constraints from the general Mpc correction problem.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralRowKernel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Roe.Labute

private theorem abMk_sq_eq_one_of_rowKer {alpha h : ℕ} (halpha : 1 ≤ alpha)
    {x : DM alpha h} (hx : x ∈ mpcGeneralRowKer alpha h) :
    (GQ2.SectionThree.abMk x) ^ 2 = 1 := by
  have hB : mBHom alpha h (GQ2.SectionThree.abMk x) = 1 :=
    (mem_mpcGeneralRowKer_iff.mp hx) ((mBHom alpha h).comp (mAbMkHom alpha h))
  have hC : mCHom halpha h (GQ2.SectionThree.abMk x) = 1 :=
    (mem_mpcGeneralRowKer_iff.mp hx) ((mCHom halpha h).comp (mAbMkHom alpha h))
  have hD : mDHom alpha h (GQ2.SectionThree.abMk x) = 1 :=
    (mem_mpcGeneralRowKer_iff.mp hx) ((mDHom alpha h).comp (mAbMkHom alpha h))
  have hH : ∀ k, mHHom alpha k (GQ2.SectionThree.abMk x) = 1 := fun k =>
    (mem_mpcGeneralRowKer_iff.mp hx) ((mHHom alpha k).comp (mAbMkHom alpha h))
  apply mPhiHom_injective halpha h
  rw [map_pow, map_one]
  change (ofAdd ((mTHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mBHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mCHom halpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mDHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      fun k => (mHHom alpha k (GQ2.SectionThree.abMk x)).toAdd)) ^ 2 = 1
  rw [← ofAdd_nsmul]
  apply congrArg ofAdd
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change (2 : ℕ) • (mTHom alpha h (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  · change (2 : ℕ) • (mBHom alpha h (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [hB, toAdd_one, smul_zero]
  · change (2 : ℕ) • (mCHom halpha h (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [hC, toAdd_one, smul_zero]
  · change (2 : ℕ) • (mDHom alpha h (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [hD, toAdd_one, smul_zero]
  · funext k
    change (2 : ℕ) • (mHHom alpha k (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [hH k, toAdd_one, smul_zero]

private theorem rowKer_of_abMk_sq_eq_one {alpha h : ℕ} {x : DM alpha h}
    (hx : (GQ2.SectionThree.abMk x) ^ 2 = 1) :
    x ∈ mpcGeneralRowKer alpha h := by
  apply mem_mpcGeneralRowKer_iff.mpr
  intro f
  have hf2 : (f x) ^ 2 = 1 := by
    have H := congrArg (GQ2.SectionThree.abLiftG f) hx
    simpa only [map_pow, map_one, GQ2.SectionThree.abLiftG_abMk] using H
  apply Multiplicative.toAdd.injective
  have hzero : (2 : ℤ_[2]) * toAdd (f x) = 0 := by
    have H := congrArg Multiplicative.toAdd hf2
    rw [pow_two, toAdd_mul, toAdd_one] at H
    simpa [two_mul] using H
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- Universal `Z_2`-row neutrality is exactly order at most two in the full topological
abelianization. -/
theorem mem_mpcGeneralRowKer_iff_abMk_sq_eq_one {alpha h : ℕ} (halpha : 1 ≤ alpha)
    {x : DM alpha h} :
    x ∈ mpcGeneralRowKer alpha h ↔ (GQ2.SectionThree.abMk x) ^ 2 = 1 :=
  ⟨abMk_sq_eq_one_of_rowKer halpha, rowKer_of_abMk_sq_eq_one⟩

private theorem torsion_coord_eq_one_of_mem_lambda_two {alpha h : ℕ} {x : DM alpha h}
    (hx : x ∈ twoCentralSeries (DM alpha h : Type) 2) :
    mTHom alpha h (GQ2.SectionThree.abMk x) = 1 := by
  let f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod 2)) :=
    (mTHom alpha h).comp (mAbMkHom alpha h)
  have hle : twoCentralSeries (DM alpha h : Type) 2 ≤ f.toMonoidHom.ker := by
    rw [twoCentralSeries_succ (DM alpha h : Type) (by omega), twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
      (show IsClosed (f ⁻¹' ({1} : Set (Multiplicative (ZMod 2)))) from
        isClosed_singleton.preimage f.continuous_toFun)
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, -, rfl⟩
      apply MonoidHom.mem_ker.mpr
      rw [map_pow, pow_two]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact CharTwo.add_self_eq_zero _
    · rw [Subgroup.commutator_le]
      intro y _ z _
      apply MonoidHom.mem_ker.mpr
      simp only [commutatorElement_def, map_mul, map_inv]
      rw [mul_comm (f.toMonoidHom y) (f.toMonoidHom z)]
      group
  exact MonoidHom.mem_ker.mp (hle hx)

/-- At depth at least two, row neutrality is exactly triviality in the full topological
abelianization; the residual order-two class cannot occur in the square-commutator layer. -/
theorem mem_mpcGeneralRowKer_iff_abMk_eq_one_of_lambda_two
    {alpha h : ℕ} (halpha : 1 ≤ alpha) {x : DM alpha h}
    (hx : x ∈ twoCentralSeries (DM alpha h : Type) 2) :
    x ∈ mpcGeneralRowKer alpha h ↔ GQ2.SectionThree.abMk x = 1 := by
  constructor
  · intro hrow
    apply mPhiHom_injective halpha h
    have hsq := (mem_mpcGeneralRowKer_iff_abMk_sq_eq_one halpha).mp hrow
    have hB := (mem_mpcGeneralRowKer_iff.mp hrow)
      ((mBHom alpha h).comp (mAbMkHom alpha h))
    have hC := (mem_mpcGeneralRowKer_iff.mp hrow)
      ((mCHom halpha h).comp (mAbMkHom alpha h))
    have hD := (mem_mpcGeneralRowKer_iff.mp hrow)
      ((mDHom alpha h).comp (mAbMkHom alpha h))
    change mBHom alpha h (GQ2.SectionThree.abMk x) = 1 at hB
    change mCHom halpha h (GQ2.SectionThree.abMk x) = 1 at hC
    change mDHom alpha h (GQ2.SectionThree.abMk x) = 1 at hD
    have hH : ∀ k, mHHom alpha k (GQ2.SectionThree.abMk x) = 1 := fun k =>
      (mem_mpcGeneralRowKer_iff.mp hrow) ((mHHom alpha k).comp (mAbMkHom alpha h))
    rw [map_one]
    change ofAdd ((mTHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mBHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mCHom halpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mDHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      fun k => (mHHom alpha k (GQ2.SectionThree.abMk x)).toAdd) = 1
    rw [torsion_coord_eq_one_of_mem_lambda_two hx, hB, hC, hD]
    simp only [toAdd_one, hH]
    rfl
  · intro hab
    apply (mem_mpcGeneralRowKer_iff_abMk_sq_eq_one halpha).mpr
    rw [hab, one_pow]

/-- At every correction depth, the distinguished `C` source is simply the deep kernel of
topological abelianization.  Exact `chiM` neutrality is then automatic. -/
theorem mpcGeneralCorrectionSource_two_eq_abMkKernel
    {alpha h j : ℕ} (halpha : 1 ≤ alpha) (hj : 2 ≤ j) :
    mpcGeneralCorrectionSource alpha h j (2 : Fin (coreRank h)) =
      twoCentralSeries (DM alpha h : Type) j ⊓
        (mAbMkHom alpha h).toMonoidHom.ker := by
  ext x
  rw [mpcGeneralCorrectionSource, if_pos rfl]
  constructor
  · rintro ⟨⟨hdepth, -⟩, hrow⟩
    refine ⟨hdepth, MonoidHom.mem_ker.mpr ?_⟩
    exact (mem_mpcGeneralRowKer_iff_abMk_eq_one_of_lambda_two halpha
      (twoCentralSeries_antitone (G := (DM alpha h : Type)) hj hdepth)).mp hrow
  · rintro ⟨hdepth, hab⟩
    have hab' : GQ2.SectionThree.abMk x = 1 := MonoidHom.mem_ker.mp hab
    have hchi : chiM alpha h x = 1 := by
      have H := congrArg (GQ2.SectionThree.abLiftG (chiM alpha h)) hab'
      simpa only [GQ2.SectionThree.abLiftG_abMk, map_one] using H
    refine ⟨⟨hdepth, MonoidHom.mem_ker.mpr hchi⟩, ?_⟩
    exact (mem_mpcGeneralRowKer_iff_abMk_eq_one_of_lambda_two halpha
      (twoCentralSeries_antitone (G := (DM alpha h : Type)) hj hdepth)).mpr hab'

end

end GQ2.Dyadic.Instances.MpcGeneralRowKernel

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralRowKernel

#print axioms mem_mpcGeneralRowKer_iff_abMk_sq_eq_one
#print axioms mem_mpcGeneralRowKer_iff_abMk_eq_one_of_lambda_two
#print axioms mpcGeneralCorrectionSource_two_eq_abMkKernel

end AxiomPins
