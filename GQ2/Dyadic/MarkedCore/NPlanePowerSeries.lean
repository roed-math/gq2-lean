import GQ2.Dyadic.MarkedCore.NPlaneUnitaryShadow
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
/-!
# Completed-ring unitary plane scaling, uniformly in the handle rank

This module constructs the coefficient involution and the isometry on the actual
power-series ring Z2[[X]], with its p-adic coefficient topology. The formulas are
fully integral. No identification with the Alexander module of DN, no assertion
about its intersection form, and no lift to a DN automorphism are made here.
-/

open scoped PowerSeries.WithPiTopology
namespace GQ2.Dyadic.MarkedCore
noncomputable section
open Filter Topology

private def ballIdeal (r : ℝ) (hr : 0 < r) : Ideal ℤ_[2] where
  carrier := {z | ‖z‖ < r}
  zero_mem' := by simpa using hr
  add_mem' := by
    intro x y hx hy
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    change ‖c*x‖ < r
    exact lt_of_le_of_lt ((norm_mul_le c x).trans
      (mul_le_of_le_one_left (norm_nonneg x) (PadicInt.norm_le_one c))) hx

local instance : IsLinearTopology ℤ_[2] ℤ_[2] := by
  apply IsLinearTopology.mk_of_hasBasis ℤ_[2]
    (S := Ideal ℤ_[2]) (s := fun r : {r : ℝ // 0 < r} => ballIdeal r r.2)
    (p := fun _ => True)
  have h := Metric.nhds_basis_ball (x := (0 : ℤ_[2]))
  refine h.to_hasBasis ?_ ?_
  · intro r hr
    refine ⟨⟨r, hr⟩, trivial, ?_⟩
    intro x hx
    simpa [ballIdeal, Metric.mem_ball, dist_zero_right] using hx
  · intro r _
    refine ⟨r, r.2, ?_⟩
    intro x hx
    simpa [ballIdeal, Metric.mem_ball, dist_zero_right] using hx


abbrev NPlaneSeries := PowerSeries ℤ_[2]
def nSeriesDeck : NPlaneSeriesˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp :
    IsUnit (PowerSeries.constantCoeff (1 + PowerSeries.X : NPlaneSeries)))).unit
theorem nSeriesDeck_val : (nSeriesDeck : NPlaneSeries) = 1 + PowerSeries.X := IsUnit.unit_spec _
private theorem deck_const : PowerSeries.constantCoeff (nSeriesDeck : NPlaneSeries) = 1 := by
  rw [nSeriesDeck_val]; simp
private theorem deck_inv_const : PowerSeries.constantCoeff (↑(nSeriesDeck⁻¹) : NPlaneSeries) = 1 := by
  have hh := congrArg PowerSeries.constantCoeff nSeriesDeck.val_inv
  change PowerSeries.constantCoeff nSeriesDeck.inv = 1
  simpa only [map_mul, deck_const, one_mul, map_one] using hh

def nSeriesStarPoint (v : ℤ_[2]ˣ) : NPlaneSeries :=
  PowerSeries.C (v : ℤ_[2]) * (nSeriesDeck⁻¹ : NPlaneSeriesˣ) - 1

theorem nSeriesStarPoint_hasEval (v : ℤ_[2]ˣ) : PowerSeries.HasEval (nSeriesStarPoint v) := by
  change IsTopologicallyNilpotent (nSeriesStarPoint v)
  apply MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff
  change IsTopologicallyNilpotent (PowerSeries.constantCoeff (nSeriesStarPoint v))
  have hc : PowerSeries.constantCoeff (nSeriesStarPoint v) = (v : ℤ_[2]) - 1 := by
    simp [nSeriesStarPoint, deck_inv_const]
  rw [hc]
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  exact (PadicInt.norm_lt_one_iff_dvd _).mpr (two_dvd_val_sub_one v)

/-- The continuous substitution X maps to v/(1+X)-1. The denominator is the
explicit unit 1+X, not an inversion of a nonunit in a fraction field. -/
def nSeriesStar (v : ℤ_[2]ˣ) : NPlaneSeries →ₐ[ℤ_[2]] NPlaneSeries := PowerSeries.aeval (nSeriesStarPoint_hasEval v)
theorem nSeriesStar_continuous (v : ℤ_[2]ˣ) : Continuous (nSeriesStar v) :=
  PowerSeries.continuous_aeval _
theorem nSeriesStar_C (v : ℤ_[2]ˣ) (a : ℤ_[2]) : nSeriesStar v (PowerSeries.C a) = PowerSeries.C a :=
  (nSeriesStar v).commutes a
theorem nSeriesStar_X (v : ℤ_[2]ˣ) : nSeriesStar v PowerSeries.X = nSeriesStarPoint v := by
  simp [nSeriesStar, PowerSeries.coe_aeval, PowerSeries.eval₂_X]
theorem nSeriesStar_deck (v : ℤ_[2]ˣ) :
    nSeriesStar v (nSeriesDeck : NPlaneSeries) = PowerSeries.C (v : ℤ_[2]) * (nSeriesDeck⁻¹ : NPlaneSeriesˣ) := by
  rw [nSeriesDeck_val, map_add, map_one, nSeriesStar_X, nSeriesStarPoint]
  ring

private theorem star_deck_inv (v : ℤ_[2]ˣ) :
    nSeriesStar v (↑(nSeriesDeck⁻¹) : NPlaneSeries) = PowerSeries.C (↑(v⁻¹) : ℤ_[2]) * (nSeriesDeck : NPlaneSeries) := by
  have h : Units.map (nSeriesStar v).toMonoidHom nSeriesDeck =
      Units.map PowerSeries.C.toMonoidHom v * nSeriesDeck⁻¹ := by
    apply Units.ext
    exact nSeriesStar_deck v
  have hi := congrArg Inv.inv h
  have hv := congrArg (fun u : NPlaneSeriesˣ => (u : NPlaneSeries)) hi
  simpa [map_inv, mul_comm] using hv

theorem nSeriesStar_involutive (v : ℤ_[2]ˣ) : Function.Involutive (nSeriesStar v) := by
  have hX : nSeriesStar v (nSeriesStar v PowerSeries.X) = PowerSeries.X := by
    rw [nSeriesStar_X, nSeriesStarPoint, map_sub, map_mul, nSeriesStar_C, star_deck_inv, map_one]
    calc
      PowerSeries.C (v : ℤ_[2]) * (PowerSeries.C (↑(v⁻¹) : ℤ_[2]) * (nSeriesDeck : NPlaneSeries)) - 1
          = PowerSeries.C ((v : ℤ_[2]) * (↑(v⁻¹) : ℤ_[2])) * (nSeriesDeck : NPlaneSeries) - 1 := by
            rw [map_mul]; ring
      _ = PowerSeries.X := by simp [nSeriesDeck_val]
  intro f
  refine (PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[2]).induction_on f
    (isClosed_eq ((nSeriesStar_continuous v).comp (nSeriesStar_continuous v)) continuous_id) ?_
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.coe_add, map_add] using congrArg₂ HAdd.hAdd hp hq
  | monomial n a =>
    rw [Polynomial.coe_monomial]
    rw [PowerSeries.monomial_eq_C_mul_X_pow]
    simp only [map_mul, map_pow, nSeriesStar_C, hX]

def nSeriesStarEquiv (v : ℤ_[2]ˣ) : NPlaneSeries ≃ₐ[ℤ_[2]] NPlaneSeries :=
  { nSeriesStar v with
    invFun := nSeriesStar v
    left_inv := nSeriesStar_involutive v
    right_inv := nSeriesStar_involutive v }

def nSeriesAffineUnit (a : ℤ_[2]) : NPlaneSeriesˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp :
    IsUnit (PowerSeries.constantCoeff (1 + PowerSeries.C a * PowerSeries.X : NPlaneSeries)))).unit
theorem nSeriesAffineUnit_val (a : ℤ_[2]) :
    (nSeriesAffineUnit a : NPlaneSeries) = 1 + PowerSeries.C a * PowerSeries.X := IsUnit.unit_spec _
theorem nSeriesAffineUnit_constantCoeff (a : ℤ_[2]) :
    PowerSeries.constantCoeff (nSeriesAffineUnit a : NPlaneSeries) = 1 := by simp [nSeriesAffineUnit_val]
theorem nSeriesAffineUnit_star_constantCoeff (v : ℤ_[2]ˣ) (a : ℤ_[2]) :
    PowerSeries.constantCoeff (nSeriesStar v (nSeriesAffineUnit a : NPlaneSeries)) = 1 + a*((v : ℤ_[2])-1) := by
  simp [nSeriesAffineUnit_val, nSeriesStar_X, nSeriesStar_C, nSeriesStarPoint, deck_inv_const]

def nSeriesSkewPair (v : ℤ_[2]ˣ) (x y : NPlaneSeries × NPlaneSeries) : NPlaneSeries :=
  nSeriesStar v x.1*y.2-nSeriesStar v x.2*y.1
def nSeriesPlaneScale (v : ℤ_[2]ˣ) (u : NPlaneSeriesˣ) (x : NPlaneSeries × NPlaneSeries) : NPlaneSeries × NPlaneSeries :=
  (nSeriesStar v (u : NPlaneSeries)*x.1, (↑(u⁻¹) : NPlaneSeries)*x.2)
theorem nSeriesPlaneScale_skewPair (v : ℤ_[2]ˣ) (u : NPlaneSeriesˣ) (x y : NPlaneSeries × NPlaneSeries) :
    nSeriesSkewPair v (nSeriesPlaneScale v u x) (nSeriesPlaneScale v u y) = nSeriesSkewPair v x y := by
  have hu : (u : NPlaneSeries)*(↑(u⁻¹) : NPlaneSeries)=1 := u.val_inv
  have hsu : nSeriesStar v (u : NPlaneSeries)*nSeriesStar v (↑(u⁻¹) : NPlaneSeries)=1 := by
    rw [← map_mul, hu, map_one]
  simp only [nSeriesSkewPair, nSeriesPlaneScale, map_mul]
  rw [nSeriesStar_involutive v (u : NPlaneSeries)]
  calc
    _ = ((u : NPlaneSeries)*(↑(u⁻¹) : NPlaneSeries))*(nSeriesStar v x.1*y.2) -
      (nSeriesStar v (u : NPlaneSeries)*nSeriesStar v (↑(u⁻¹) : NPlaneSeries))*(nSeriesStar v x.2*y.1) := by ring
    _ = nSeriesSkewPair v x y := by rw [hu, hsu]; simp [nSeriesSkewPair]

theorem nSeriesPlaneScale_constantCoeff (v : ℤ_[2]ˣ) (a : ℤ_[2]) (x : NPlaneSeries × NPlaneSeries) :
    (PowerSeries.constantCoeff (nSeriesPlaneScale v (nSeriesAffineUnit a) x).1,
     PowerSeries.constantCoeff (nSeriesPlaneScale v (nSeriesAffineUnit a) x).2) =
      ((1+a*((v:ℤ_[2])-1))*PowerSeries.constantCoeff x.1,
        PowerSeries.constantCoeff x.2) := by
  have hi : PowerSeries.constantCoeff (↑((nSeriesAffineUnit a)⁻¹) : NPlaneSeries) = 1 := by
    change PowerSeries.constantCoeff (nSeriesAffineUnit a).inv = 1
    have hi := congrArg PowerSeries.constantCoeff (nSeriesAffineUnit a).val_inv
    simpa only [map_mul, nSeriesAffineUnit_constantCoeff, one_mul, map_one] using hi
  simp [nSeriesPlaneScale, nSeriesAffineUnit_star_constantCoeff, hi]

theorem nSeriesPlaneScale_inverse (v : ℤ_[2]ˣ) (u : NPlaneSeriesˣ) (x : NPlaneSeries × NPlaneSeries) :
    nSeriesPlaneScale v u⁻¹ (nSeriesPlaneScale v u x) = x := by
  have hu : (↑(u⁻¹) : NPlaneSeries)*(u : NPlaneSeries)=1 := u.inv_val
  have hsu : nSeriesStar v (↑(u⁻¹) : NPlaneSeries)*nSeriesStar v (u : NPlaneSeries)=1 := by
    rw [← map_mul, hu, map_one]
  apply Prod.ext
  · change nSeriesStar v (↑(u⁻¹) : NPlaneSeries)*(nSeriesStar v (u : NPlaneSeries)*x.1)=x.1
    rw [← mul_assoc, hsu, one_mul]
  · change (↑(u⁻¹⁻¹) : NPlaneSeries)*((↑(u⁻¹) : NPlaneSeries)*x.2)=x.2
    rw [inv_inv, ← mul_assoc, Units.mul_inv, one_mul]

def nSeriesPlaneScaleEquiv (v : ℤ_[2]ˣ) (u : NPlaneSeriesˣ) : (NPlaneSeries × NPlaneSeries) ≃ₗ[NPlaneSeries] (NPlaneSeries × NPlaneSeries) where
  toFun := nSeriesPlaneScale v u
  invFun := nSeriesPlaneScale v u⁻¹
  left_inv := nSeriesPlaneScale_inverse v u
  right_inv x := by simpa using nSeriesPlaneScale_inverse v u⁻¹ x
  map_add' x y := by ext <;> simp [nSeriesPlaneScale, mul_add]
  map_smul' r x := by ext <;> simp [nSeriesPlaneScale, smul_eq_mul, mul_left_comm]

def nSeriesFullPair (h : ℕ) (v : ℤ_[2]ˣ)
    (x y : (NPlaneSeries × NPlaneSeries) × (Fin h → NPlaneSeries × NPlaneSeries)) : NPlaneSeries :=
  nSeriesSkewPair v x.1 y.1 + ∑ j, nSeriesSkewPair v (x.2 j) (y.2 j)

/-- A genuine all-rank unitary linear automorphism of the completed coefficient
module, with diag(kappa,1) on the constant coefficients of the selected plane
and the identity on every handle. This is not NPlaneScalingHypothesis. -/
theorem exists_nSeriesFullPlaneScale (h : ℕ) {alpha : ℕ} (ha : 2 ≤ alpha) (kappa : ℤ_[2]ˣ) :
    ∃ F : ((NPlaneSeries × NPlaneSeries) × (Fin h → NPlaneSeries × NPlaneSeries)) ≃ₗ[NPlaneSeries]
        ((NPlaneSeries × NPlaneSeries) × (Fin h → NPlaneSeries × NPlaneSeries)),
      (∀ x y, nSeriesFullPair h (nUnit alpha) (F x) (F y) = nSeriesFullPair h (nUnit alpha) x y) ∧
      (∀ x, (F x).2 = x.2) ∧
      (∀ x, (PowerSeries.constantCoeff (F x).1.1,
        PowerSeries.constantCoeff (F x).1.2) =
        ((kappa : ℤ_[2])*PowerSeries.constantCoeff x.1.1,
          PowerSeries.constantCoeff x.1.2)) := by
  obtain ⟨a, ha', _⟩ := exists_nOrientation_affine_unit ha kappa
  refine ⟨(nSeriesPlaneScaleEquiv (nUnit alpha) (nSeriesAffineUnit a)).prodCongr (LinearEquiv.refl NPlaneSeries _), ?_, ?_, ?_⟩
  · intro x y
    change nSeriesSkewPair _ (nSeriesPlaneScale _ _ x.1) (nSeriesPlaneScale _ _ y.1) + ∑ j, nSeriesSkewPair _ (x.2 j) (y.2 j) = _
    rw [nSeriesPlaneScale_skewPair]
    rfl
  · intro x
    rfl
  · intro x
    change (PowerSeries.constantCoeff (nSeriesPlaneScale _ _ x.1).1,
      PowerSeries.constantCoeff (nSeriesPlaneScale _ _ x.1).2) = _
    rw [nSeriesPlaneScale_constantCoeff, ha']

#print axioms NPlaneSeries
#print axioms nSeriesDeck
#print axioms nSeriesDeck_val
#print axioms nSeriesStarPoint
#print axioms nSeriesStarPoint_hasEval
#print axioms nSeriesStar
#print axioms nSeriesStar_continuous
#print axioms nSeriesStar_C
#print axioms nSeriesStar_X
#print axioms nSeriesStar_deck
#print axioms nSeriesStar_involutive
#print axioms nSeriesStarEquiv
#print axioms nSeriesAffineUnit
#print axioms nSeriesAffineUnit_val
#print axioms nSeriesAffineUnit_constantCoeff
#print axioms nSeriesAffineUnit_star_constantCoeff
#print axioms nSeriesSkewPair
#print axioms nSeriesPlaneScale
#print axioms nSeriesPlaneScale_skewPair
#print axioms nSeriesPlaneScale_constantCoeff
#print axioms nSeriesPlaneScale_inverse
#print axioms nSeriesPlaneScaleEquiv
#print axioms nSeriesFullPair
#print axioms exists_nSeriesFullPlaneScale

end
end GQ2.Dyadic.MarkedCore

