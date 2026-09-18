import GQ2.Dyadic.MarkedCore.NPlaneCentralCorrection

/-!
# A concrete integral two-evaluation unitary shadow of N plane scaling

The ring is Z2 ×_{F2} Z2 with involution swapping the two evaluations. We
construct, not assume, unitary plane scalings having ordinary specialization
diag(kappa,1) and fixing an arbitrary handle tail. The orientation-point
interpolation is also exact. No identification with a DN Alexander module and
no lifting from this ring to a group automorphism is asserted.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2
noncomputable section

/-- The integral compatibility ring of two evaluations agreeing modulo two. -/
def nPlaneShadowSubring : Subring (ℤ_[2] × ℤ_[2]) :=
  (nRed.comp (RingHom.fst _ _)).eqLocus (nRed.comp (RingHom.snd _ _))

abbrev NPlaneShadow := nPlaneShadowSubring

def nShadowFirst : NPlaneShadow →+* ℤ_[2] :=
  (RingHom.fst _ _).comp nPlaneShadowSubring.subtype

def nShadowSecond : NPlaneShadow →+* ℤ_[2] :=
  (RingHom.snd _ _).comp nPlaneShadowSubring.subtype

/-- Swapping the orientation and ordinary evaluations is an actual involution. -/
def nShadowSwap : NPlaneShadow ≃+* NPlaneShadow where
  toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
  invFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def nShadowScalar (a : ℤ_[2]) : NPlaneShadow := ⟨(a,a), rfl⟩

/-- The compatible pair (1,kappa), with its inverse exhibited. -/
def nShadowUnit (kappa : ℤ_[2]ˣ) : NPlaneShadowˣ where
  val := ⟨(1, (kappa : ℤ_[2])), by
    change nRed 1 = nRed (kappa : ℤ_[2])
    rw [map_one, nIsUnit_iff_nRed.mp kappa.isUnit]⟩
  inv := ⟨(1, ((kappa⁻¹ : ℤ_[2]ˣ) : ℤ_[2])), by
    change nRed 1 = nRed ((kappa⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
    rw [map_one, nIsUnit_iff_nRed.mp (kappa⁻¹).isUnit]⟩
  val_inv := by apply Subtype.ext; ext <;> simp [← Units.val_mul]
  inv_val := by apply Subtype.ext; ext <;> simp [← Units.val_mul]

/-- Exact integral interpolation at 1 and the actual N orientation value.
The same affine polynomial takes every odd argument to a unit. -/
theorem exists_nOrientation_affine_unit {alpha : ℕ} (ha : 2 ≤ alpha)
    (kappa : ℤ_[2]ˣ) :
    ∃ a : ℤ_[2], 1 + a * ((nUnit alpha : ℤ_[2]) - 1) = (kappa : ℤ_[2]) ∧
      ∀ t : ℤ_[2]ˣ, IsUnit (1 + a * ((t : ℤ_[2]) - 1)) := by
  obtain ⟨s, hs⟩ := exists_nPlaneCentralCorrectionExponent ha kappa
  refine ⟨s * (1 + 2^alpha), ?_, ?_⟩
  · have hv := nUnit_mul (show 1 ≤ alpha by omega)
    calc
      1 + s * (1 + 2^alpha) * ((nUnit alpha : ℤ_[2]) - 1)
          = 1 + s * ((nUnit alpha : ℤ_[2]) * (1 + 2^alpha)) - s*(1+2^alpha) := by ring
      _ = (kappa : ℤ_[2]) := by rw [hv]; linear_combination -hs
  · intro t
    obtain ⟨b, hb⟩ := two_dvd_val_sub_one t
    rw [hb]
    convert isUnit_one_add_two_mul (s * (1 + 2^alpha) * b) using 1
    ring

def nShadowOrientation (alpha : ℕ) : NPlaneShadow := nShadowUnit (nUnit alpha)

/-- Every compatible unit (1,kappa) has a degree-one orientation interpolation.
This supplies explicit coefficients, not a presumed Alexander-module map. -/
theorem nShadowUnit_affine {alpha : ℕ} (ha : 2 ≤ alpha) (kappa : ℤ_[2]ˣ) :
    ∃ a : ℤ_[2], 1 + nShadowScalar a * (nShadowOrientation alpha - 1) =
      (nShadowUnit kappa : NPlaneShadow) := by
  obtain ⟨a, ha', _⟩ := exists_nOrientation_affine_unit ha kappa
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change 1 + a*(1-1) = 1
    ring
  · exact ha'

def nShadowSkewPair (x y : NPlaneShadow × NPlaneShadow) : NPlaneShadow :=
  nShadowSwap x.1 * y.2 - nShadowSwap x.2 * y.1

/-- The two coefficient units are (kappa,1) and (1,kappa^-1).
Their opposite evaluations exactly compensate, rather than scaling all handles. -/
def nShadowPlaneScale (kappa : ℤ_[2]ˣ) (x : NPlaneShadow × NPlaneShadow) :
    NPlaneShadow × NPlaneShadow :=
  (nShadowSwap (nShadowUnit kappa : NPlaneShadow) * x.1,
    (nShadowUnit kappa⁻¹ : NPlaneShadow) * x.2)

theorem nShadowPlaneScale_inverse (kappa : ℤ_[2]ˣ)
    (x : NPlaneShadow × NPlaneShadow) :
    nShadowPlaneScale kappa⁻¹ (nShadowPlaneScale kappa x) = x := by
  apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext <;>
    simp [nShadowPlaneScale, nShadowSwap, nShadowUnit, ← mul_assoc, ← Units.val_mul]

private theorem unit_pair_cancel (u : ℤ_[2]ˣ) (a b : ℤ_[2]) :
    (u : ℤ_[2]) * a * ((u⁻¹ : ℤ_[2]ˣ) * b) = a*b := by
  calc
    _ = ((u : ℤ_[2]) * (u⁻¹ : ℤ_[2]ˣ)) * (a*b) := by ring
    _ = a*b := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem nShadowPlaneScale_skewPair (kappa : ℤ_[2]ˣ)
    (x y : NPlaneShadow × NPlaneShadow) :
    nShadowSkewPair (nShadowPlaneScale kappa x) (nShadowPlaneScale kappa y) =
      nShadowSkewPair x y := by
  apply Subtype.ext
  apply Prod.ext <;>
    simp [nShadowSkewPair, nShadowPlaneScale, nShadowSwap, nShadowUnit]
  · simpa using unit_pair_cancel kappa⁻¹ x.2.val.2 y.1.val.1
  · exact unit_pair_cancel kappa x.1.val.1 y.2.val.2

theorem nShadowPlaneScale_first (kappa : ℤ_[2]ˣ)
    (x : NPlaneShadow × NPlaneShadow) :
    (nShadowFirst (nShadowPlaneScale kappa x).1,
      nShadowFirst (nShadowPlaneScale kappa x).2) =
    ((kappa : ℤ_[2]) * nShadowFirst x.1, nShadowFirst x.2) := by
  simp [nShadowFirst, nShadowPlaneScale, nShadowSwap, nShadowUnit]

/-- The constructed isometry is an actual linear automorphism of the shadow
plane; no group-lifting premise is folded into this record. -/
def nShadowPlaneScaleEquiv (kappa : ℤ_[2]ˣ) :
    (NPlaneShadow × NPlaneShadow) ≃ₗ[NPlaneShadow] (NPlaneShadow × NPlaneShadow) where
  toFun := nShadowPlaneScale kappa
  invFun := nShadowPlaneScale kappa⁻¹
  left_inv := nShadowPlaneScale_inverse kappa
  right_inv x := by simpa using nShadowPlaneScale_inverse kappa⁻¹ x
  map_add' x y := by ext <;> simp [nShadowPlaneScale, mul_add]
  map_smul' r x := by
    ext <;> simp [nShadowPlaneScale, smul_eq_mul, mul_left_comm]

def nShadowFullScaleEquiv (h : ℕ) (kappa : ℤ_[2]ˣ) :
    ((NPlaneShadow × NPlaneShadow) × (Fin h → NPlaneShadow × NPlaneShadow)) ≃ₗ[NPlaneShadow]
    ((NPlaneShadow × NPlaneShadow) × (Fin h → NPlaneShadow × NPlaneShadow)) :=
  (nShadowPlaneScaleEquiv kappa).prodCongr (LinearEquiv.refl NPlaneShadow _)

def nShadowFullPair (h : ℕ)
    (x y : (NPlaneShadow × NPlaneShadow) × (Fin h → NPlaneShadow × NPlaneShadow)) :
    NPlaneShadow := nShadowSkewPair x.1 y.1 + ∑ j, nShadowSkewPair (x.2 j) (y.2 j)

/-- All-rank isometry: one selected core plane changes, every handle is literally
fixed, and ordinary evaluation on the selected plane is diag(kappa,1). -/
theorem nShadowFullPair_planeScale (h : ℕ) (kappa : ℤ_[2]ˣ)
    (x y : (NPlaneShadow × NPlaneShadow) × (Fin h → NPlaneShadow × NPlaneShadow)) :
    nShadowFullPair h (nShadowPlaneScale kappa x.1, x.2)
        (nShadowPlaneScale kappa y.1, y.2) = nShadowFullPair h x y := by
  simp only [nShadowFullPair, nShadowPlaneScale_skewPair]

#print axioms nPlaneShadowSubring
#print axioms nShadowFirst
#print axioms nShadowSecond
#print axioms nShadowSwap
#print axioms nShadowScalar
#print axioms nShadowUnit
#print axioms exists_nOrientation_affine_unit
#print axioms nShadowOrientation
#print axioms nShadowUnit_affine
#print axioms nShadowSkewPair
#print axioms nShadowPlaneScale
#print axioms nShadowPlaneScale_inverse
#print axioms nShadowPlaneScale_skewPair
#print axioms nShadowPlaneScale_first
#print axioms nShadowPlaneScaleEquiv
#print axioms nShadowFullScaleEquiv
#print axioms nShadowFullPair
#print axioms nShadowFullPair_planeScale

end
end GQ2.Dyadic.MarkedCore

