/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.PadicOmegaProTwo
import GQ2.Dyadic.Instances.GammaRCorePresentationNielsen

/-!
# Rank-generic normalization of the unramified core rows

Once the distinguished `sigma` row has value `1` in `Ztwo`, one simultaneous triangular
Nielsen transformation kills every wild row.  The construction works in every rank and makes
no reference to a dyadic branch, degree, handle count, field, or nilpotency class.

For the additive coordinate `k_i` of the old `i`-th wild row, the forward substitution is
`x_i ↦ x_i * sigma^(-k_i)`.  Its inverse uses `sigma^(k_i)`.  Transporting the complete
`CorePresentation` through this pair immediately gives normalized `FlexibleCoreLeavesRN`.
-/

namespace GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.PadicOmegaProTwo
open GQ2.Dyadic.Instances.GammaRPWordNielsen
open GQ2.Dyadic.Instances.GammaRPWordNielsenElementary
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-- Simultaneously shear every wild letter by a power of `sigma`. -/
def wildShearForward {n : ℕ} (k : Fin (n + 1) → ℤ_[2]) :
    Generator n → PWord (Generator n)
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild i => .mul (.gen (.wild i))
      (.inv (.profPow (.gen .sigma) (padicOmega2 (k i))))

/-- The inverse simultaneous wild shear. -/
def wildShearBackward {n : ℕ} (k : Fin (n + 1) → ℤ_[2]) :
    Generator n → PWord (Generator n)
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild i => .mul (.gen (.wild i))
      (.profPow (.gen .sigma) (padicOmega2 (k i)))

/-- The simultaneous wild shear is one syntactic Nielsen pair. -/
def wildShearNielsen {n : ℕ} (k : Fin (n + 1) → ℤ_[2]) :
    PWordNielsenPair n where
  forward := wildShearForward k
  backward := wildShearBackward k
  backward_forward g := by
    cases g with
    | sigma =>
      simp [wildShearForward, wildShearBackward]
      rfl
    | tau =>
      simp [wildShearForward, wildShearBackward]
      rfl
    | wild i =>
      simp [wildShearForward, wildShearBackward, mul_assoc]
      rfl
  forward_backward g := by
    cases g with
    | sigma =>
      simp [wildShearForward, wildShearBackward]
      rfl
    | tau =>
      simp [wildShearForward, wildShearBackward]
      rfl
    | wild i =>
      simp [wildShearForward, wildShearBackward, mul_assoc]
      rfl

@[simp] theorem wildShearNielsen_forward_sigma {n : ℕ}
    (k : Fin (n + 1) → ℤ_[2]) :
    (wildShearNielsen k).forward .sigma = .gen .sigma := rfl

@[simp] theorem wildShearNielsen_forward_tau {n : ℕ}
    (k : Fin (n + 1) → ℤ_[2]) :
    (wildShearNielsen k).forward .tau = .gen .tau := rfl

@[simp] theorem wildShearNielsen_backward_tau {n : ℕ}
    (k : Fin (n + 1) → ℤ_[2]) :
    (wildShearNielsen k).backward .tau = .gen .tau := rfl

@[simp] theorem wildShearNielsen_forward_wild {n : ℕ}
    (k : Fin (n + 1) → ℤ_[2]) (i : Fin (n + 1)) :
    (wildShearNielsen k).forward (.wild i) =
      .mul (.gen (.wild i))
        (.inv (.profPow (.gen .sigma) (padicOmega2 (k i)))) := rfl

/-- The additive coordinate of an old wild row. -/
def wildNuCoefficient {n : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo) (t : Marking n P)
    (i : Fin (n + 1)) : ℤ_[2] :=
  (ztwoIota (nuP (t (.wild i)))).toAdd

theorem wildShearNielsen_nu_sigma {n : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo) (t : Marking n P)
    (hSigma : nuP (t .sigma) = ztwoOne) :
    nuP ((wildShearNielsen (wildNuCoefficient nuP t)).forwardMark t .sigma) =
      ztwoOne := by
  change nuP (t .sigma) = ztwoOne
  exact hSigma

/-- Every forward wild row has value zero after the simultaneous shear. -/
theorem wildShearNielsen_nu_wild {n : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo) (t : Marking n P)
    (hSigma : nuP (t .sigma) = ztwoOne) (i : Fin (n + 1)) :
    nuP ((wildShearNielsen (wildNuCoefficient nuP t)).forwardMark t (.wild i)) =
      1 := by
  change nuP (t (.wild i) * (t .sigma ^ᶻ
    padicOmega2 (wildNuCoefficient nuP t i))⁻¹) = 1
  rw [map_mul, map_inv, map_zpowHat, hSigma]
  have hpow : ztwoIota
      (ztwoOne ^ᶻ padicOmega2 (wildNuCoefficient nuP t i)) =
      zpowZtwo PropOneOne.isProP_two_multPadicInt
        (Multiplicative.ofAdd (1 : ℤ_[2])) (wildNuCoefficient nuP t i) := by
    calc
      ztwoIota (ztwoOne ^ᶻ padicOmega2 (wildNuCoefficient nuP t i)) =
          ztwoIota ztwoOne ^ᶻ padicOmega2 (wildNuCoefficient nuP t i) :=
        map_zpowHat (ztwoIota : ContinuousMonoidHom (Ztwo : Type)
          (Multiplicative ℤ_[2])) _ _
      _ = Multiplicative.ofAdd (1 : ℤ_[2]) ^ᶻ
          padicOmega2 (wildNuCoefficient nuP t i) := by rw [ztwoIota_ztwoOne]
      _ = _ := zpowHat_padicOmega2_eq_zpowZtwo
        PropOneOne.isProP_two_multPadicInt _ _
  apply ztwoIota.injective
  rw [map_mul, map_inv, hpow]
  rw [SectionThree.zpowZtwo_ofAdd]
  simp [wildNuCoefficient]

/-- A normalized head is enough to turn any core presentation into flexible corrected leaves. -/
noncomputable def normalizedFlexibleCoreLeaves {n : ℕ}
    {R : PWord (Generator n)} {P : ProfiniteGrp}
    (C : CorePresentation n R P) (nuP : ContinuousMonoidHom P Ztwo)
    (hSigma : nuP (C.mark .sigma) = ztwoOne) :
    FlexibleCoreLeavesRN n
      (PWord.subst (wildShearNielsen (wildNuCoefficient nuP C.mark)).backward R)
      P nuP :=
  { presentation := C.ofNielsen
      (wildShearNielsen (wildNuCoefficient nuP C.mark))
      (wildShearNielsen_forward_tau _)
      (wildShearNielsen_backward_tau _)
    nu_sigma := wildShearNielsen_nu_sigma nuP C.mark hSigma
    nu_wild := wildShearNielsen_nu_wild nuP C.mark hSigma }

#print axioms wildShearForward
#print axioms wildShearBackward
#print axioms wildShearNielsen
#print axioms wildNuCoefficient
#print axioms wildShearNielsen_nu_sigma
#print axioms wildShearNielsen_nu_wild
#print axioms normalizedFlexibleCoreLeaves

end

end GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
