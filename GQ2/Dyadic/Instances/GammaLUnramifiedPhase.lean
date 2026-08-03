/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLDeterminantBridge
import GQ2.Dyadic.Instances.GammaLScalarH2Surjectivity

/-!
# The unramified word phase for the improved L presentation

The improved `L_sq` endpoint is a Wall head together with `h` hyperbolic handle planes.  In the
unramified branch Frobenius acts trivially on the relevant simple `2`-primary module, so the
Wall operator is the identity and the head is just the original quadratic form.  Proposition
6.9 gives that form Arf invariant one.  The handle planes have positive Gauss sign, hence the
complete odd-degree endpoint has the expected negative signed Gauss value.

This file also records the canonical `Z¹/B¹ ≃ H¹` source equivalence in the exact form needed by
`SourceWordPhaseComparison`.  The still-missing comparison is therefore only the pointwise
identity between `QZeroBar` and the evaluated word Hessian; no quotient-surjectivity or
reindexing problem remains hidden in that obligation.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

/-! ## The canonical source quotient equivalence -/

/-- The already-proved bijection `Z¹/B¹ → H¹`, packaged as an equivalence. -/
noncomputable def sourceQuotientH1Equiv
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v) :
    (VCocycle DD rho ⧸ vCobRange DD rho) ≃ H1 Gamma DD.Vmod :=
  Equiv.ofBijective (h1OfVQuot hcomp)
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩

/-- Compose the canonical source quotient equivalence with any additive word model of `H¹`. -/
noncomputable def sourceQuotientWordH1Equiv
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    {W : Type} [AddCommGroup W]
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (e : H1 Gamma DD.Vmod ≃+ W) :
    (VCocycle DD rho ⧸ vCobRange DD rho) ≃ W :=
  (sourceQuotientH1Equiv hcomp).trans e.toEquiv

/-- Build the source/word phase comparison from an `H¹` word model.  After the canonical
quotient equivalence, the only remaining datum is the pointwise phase identity. -/
noncomputable def SourceWordPhaseComparison.ofH1Equiv
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction Gamma DD.Vmod]
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    {W : Type} [Fintype W] {Q : W → ZMod 2}
    (hcomp : ∀ (g : Gamma) (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (e : H1 Gamma DD.Vmod ≃ W)
    (hphase : ∀ x, QZeroBar DD rho htriv x = Q (e (h1OfVQuot hcomp x))) :
    SourceWordPhaseComparison DD rho htriv W Q where
  phaseEquiv := (sourceQuotientH1Equiv hcomp).trans e
  phase_eq := hphase

/-! ## The direct scalar orientation -/

/-- Any additive orientation `H²(Γ, 𝔽₂) ≃ 𝔽₂` computes the abstract coboundary indicator on
cocycles.  The proof uses only the common vanishing locus, so it introduces no duality axiom. -/
theorem iotaB_eq_h2Equiv
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
    (e : H2 Gamma (ZMod 2) ≃+ ZMod 2) (f : Z2 Gamma (ZMod 2)) :
    iotaB f.1 = e (H2mk Gamma (ZMod 2) f) := by
  refine (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _ ?_
  rw [iotaB_eq_zero_iff, e.map_eq_zero_iff, H2mk_eq_zero_iff]

/-! ## Generic Wall-head and Arf lemmas -/

/-- Wall doubling preserves quadraticity.  This reusable declaration extracts the short proof
previously local to the zero-count argument. -/
theorem isQuadraticFp2_qDouble
    {V : Type} [AddCommGroup V] (q : V → ZMod 2) (U : V ≃+ V)
    (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hUq : ∀ v, q (U v) = q v) : IsQuadraticFp2 (qDouble q U) := by
  constructor
  · rw [qDouble, hq.map_zero, map_zero, polar_self q hq h2, add_zero]
  · intro u v w
    rw [polar_qDouble_eq q U hq hUq, polar_qDouble_eq q U hq hUq,
      polar_qDouble_eq q U hq hUq, hq.polar_add_left]
  · intro u v w
    rw [polar_qDouble_eq q U hq hUq, polar_qDouble_eq q U hq hUq,
      polar_qDouble_eq q U hq hUq, ← hq.polar_add_right]
    congr 1
    rw [map_add, map_add]
    abel

/-- If the Wall operator fixes every vector, its doubling is the original form. -/
theorem qDouble_eq_self_of_fixed
    {V : Type} [AddCommGroup V] (q : V → ZMod 2) (U : V ≃+ V)
    (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hU : ∀ v, U v = v) : qDouble q U = q := by
  funext v
  rw [qDouble, hU, polar_self q hq h2, add_zero]

/-- A nonsingular quadratic form of Arf invariant one has the negative Gauss sign. -/
theorem gaussSum_eq_neg_pow_of_arf_one
    {V : Type} [AddCommGroup V] [Fintype V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m : ℕ} (hcard : Fintype.card V = 2 ^ (2 * m)) (harf : arf q = 1) :
    QuadraticFp2.gaussSum q = -(2 ^ m : ℤ) := by
  rcases gaussSum_eq_pow q hq hns hcard with hpos | hneg
  · have hz : arf q = 0 := (arf_eq_zero_iff_gaussSum_pos q).2 (by rw [hpos]; positivity)
    rw [harf] at hz
    exact (one_ne_zero hz).elim
  · exact hneg

/-- The negative candidate zero count forces Arf invariant one.  This is the exact parity/sign
lemma used after Proposition 6.9. -/
theorem arf_eq_one_of_zeroCount_sub
    {V : Type} [AddCommGroup V] [Fintype V]
    (q : V → ZMod 2) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (hzero : zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1)) : arf q = 1 := by
  rw [arf, hzero, Nat.card_eq_fintype_card, hcard]
  rw [ite_eq_right_iff]
  intro hgt
  exfalso
  have hpow : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
  have hle : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have htwod : 2 * 2 ^ (2 * m - 1) = 2 ^ (2 * m) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [Nat.mul_sub_left_distrib, htwod] at hgt
  have htwopow : 0 < 2 * 2 ^ (m - 1) := Nat.mul_pos (by omega) hpow
  omega

/-! ## The full improved L endpoint -/

/-- The normal form of the improved `L_sq` endpoint: a Wall head and `h` hyperbolic planes. -/
def lSqWallHandlePhase
    {V : Type} [AddCommGroup V] (q : V → ZMod 2) (U : V ≃+ V) (h : ℕ) :
    V × (Fin h → V × V) → ZMod 2 :=
  fun p ↦ qDouble q U p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2

/-- In the unramified fixed-operator branch, an Arf-one head gives the expected negative Gauss
value after adjoining all hyperbolic handles. -/
theorem lSqWallHandlePhase_gaussSum_of_fixed_arf_one
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (U : V ≃+ V) (hU : ∀ v, U v = v) (harf : arf q = 1) (h : ℕ) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
      -(2 ^ (m * (2 * h + 1)) : ℤ) := by
  change QuadraticFp2.gaussSum (fun p : V × (Fin h → V × V) =>
    qDouble q U p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2) =
      -(2 ^ (m * (2 * h + 1)) : ℤ)
  rw [lSq_handle_form_gaussSum hq hns hcard (qDouble q U) h,
    qDouble_eq_self_of_fixed q U hq h2 hU,
    gaussSum_eq_neg_pow_of_arf_one q hq hns hcard harf]
  have hexp : m * (2 * h + 1) = m + 2 * m * h := by ring
  rw [hexp, pow_add]
  ring

/-- The preceding endpoint value in the `SourceNumerics` spelling consumed by the determinant
certificate. -/
theorem lSqWallHandlePhase_gaussSum_standardUnram
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (U : V ≃+ V) (hU : ∀ v, U v = v) (harf : arf q = 1) (h : ℕ) :
    QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
      (standardNumerics (2 * h + 1)).gaussUnram m := by
  rw [lSqWallHandlePhase_gaussSum_of_fixed_arf_one hq hns h2 hcard U hU harf h]
  change -(2 ^ (m * (2 * h + 1)) : ℤ) =
    (-1 : ℤ) ^ (2 * h + 1) * 2 ^ ((2 * h + 1) * m)
  rw [Odd.neg_one_pow (odd_two_mul_add_one h), Nat.mul_comm (2 * h + 1) m]
  ring

/-- Concrete unramified closure from the cyclic simple-module hypotheses of Proposition 6.9.
This computes both the Arf invariant and the signed Gauss value of the full improved endpoint. -/
theorem lSqWallHandlePhase_unramified_of_cyclic
    {V Hf : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Group Hf] [Finite Hf] [DistribMulAction Hf V]
    {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) (m : ℕ) (hm : 1 ≤ m)
    (hcard : Fintype.card V = 2 ^ (2 * m))
    (g : Hf) (hgen : ∀ x : Hf, x ∈ Subgroup.zpowers g)
    (hfaith : ∀ a : Hf, (∀ v : V, a • v = v) → a = 1)
    (hsimple : ∀ W : AddSubgroup V,
      (∀ (a : Hf), ∀ w ∈ W, a • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hinv : ∀ (a : Hf) (v : V), q (a • v) = q v)
    (U : V ≃+ V) (hU : ∀ v, U v = v) (h : ℕ) :
    arf q = 1 ∧
      QuadraticFp2.gaussSum (lSqWallHandlePhase q U h) =
        (standardNumerics (2 * h + 1)).gaussUnram m := by
  have hzero := GQ2.GaussSigns.prop_6_9_unramified_of_cyclic q hq hns m hm
    (by simpa only [Nat.card_eq_fintype_card] using hcard) h2 g hgen hfaith hsimple hinv
  have harf := arf_eq_one_of_zeroCount_sub q hm hcard hzero
  exact ⟨harf,
    lSqWallHandlePhase_gaussSum_standardUnram hq hns h2 hcard U hU harf h⟩

end

end GQ2.Dyadic.LSquare
