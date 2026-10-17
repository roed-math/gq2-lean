/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowHessian
import GQ2.Dyadic.Instances.TameShadowRamified

/-!
# Ramified shadows in the extraspecial phase extension

The averaging shadow of an endpoint, tame-specializing word vanishes in the
full kappa-zero central extension. This retains the quadratic diagonal and
factor-set action correction, information not supplied by Stokes pairing alone.

Actual triviality of every wild lower base is an explicit hypothesis. It may
be obtained from an independently proved factor-set descent to a projected
head group, but is not inferred merely from trivial action on V. The resolver
hypotheses include the entire extraspecial lift, not just its lower action.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.SectionSix Count Certificates.MProcyclic

local instance {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V] : Finite (SemiProd C V) := inferInstanceAs (Finite (V×C))

/-- The central F2 inclusion as a multiplicative homomorphism. -/
def centExtInclHom {L : Type} [Group L] (c : WordCoh.TwoCocycle L) :
    Multiplicative (ZMod 2) →* WordCoh.CentExt c where
  toFun z := WordCoh.CentExt.incl c z.toAdd
  map_one' := rfl
  map_mul' z w := (centExt_incl_mul z.toAdd w.toAdd).symm

/-- The central inclusion commutes with every lifted element. -/
theorem centExtInclHom_comm {L : Type} [Group L] (c : WordCoh.TwoCocycle L)
    (z : Multiplicative (ZMod 2)) (p : WordCoh.CentExt c) :
    Commute (centExtInclHom c z) p := by
  apply WordCoh.CentExt.ext
  · change (1 : L) * p.base = p.base * 1
    rw [one_mul, mul_one]
  · change z.toAdd+p.fib+c.κ 1 p.base=p.fib+z.toAdd+c.κ p.base 1
    rw [c.κ_one_left, c.κ_one_right, add_zero, add_zero, add_comm]

/-- Central charges split off from a free-word evaluation by their exponent character. -/
theorem centExtWord_central_normalization
    {X L : Type} [Group L] (c : WordCoh.TwoCocycle L)
    (p : X → WordCoh.CentExt c) (r : FreeGroup X) :
    FreeGroup.lift p r = FreeGroup.lift (WordCoh.lift (fun i ↦ (p i).base) c) r *
      centExtInclHom c (FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (p i).fib) r) := by
  let q : X → WordCoh.CentExt c := WordCoh.lift (fun i ↦ (p i).base) c
  let eps : X → Multiplicative (ZMod 2) := fun i ↦ Multiplicative.ofAdd (p i).fib
  let rhs : FreeGroup X →* WordCoh.CentExt c := {
    toFun w := FreeGroup.lift q w * centExtInclHom c (FreeGroup.lift eps w)
    map_one' := by simp
    map_mul' u v := by
      simp only [map_mul]
      exact Commute.mul_mul_mul_comm
        (centExtInclHom_comm c (FreeGroup.lift eps u) (FreeGroup.lift q v)).symm _ _ }
  have hh : FreeGroup.lift p=rhs := by
    apply FreeGroup.ext_hom
    intro i
    change FreeGroup.lift p (FreeGroup.of i) =
      FreeGroup.lift q (FreeGroup.of i) * centExtInclHom c (FreeGroup.lift eps (FreeGroup.of i))
    simp only [FreeGroup.lift_apply_of]
    change p i = q i * WordCoh.CentExt.incl c (p i).fib
    apply WordCoh.CentExt.ext
    · change (p i).base=(p i).base*1
      rw [mul_one]
    · change (p i).fib=0+(p i).fib+c.κ (p i).base 1
      rw [c.κ_one_right, zero_add, add_zero]
  exact DFunLike.congr_fun hh r

/-- Even charged exponents and vanishing normalized evaluation kill the full lift. -/
theorem centExtWord_eq_one_of_central_normalization
    {X L : Type} [Fintype X] [DecidableEq X] [Group L] (c : WordCoh.TwoCocycle L)
    (p : X → WordCoh.CentExt c) (r : FreeGroup X)
    (hnorm : FreeGroup.lift (WordCoh.lift (fun i ↦ (p i).base) c) r=1)
    (heven : ∀ i, heisEps i r=1 ∨ (p i).fib=0) : FreeGroup.lift p r=1 := by
  rw [centExtWord_central_normalization, hnorm, one_mul]
  have hz : FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (p i).fib) r=1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_freeGroup_lift_zmod2]
    change (∑ i, Multiplicative.toAdd (heisEps i r) * (p i).fib)=0
    apply Finset.sum_eq_zero
    intro i _
    rcases heven i with hi | hi
    · simp [hi]
    · rw [hi, mul_zero]
  rw [hz, map_one]

/-- Forget the quadratic central coordinate, retaining the twisted first jet. -/
def hessPrimal {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat) :
    WordCoh.CentExt (kappa0Cocycle dat hdat) →* WordLift V C where
  toFun p := ⟨p.base.1, p.base.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Odd fixed-point-free averaging kills the vector coordinate, not necessarily its phase. -/
theorem hessZpow_fst_eq_zero_of_oddFixedPointFree
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (p : WordCoh.CentExt (kappa0Cocycle dat hdat)) (E : Zhat → ℤ)
    (hres : ResolverLifts E (WordLift V C))
    (hfpf : ∀ v : V, p.base.2 • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 p.base.2 • v=v) :
    (p ^ E omega2).base.1=0 := by
  have H := congrArg WordLift.u (map_zpow (hessPrimal dat hdat) p (E omega2))
  change (p ^ E omega2).base.1=((hessPrimal dat hdat p)^E omega2).u at H
  rw [H, hres]
  exact WordLift.powOmega2_u_of_oddFixedPointFree _ hfpf hodd

/-- A shadow wild generator is central when its actual lower base is one. -/
theorem hessEvalZ_tameShadowSubst_wild_base_eq_one
    {n : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : ResolverLifts E (WordLift V C))
    (hwild : ∀ i, (mu (.wild i)).2=1)
    (hfpf : ∀ v : V, (mu .tau).2 • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 (mu .tau).2 • v=v) (i : Fin (n+1)) :
    (hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameShadowSubst (.wild i))).base=1 := by
  let p := WordCoh.lift mu (kappa0Cocycle dat hdat)
  have ht := hessZpow_fst_eq_zero_of_oddFixedPointFree dat hdat (p .tau) E hres hfpf hodd
  have hwt := hessZpow_fst_eq_zero_of_oddFixedPointFree dat hdat (p (.wild i)*p .tau) E hres
    (by simpa only [WordCoh.CentExt.mul_base, semiProd_mul_snd, p, WordCoh.lift_base,
      hwild i, one_mul] using hfpf)
    (by simpa only [WordCoh.CentExt.mul_base, semiProd_mul_snd, p, WordCoh.lift_base,
      hwild i, one_mul] using hodd)
  change (((p (.wild i)*p .tau)^E omega2 * (p .tau^E omega2)⁻¹)).base=1
  apply Prod.ext
  · change (hessPrimal dat hdat (((p (.wild i)*p .tau)^E omega2 *
      (p .tau^E omega2)⁻¹))).u=0
    rw [map_mul, map_inv, WordLift.mul_u, WordLift.inv_u]
    change ((p (.wild i)*p .tau)^E omega2).base.1 +
      ((p (.wild i)*p .tau)^E omega2).base.2 •
        (-(((p .tau^E omega2).base.2)⁻¹ • (p .tau^E omega2).base.1))=0
    rw [ht, hwt, smul_zero, neg_zero, smul_zero, add_zero]
  · change sdSnd (WordCoh.CentExt.proj (kappa0Cocycle dat hdat)
      ((p (.wild i)*p .tau)^E omega2 * (p .tau^E omega2)⁻¹))=1
    simp only [map_mul, map_inv, map_zpow]
    change (((mu (.wild i)).2*(mu .tau).2)^E omega2)*((mu .tau).2^E omega2)⁻¹=1
    rw [hwild, one_mul, mul_inv_cancel]

/-- A vanishing pure-sigma word and even wild exponents kill an extraspecial shadow. -/
theorem hessEvalZ_tameShadow_eq_one
    {n : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (hres : ResolverLifts E (WordLift V C))
    (hwild : ∀ i, (mu (.wild i)).2=1)
    (hfpf : ∀ v : V, (mu .tau).2 • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 (mu .tau).2 • v=v)
    (heven : ∀ i, heisEps (.wild i) (heisToFree E E₂ R)=1)
    (hkill : PWord.evalZ (fun g : Generator n ↦ match g with
      | .sigma => WordCoh.lift mu (kappa0Cocycle dat hdat) .sigma | _ => 1) E E₂ R=1) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameShadow R)=1 := by
  let p : Generator n → WordCoh.CentExt (kappa0Cocycle dat hdat) :=
    fun g ↦ hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameShadowSubst g)
  change PWord.evalZ (WordCoh.lift mu (kappa0Cocycle dat hdat)) E E₂
    (PWord.subst tameShadowSubst R)=1
  rw [PWord.evalZ_subst, evalZ_eq_lift_heisToFree]
  change FreeGroup.lift p (heisToFree E E₂ R)=1
  apply centExtWord_eq_one_of_central_normalization
  · have hnorm : WordCoh.lift (fun g ↦ (p g).base) (kappa0Cocycle dat hdat) =
        (fun g : Generator n ↦ match g with
        | .sigma => WordCoh.lift mu (kappa0Cocycle dat hdat) .sigma | _ => 1) := by
      funext g
      cases g with
      | sigma => rfl
      | tau => rfl
      | wild i =>
          apply WordCoh.CentExt.ext
          · exact hessEvalZ_tameShadowSubst_wild_base_eq_one dat hdat mu E E₂ hres hwild hfpf hodd i
          · rfl
    rw [hnorm, ← evalZ_eq_lift_heisToFree]
    exact hkill
  · intro g
    cases g with
    | sigma => exact Or.inr rfl
    | tau => exact Or.inr rfl
    | wild i => exact Or.inl (heven i)

/-- Tame specialization and the endpoint supply the two word conditions. -/
theorem hessEvalZ_tameShadow_eq_one_of_tameSpecializes
    {n q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (hres : ResolverLifts E (WordLift V C))
    (hwild : ∀ i, (mu (.wild i)).2=1)
    (hfpf : ∀ v : V, (mu .tau).2 • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 (mu .tau).2 • v=v)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hspec : TameSpec.TameSpecializes n q R)
    (hresolve : ∀ p : WordCoh.CentExt (kappa0Cocycle dat hdat),
      PWord.ResolvedAt (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ R) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameShadow R)=1 := by
  apply hessEvalZ_tameShadow_eq_one dat hdat mu E E₂ R hres hwild hfpf hodd
  · exact heisEps_wild_eq_one_of_gammaFam_endpoint hend
  · exact evalZ_pureSigma_of_tameSpecializes hspec
      (WordCoh.lift mu (kappa0Cocycle dat hdat) .sigma) E E₂ (hresolve _)

/-- A ramified splice has exactly the analytic template's full extraspecial evaluation. -/
theorem hessEvalZ_tameSplice_ramified
    {n q : ℕ} {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R H : PWord (Generator n)) (hres : ResolverLifts E (WordLift V C))
    (hwild : ∀ i, (mu (.wild i)).2=1)
    (hfpf : ∀ v : V, (mu .tau).2 • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 (mu .tau).2 • v=v)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hendH : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q H k)))
    (hspecR : TameSpec.TameSpecializes n q R)
    (hspecH : TameSpec.TameSpecializes n q H)
    (hresolveR : ∀ p : WordCoh.CentExt (kappa0Cocycle dat hdat),
      PWord.ResolvedAt (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ R)
    (hresolveH : ∀ p : WordCoh.CentExt (kappa0Cocycle dat hdat),
      PWord.ResolvedAt (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ H) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameSplice R H) =
      hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ H := by
  rw [tameSplice, hessEvalZ_mul, hessEvalZ_mul, hessEvalZ_inv,
    hessEvalZ_tameShadow_eq_one_of_tameSpecializes dat hdat mu E E₂ R hres hwild hfpf hodd
      hendR hspecR hresolveR,
    hessEvalZ_tameShadow_eq_one_of_tameSpecializes dat hdat mu E E₂ H hres hwild hfpf hodd
      hendH hspecH hresolveH,
    one_mul, inv_one, mul_one]

#print axioms centExtInclHom
#print axioms centExtInclHom_comm
#print axioms centExtWord_central_normalization
#print axioms centExtWord_eq_one_of_central_normalization
#print axioms hessPrimal
#print axioms hessZpow_fst_eq_zero_of_oddFixedPointFree
#print axioms hessEvalZ_tameShadowSubst_wild_base_eq_one
#print axioms hessEvalZ_tameShadow_eq_one
#print axioms hessEvalZ_tameShadow_eq_one_of_tameSpecializes
#print axioms hessEvalZ_tameSplice_ramified

end
end GQ2.Dyadic

