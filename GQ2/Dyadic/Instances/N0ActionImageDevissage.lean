/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaRActionImage
import GQ2.Dyadic.Instances.N0M0PushedHsimp
import GQ2.Dyadic.Instances.GammaLActionImageDevissage

/-!
# Action-image devissage for the compact-`N` presentation

The odd row proves its uniform word residue by devissing inside the *actual finite action image*
of an arbitrary elementary coefficient and then transporting the result to every ambient finite
quotient (`GammaLActionImageDevissage`).  Two of the three ingredients of that argument are
word-generic and are reused verbatim here:

* the action transport `stokesDuality_iff_of_resolvers_action_maps`, which identifies two resolved
  Stokes complexes with the same generator actions even when the acting groups and the resolving
  words differ; and
* the whole action-image package of `GammaRActionImage`, which is stated for an arbitrary
  branch word.

The third ingredient, the *simple*-module Stokes theorem for the row's own word, is genuinely
word-specific.  It is isolated below as the two named propositions `UnramifiedSimpleStokes` and
`RamifiedSimpleStokes`, one per branch of the `tau` dichotomy, and everything else in the chain
from there to `UniformPushedHsimp` is proved.
-/

namespace GQ2.Dyadic.NCompact

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates

local instance nCompactActionImageHeisTopology
    {C A : Type} [Group C] [AddCommGroup A] : TopologicalSpace (HeisLift A C) := ⊥

local instance nCompactActionImageHeisDiscrete
    {C A : Type} [Group C] [AddCommGroup A] : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-! ## The compact-`N` action image -/

/-- The finite action image of a coefficient of the compact-`N` candidate. -/
noncomputable abbrev ActionImage (α h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M] : Type :=
  RowActionImage.ActionImage (2 + 2 * h) q (nCompactW α h) M

/-- The marked generators of the compact-`N` presentation, read in that image. -/
noncomputable abbrev actionGenerators (α h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M] :
    Generator (2 + 2 * h) → ActionImage α h q M :=
  actionImageGenerators (2 + 2 * h) q (nCompactW α h) M

/-- The intrinsic compact-`N` relator death agrees with the uniform integer resolver used by the
Stokes complex.  The word is `ω₂`-only, so the profinite exponents may be replaced by the
constant representative at the image's own level. -/
theorem actionImage_nCompact_relator_death_resolved
    {α h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M] :
    PWord.evalZ (actionGenerators α h q M)
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)) : ℤ))
      (nCompactW α h) = 1 := by
  let C := ActionImage α h q M
  let N := 4 * Monoid.exponent C
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even C).1
  have hord : ∀ c : C, orderOf c ∣ N := by
    intro c
    exact (Monoid.order_dvd_exponent c).trans (by
      simp [N])
  have hresolved : PWord.ResolvedAt (actionGenerators α h q M)
      (fun _ ↦ (omega2Exp N : ℤ)) (fun _ ↦ (omega2Exp N : ℤ)) (nCompactW α h) :=
    PWord.resolvedAt_of_isOmega2Only _ _ _
      (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (Words.isOmega2Only_nCompact α h)
  have hrel := actionImageGenerators_relator_death
    (n := 2 + 2 * h) (q := q) (R := nCompactW α h) (M := M) (1 : Fin 2)
  change PWord.eval (actionGenerators α h q M) (nCompactW α h) = 1 at hrel
  rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
  simp [C, N] at hrel
  exact hrel

/-- The intrinsic tame relation on the compact-`N` action image. -/
theorem actionImage_nCompact_tameRelAt
    {α h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M] :
    (actionImageMarking (2 + 2 * h) q (nCompactW α h) M).TameRelAt q :=
  actionImage_tameRelAt

/-! ## The two word-specific simple branches

These are the only compact-`N` inputs the devissage still needs.  Both are statements about a
*single* marking (the canonical action image) and a *single* word (the uniform one), on a simple
elementary module; in particular each is strictly weaker than `Hsimp`, which quantifies over all
finite markings, all odd resolvers, and all simple modules at once. -/

/-- The unramified simple branch: `tau` acts trivially on the simple coefficient. -/
def UnramifiedSimpleStokes (α h q : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo (gamma α h q : Type) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (nCompactW α h) .tau • m = m) →
      StokesDuality (actionGenerators α h q M)
        (nCompactFam α h q
          (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)))) M

/-- The ramified simple branch: `tau` has no nonzero fixed vector on the simple coefficient. -/
def RamifiedSimpleStokes (α h q : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo (gamma α h q : Type) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (nCompactW α h) .tau • m = m → m = 0) →
      StokesDuality (actionGenerators α h q M)
        (nCompactFam α h q
          (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)))) M

/-- Both branch residues are consequences of the historical all-markings residue.  This records
that the reduction below is a genuine weakening and not a restatement. -/
theorem actionImage_simpleStokes_of_hsimp {α h q : ℕ} (hsimp : Hsimp α h q)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma α h q : Type) M) :
    StokesDuality (actionGenerators α h q M)
      (nCompactFam α h q
        (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)))) M := by
  have he : Odd (omega2Exp (4 * Monoid.exponent (ActionImage α h q M))) :=
    odd_omega2Exp (fourMulExponent_ne_zero_and_even (ActionImage α h q M)).1
      (fourMulExponent_ne_zero_and_even (ActionImage α h q M)).2
  have hrt : PWord.evalZ ⇑(actionImageMarking (2 + 2 * h) q (nCompactW α h) M)
      (fun _ => ((omega2Exp (4 * Monoid.exponent (ActionImage α h q M)) : ℕ) : ℤ))
      (fun _ => ((omega2Exp (4 * Monoid.exponent (ActionImage α h q M)) : ℕ) : ℤ))
      (tameRelW (2 + 2 * h) q) = 1 :=
    evalZ_tameRelW_eq_one_of_tameRelAt _ _ _
      (actionImage_nCompact_tameRelAt (α := α) (h := h) (q := q) (M := M))
  exact hsimp (ActionImage α h q M)
    (actionImageMarking (2 + 2 * h) q (nCompactW α h) M) _ he hrt
    actionImage_nCompact_relator_death_resolved M hM₂
    (isSimpleModTwo_actionImage hsimple)

/-- The unramified branch residue follows from the all-markings residue. -/
theorem unramifiedSimpleStokes_of_hsimp {α h q : ℕ}
    (hsimp : Hsimp α h q) : UnramifiedSimpleStokes α h q :=
  fun _M _ _ _ _ _ _ hM₂ hsimple _ => actionImage_simpleStokes_of_hsimp hsimp hM₂ hsimple

/-- The ramified branch residue follows from the all-markings residue. -/
theorem ramifiedSimpleStokes_of_hsimp {α h q : ℕ}
    (hsimp : Hsimp α h q) : RamifiedSimpleStokes α h q :=
  fun _M _ _ _ _ _ _ hM₂ hsimple _ => actionImage_simpleStokes_of_hsimp hsimp hM₂ hsimple

/-- The canonical action-image Stokes theorem for every simple elementary coefficient, from the
two branch residues and the `tau` dichotomy. -/
theorem actionImage_stokesDuality_simple {α h q : ℕ}
    (hunram : UnramifiedSimpleStokes α h q) (hram : RamifiedSimpleStokes α h q)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma α h q : Type) M) :
    StokesDuality (actionGenerators α h q M)
      (nCompactFam α h q
        (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)))) M := by
  rcases actionImage_tau_split_or_ramified_simple
    (n := 2 + 2 * h) (q := q) (R := nCompactW α h) hM₂ hsimple with hτ | hτfpf
  · exact hunram M hM₂ hsimple hτ
  · exact hram M hM₂ hsimple hτfpf

set_option maxHeartbeats 2400000 in
/-- Fixed-word devissage on the action image of an arbitrary finite elementary coefficient of the
compact-`N` candidate. -/
theorem actionImage_stokesDuality {α h q : ℕ}
    (hunram : UnramifiedSimpleStokes α h q) (hram : RamifiedSimpleStokes α h q)
    (hα : 1 ≤ α) (hq : Even q)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma α h q : Type)) M]
    [ContinuousSMul ((gamma α h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) :
    StokesDuality (actionGenerators α h q M)
      (nCompactFam α h q
        (omega2Exp (4 * Monoid.exponent (ActionImage α h q M)))) M := by
  let C₀ := ActionImage α h q M
  let c₀ := actionGenerators α h q M
  let w₀ := nCompactFam α h q (omega2Exp (4 * Monoid.exponent C₀))
  have hb := resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := C₀) (A := M) hM₂ (α := α) (h := h) (q := q) hα hq
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h)) w₀
      (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift c₀ (w₀ k) = 1 := fun k ↦
    lower_rel (A := M) (actionImageHom (2 + 2 * h) q (nCompactW α h) M) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hresWord k
  apply stokesDuality_of_simple c₀ w₀ hr hb.2
  · intro V _ _ _ hV₂ hsimple
    letI : TopologicalSpace V := ⊥
    letI : DiscreteTopology V := ⟨rfl⟩
    letI : ContinuousSMul C₀ V := ⟨continuous_of_discreteTopology⟩
    letI : DistribMulAction ((gamma α h q : Type)) V :=
      DistribMulAction.compHom V (actionImageHom (2 + 2 * h) q (nCompactW α h) M).toMonoidHom
    letI : ContinuousSMul ((gamma α h q : Type)) V :=
      continuousSMul_of_comp_finite
        (actionImageHom (2 + 2 * h) q (nCompactW α h) M) (fun _ _ ↦ rfl)
    have hsimpleGamma : IsSimpleModTwo (gamma α h q : Type) V := by
      refine ⟨hsimple.1, fun W hW ↦ hsimple.2 W ?_⟩
      intro c v hv
      obtain ⟨g, rfl⟩ :=
        (finiteActionHom (G := (gamma α h q : Type))
          (M := M)).toMonoidHom.rangeRestrict_surjective c
      exact hW g v hv
    have hdV := actionImage_stokesDuality_simple hunram hram hV₂ hsimpleGamma
    let D := Multiplicative (AddAut V)
    let piV : ActionImage α h q V →* D := Subgroup.subtype _
    let pi₀ : C₀ →* D := (finiteActionHom (G := C₀) (M := V)).toMonoidHom
    have hc : ∀ i, piV (actionGenerators α h q V i) = pi₀ (c₀ i) := by
      intro i
      apply Multiplicative.toAdd.injective
      ext v
      rfl
    have hresV : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
        (nCompactFam α h q
          (omega2Exp (4 * Monoid.exponent (ActionImage α h q V))))
        (HeisLift V (ActionImage α h q V)) :=
      resolvesAt_nCompactFam_uniformHeis hV₂ α h q
    have hres₀ : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h)) w₀
        (HeisLift V C₀) := resolvesAt_nCompactFam_uniformHeis hV₂ α h q
    exact (stokesDuality_iff_of_resolvers_action_maps piV pi₀
      (fun _ _ ↦ rfl) (fun g v ↦ (finiteActionHom_smul g v).symm)
      hc hresV hres₀).mp hdV
  · exact hM₂

set_option maxHeartbeats 2400000 in
/-- The two branch residues and exact word-level devissage discharge the uniform Stokes residue
consumed by the compact-`N` exact-lifting assembly. -/
theorem uniformPushedHsimp_of_actionImage {α h q : ℕ}
    (hunram : UnramifiedSimpleStokes α h q) (hram : RamifiedSimpleStokes α h q)
    (hα : 1 ≤ α) (hq : Even q) : UniformPushedHsimp α h q := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((gamma α h q : Type)) A :=
    continuousSMul_of_comp_finite rho (fun _ _ ↦ rfl)
  have hdA := actionImage_stokesDuality (α := α) (h := h) (q := q) (M := A)
    hunram hram hα hq hA₂
  letI : ContinuousSMul C A := ⟨continuous_of_discreteTopology⟩
  let D := Multiplicative (AddAut A)
  let piA : ActionImage α h q A →* D := Subgroup.subtype _
  let piC : C →* D := (finiteActionHom (G := C) (M := A)).toMonoidHom
  have hc : ∀ i, piA (actionGenerators α h q A i) =
      piC (rho (gammaGen (2 + 2 * h) q (nCompactW α h) i)) := by
    intro i
    apply Multiplicative.toAdd.injective
    ext a
    rfl
  have hresA : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q
        (omega2Exp (4 * Monoid.exponent (ActionImage α h q A))))
      (HeisLift A (ActionImage α h q A)) :=
    resolvesAt_nCompactFam_uniformHeis hA₂ α h q
  have hresC : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) (HeisLift A C) :=
    resolvesAt_nCompactFam_uniformHeis hA₂ α h q
  exact (stokesDuality_iff_of_resolvers_action_maps piA piC
    (fun _ _ ↦ rfl) (by
      intro g a
      change g • a = finiteActionHom (G := C) (M := A) g • a
      exact (finiteActionHom_smul g a).symm)
    hc hresA hresC).mp hdA

/-- Corrected exact lifting for the compact-`N` presentation, reduced to the two word-specific
simple branches.  Everything else in the chain is proved. -/
theorem exactLiftingRN_of_actionImage {α h q : ℕ}
    (hunram : UnramifiedSimpleStokes α h q) (hram : RamifiedSimpleStokes α h q)
    (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_uniformPushed
    (uniformPushedHsimp_of_actionImage hunram hram hα hqe) hα hq0 hqe nuP

end

end GQ2.Dyadic.NCompact
