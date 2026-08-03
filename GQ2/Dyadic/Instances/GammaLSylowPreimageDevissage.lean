/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SylowPreimageDevissage
import GQ2.Dyadic.Instances.GammaLSylowRightExact

/-!
# Simple modules on the `GammaL` Sylow preimage

For a simultaneous finite coefficient-action image `C` and `P ∈ Sylow 2 C`, the action of
`U = rho⁻¹(P)` on either coefficient factors through `P`.  Consequently every simple
elementary `U`-module occurring on either side is trivial.

This is the exact representation-theoretic reduction available from the Sylow step.  It does
not supply the remaining degree-two right-exactness across nonsplit extensions; even after the
simple kernel has become trivial, that map is the `H³(U, ZMod 2)`/CD-2 tail.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ} {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B]

local notation "GammaL" => (gamma h q : Type)
local notation "C" => PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)
local notation "rho" => pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)

/-- A simple elementary first coefficient becomes trivial on the Sylow preimage. -/
theorem simple_fst_smul_trivial_on_sylowTwoPreimage
    (P : Sylow 2 C) (hA₂ : ∀ a : A, a + a = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) A) :
    ∀ (u : sylowTwoPreimage rho P) (a : A), u • a = a := by
  letI : DistribMulAction C A :=
    DistribMulAction.compHom A
      (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
  exact smul_eq_self_of_simple_sylowTwoPreimage rho P
    (fun g a ↦ (pairFiniteActionImageHom_smul_fst g a).symm) hA₂ hsimple

/-- In particular, a simple first coefficient on the Sylow preimage has two elements. -/
theorem simple_fst_natCard_eq_two_on_sylowTwoPreimage
    (P : Sylow 2 C) (hA₂ : ∀ a : A, a + a = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) A) : Nat.card A = 2 := by
  letI : DistribMulAction C A :=
    DistribMulAction.compHom A
      (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
  exact natCard_eq_two_of_simple_sylowTwoPreimage rho P
    (fun g a ↦ (pairFiniteActionImageHom_smul_fst g a).symm) hA₂ hsimple

/-- A simple elementary second coefficient becomes trivial on the Sylow preimage. -/
theorem simple_snd_smul_trivial_on_sylowTwoPreimage
    (P : Sylow 2 C) (hB₂ : ∀ b : B, b + b = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) B) :
    ∀ (u : sylowTwoPreimage rho P) (b : B), u • b = b := by
  letI : DistribMulAction C B :=
    DistribMulAction.compHom B
      (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
  exact smul_eq_self_of_simple_sylowTwoPreimage rho P
    (fun g b ↦ (pairFiniteActionImageHom_smul_snd g b).symm) hB₂ hsimple

/-- In particular, a simple second coefficient on the Sylow preimage has two elements. -/
theorem simple_snd_natCard_eq_two_on_sylowTwoPreimage
    (P : Sylow 2 C) (hB₂ : ∀ b : B, b + b = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) B) : Nat.card B = 2 := by
  letI : DistribMulAction C B :=
    DistribMulAction.compHom B
      (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
  exact natCard_eq_two_of_simple_sylowTwoPreimage rho P
    (fun g b ↦ (pairFiniteActionImageHom_smul_snd g b).symm) hB₂ hsimple

/-- The exact residual local premise after choosing a Sylow subgroup: degree-two right
exactness only for coefficient quotients with a two-element kernel.  By the theorems above,
these are exactly the simple kernels produced by coefficient devissage, and their `U`-action is
trivial.  Mathematically this is the `H³(U, ZMod 2)=0` tail. -/
noncomputable abbrev GammaLSylowPreimageScalarKernelH2Tail (P : Sylow 2 C) : Prop :=
  TwoGroupActionScalarKernelH2Tail (sylowTwoPreimageHom rho P)

end

end GQ2.Dyadic.LSquare
