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

/-- The sole scalar-kernel input left by the combined Sylow and coefficient-devissage
reductions.  For each simultaneous finite coefficient-action image, choose a Sylow `2`-subgroup
and prove H² right exactness only for quotients whose kernel has two elements on its preimage. -/
noncomputable abbrev GammaLSylowPreimageScalarKernelH2TailSupply (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        GammaLSylowPreimageScalarKernelH2Tail (h := h) (q := q) (A := A) (B := B) P

/-- Scalar two-element-kernel tails on the Sylow preimages imply the transfer-free local H²
right-exactness supply.  The strong induction is entirely coefficient-theoretic; no transfer
data or higher-cohomology API is required at this point. -/
theorem gammaLSylowTwoLocalH2RightExactSupply_of_scalarKernelTails
    (S : GammaLSylowPreimageScalarKernelH2TailSupply h q) :
    GammaLSylowTwoLocalH2RightExactSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  let c₀ := PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)
  let rho₀ : ContinuousMonoidHom GammaL c₀ :=
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)
  obtain ⟨pSylow, tail⟩ := S A B
  let rhoP : ContinuousMonoidHom (sylowTwoPreimage rho₀ pSylow) pSylow :=
    sylowTwoPreimageHom rho₀ pSylow
  letI : DistribMulAction c₀ A :=
    DistribMulAction.compHom A
      (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
  letI : DistribMulAction c₀ B :=
    DistribMulAction.compHom B
      (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
  letI : DistribMulAction pSylow A :=
    DistribMulAction.compHom A
      ((pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B)).comp
        pSylow.toSubgroup.subtype)
  letI : DistribMulAction pSylow B :=
    DistribMulAction.compHom B
      ((pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B)).comp
        pSylow.toSubgroup.subtype)
  have hgP : ∀ (p : pSylow) (a : A), g (p • a) = p • g a := by
    intro p a
    change g (p.1 • a) = p.1 • g a
    exact pairFiniteActionImage_equivariant g hg p.1 a
  have hcompatA : ∀ (u : sylowTwoPreimage rho₀ pSylow) (a : A), u • a = rhoP u • a := by
    intro u a
    change u.1 • a = (rhoP u).1 • a
    exact (pairFiniteActionImageHom_smul_fst u.1 a).symm
  have hcompatB : ∀ (u : sylowTwoPreimage rho₀ pSylow) (b : B), u • b = rhoP u • b := by
    intro u b
    change u.1 • b = (rhoP u).1 • b
    exact (pairFiniteActionImageHom_smul_snd u.1 b).symm
  refine ⟨pSylow, ?_⟩
  exact h2RightExactAt_of_twoGroupActionScalarKernelTail rhoP
    (sylowTwoPreimageHom_surjective rho₀ pairFiniteActionImageHom_surjective pSylow)
    pSylow.2 tail g (fun u a ↦ hg u.1 a) hgP hcompatA hcompatB hA₂ hB₂ hsurj

/-- End-to-end scalar-kernel constructor for full Tate duality on the improved L presentation. -/
noncomputable def tateDualityG_of_sylowPreimageScalarKernelTails
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (S : GammaLSylowPreimageScalarKernelH2TailSupply h q) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_sylowTwoLocal hq
    (gammaLSylowTwoLocalH2RightExactSupply_of_scalarKernelTails S)

end

end GQ2.Dyadic.LSquare
