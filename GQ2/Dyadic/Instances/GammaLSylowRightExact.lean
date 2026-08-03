/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2Corestriction
import GQ2.Dyadic.Instances.GammaLAsphericityRightExact

/-!
# The Sylow-2 reduction of the `GammaL` right-exactness obstruction

Every finite elementary coefficient quotient has a common finite action image, namely the
actual image of the simultaneous action on source and target.  Restricting `GammaL` to the
preimage of a Sylow `2`-subgroup of this image has odd index.  Hence the standard transfer
argument reduces the remaining `GammaLH2RightExactSupply` to right exactness on this preimage.

The original witness interface below retains the transfer square explicitly.  The second,
transfer-free interface uses the canonical general-coefficient corestriction from
`GQ2.Dyadic.Count.H2Corestriction`, so the only remaining input is right exactness on the
Sylow preimage itself; it is the preferred endpoint for subsequent reductions.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

/-- The exact Sylow-local sufficient condition for the all-elementary `GammaL` degree-two
right-exactness supply.

For each finite elementary coefficient surjection, a witness chooses a Sylow `2`-subgroup of
the simultaneous finite action image, supplies the restriction/corestriction square, and
proves right exactness over its open preimage. -/
noncomputable abbrev GammaLSylowTwoH2RightExactWitnessSupply (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B]
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : (gamma h q : Type)) (a : A), g (c • a) = c • g a),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective g →
        Nonempty (SylowTwoH2RightExactWitness
          (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B))
          g hgC hg)

/-- Sylow-local right exactness plus the standard transfer square proves the full
`GammaLH2RightExactSupply`.

This theorem is the formal odd-index diagram chase at the campaign's exact obstruction
surface.  The finite target is the surjective simultaneous action image, so no faithfulness or
generation assumption is added. -/
theorem gammaLH2RightExactSupply_of_sylowTwoPreimages
    {h q : ℕ}
    (S : GammaLSylowTwoH2RightExactWitnessSupply h q) :
    GammaLH2RightExactSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  let rho : ContinuousMonoidHom (gamma h q : Type)
      (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) :=
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)
  obtain ⟨W⟩ := S A B g hgC hg hA₂ hB₂ hsurj
  exact W.toH2RightExact rho pairFiniteActionImageHom_surjective g hgC hg hB₂

/-! ## Transfer-free endpoint -/

/-- The residual Sylow-local input after constructing general-coefficient corestriction.

For each elementary coefficient quotient, one only has to prove right exactness over the
preimage of a Sylow `2`-subgroup of the simultaneous finite action image. -/
noncomputable abbrev GammaLSylowTwoLocalH2RightExactSupply (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B]
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : (gamma h q : Type)) (a : A), g (c • a) = c • g a),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) → Function.Surjective g →
      ∃ P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        H2RightExactAt (G := sylowTwoPreimage
          (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P)
          g hgC (fun u a ↦ hg u.1 a)

/-- Canonical general-coefficient transfer removes the transfer square from the `GammaL`
Sylow reduction.  Thus the sole remaining obstruction is right exactness on the open Sylow
preimage. -/
theorem gammaLH2RightExactSupply_of_sylowTwoLocal
    {h q : ℕ} (S : GammaLSylowTwoLocalH2RightExactSupply h q) :
    GammaLH2RightExactSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgC hg hA₂ hB₂ hsurj
  let rho : ContinuousMonoidHom (gamma h q : Type)
      (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) :=
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)
  obtain ⟨P, hP⟩ := S A B g hgC hg hA₂ hB₂ hsurj
  let U : Subgroup (gamma h q : Type) := sylowTwoPreimage rho P
  have hU : IsOpen (U : Set (gamma h q : Type)) := isOpen_sylowTwoPreimage rho P
  letI : Finite ((gamma h q : Type) ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U hU
  exact H2RightExactAt.of_sylowTwoPreimage rho pairFiniteActionImageHom_surjective P
    g hgC hg hB₂ (h2RestrictionTransferSquare U hU g hgC hg) hP

/-- For even `q`, explicit Sylow witnesses (including a transfer square) give the full
Tate-duality package directly. -/
noncomputable def tateDualityG_of_sylowTwoPreimages
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (S : GammaLSylowTwoH2RightExactWitnessSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_sylowTwoPreimages S)

/-- For even `q`, right exactness on the Sylow preimages is the sole remaining input to the
full Tate-duality package; general-coefficient transfer is supplied canonically. -/
noncomputable def tateDualityG_of_sylowTwoLocal
    {h q : ℕ} (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (S : GammaLSylowTwoLocalH2RightExactSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_sylowTwoLocal S)

end

end GQ2.Dyadic.LSquare
