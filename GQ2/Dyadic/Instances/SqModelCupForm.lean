/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteDegreeThree

/-!
# The Frattini cup form of the square core, in the basis dual to its generators

This file computes the mod-two cup product on `H²(D_sq h, 𝔽₂)` in the shape the odd-degree
frame lane consumes, and states the answer as a *character-indexed* identity so that it can be
transported along an isomorphism.

## The one generic theorem

The whole computation is `obsH2_sqNatWord_characterCup`, which is stated for an **arbitrary**
profinite group `G` carrying a marking `μ : Fin (sqRank h) → G` that kills the improved word.
It says: the one-relator obstruction of the cup product of two mod-two characters `c`, `d` is
the improved relator's quadratic initial Gram evaluated on the rank-one matrix of their values
at the marking,

`obsH2 (χ_c ⌣ χ_d) = sqRelatorQuadraticInitialGram h (i, j ↦ c(μ i) · d(μ j))`.

Nothing in the proof uses a presentation: only `MarkedRelator` (Frattini plus `W.ev μ = 1`),
because `WordCoh.obsH2_eq_of_factor` turns the obstruction of a cocycle factoring through a
finite quotient into `relZ`, and `sqRelWord_centLift_fib_eq_quadraticInitialGram` evaluates
that `relZ` for the improved word against any bilinear cocycle.

That genericity is the point: the same theorem is read at the model `D_sq h` with its canonical
marking `sqGen h` (§2, the Frattini cup form of the model), and at `G_K(2)` with the marking
supplied by an oriented equivalence (`SqModelPresentingFrameCupAdapted`).

## Relation to what was already in tree

`obsH2_DSq_coordinateCup` (`GammaLSylowPreimageFieldLabuteDegreeThree`) is the *coordinate*
version of §2: it fixes a pair of coordinate vectors rather than a pair of characters, and it
is proved at `D_sq h` only.  §2's `dsqFrattiniCupForm` is its character-indexed restatement,
and §1 is the observation that the same proof never touched `D_sq h`.

`card_H2_DSq` and `demushkinRank_DSq` are already theorems of
`GammaLSylowPreimageFieldLabuteElementaryH2`; §3 only records that they make `dsqObs h` an
additive **bijection** `H²(D_sq h, 𝔽₂) ≃ 𝔽₂`, which is the fact a transport needs (the
identification of `H²` with `𝔽₂` is unique, so any other injective additive functional on
`H²` agrees with it).
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Dyadic.SqCore

/-! ## §1 The generic square-relator cup obstruction -/

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- The degree-one class of a continuous mod-two character.  This is the group-generic form of
`SqCyclotomicFrattiniFrame.characterClass`. -/
def sqCharacterClass (c : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    H1 G (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 c)

/-- The standard cocycle representative of the cup product of two character classes. -/
def sqCharacterCupZTwo (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) : Z2 G (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (Count.homEquivZ1 c).1 (Count.homEquivZ1 d).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [htriv, htriv, htriv])
      (Count.homEquivZ1 c) (Count.homEquivZ1 d)⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The cup product of two character classes is represented by `sqCharacterCupZTwo`. -/
theorem sqCharacterClass_cup (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    trivialCupPairing 2 G htriv (sqCharacterClass c) (sqCharacterClass d) =
      H2mk G (ZMod 2) (sqCharacterCupZTwo htriv c d) := rfl

/-- **The square-relator cup obstruction, for an arbitrary marking.**  If the improved word
`Y²[S,X]∏ⱼ[Uⱼ,Vⱼ]` is a marked relator at `μ`, then the one-relator obstruction of the cup
product of two mod-two characters is the relator's quadratic initial Gram contracted against
the rank-one matrix of character values at the marking.

No presentation hypothesis appears: `MarkedRelator` is all `obsH2` needs, and the value is
computed by `sqRelWord_centLift_fib_eq_quadraticInitialGram` against the bilinear pair
cocycle. -/
theorem obsH2_sqNatWord_characterCup (htriv : ∀ (g : G) (m : ZMod 2), g • m = m) (h : ℕ)
    (μ : Fin (SqCore.sqRank h) → G)
    (hW : WordCoh.MarkedRelator G (MarkedCore.sqNatWord h) μ)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    WordCoh.obsH2 htriv (MarkedCore.sqNatWord h) μ hW
        (trivialCupPairing 2 G htriv (sqCharacterClass c) (sqCharacterClass d)) =
      sqRelatorQuadraticInitialGram h
        (fun i j => Multiplicative.toAdd (c (μ i)) * Multiplicative.toAdd (d (μ j))) := by
  rw [sqCharacterClass_cup htriv c d]
  let rho : G →* DsqCupBase := c.toMonoidHom.prod d.toMonoidHom
  have hfactor : ∀ g k : G, (sqCharacterCupZTwo htriv c d).1 (g, k) =
      (WordCoh.ofDRCoh dsqPairCupCocycle).κ (rho g) (rho k) := by
    intro g k
    show (AddMonoidHom.mul (Multiplicative.toAdd (c g)))
      (g • Multiplicative.toAdd (d k)) = _
    rw [htriv]
    rfl
  rw [WordCoh.obsH2_eq_of_factor htriv (MarkedCore.sqNatWord h) μ hW
    (sqCharacterCupZTwo htriv c d) rho (WordCoh.ofDRCoh dsqPairCupCocycle) hfactor,
    WordCoh.relZ_ofDRCoh]
  change (SqCore.sqRelWord fun i =>
    MarkedCore.centLift dsqPairCupCocycle (rho (μ i))).fib = _
  rw [sqRelWord_centLift_fib_eq_quadraticInitialGram dsqPairCupCocycle_isCup]
  congr 1

end Generic

/-! ## §2 The Frattini cup form of the model -/

section Model

local instance (h : ℕ) : DistribMulAction (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance (h : ℕ) : ContinuousSMul (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The Frattini cup functional of the improved model.**  `H²(D_sq h, 𝔽₂) →+ 𝔽₂`, the
one-relator obstruction of the improved word at the canonical marking.  §3 shows it is
bijective, so it *is* the identification of `H²` with `𝔽₂`. -/
def dsqObs (h : ℕ) : H2 (SqCore.DSq h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h) (SqCore.sqGen h)
    (markedRelator_DSq h)

/-- **Deliverable: the Frattini cup form of `D_sq h` is the relator's quadratic initial Gram.**
Read in the basis dual to the presentation generators `sqGen h` — i.e. evaluated on an
arbitrary pair of continuous mod-two characters, which is exactly a pair of dual-basis
coordinate vectors — the mod-two cup form of the model is
`sqRelatorQuadraticInitialGram h`.

The statement is in the shape `SqCyclotomicFrattiniFrame.IsCupAdapted` uses, with the field
cup form `b_K` replaced by the model's own `H² ≃ 𝔽₂` identification `dsqObs`. -/
theorem dsqFrattiniCupForm (h : ℕ)
    (c d : ContinuousMonoidHom (SqCore.DSq h : Type) (Multiplicative (ZMod 2))) :
    dsqObs h (trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (sqCharacterClass c) (sqCharacterClass d)) =
      sqRelatorQuadraticInitialGram h
        (fun i j => Multiplicative.toAdd (c (SqCore.sqGen h i)) *
          Multiplicative.toAdd (d (SqCore.sqGen h j))) :=
  obsH2_sqNatWord_characterCup (fun _ _ => rfl) h (SqCore.sqGen h) (markedRelator_DSq h) c d

/-! ## §3 `dsqObs` is the identification of `H²` with `𝔽₂` -/

/-- `dsqObs h` is injective: this is `WordCoh.obsH2_injective` at the improved presentation,
and it is the `#H² ≤ 2` half of `card_H2_DSq`. -/
theorem dsqObs_injective (h : ℕ) : Function.Injective (dsqObs h) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (MarkedCore.sqNatWord h) (SqCore.sqGen h)
    (markedRelator_DSq h) (presentedBy_DSq h) (SqCore.isProP_DSq h)

/-- `dsqObs h` is surjective — with `card_H2_DSq` this makes it an additive bijection
`H²(D_sq h, 𝔽₂) ≃ 𝔽₂`.  Concretely: the `Y` cup square already has obstruction `1`. -/
theorem dsqObs_surjective (h : ℕ) : Function.Surjective (dsqObs h) := by
  have hne : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  have hone : dsqObs h (H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqYCupZTwo h)) = 1 :=
    obsH2_DSq_dsqYCup h
  intro t
  by_cases ht : t = 0
  · exact ⟨0, by rw [map_zero, ht]⟩
  · exact ⟨H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqYCupZTwo h), by rw [hone, hne t ht]⟩

end Model

/-! ## §4 Axiom hygiene

The last three prints are the in-tree results this file's deliverables were checked against:
`#H²(D_sq h, 𝔽₂) = 2`, the Demushkin rank, and the coordinate form of §2's cup formula.  They
are reprinted here so the axiom state of the whole square-core cohomology block is visible in
one place. -/

#print axioms sqCharacterClass
#print axioms sqCharacterCupZTwo
#print axioms sqCharacterClass_cup
#print axioms obsH2_sqNatWord_characterCup
#print axioms dsqObs
#print axioms dsqFrattiniCupForm
#print axioms dsqObs_injective
#print axioms dsqObs_surjective
#print axioms card_H2_DSq
#print axioms demushkinRank_DSq
#print axioms obsH2_DSq_coordinateCup

end

end GQ2.Dyadic.LSquare
