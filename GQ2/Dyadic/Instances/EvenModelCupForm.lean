/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenModelH2

/-!
# The Frattini cup form of the two even cores, in the basis dual to their generators

The even analogue of `GQ2/Dyadic/Instances/SqModelCupForm.lean`, recorded as missing by EV1E:
the odd lane has a group-generic `obsH2` cup transport for the square core, and the even models
had none, so nothing could carry the even cup form along an isomorphism.  This file supplies it,
for both even rows.

## The two generic theorems

`obsH2_evenModel_nNatWord_characterCup` and `obsH2_evenModel_mNatWord_characterCup` are stated
for an **arbitrary** profinite group `G` carrying a marking `μ : Fin (coreRank h) → G` that
makes the even relator a marked relator.  Each says: the one-relator obstruction of the cup
product of two mod-two characters is the even Gram evaluated on their values at the marking,

`obsH2 (χ_c ⌣ χ_d) = evenCupForm (i ↦ c(μ i)) (i ↦ d(μ i))`.

No presentation hypothesis appears.  `WordCoh.obsH2_eq_of_factor` turns the obstruction of a
cocycle factoring through a finite quotient into `relZ`, and `relZ_nNatWord_cupGram` /
`relZ_mNatWord_cupGram` evaluate that `relZ` against any cup cocycle.  The `α ≥ 2` hypothesis
is inherited from those two and is the same one `EvenModelH2.lean` explains at length: at
`α = 1` the displayed matrix is wrong on both rows.

That genericity is the point.  The same theorem is read at the models `DN α h`, `DM α h` with
their canonical markings (§2), and at any group carrying an oriented equivalence to one of them,
which is what a frame-adapted transport on the even side needs.

## Relation to what was already in tree

`obsH2_DN_coordinateCup` / `obsH2_DM_coordinateCup` (`EvenModelH2.lean` §4) are the *coordinate*
versions of §2: they fix a pair of coordinate vectors rather than a pair of characters, and they
are proved at the models only.  §2's `dnFrattiniCupForm`/`dmFrattiniCupForm` are their
character-indexed restatements, and §1 is the observation that the same proof never touched the
models.

`card_H2_DN`/`card_H2_DM` are already theorems of `EvenModelH2.lean`; §3 only records that they
make `dnObs`/`dmObs` additive **bijections** onto `𝔽₂`, which is the fact a transport needs (the
identification of `H²` with `𝔽₂` is unique, so any other injective additive functional on `H²`
agrees with it).

## Numbering

1. the generic even-relator cup obstruction, on both rows;
2. the Frattini cup functionals of the two models and their character-indexed cup forms;
3. those functionals are the identifications of `H²` with `𝔽₂`.
-/

namespace GQ2.Dyadic.EvenModel

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore ContCoh

/-! ## §1 The generic even-relator cup obstruction -/

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- The degree-one class of a continuous mod-two character.  This is the even lane's copy of
`GQ2.Dyadic.LSquare.sqCharacterClass`, and the group-generic form of the coordinate classes
`dnCoordinateHOne`/`dmCoordinateHOne`. -/
def evenModelCharacterClass (c : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    H1 G (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 c)

/-- The standard cocycle representative of the cup product of two character classes. -/
def evenModelCharacterCupZTwo (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) : Z2 G (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (Count.homEquivZ1 c).1 (Count.homEquivZ1 d).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [htriv, htriv, htriv])
      (Count.homEquivZ1 c) (Count.homEquivZ1 d)⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The cup product of two character classes is represented by `evenModelCharacterCupZTwo`. -/
theorem evenModelCharacterClass_cup (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    trivialCupPairing 2 G htriv (evenModelCharacterClass c) (evenModelCharacterClass d) =
      H2mk G (ZMod 2) (evenModelCharacterCupZTwo htriv c d) := rfl

/-- **The `N`-relator cup obstruction, for an arbitrary marking.**  If the `N_α` word is a
marked relator at `μ` and `α ≥ 2`, then the one-relator obstruction of the cup product of two
mod-two characters is the even Gram of their values at the marking.

No presentation hypothesis appears: `MarkedRelator` is all `obsH2` needs, and the value is
computed by `relZ_nNatWord_cupGram` against the bilinear pair cocycle. -/
theorem obsH2_evenModel_nNatWord_characterCup (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (α h : ℕ) (hα2 : 2 ≤ α) (μ : Fin (coreRank h) → G)
    (hW : WordCoh.MarkedRelator G (nNatWord α h) μ)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    WordCoh.obsH2 htriv (nNatWord α h) μ hW
        (trivialCupPairing 2 G htriv (evenModelCharacterClass c) (evenModelCharacterClass d)) =
      evenCupForm (fun i => Multiplicative.toAdd (c (μ i)))
        (fun i => Multiplicative.toAdd (d (μ i))) := by
  rw [evenModelCharacterClass_cup htriv c d]
  let rho : G →* EvenCupBase := c.toMonoidHom.prod d.toMonoidHom
  have hfactor : ∀ g k : G, (evenModelCharacterCupZTwo htriv c d).1 (g, k) =
      (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := by
    intro g k
    show (AddMonoidHom.mul (Multiplicative.toAdd (c g)))
      (g • Multiplicative.toAdd (d k)) = _
    rw [htriv]
    rfl
  rw [WordCoh.obsH2_eq_of_factor htriv (nNatWord α h) μ hW
    (evenModelCharacterCupZTwo htriv c d) rho (WordCoh.ofDRCoh evenPairCupCocycle) hfactor,
    relZ_nNatWord_cupGram evenPairCupCocycle_isCup hα2 fun i => rho (μ i)]
  simp only [evenCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply,
    ContinuousMonoidHom.coe_toMonoidHom]
  rfl

/-- **The `M`-relator cup obstruction, for an arbitrary marking** — the same Gram, in the `M`
basis, by `relZ_mNatWord_cupGram`. -/
theorem obsH2_evenModel_mNatWord_characterCup (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (α h : ℕ) (hα2 : 2 ≤ α) (μ : Fin (coreRank h) → G)
    (hW : WordCoh.MarkedRelator G (mNatWord α h) μ)
    (c d : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    WordCoh.obsH2 htriv (mNatWord α h) μ hW
        (trivialCupPairing 2 G htriv (evenModelCharacterClass c) (evenModelCharacterClass d)) =
      evenCupForm (fun i => Multiplicative.toAdd (c (μ i)))
        (fun i => Multiplicative.toAdd (d (μ i))) := by
  rw [evenModelCharacterClass_cup htriv c d]
  let rho : G →* EvenCupBase := c.toMonoidHom.prod d.toMonoidHom
  have hfactor : ∀ g k : G, (evenModelCharacterCupZTwo htriv c d).1 (g, k) =
      (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := by
    intro g k
    show (AddMonoidHom.mul (Multiplicative.toAdd (c g)))
      (g • Multiplicative.toAdd (d k)) = _
    rw [htriv]
    rfl
  rw [WordCoh.obsH2_eq_of_factor htriv (mNatWord α h) μ hW
    (evenModelCharacterCupZTwo htriv c d) rho (WordCoh.ofDRCoh evenPairCupCocycle) hfactor,
    relZ_mNatWord_cupGram evenPairCupCocycle_isCup hα2 fun i => rho (μ i)]
  simp only [evenCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply,
    ContinuousMonoidHom.coe_toMonoidHom]
  rfl

end Generic

/-! ## §2 The Frattini cup forms of the two models -/

section Model

local instance evenCupScalarActionDN (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenCupContinuousScalarDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

local instance evenCupScalarActionDM (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenCupContinuousScalarDM (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The Frattini cup functional of the `N` model.**  `H²(D_N, 𝔽₂) →+ 𝔽₂`, the one-relator
obstruction of the `N_α` word at the canonical marking.  §3 shows it is bijective, so it *is*
the identification of `H²` with `𝔽₂`. -/
def dnObs (α h : ℕ) (hα : 1 ≤ α) : H2 (DN α h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (nNatWord α h) (dnGen α h) (markedRelator_DN α h hα)

/-- The `M`-row Frattini cup functional. -/
def dmObs (α h : ℕ) (hα : 1 ≤ α) : H2 (DM α h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (mNatWord α h) (dmGen α h) (markedRelator_DM α h hα)

/-- **Deliverable, `N` row: the Frattini cup form of `D_N` is the even Gram.**  Read in the
basis dual to the presentation generators `dnGen α h` — i.e. evaluated on an arbitrary pair of
continuous mod-two characters, which is exactly a pair of dual-basis coordinate vectors — the
mod-two cup form of the model is `evenCupForm`. -/
theorem dnFrattiniCupForm (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    (c d : ContinuousMonoidHom (DN α h : Type) (Multiplicative (ZMod 2))) :
    dnObs α h hα (trivialCupPairing 2 (DN α h : Type) (fun _ _ => rfl)
        (evenModelCharacterClass c) (evenModelCharacterClass d)) =
      evenCupForm (fun i => Multiplicative.toAdd (c (dnGen α h i)))
        (fun i => Multiplicative.toAdd (d (dnGen α h i))) :=
  obsH2_evenModel_nNatWord_characterCup (fun _ _ => rfl) α h hα2 (dnGen α h)
    (markedRelator_DN α h hα) c d

/-- **Deliverable, `M` row.** -/
theorem dmFrattiniCupForm (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α)
    (c d : ContinuousMonoidHom (DM α h : Type) (Multiplicative (ZMod 2))) :
    dmObs α h hα (trivialCupPairing 2 (DM α h : Type) (fun _ _ => rfl)
        (evenModelCharacterClass c) (evenModelCharacterClass d)) =
      evenCupForm (fun i => Multiplicative.toAdd (c (dmGen α h i)))
        (fun i => Multiplicative.toAdd (d (dmGen α h i))) :=
  obsH2_evenModel_mNatWord_characterCup (fun _ _ => rfl) α h hα2 (dmGen α h)
    (markedRelator_DM α h hα) c d

/-! ## §3 The two functionals are the identifications of `H²` with `𝔽₂` -/

/-- `dnObs` is injective: `WordCoh.obsH2_injective` at the `N` presentation, the `#H² ≤ 2`
half of `card_H2_DN`. -/
theorem dnObs_injective (α h : ℕ) (hα : 1 ≤ α) : Function.Injective (dnObs α h hα) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (nNatWord α h) (dnGen α h)
    (markedRelator_DN α h hα) (presentedBy_DN α h) (isProP_DN α h)

/-- `dmObs` is injective. -/
theorem dmObs_injective (α h : ℕ) (hα : 1 ≤ α) : Function.Injective (dmObs α h hα) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (mNatWord α h) (dmGen α h)
    (markedRelator_DM α h hα) (presentedBy_DM α h) (isProP_DM α h)

/-- The head coordinate cup class realizes the value `1` on the `N` row: its Gram is
`evenCupForm_head`. -/
theorem dnObs_coordinateCup_head (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α) :
    dnObs α h hα (H2mk (DN α h : Type) (ZMod 2)
        (dnCoordinateCupZTwo α h hα (evenHeadVector h) (evenHeadVector h))) = 1 := by
  rw [dnObs, obsH2_DN_coordinateCup α h hα hα2, evenCupForm_head]

/-- The same on the `M` row. -/
theorem dmObs_coordinateCup_head (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α) :
    dmObs α h hα (H2mk (DM α h : Type) (ZMod 2)
        (dmCoordinateCupZTwo α h hα (evenHeadVector h) (evenHeadVector h))) = 1 := by
  rw [dmObs, obsH2_DM_coordinateCup α h hα hα2, evenCupForm_head]

/-- `dnObs` is surjective — with `card_H2_DN` this makes it an additive bijection
`H²(D_N, 𝔽₂) ≃ 𝔽₂`.  Concretely: the head cup square already has obstruction `1`. -/
theorem dnObs_surjective (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α) :
    Function.Surjective (dnObs α h hα) := by
  have hne : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  intro t
  by_cases ht : t = 0
  · exact ⟨0, by rw [map_zero, ht]⟩
  · exact ⟨H2mk (DN α h : Type) (ZMod 2)
      (dnCoordinateCupZTwo α h hα (evenHeadVector h) (evenHeadVector h)),
      by rw [dnObs_coordinateCup_head α h hα hα2, hne t ht]⟩

/-- `dmObs` is surjective. -/
theorem dmObs_surjective (α h : ℕ) (hα : 1 ≤ α) (hα2 : 2 ≤ α) :
    Function.Surjective (dmObs α h hα) := by
  have hne : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  intro t
  by_cases ht : t = 0
  · exact ⟨0, by rw [map_zero, ht]⟩
  · exact ⟨H2mk (DM α h : Type) (ZMod 2)
      (dmCoordinateCupZTwo α h hα (evenHeadVector h) (evenHeadVector h)),
      by rw [dmObs_coordinateCup_head α h hα hα2, hne t ht]⟩

end Model

/-! ## §4 Axiom hygiene

The last two prints are the in-tree results this file's deliverables were checked against: the
coordinate forms of §2's cup formula on the two rows.  They are reprinted here so the axiom
state of the even-core cup block is visible in one place. -/

#print axioms evenModelCharacterClass
#print axioms evenModelCharacterCupZTwo
#print axioms evenModelCharacterClass_cup
#print axioms obsH2_evenModel_nNatWord_characterCup
#print axioms obsH2_evenModel_mNatWord_characterCup
#print axioms dnObs
#print axioms dmObs
#print axioms dnFrattiniCupForm
#print axioms dmFrattiniCupForm
#print axioms dnObs_injective
#print axioms dmObs_injective
#print axioms dnObs_coordinateCup_head
#print axioms dmObs_coordinateCup_head
#print axioms dnObs_surjective
#print axioms dmObs_surjective
#print axioms obsH2_DN_coordinateCup
#print axioms obsH2_DM_coordinateCup

end

end GQ2.Dyadic.EvenModel
