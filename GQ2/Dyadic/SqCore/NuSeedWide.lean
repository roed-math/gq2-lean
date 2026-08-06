/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.ChiFreeClearing

/-!
# The five-slot χ-free seed: the `v_j`-slot released

**Lane SQ, the P2′ residue, ansatz correction.**  `sqEichlerSub` — the scaffold under
`SqEichlerSeed` and `SqNuSeed`, and therefore under both banked machine searches — fixes the
`v_j`-slot **literally** (`sqEichlerSub_handleV`).  That is a restriction of the *search*, not
of the target: `SqNuMoveAt h j k` only asks that the automorphism leave the `v`-**rows** where
they are, i.e. that the `v_j`-correction be `ν`-invisible, exactly like the three core
corrections `β₁`, `β₀`, `β₂`.  Nothing in the move statement, and nothing in
`SqNuClearHypothesis`, requires the `v_j`-letter itself to stay still.

This file releases that slot.  `sqNuSubW` is `sqEichlerSub` with one more `Function.update`, at
`sqHandleIdxV j`; `SqNuSeedW` is `SqNuSeed` with the two extra words and one extra `ν`-field;
and `sqNuMoveAt_of_seedW` shows the widened family still realizes the move, so the whole pricing
chain `seed ⇒ move ⇒ clearing` is unchanged.  `SqNuSeedW.ofNuSeed` embeds the old family at
`ρ_v = 1`, so the widening is strict by construction and costs nothing already proved.

## Why this is the ansatz to search next

The banked class-4 report is a statement about `sqEichlerSub`'s four slots.  Two things about
it are worth recording here:

* the searched family is **three** strict weakenings above the campaign's actual need — seed ⇒
  move ⇒ clearing hypothesis ⇒ the transported binder the L-row bypass consumes
  (`Instances/GammaLSylowPreimageMarkingAudit.lean` §5–§6 pins the chain);
* the search's solver is a *linear* model: it fixes a layer of the lower exponent-2 central
  series, computes the effect of each move separately, and asks whether the defect lies in the
  span of those effects.  Two weight-`2` corrections cross at weight `4` — precisely the layer
  the report calls obstructed — and that cross term is not in the model.  Adding the exact
  pairwise effects to the same solver lifts the layer-4 span from `150/175` to `159/175` and
  carries the seed **through** class 4, witness in hand.  The class-4 obstruction is an artifact
  of the linearization, not an invariant of the group.

So: no refutation is available from the banked data, and the correct next move is a wider
search, not a weight-4 impossibility proof.  This file supplies the first widening (the
`v_j`-slot); the second is the solver's cross terms.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`); no census axiom is reachable.  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The five-slot scaffold

One further `Function.update` on top of `sqEichlerSub`, at the `v_j` index.  Every slot lemma
of the four-slot scaffold is reused verbatim; only the `v`-slots change. -/

section Scaffold

variable {h : ℕ}

/-- **The five-slot χ-free substitution scaffold**: `σ ↦ σ·β₁`, `x₀ ↦ x₀·β₀`, `x₁ ↦ x₁·β₂`,
`u_j ↦ ρ·u_j`, `v_j ↦ ρ_v·v_j`, every other letter fixed.  This is `sqEichlerSub` with the
`v_j`-slot released. -/
noncomputable def sqNuSubW (h : ℕ) (j : Fin h) (β₁ β₀ β₂ ρ ρv : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  Function.update (sqEichlerSub h j β₁ β₀ β₂ ρ) (sqHandleIdxV j)
    (ρv * sqGen h (sqHandleIdxV j))

variable (j : Fin h) (β₁ β₀ β₂ ρ ρv : (DSq h : Type))

@[simp] theorem sqNuSubW_zero : sqNuSubW h j β₁ β₀ β₂ ρ ρv 0 = dsqSigma h * β₁ := by
  rw [sqNuSubW,
    Function.update_of_ne (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_zero]; omega))),
    sqEichlerSub_zero]

@[simp] theorem sqNuSubW_one : sqNuSubW h j β₁ β₀ β₂ ρ ρv 1 = dsqX0 h * β₀ := by
  rw [sqNuSubW,
    Function.update_of_ne (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_one]; omega))),
    sqEichlerSub_one]

@[simp] theorem sqNuSubW_two : sqNuSubW h j β₁ β₀ β₂ ρ ρv 2 = dsqX1 h * β₂ := by
  rw [sqNuSubW,
    Function.update_of_ne (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_two]; omega))),
    sqEichlerSub_two]

@[simp] theorem sqNuSubW_handleU_self :
    sqNuSubW h j β₁ β₀ β₂ ρ ρv (sqHandleIdxU j) = ρ * sqGen h (sqHandleIdxU j) := by
  rw [sqNuSubW, Function.update_of_ne (sqHandleIdxU_ne_sqHandleIdxV j j),
    sqEichlerSub_handleU_self]

theorem sqNuSubW_handleU_of_ne {i : Fin h} (hi : i ≠ j) :
    sqNuSubW h j β₁ β₀ β₂ ρ ρv (sqHandleIdxU i) = sqGen h (sqHandleIdxU i) := by
  rw [sqNuSubW, Function.update_of_ne (sqHandleIdxU_ne_sqHandleIdxV i j),
    sqEichlerSub_handleU_of_ne j β₁ β₀ β₂ ρ hi]

@[simp] theorem sqNuSubW_handleV_self :
    sqNuSubW h j β₁ β₀ β₂ ρ ρv (sqHandleIdxV j) = ρv * sqGen h (sqHandleIdxV j) := by
  rw [sqNuSubW, Function.update_self]

theorem sqNuSubW_handleV_of_ne {i : Fin h} (hi : i ≠ j) :
    sqNuSubW h j β₁ β₀ β₂ ρ ρv (sqHandleIdxV i) = sqGen h (sqHandleIdxV i) := by
  rw [sqNuSubW, Function.update_of_ne (fun hc => hi (sqHandleIdxV_injective hc)),
    sqEichlerSub_handleV]

/-- **The old scaffold is the new one at `ρ_v = 1`**: the four-slot family embeds in the
five-slot family, so the widening loses nothing. -/
theorem sqNuSubW_one_rhoV : sqNuSubW h j β₁ β₀ β₂ ρ 1 = sqEichlerSub h j β₁ β₀ β₂ ρ := by
  rw [sqNuSubW, one_mul, ← sqEichlerSub_handleV j β₁ β₀ β₂ ρ j, Function.update_eq_self]

end Scaffold

/-! ## §2 The five-slot χ-free seed

`SqNuSeed` with the two `v_j`-slot words added and one further `ν`-field: the `v_j`-correction
must be invisible to every admissible marking, exactly like the three core corrections.  That
is the whole cost of releasing the slot. -/

section SeedW

variable {h : ℕ}

/-- **The five-slot χ-free Eichler seed at `(h, j, k)`.**  `SqNuSeed` with the `v_j`-slot
released: two more substitution words, one more `ν`-field.  The `ν`-field is the exact price of
the release — `SqNuMoveAt` fixes the `v`-**rows**, not the `v`-letters. -/
structure SqNuSeedW (h : ℕ) (j : Fin h) (k : ℤ_[2]) where
  /-- The σ-slot correction word. -/
  beta1 : (DSq h : Type)
  /-- The `x₀`-slot correction word. -/
  beta0 : (DSq h : Type)
  /-- The `x₁`-slot correction word. -/
  beta2 : (DSq h : Type)
  /-- The `u_j`-slot shift word (of class `k·σ̄` up to ν'-invisible classes). -/
  rho : (DSq h : Type)
  /-- The `v_j`-slot correction word — the released slot. -/
  rhoV : (DSq h : Type)
  /-- The σ-slot word of the inverse substitution. -/
  beta1Inv : (DSq h : Type)
  /-- The `x₀`-slot word of the inverse substitution. -/
  beta0Inv : (DSq h : Type)
  /-- The `x₁`-slot word of the inverse substitution. -/
  beta2Inv : (DSq h : Type)
  /-- The `u_j`-slot word of the inverse substitution. -/
  rhoInv : (DSq h : Type)
  /-- The `v_j`-slot word of the inverse substitution. -/
  rhoVInv : (DSq h : Type)
  /-- The forward substitution kills the relator. -/
  rel_fwd : sqRelWord (sqNuSubW h j beta1 beta0 beta2 rho rhoV) = 1
  /-- The backward substitution kills the relator. -/
  rel_bwd : sqRelWord (sqNuSubW h j beta1Inv beta0Inv beta2Inv rhoInv rhoVInv) = 1
  /-- Forward after backward is the identity on generators. -/
  comp_fwd : ∀ i, sqLiftHom h (isProP_DSq h)
      (sqNuSubW h j beta1 beta0 beta2 rho rhoV) rel_fwd
      (sqNuSubW h j beta1Inv beta0Inv beta2Inv rhoInv rhoVInv i) = sqGen h i
  /-- Backward after forward is the identity on generators. -/
  comp_bwd : ∀ i, sqLiftHom h (isProP_DSq h)
      (sqNuSubW h j beta1Inv beta0Inv beta2Inv rhoInv rhoVInv) rel_bwd
      (sqNuSubW h j beta1 beta0 beta2 rho rhoV i) = sqGen h i
  /-- The σ-correction is invisible to every marking with the selected rows and vanishing
  `v_j`-row. -/
  nu_beta1 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta1 = 1
  /-- The `x₀`-correction is invisible to every such marking. -/
  nu_beta0 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta0 = 1
  /-- The `v_j`-correction is invisible to every such marking — the released slot's price. -/
  nu_rhoV : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' rhoV = 1
  /-- The `u_j`-shift has row exactly `k` against every such marking (the σ-pivot). -/
  nu_rho : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → toAdd (nu' rho) = k

variable {j : Fin h} {k : ℤ_[2]}

/-- The forward substitution of a five-slot seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqNuSeedW.hom (S : SqNuSeedW h j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqNuSubW h j S.beta1 S.beta0 S.beta2 S.rho S.rhoV) S.rel_fwd

/-- The backward substitution of a five-slot seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqNuSeedW.homInv (S : SqNuSeedW h j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h)
    (sqNuSubW h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv S.rhoVInv) S.rel_bwd

@[simp] theorem SqNuSeedW.hom_gen (S : SqNuSeedW h j k) (i : Fin (sqRank h)) :
    S.hom (sqGen h i) = sqNuSubW h j S.beta1 S.beta0 S.beta2 S.rho S.rhoV i :=
  sqLiftHom_gen _ _ _ _ _

@[simp] theorem SqNuSeedW.homInv_gen (S : SqNuSeedW h j k) (i : Fin (sqRank h)) :
    S.homInv (sqGen h i) =
      sqNuSubW h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv S.rhoVInv i :=
  sqLiftHom_gen _ _ _ _ _

/-- **The five-slot seed's automorphism.** -/
noncomputable def SqNuSeedW.equiv (S : SqNuSeedW h j k) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective S.hom (Function.bijective_iff_has_inverse.mpr
    ⟨S.homInv,
      dsq_leftInverse S.homInv S.hom fun i => by rw [S.hom_gen]; exact S.comp_bwd i,
      dsq_leftInverse S.hom S.homInv fun i => by rw [S.homInv_gen]; exact S.comp_fwd i⟩)

@[simp] theorem SqNuSeedW.equiv_gen (S : SqNuSeedW h j k) (i : Fin (sqRank h)) :
    S.equiv (sqGen h i) = sqNuSubW h j S.beta1 S.beta0 S.beta2 S.rho S.rhoV i :=
  S.hom_gen i

/-- **Seed to move, five slots**: the widened family still realizes the χ-free `(j, k)`-move,
so the pricing chain `seed ⇒ move ⇒ clearing hypothesis` is untouched by the release. -/
theorem sqNuMoveAt_of_seedW (S : SqNuSeedW h j k) : SqNuMoveAt h j k := by
  intro nu' hsigma hx0 hv
  refine ⟨S.equiv, ?_, ?_, ?_, ?_, ?_⟩
  · show nu' (S.equiv (sqGen h 0)) = nu' (dsqSigma h)
    rw [S.equiv_gen, sqNuSubW_zero, map_mul, S.nu_beta1 nu' hsigma hx0 hv, mul_one]
  · show nu' (S.equiv (sqGen h 1)) = nu' (dsqX0 h)
    rw [S.equiv_gen, sqNuSubW_one, map_mul, S.nu_beta0 nu' hsigma hx0 hv, mul_one]
  · rw [S.equiv_gen, sqNuSubW_handleU_self, map_mul, toAdd_mul,
      S.nu_rho nu' hsigma hx0 hv]
    ring
  · intro i
    by_cases hij : i = j
    · subst hij
      rw [S.equiv_gen, sqNuSubW_handleV_self, map_mul, S.nu_rhoV nu' hsigma hx0 hv, one_mul]
    · rw [S.equiv_gen, sqNuSubW_handleV_of_ne j S.beta1 S.beta0 S.beta2 S.rho S.rhoV hij]
  · intro i hi
    rw [S.equiv_gen,
      sqNuSubW_handleU_of_ne j S.beta1 S.beta0 S.beta2 S.rho S.rhoV hi]

end SeedW

/-! ## §3 The embedding of the four-slot family, and the assemblies -/

section Embedding

variable {h : ℕ} {j : Fin h} {k : ℤ_[2]}

/-- Transport of a lifted substitution along an equality of markings: the relator proof is
irrelevant, so only the marking matters. -/
theorem sqLiftHom_apply_congr {m m' : Fin (sqRank h) → (DSq h : Type)} (hm : m = m')
    (hrel : sqRelWord m = 1) (hrel' : sqRelWord m' = 1) (x : (DSq h : Type)) :
    sqLiftHom h (isProP_DSq h) m hrel x = sqLiftHom h (isProP_DSq h) m' hrel' x := by
  subst hm
  rfl

/-- **The four-slot seed is a five-slot seed at `ρ_v = 1`.**  The widening is strict by
construction and inherits every already-proved instance. -/
noncomputable def SqNuSeedW.ofNuSeed (S : SqNuSeed h j k) : SqNuSeedW h j k where
  beta1 := S.beta1
  beta0 := S.beta0
  beta2 := S.beta2
  rho := S.rho
  rhoV := 1
  beta1Inv := S.beta1Inv
  beta0Inv := S.beta0Inv
  beta2Inv := S.beta2Inv
  rhoInv := S.rhoInv
  rhoVInv := 1
  rel_fwd := by rw [sqNuSubW_one_rhoV]; exact S.rel_fwd
  rel_bwd := by rw [sqNuSubW_one_rhoV]; exact S.rel_bwd
  comp_fwd := fun i => by
    rw [congrFun (sqNuSubW_one_rhoV j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv) i,
      sqLiftHom_apply_congr (sqNuSubW_one_rhoV j S.beta1 S.beta0 S.beta2 S.rho) _ S.rel_fwd]
    exact S.comp_fwd i
  comp_bwd := fun i => by
    rw [congrFun (sqNuSubW_one_rhoV j S.beta1 S.beta0 S.beta2 S.rho) i,
      sqLiftHom_apply_congr
        (sqNuSubW_one_rhoV j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv) _ S.rel_bwd]
    exact S.comp_bwd i
  nu_beta1 := S.nu_beta1
  nu_beta0 := S.nu_beta0
  nu_rhoV := fun nu' _ _ _ => map_one nu'
  nu_rho := S.nu_rho

/-- **The assembly**: five-slot seeds at every parameter discharge the clearing target. -/
theorem sqNuClearHypothesis_of_wideSeeds {h : ℕ}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), Nonempty (SqNuSeedW h j k)) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_moves fun j k => (H j k).elim fun S => sqNuMoveAt_of_seedW S

/-- The assembly from the unit slice alone. -/
theorem sqNuClearHypothesis_of_unit_wideSeeds {h : ℕ}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → Nonempty (SqNuSeedW h j k)) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_unit_moves fun j k hk => (H j k hk).elim fun S =>
    sqNuMoveAt_of_seedW S

end Embedding

/-! ## §4 Stress pins -/

section StressTests

/-- The released slot at one handle: the `v`-letter really does move. -/
example (β₁ β₀ β₂ ρ ρv : (DSq 1 : Type)) :
    sqNuSubW 1 0 β₁ β₀ β₂ ρ ρv (sqHandleIdxV 0) = ρv * sqGen 1 (sqHandleIdxV 0) :=
  sqNuSubW_handleV_self 0 β₁ β₀ β₂ ρ ρv

/-- …and at `ρ_v = 1` the scaffold is the old one, on the nose. -/
example (β₁ β₀ β₂ ρ : (DSq 1 : Type)) :
    sqNuSubW 1 0 β₁ β₀ β₂ ρ 1 = sqEichlerSub 1 0 β₁ β₀ β₂ ρ :=
  sqNuSubW_one_rhoV 0 β₁ β₀ β₂ ρ

/-- A four-slot seed forgets into the five-slot family. -/
noncomputable example {k : ℤ_[2]} (S : SqNuSeed 1 0 k) : SqNuSeedW 1 0 k :=
  SqNuSeedW.ofNuSeed S

/-- A five-slot seed still realizes the move. -/
example {k : ℤ_[2]} (S : SqNuSeedW 1 0 k) : SqNuMoveAt 1 0 k :=
  sqNuMoveAt_of_seedW S

/-- Widened unit seeds at one handle discharge the clearing target. -/
example (H : ∀ (j : Fin 1) (k : ℤ_[2]), IsUnit k → Nonempty (SqNuSeedW 1 j k)) :
    SqNuClearHypothesis 1 :=
  sqNuClearHypothesis_of_unit_wideSeeds H

/-- The core slots are untouched by the release. -/
example (β₁ β₀ β₂ ρ ρv : (DSq 1 : Type)) :
    sqNuSubW 1 0 β₁ β₀ β₂ ρ ρv 0 = dsqSigma 1 * β₁ :=
  sqNuSubW_zero 0 β₁ β₀ β₂ ρ ρv

end StressTests

/-! ## §5 Axiom pins

Committed prints: the whole file is **std-3**.  Census unchanged at **11**. -/

section AxiomPins

#print axioms sqNuSubW_zero
#print axioms sqNuSubW_handleU_self
#print axioms sqNuSubW_handleV_self
#print axioms sqNuSubW_handleV_of_ne
#print axioms sqNuSubW_one_rhoV
#print axioms SqNuSeedW.equiv_gen
#print axioms sqNuMoveAt_of_seedW
#print axioms SqNuSeedW.ofNuSeed
#print axioms sqNuClearHypothesis_of_wideSeeds
#print axioms sqNuClearHypothesis_of_unit_wideSeeds

end AxiomPins

end SqCore

end Dyadic

end GQ2
