/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotClimb
import GQ2.Dyadic.SqCore.HandleEichler

/-!
# W43 — the sign row is automatic, and the residual is one `ℤ₂`-linear row

`SqCore/HandleEichler.lean` cut the `h ≥ 1` residual `SqHandleMixFixesCore h c` down to
`IsUnit c ∧ SqChiNuClearHypothesis h`, and split the surviving χ-clause into two row conditions
(`chiSq_preserving_iff`): the correcting automorphism must preserve the `ℤ₂`-valued χ-exponent
row `λ` **and** the `±1`-valued sign row `sign`.  This file removes the second one.

## Headline

```text
theorem sqSign_of_aut (Ψ : ContinuousMulEquiv (DSq h) (DSq h)) (x) : sqSign h (Ψ x) = sqSign h x
theorem chiSq_preserving_iff_nuLam (Ψ) :
    (∀ x, chiSq h (Ψ x) = chiSq h x) ↔ ∀ x, nuLam h (Ψ x) = nuLam h x
theorem sqChiNuClearHypothesis_iff_lam : SqChiNuClearHypothesis h ↔ SqLamNuClearHypothesis h
```

`sqSign_of_aut` carries **no orientation clause**: *every* continuous automorphism of `D_sq h`
preserves the sign character.  So the χ-clause of the cut is the λ-row and nothing else, and the
certificate route and the realization bypass now differ by a **single `ℤ₂`-linear condition** on
`Ψ` (`SqLamNuClearHypothesis` versus `ChiFreeClearing`'s `SqNuClearHypothesis`), rather than by a
`ℤ₂ˣ`-valued equation.

## The mechanism: `ε` is the characteristic vector of the cup form

`PivotClimb` §2 shows the mod-two cup form `sqGram` is invariant under the **whole** automorphism
group, and §4 evaluates the cup square: `c ⌣ c = c(x₁)`.  Here that identity is read the other
way round.  Let `ε` be the mod-two coordinate character of the torsion letter `x₁` (`sqEps`).
In the relator's constructor table `Gram κ = κ₂₂ + (κ₀₁ + κ₁₀) + Σⱼ(κ_{UⱼVⱼ} + κ_{VⱼUⱼ})` one has

```text
  ε ⌣ c = c(x₁) = c ⌣ c        for every mod-two character c        (`sqGram_sqEps`)
```

— i.e. `ε` is the characteristic vector (Dickson invariant / Arf datum) of the quadratic form
`c ↦ c ⌣ c` whose polar form is the cup form.  Characteristic vectors are unique because the cup
form is **nondegenerate**, and that is exactly the Demushkin clause 3: pairing against the
partner coordinate character `e_{i*}` reads off the `i`-th coordinate
(`sqGram_sqPartnerChar_right`, from `sqRelatorQuadraticInitialGram_basis_partner`).  So:

```text
  b(ε∘Ψ, d) = b(ε∘Ψ, (d∘Ψ⁻¹)∘Ψ) = b(ε, d∘Ψ⁻¹) = b(d∘Ψ⁻¹, d∘Ψ⁻¹) = b(d, d) = b(ε, d) ,
```

using the isometry property twice, and nondegeneracy gives `ε∘Ψ = ε`.  Since `sqSign = (−1)^ε`
(`sqSign_eq_comp_sqEps`, via the `±1`-realisation `sqNegOnePow`), the sign row is fixed too.

Note the asymmetry with `PivotClimb`'s `modTwoChar_aut_dsqX1`: that theorem says `Ψ` fixes the
**vector** `x̄₁` in the Frattini quotient; this one says `Ψ` fixes the **functional** `ε` on the
nose.  The cup form is what converts one into the other, and it is nondegeneracy — not the
`Aut`-invariance alone — that does the converting.

## Demushkin status of `D_sq h`

`IsDemushkin 2 (D_sq h)` is **already a theorem** of the tree
(`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteDegreeThree.lean`, `isDemushkin_DSq`,
with `demushkinRank_DSq h = 3 + 2h` and `card_H2_DSq h = 2` from
`…LabuteElementaryH2.lean`).  §5 restates the package inside `SqCore` — where the residual
lives — together with the nondegeneracy input in the form this file actually uses, so that the
Demushkin clause and the cup-form calculus are visibly the same statement.

`demushkinQ (D_sq h) = 2` is **not** proved, here or anywhere in the tree.  Both precedents get
it from an explicit abelianization decomposition — `GQ2/Roe/DRDemushkin.lean`'s `demushkinQ_DR`
from `BRDecomposition`, and `MarkedCore/N.lean`'s `demushkinQ_DN_nFrame` from an `NFrame α h`
(a `ContinuousMulEquiv (topAbelianization G) (NFrameModel h)`) — and the square family has no
such frame yet.  Nothing below uses it.

## What this file does **not** settle

`SqLamNuClearHypothesis h` at `h ≥ 1` is open, exactly as `SqChiNuClearHypothesis h` was — the
two are now equivalent.  §6 names the transitivity statement that would discharge it
(`SqLamMarkTransitivity`), and §6b reduces it to a **word-level** existence statement: it is
enough to exhibit, per selected marking, one relator-killing frame with a surjective lift and
the prescribed rows — no inverse substitution and no composition identity, because `D_sq h` is
Hopfian.

What §6b does *not* do is produce the frame.  Nor does the Demushkin classification hand one
over: the classification's uniqueness clause yields an *abstract* isomorphism, with no control
over `ν`, whereas the residual needs the finer `Aut`-transitivity on markings.  And the odd-rank
classification input is itself absent by design — `GQ2/Dyadic/LabuteInterface.lean` records that
there is deliberately no `SqLabHypothesis`, because the repository has not fixed an abstract
characterization of the canonical orientation, and `q = 2` is exactly the case of Labute's
classification where the pair `(n, q)` does not suffice and the extra invariant `im χ` is needed
(compare `MLabHypothesis`/`NLabHypothesis`, which carry an `im χ` clause).  For `D_sq h` that
invariant is at least *available*: `chiSq_surjective` (`PivotClimb` §7) gives `im χ_sq = ℤ₂ˣ`.

## Contents

* **§1** partner characters and nondegeneracy of `sqGram` (`modTwoChar_eq_of_sqGram_eq`);
* **§2** `sqEps`, `sqGram_sqEps`, and `sqEps_of_aut` — the functional `ε` is `Aut`-invariant;
* **§3** `sqNegOnePow`, `sqSign_eq_comp_sqEps`, and **`sqSign_of_aut`**;
* **§4** `chiSq_preserving_iff_nuLam`, `SqLamNuClearHypothesis`, and the cut restated;
* **§5** the Demushkin package of `D_sq h`, restated in `SqCore`;
* **§6** the transitivity statement and the reduction of the residual to it;
* **§6b** `sqAutOfMark` and `sqLamMarkTransitivity_of_frames` — the frame form, with no inverse;
* **§7** stress pins, **§8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore GQ2.Dyadic.LSquare

noncomputable local instance (h : ℕ) : DistribMulAction (DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

noncomputable local instance (h : ℕ) : ContinuousSMul (DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The mod-two cup form is nondegenerate

Demushkin clause 3, in the coordinate form the residual consumes: pairing a character against the
**partner** coordinate character of a letter reads off that letter's coordinate.  The partner
permutation is the one recorded by the relator's quadratic initial form — `σ ↔ x₀`, `x₁` fixed,
`u_j ↔ v_j` — so the Gram matrix is a permutation matrix and the reading is one line. -/

section Nondegeneracy

variable {h : ℕ}

/-- **The partner character** of a generator index `i`: the mod-two coordinate character of the
letter that the relator's quadratic initial form pairs with `i`
(`ContCoh.sqInitialPartner`). -/
noncomputable def sqPartnerChar (h : ℕ) (i : Fin (sqRank h)) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) :=
  dsqCoordinateCharacter h (dsqCoordinateBasis h (ContCoh.sqInitialPartner h i))

@[simp] theorem toAdd_sqPartnerChar_gen (i j : Fin (sqRank h)) :
    toAdd (sqPartnerChar h i (sqGen h j))
      = dsqCoordinateBasis h (ContCoh.sqInitialPartner h i) j := by
  rw [sqPartnerChar, dsqCoordinateCharacter_gen, toAdd_ofAdd]

/-- **Right nondegeneracy, in coordinates**: `c ⌣ e_{i*} = c(g_i)`. -/
theorem sqGram_sqPartnerChar_right
    (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) (i : Fin (sqRank h)) :
    sqGram h c (sqPartnerChar h i) = toAdd (c (sqGen h i)) := by
  show ContCoh.sqRelatorQuadraticInitialGram h
      (fun a b => toAdd (c (sqGen h a)) * toAdd (sqPartnerChar h i (sqGen h b))) = _
  rw [show (fun a b => toAdd (c (sqGen h a)) * toAdd (sqPartnerChar h i (sqGen h b)))
      = dsqCupMatrix h (fun a => toAdd (c (sqGen h a)))
          (dsqCoordinateBasis h (ContCoh.sqInitialPartner h i)) from by
    funext a b
    show toAdd (c (sqGen h a)) * toAdd (sqPartnerChar h i (sqGen h b)) = _
    rw [toAdd_sqPartnerChar_gen]
    rfl]
  exact sqRelatorQuadraticInitialGram_basis_partner h _ i

/-- **Left nondegeneracy, in coordinates**: `e_{i*} ⌣ d = d(g_i)`. -/
theorem sqGram_sqPartnerChar_left
    (d : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) (i : Fin (sqRank h)) :
    sqGram h (sqPartnerChar h i) d = toAdd (d (sqGen h i)) := by
  show ContCoh.sqRelatorQuadraticInitialGram h
      (fun a b => toAdd (sqPartnerChar h i (sqGen h a)) * toAdd (d (sqGen h b))) = _
  rw [show (fun a b => toAdd (sqPartnerChar h i (sqGen h a)) * toAdd (d (sqGen h b)))
      = dsqCupMatrix h (dsqCoordinateBasis h (ContCoh.sqInitialPartner h i))
          (fun b => toAdd (d (sqGen h b))) from by
    funext a b
    show toAdd (sqPartnerChar h i (sqGen h a)) * toAdd (d (sqGen h b)) = _
    rw [toAdd_sqPartnerChar_gen]
    rfl]
  exact sqRelatorQuadraticInitialGram_partner_basis h _ i

/-- **Nondegeneracy of the mod-two cup form**: a mod-two character of `D_sq h` is determined by
its cup pairings.  This is the `IsDemushkin` clause-3 content of `isDemushkin_DSq`, restated as
the separation property the automorphism calculus needs. -/
theorem modTwoChar_eq_of_sqGram_eq
    {c d : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))}
    (hg : ∀ e, sqGram h c e = sqGram h d e) : c = d := by
  refine dsq_hom_ext _ _ fun i => Multiplicative.toAdd.injective ?_
  rw [← sqGram_sqPartnerChar_right c i, ← sqGram_sqPartnerChar_right d i, hg]

end Nondegeneracy

/-! ## §2 The characteristic vector of the cup form is `Aut`-invariant -/

section CharacteristicVector

variable {h : ℕ}

/-- **The characteristic vector `ε`** of the mod-two cup form: the coordinate character of the
torsion letter `x₁`.  (`x₁` is its own partner, so `ε` is at once the `x₁`-coordinate functional
and the `x₁`-partner character.) -/
noncomputable def sqEps (h : ℕ) : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) :=
  sqPartnerChar h 2

theorem toAdd_sqEps_gen (i : Fin (sqRank h)) :
    toAdd (sqEps h (sqGen h i)) = if i = 2 then 1 else 0 := by
  rw [sqEps, toAdd_sqPartnerChar_gen, ContCoh.sqInitialPartner_two, dsqCoordinateBasis,
    Pi.single_apply]

/-- **`ε` is the characteristic vector**: `ε ⌣ c = c ⌣ c` for every mod-two character `c`.  The
left-hand side is `sqGram_sqPartnerChar_left` at `i = 2`, the right-hand side is `PivotClimb`'s
`sqGram_self`, and both are `c(x₁)`. -/
theorem sqGram_sqEps (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    sqGram h (sqEps h) c = sqGram h c c := by
  rw [sqEps, sqGram_sqPartnerChar_left, sqGram_self]

/-- **The characteristic vector is fixed by the whole automorphism group** — no orientation
clause.  The cup form is an isometry invariant of `Aut(D_sq h)` (`sqGram_comp_autHom`), so
`ε∘Ψ` is again a characteristic vector; nondegeneracy makes it *the* one. -/
theorem sqEps_of_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (x : (DSq h : Type)) : sqEps h (Ψ x) = sqEps h x := by
  have key : ∀ e : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)),
      sqGram h ((sqEps h).comp (autHom Ψ)) e = sqGram h (sqEps h) e := by
    intro e
    set d : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) :=
      e.comp (autHom Ψ.symm) with hddef
    have hde : ∀ y : (DSq h : Type), d (Ψ y) = e y := fun y => by
      show e (Ψ.symm (Ψ y)) = e y
      rw [Ψ.symm_apply_apply]
    calc sqGram h ((sqEps h).comp (autHom Ψ)) e
        = sqGram h ((sqEps h).comp (autHom Ψ)) (d.comp (autHom Ψ)) :=
          sqGram_congr (fun _ => rfl) (fun i => (hde (sqGen h i)).symm)
      _ = sqGram h (sqEps h) d := sqGram_comp_autHom Ψ _ _
      _ = sqGram h d d := sqGram_sqEps d
      _ = sqGram h (d.comp (autHom Ψ)) (d.comp (autHom Ψ)) := (sqGram_comp_autHom Ψ d d).symm
      _ = sqGram h e e := sqGram_congr (fun i => hde (sqGen h i)) (fun i => hde (sqGen h i))
      _ = sqGram h (sqEps h) e := (sqGram_sqEps e).symm
  exact DFunLike.congr_fun (modTwoChar_eq_of_sqGram_eq key) x

end CharacteristicVector

/-! ## §3 The sign row is automatic -/

section SignRow

/-- The `±1`-realisation of a mod-two value: `ofAdd 0 ↦ 1`, `ofAdd 1 ↦ −1`. -/
noncomputable def sqNegOnePow : ContinuousMonoidHom (Multiplicative (ZMod 2)) ℤ_[2]ˣ :=
  ⟨{ toFun := fun a => if toAdd a = 0 then 1 else -1
     map_one' := by
       show (if toAdd (1 : Multiplicative (ZMod 2)) = 0 then (1 : ℤ_[2]ˣ) else -1) = 1
       rw [toAdd_one, if_pos rfl]
     map_mul' := fun a b => by
       have hab : toAdd (a * b) = toAdd a + toAdd b := rfl
       have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
       show (if toAdd (a * b) = 0 then (1 : ℤ_[2]ˣ) else -1)
         = (if toAdd a = 0 then (1 : ℤ_[2]ˣ) else -1) *
             if toAdd b = 0 then (1 : ℤ_[2]ˣ) else -1
       rcases h2 (toAdd a) with ha | ha <;> rcases h2 (toAdd b) with hb | hb <;>
         rw [hab, ha, hb]
       all_goals simp
       all_goals decide },
   continuous_of_discreteTopology⟩

theorem sqNegOnePow_apply (a : Multiplicative (ZMod 2)) :
    sqNegOnePow a = if toAdd a = 0 then 1 else -1 := rfl

variable {h : ℕ}

theorem sqZero_ne_two (h : ℕ) : (0 : Fin (sqRank h)) ≠ 2 := fun e => by
  have hv := congrArg Fin.val e
  rw [sqVal_zero, sqVal_two] at hv
  omega

theorem sqOne_ne_two (h : ℕ) : (1 : Fin (sqRank h)) ≠ 2 := fun e => by
  have hv := congrArg Fin.val e
  rw [sqVal_one, sqVal_two] at hv
  omega

theorem sqHandleIdxU_ne_two (j : Fin h) : sqHandleIdxU j ≠ (2 : Fin (sqRank h)) :=
  (sqTwo_ne_handleU j).symm

theorem sqHandleIdxV_ne_two (j : Fin h) : sqHandleIdxV j ≠ (2 : Fin (sqRank h)) :=
  (sqTwo_ne_handleV j).symm

/-- **The sign character is the `±1`-realisation of the characteristic vector**:
`sign = (−1)^ε`.  Generator by generator: `x₁ ↦ −1` on both sides, everything else `↦ 1`. -/
theorem sqSign_eq_comp_sqEps (h : ℕ) : sqSign h = sqNegOnePow.comp (sqEps h) := by
  have hval : ∀ j : Fin (sqRank h), (sqNegOnePow.comp (sqEps h)) (sqGen h j)
      = if j = 2 then (-1 : ℤ_[2]ˣ) else 1 := by
    intro j
    show (if toAdd (sqEps h (sqGen h j)) = 0 then (1 : ℤ_[2]ˣ) else -1) = _
    rw [toAdd_sqEps_gen]
    by_cases hj : j = 2
    · rw [if_pos hj, if_pos hj, if_neg (by decide)]
    · rw [if_neg hj, if_neg hj, if_pos rfl]
  refine dsq_hom_ext _ _ fun i => ?_
  rw [hval i]
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [if_neg (sqZero_ne_two h)]
    exact sqSign_sigma h
  · rw [if_neg (sqOne_ne_two h)]
    exact sqSign_x0 h
  · rw [if_pos rfl]
    exact sqSign_x1 h
  · rw [if_neg (sqHandleIdxU_ne_two j)]
    exact sqSign_handleU j
  · rw [if_neg (sqHandleIdxV_ne_two j)]
    exact sqSign_handleV j

/-- **THE HEADLINE — the sign row is automatic.**  *Every* continuous automorphism of `D_sq h`
preserves the sign character; no orientation clause is needed.  So the second of
`chiSq_preserving_iff`'s two row conditions is vacuous. -/
theorem sqSign_of_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (x : (DSq h : Type)) : sqSign h (Ψ x) = sqSign h x := by
  rw [sqSign_eq_comp_sqEps]
  show sqNegOnePow (sqEps h (Ψ x)) = sqNegOnePow (sqEps h x)
  rw [sqEps_of_aut Ψ x]

end SignRow

/-! ## §4 The χ-clause collapses onto the λ-row -/

section LamRow

variable {h : ℕ}

/-- **The χ-clause is exactly the λ-row.**  `HandleEichler` §4 splits χ-preservation into the
λ-row and the sign row; §3 shows the sign row costs nothing. -/
theorem chiSq_preserving_iff_nuLam (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    (∀ x, chiSq h (Ψ x) = chiSq h x) ↔ ∀ x, nuLam h (Ψ x) = nuLam h x :=
  (chiSq_preserving_iff Ψ).trans
    ⟨fun H => H.1, fun H => ⟨H, fun x => sqSign_of_aut Ψ x⟩⟩

/-- **The residual, with the χ-clause replaced by the λ-row.**  Same statement as
`SqChiNuClearHypothesis`, with the `ℤ₂ˣ`-valued clause `χ_sq ∘ Ψ = χ_sq` traded for the
`ℤ₂`-linear clause `λ ∘ Ψ = λ`. -/
def SqLamNuClearHypothesis (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x

/-- **The two forms of the residual agree.** -/
theorem sqChiNuClearHypothesis_iff_lam :
    SqChiNuClearHypothesis h ↔ SqLamNuClearHypothesis h := by
  constructor
  · intro H nu' hs hx
    obtain ⟨Ψ, hchi, hval⟩ := H nu' hs hx
    exact ⟨Ψ, (chiSq_preserving_iff_nuLam Ψ).mp hchi, hval⟩
  · intro H nu' hs hx
    obtain ⟨Ψ, hlam, hval⟩ := H nu' hs hx
    exact ⟨Ψ, (chiSq_preserving_iff_nuLam Ψ).mpr hlam, hval⟩

/-- **The cut, in λ-row form.**  Combining with `HandleEichler`'s headline: at the canonical
exponent the one-binder handle stratum *is* the λ-row clearing hypothesis. -/
theorem sqHandleMixFixesCore_sqPivotExp_iff_lam :
    SqHandleMixFixesCore h sqPivotExp ↔ SqLamNuClearHypothesis h :=
  sqHandleMixFixesCore_sqPivotExp_iff.trans sqChiNuClearHypothesis_iff_lam

/-- **The complete pinning at `h ≥ 1`**, in λ-row form. -/
theorem sqHandleMixFixesCore_iff_lam (hh : 0 < h) {c : ℤ_[2]} :
    SqHandleMixFixesCore h c ↔ IsUnit c ∧ SqLamNuClearHypothesis h := by
  rw [sqHandleMixFixesCore_iff_chiNuClearHypothesis hh, sqChiNuClearHypothesis_iff_lam]

/-- **The exact gap between the two routes.**  Forgetting the λ-row lands on `ChiFreeClearing`'s
χ-free target: after this file the certificate route and the realization bypass differ by one
`ℤ₂`-linear row condition on the correcting automorphism, and by nothing else. -/
theorem sqNuClearHypothesis_of_lamNuClearHypothesis (H : SqLamNuClearHypothesis h) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_chiNuClearHypothesis (sqChiNuClearHypothesis_iff_lam.mpr H)

/-- At `h = 0` the λ-row form is a theorem, exactly as the χ-form is. -/
theorem sqLamNuClearHypothesis_zero : SqLamNuClearHypothesis 0 :=
  sqChiNuClearHypothesis_iff_lam.mp sqChiNuClearHypothesis_zero

end LamRow

/-! ## §5 The Demushkin package of `D_sq h`, inside `SqCore`

`IsDemushkin 2 (D_sq h)` is already a theorem of the tree; it is restated here so that the
residual's own file can name it, and so that the identification of "Demushkin clause 3" with
"`sqGram` is nondegenerate" (§1) is visible in one place. -/

section DemushkinPackage

/-- **`D_sq h` is a Demushkin pro-2 group**, at every handle count
(`GammaLSylowPreimageFieldLabuteDegreeThree.isDemushkin_DSq`; its nondegenerate cup matrix is
the certified constructor table `YY + SX + XS + Σ(UV + VU)`). -/
theorem dsq_isDemushkin (h : ℕ) : IsDemushkin 2 (DSq h : Type) := isDemushkin_DSq h

/-- **The Demushkin rank is `3 + 2h`** — the presentation's generator count. -/
theorem dsq_demushkinRank (h : ℕ) : demushkinRank 2 (DSq h : Type) = 3 + 2 * h :=
  demushkinRank_DSq h

/-- `dim H²(D_sq h, 𝔽₂) = 1`, in `Nat.card` form: the presentation is one-relator and minimal. -/
theorem dsq_cardH2 (h : ℕ) : Nat.card (ContCoh.H2 (DSq h : Type) (ZMod 2)) = 2 :=
  card_H2_DSq h

end DemushkinPackage

/-! ## §6 What would discharge the residual: transitivity on markings

The residual asks for an automorphism carrying an arbitrary **selected** marking onto `ν_sq`.
`JointClearing` §7 already records the easy half of the basis-transitivity route
(`sqRelWord_of_aut`: any tuple in the `Aut`-orbit of the standard generators kills the relator).
The hard half is the statement below.  It is stated as a `Prop` and *not* proved: it is the
Demushkin classification's uniqueness clause, specialised to markings.

Note what §4 buys here: the automorphism produced is only required to fix the `ℤ₂`-functional
`λ`, so the hypothesis is a statement about the `Aut`-action on `Hom(D_sq h, ℤ₂)` alone — a
`ℤ₂`-lattice of rank `2 + 2h` — with no `ℤ₂ˣ`-valued side condition. -/

section Transitivity

/-- **The marking-transitivity hypothesis**: the stabiliser of the χ-exponent functional `λ` in
`Aut(D_sq h)` acts transitively on the selected markings, i.e. carries every marking with the
P3-selected core rows `(ν(σ), ν(x₀)) = (1, 0)` onto the standard marking `ν_sq`.

This is *literally* `SqLamNuClearHypothesis h` (`sqLamMarkTransitivity_iff`); it is named
separately so that the residual can be quoted as "one transitivity statement about a Demushkin
group" rather than as a clearing condition, and so that a future supplier has a target whose
name says what it is. -/
def SqLamMarkTransitivity (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x

theorem sqLamMarkTransitivity_iff (h : ℕ) :
    SqLamMarkTransitivity h ↔ SqLamNuClearHypothesis h := Iff.rfl

/-- **The residual over the transitivity hypothesis.**  With `SqLamMarkTransitivity h` in hand
the whole `h ≥ 1` handle stratum follows, at every unit exponent. -/
theorem sqHandleMixFixesCore_of_lamMarkTransitivity {h : ℕ} {c : ℤ_[2]} (hc : IsUnit c)
    (hh : 0 < h) (H : SqLamMarkTransitivity h) : SqHandleMixFixesCore h c :=
  (sqHandleMixFixesCore_iff_lam hh).mpr ⟨hc, (sqLamMarkTransitivity_iff h).mp H⟩

/-- …and so does `ChiFreeClearing`'s χ-free target, a fortiori. -/
theorem sqNuClearHypothesis_of_lamMarkTransitivity {h : ℕ} (H : SqLamMarkTransitivity h) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_lamNuClearHypothesis ((sqLamMarkTransitivity_iff h).mp H)

/-- The hypothesis is a theorem at `h = 0` — where the residual is closed — so it is not
vacuous. -/
theorem sqLamMarkTransitivity_zero : SqLamMarkTransitivity 0 := sqLamNuClearHypothesis_zero

end Transitivity

/-! ## §6b The frame form: no inverse substitution is needed

`JointClearing` §7 has the easy half of the basis-transitivity route.  This section supplies the
**hard half**, and it is cheap: a relator-killing frame whose lift is *surjective* is
automatically an automorphism, because `D_sq h` is topologically finitely generated profinite and
therefore **Hopfian** (`profinite_hopfian`, paper Lemma 2.5).

This is a real reduction of the search burden.  The seed calculus in `SqCore/NuSeeds.lean` and
`SqCore/NuSeedWide.lean` currently asks a residual seed for **ten** words — five forward slots and
five inverse slots — plus the two composition identities `comp_fwd`/`comp_bwd` that certify the
substitution is invertible.  `sqAutOfMark` replaces all of that by surjectivity of the forward
substitution alone, and `sqSurjective_of_gens_mem_range` reduces *that* to "each standard
generator lies in the image", which is what the Frattini/Burnside criterion checks. -/

section Frames

/-- **Surjectivity from a topological generating set inside the range**: the set form of
`SectionThree.surjective_of_mem_range_topGen` (the range of a continuous map out of a compact
group is closed, so it swallows the topological closure of the subgroup it generates). -/
theorem surjective_of_topGen_subset_range {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [IsTopologicalGroup G] [T2Space G] {S : Set G}
    (hgen : (Subgroup.closure S).topologicalClosure = ⊤)
    (f : ContinuousMonoidHom G G) (hS : S ⊆ Set.range f) : Function.Surjective f := by
  have hclosed : IsClosed ((f.toMonoidHom.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range f.continuous_toFun).isClosed
  have h1 : Subgroup.closure S ≤ f.toMonoidHom.range :=
    Subgroup.closure_le _ |>.mpr (by rw [MonoidHom.coe_range]; exact hS)
  have h2 : (Subgroup.closure S).topologicalClosure ≤ f.toMonoidHom.range :=
    Subgroup.topologicalClosure_minimal _ h1 hclosed
  rw [hgen] at h2
  exact fun y => h2 (Subgroup.mem_top y)

variable {h : ℕ} {m : Fin (sqRank h) → (DSq h : Type)}

/-- **A relator-killing frame whose lift is surjective is an automorphism.**  The injectivity is
free: `D_sq h` is topologically finitely generated profinite, hence Hopfian. -/
noncomputable def sqAutOfMark (hrel : sqRelWord m = 1)
    (hsurj : Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel)) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective (sqLiftHom h (isProP_DSq h) m hrel)
    ⟨profinite_hopfian (dsqFinsetTopGen h) _ hsurj, hsurj⟩

@[simp] theorem sqAutOfMark_gen (hrel : sqRelWord m = 1)
    (hsurj : Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel)) (i : Fin (sqRank h)) :
    sqAutOfMark hrel hsurj (sqGen h i) = m i :=
  sqLiftHom_gen h (isProP_DSq h) m hrel i

/-- The Frattini-checkable form of the surjectivity hypothesis: it suffices that every standard
generator lies in the image of the substitution. -/
theorem sqSurjective_of_gens_mem_range (hrel : sqRelWord m = 1)
    (hS : Set.range (sqGen h) ⊆ Set.range (sqLiftHom h (isProP_DSq h) m hrel)) :
    Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) :=
  surjective_of_topGen_subset_range (dsq_topGen h) _ hS

/-- **The frame form of the transitivity input.**  Exhibiting, for each selected marking, one
relator-killing frame with a surjective lift and the prescribed `λ`- and `ν`-rows discharges the
whole residual.  No inverse substitution, and no composition identity, is required. -/
theorem sqLamMarkTransitivity_of_frames
    (H : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
          Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
            (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
              ∀ i, nu' (m i) = nuSq h (sqGen h i)) :
    SqLamMarkTransitivity h := by
  intro nu' hsigma hx0
  obtain ⟨m, hrel, hsurj, hlam, hval⟩ := H nu' hsigma hx0
  refine ⟨sqAutOfMark hrel hsurj, fun x => ?_, fun x => ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel hsurj)) = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel hsurj (sqGen h i)) = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen]
        exact hlam i
    exact DFunLike.congr_fun hext x
  · have hext : nu'.comp (autHom (sqAutOfMark hrel hsurj)) = nuSq h :=
      dsq_hom_ext _ _ fun i => by
        show nu' (sqAutOfMark hrel hsurj (sqGen h i)) = nuSq h (sqGen h i)
        rw [sqAutOfMark_gen]
        exact hval i
    exact DFunLike.congr_fun hext x

/-- …and hence the handle stratum itself, at every unit exponent. -/
theorem sqHandleMixFixesCore_of_frames {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h)
    (H : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
          Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
            (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
              ∀ i, nu' (m i) = nuSq h (sqGen h i)) :
    SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_frames H)

/-- The identity frame is a frame: the reduction is not vacuous. -/
theorem sqSurjective_sqGen :
    Function.Surjective (sqLiftHom h (isProP_DSq h) (sqGen h) (dsq_relation h)) := by
  refine sqSurjective_of_gens_mem_range (dsq_relation h) ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨sqGen h i, sqLiftHom_gen _ _ _ _ i⟩

end Frames

/-! ## §7 Stress pins -/

section StressTests

/-- Stress: the sign row costs nothing even for automorphisms that move the orientation. -/
example (h : ℕ) (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) (x : (DSq h : Type)) :
    sqSign h (Ψ x) = sqSign h x := sqSign_of_aut Ψ x

/-- Stress: the sign character is still non-trivial — §3 does not make it vacuous, it makes it
*invariant*. -/
example (h : ℕ) : sqSign h (dsqX1 h) ≠ 1 := by
  rw [sqSign_x1]
  exact negOne_ne_one_unitsPadicInt

/-- Stress: `ε` is genuinely non-trivial, so `sqEps_of_aut` is not a statement about the trivial
character. -/
example (h : ℕ) : toAdd (sqEps h (sqGen h 2)) = 1 := by
  rw [toAdd_sqEps_gen, if_pos rfl]

/-- Stress: `ε` vanishes on the pivot letters, so it is *not* the λ-row — the two clauses of
`chiSq_preserving_iff` really were independent conditions before §3. -/
example (h : ℕ) : toAdd (sqEps h (sqGen h 0)) = 0 := by
  rw [toAdd_sqEps_gen, if_neg (sqZero_ne_two h)]

/-- Stress: the characteristic-vector identity, at the standard marking's own reduction. -/
example (h : ℕ) (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    sqGram h (sqEps h) c = toAdd (c (sqGen h 2)) := by
  rw [sqGram_sqEps, sqGram_self]

/-- Stress: nondegeneracy is sharp — the pairing separates the coordinate characters. -/
example (h : ℕ) (i : Fin (sqRank h)) :
    sqGram h (sqEps h) (sqPartnerChar h i) = toAdd (sqEps h (sqGen h i)) :=
  sqGram_sqPartnerChar_right _ i

/-- Stress: the cut, in λ-row form, at one handle. -/
example : SqHandleMixFixesCore 1 sqPivotExp ↔ SqLamNuClearHypothesis 1 :=
  sqHandleMixFixesCore_sqPivotExp_iff_lam

/-- Stress: the refuted exponent stays refuted through the λ-row form. -/
example : ¬ SqHandleMixFixesCore 1 0 := not_sqHandleMixFixesCore_zero (by omega)

/-- Stress: the two residual shapes are the same statement. -/
example (h : ℕ) : SqChiNuClearHypothesis h ↔ SqLamNuClearHypothesis h :=
  sqChiNuClearHypothesis_iff_lam

/-- Stress: `h = 0` is a theorem on the λ-row side too. -/
example : SqLamNuClearHypothesis 0 := sqLamNuClearHypothesis_zero

/-- Stress: the Demushkin package, at one handle — rank `5`, `#H² = 2`. -/
example : demushkinRank 2 (DSq 1 : Type) = 5 := by rw [dsq_demushkinRank]

/-- Stress: the transitivity hypothesis discharges the one-handle residual at every unit
exponent. -/
example {c : ℤ_[2]} (hc : IsUnit c) (H : SqLamMarkTransitivity 1) :
    SqHandleMixFixesCore 1 c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc (by omega) H

/-- Stress: the frame route is not vacuous — the identity frame kills the relator and its lift
is surjective, so `sqAutOfMark` really produces automorphisms. -/
example (h : ℕ) (i : Fin (sqRank h)) :
    sqAutOfMark (dsq_relation h) sqSurjective_sqGen (sqGen h i) = sqGen h i :=
  sqAutOfMark_gen _ _ i

/-- Stress: the frame form of the residual, at one handle — five words and a surjectivity
check, where the seed calculus asks for ten words and two composition identities. -/
example {c : ℤ_[2]} (hc : IsUnit c)
    (H : ∀ nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma 1) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 1) = ofAdd (0 : ℤ_[2]) →
        ∃ (m : Fin (sqRank 1) → (DSq 1 : Type)) (hrel : sqRelWord m = 1),
          Function.Surjective (sqLiftHom 1 (isProP_DSq 1) m hrel) ∧
            (∀ i, nuLam 1 (m i) = nuLam 1 (sqGen 1 i)) ∧
              ∀ i, nu' (m i) = nuSq 1 (sqGen 1 i)) :
    SqHandleMixFixesCore 1 c :=
  sqHandleMixFixesCore_of_frames hc (by omega) H

end StressTests

/-! ## §8 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable.  Census unchanged at **11**. -/

section AxiomPins

#print axioms sqPartnerChar
#print axioms sqGram_sqPartnerChar_right
#print axioms sqGram_sqPartnerChar_left
#print axioms modTwoChar_eq_of_sqGram_eq
#print axioms sqEps
#print axioms sqGram_sqEps
#print axioms sqEps_of_aut
#print axioms sqNegOnePow
#print axioms sqSign_eq_comp_sqEps
#print axioms sqSign_of_aut
#print axioms chiSq_preserving_iff_nuLam
#print axioms SqLamNuClearHypothesis
#print axioms sqChiNuClearHypothesis_iff_lam
#print axioms sqHandleMixFixesCore_sqPivotExp_iff_lam
#print axioms sqHandleMixFixesCore_iff_lam
#print axioms sqNuClearHypothesis_of_lamNuClearHypothesis
#print axioms sqLamNuClearHypothesis_zero
#print axioms dsq_isDemushkin
#print axioms dsq_demushkinRank
#print axioms dsq_cardH2
#print axioms SqLamMarkTransitivity
#print axioms sqHandleMixFixesCore_of_lamMarkTransitivity
#print axioms sqNuClearHypothesis_of_lamMarkTransitivity
#print axioms sqLamMarkTransitivity_zero
#print axioms surjective_of_topGen_subset_range
#print axioms sqAutOfMark
#print axioms sqSurjective_of_gens_mem_range
#print axioms sqLamMarkTransitivity_of_frames
#print axioms sqHandleMixFixesCore_of_frames
#print axioms sqSurjective_sqGen

end AxiomPins

end SqCore

end Dyadic

end GQ2
