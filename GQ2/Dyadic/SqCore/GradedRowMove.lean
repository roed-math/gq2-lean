/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedClearing

/-!
# W85-ROWMOVE: the row moves, cut to per-class word solvability

Wave 84 (`SqCore/GradedClearing.lean`) collapsed the odd route's last item onto the row plane:
the clearing at every unit-pivot marking follows from the model moves `GClearModelMove h a b`,
and those from the two rays `GClearModelTranslate h c` and `GClearModelScale h d`.  The moves
ask for the campaign's first row-moving automorphisms, and nothing at `h >= 1` in the tree
moves rows.  This module does not construct them outright either.  What it does is remove
every clause except one word identity, and put that identity on the same per-class ladder the
W84-WORD lane built for the `M6` move, with the low rungs proved rather than observed.

## The reduction chain

1. **The row pair** (section 1).  `GRowPair h A B`: a lambda-preserving automorphism whose
   `nu_sq`-rows at `(sigma, x0)` are `(A, B)`.  The bridge `gRow_modelMove_of_pair` turns the
   pair at `(e(1 - c0 b), -(e b))`, `d e = 1`, `d = a - c0 b`, into `GClearModelMove h a b`:
   the model marking is the lambda-twist `d(nu_sq + e b lambda)` of the standard one (wave
   84's `gClear_nuSqOf_eq_twist`), so a lambda-preserving automorphism moves its rows exactly
   through the `nu_sq`-part, and the pair is chosen to land them on `(1, 0)`.  The rays are
   the pairs `(1 - c0 c, -c)` and `(e, 0)`.

2. **The ansatz** (section 2).  `gRowMark h A B c`: slot `i` carries `gen_i * w^{e_i} * c_i`
   with `w` the chi-trivial pivot, exponent row `(A - 1, B, 2B, 0, ..., 0)`, and one
   correction word per slot.  At `(1, 0)` with bare corrections this is the standard frame.

3. **The word reduction** (sections 3, 4).  For corrections with trivial `lambda`-rows and
   (at the two core slots) trivial `nu_sq`-rows, the frame has the prescribed rows, and on
   the unit locus `IsUnit (A - c0 B)` Frattini corrections leave it spanning `H_1`
   (`gRow_modTwoIndep`): the two twisted slots recover `sigma x0^-1`, hence the pivot, hence
   both letters, because `A - 1 - B` is even exactly on the unit locus.  So a builder owes
   ONE equation, `sqRelWord (gRowMark h A B c) = 1`, and nothing else
   (`gRow_pair_of_word`).

4. **The per-class criterion** (sections 5, 6).  The class-`k` solution sets
   `gRowSet h A B k` (corrections in the carrier `lambda_2 ⊓ ker lambda ⊓ ker nu_sq`, relator
   dead to class `k` of the two-central tower) are nested, closed, and live in a compact
   space, and the tower separates points: class-`k` solvability for every `k` gives the row
   pair outright (`gRow_pair_of_forall_class`).  Contrapositively, if a row move is false it
   fails at a finite class, in a finite 2-group, with no inverse-limit step to hide in.

   [W86-HOUSE, as of `f0de6ad5`: this summary drops a binder the theorem carries.
   `gRow_pair_of_forall_class` also takes `IsUnit (A - sqPivotExp * B)`, and it is load bearing,
   not bookkeeping: it feeds `gRow_modTwoIndep`, whose generation argument needs `A - 1 - B`
   even.  The declaration's own docstring says "on the unit locus" correctly; only this line
   does not.  The contrapositive sentence is exact and runs the right way, which is worth
   saying because the `M6` twin's `mpcBld_shift_of_bracket_supply` states it the wrong way
   round.]

5. **The low rungs are theorems** (sections 5b, 6).  `gRow_relWord_mem_two`: EVERY frame
   kills the relator to class 2 (the word is a product of squares and commutators up to
   conjugacy), at every `(A, B)`.  `gRow_relWord_bare_mem_three`: on the unit locus the BARE
   frame kills the relator to class 3.  In the class-three quotient every commutator is
   central of order two (section 5b's calculus), the twisted word collapses onto the standard
   relator times the defect `[x0, w^B] * [w^B, sigma]`, and the defect dies by parity: even
   `B` makes the pivot power a square, odd `B` makes both factors `[x0, sigma]`.  So the
   residue starts at class 4, the same threshold as the `M6` ladder, and the committed
   prose-only class-two balance (`PivotCoreMoves` module docstring, lower-central metric) is
   subsumed one rung up (`gRow_pair_of_forall_class_four`).

   [W86-HOUSE, as of `f0de6ad5`: **"the same threshold as the `M6` ladder" is stale, and was
   already stale when this module merged.**  This module's own claim is exact and unaffected:
   the row-move residue does start at class 4.  But `Instances/MpcBuild.lean`, which landed on
   `dyadic` earlier in the same wave, proves `mpcBld_nonempty_four : (mpcWordSet 4).Nonempty`,
   so the `M6` ladder's residue starts at class FIVE.  The two ladders are one rung apart, and
   that gap is now the interesting comparison rather than the equality.  Same correction at
   `gRow_pair_of_forall_class_four` and in `docs/dyadic/w85-rowmove-note.md`.]

   [W88-HOUSE, as of `ad8c2b62`: both numbers in the block above have moved by one, and the
   one-rung gap survives.  Wave 87 climbed both ladders: `SqCore/GradedRowResidue.lean`'s
   `gRsd_nonempty_four` puts THIS ladder's residue at class five, on the whole unit locus and
   not just the quarter locus, and `Instances/MpcFive.lean`'s `mpcFv_nonempty_five` puts the
   `M6` ladder's at class SIX.  The reading is now five against six: still one rung apart,
   still `M6` ahead.]

6. **The composition** (section 7).  `gRow_clearing_of_forall_class`: per-class solvability
   on the unit locus discharges `SqNuOrientedClearAtUnitPivot h` through wave 84's
   `gClear_clearing_of_model`, and the seam composites carry it to `SqMarkedForwardSupply`
   and the general theorem at every odd-degree field.

## What does not land

The moves themselves.  `GClearModelTranslate h c` and `GClearModelScale h d` at `h >= 1`
remain open at classes `k >= 4`: the obstruction is now in closed form (the class-`k`
solvability of one explicit word with corrections in one explicit closed carrier), and the
honest record of the remaining distance is `docs/dyadic/w85-rowmove-note.md`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Sections 1 to 6 print **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  The section 7 seam composites print std-3 plus the four
census members wave 83's seam always costs (`hilbertSymbol_normCriterion_finiteDyadic`,
`tateDualityAt`, and the two `Foundations` members); `localReciprocity` and `markedRecipAt`
stay binders.  Census unchanged.

[W86-HOUSE, as of `f0de6ad5`: this paragraph accounts for two of the three axiom sets in the
module and omits the third.  `gRow_pair_zero` is in §7 and prints std-3 plus
`{dyadicOrientation, peripheralCyclotomicAction}`, the `h = 0` pins B3c and B8, which is neither
"std-3" nor the seam's four.  §9's pin list records it correctly; only this summary skips it.
Re-measured by elaboration.]
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The row pair, and the bridges to the model moves -/

section RowPair

/-- **The row pair at `(A, B)`**: a lambda-preserving continuous automorphism of `D_sq h`
whose `nu_sq`-rows at the two core letters are `A` and `B`.  Nothing else is asked: no row at
`x1`, no handle rows, no behaviour at any other marking.  This is the exact automorphism
supply the wave-84 residual consumes, in `nu_sq`-coordinates. -/
def GRowPair (h : ℕ) (A B : ℤ_[2]) : Prop :=
  ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
    (∀ x, nuLam h (Ψ x) = nuLam h x)
      ∧ toAdd (nuSq h (Ψ (dsqSigma h))) = A ∧ toAdd (nuSq h (Ψ (dsqX0 h))) = B

/-- The base point is free: the identity realizes the pair `(1, 0)`. -/
theorem gRow_pair_one_zero (h : ℕ) : GRowPair h 1 0 :=
  ⟨ContinuousMulEquiv.refl _, fun _ => rfl,
    by rw [ContinuousMulEquiv.refl_apply, nuSq_sigma, toAdd_ofAdd],
    by rw [ContinuousMulEquiv.refl_apply, nuSq_x0, toAdd_ofAdd]⟩

/-- **The bridge**: the row pair at `(e(1 - c0 b), -(e b))` realizes the model move at
`(a, b)`, where `d = a - c0 b` and `d e = 1`.  The model marking is the lambda-twist
`d(nu_sq + e b lambda)` of the standard one (wave 84's `gClear_nuSqOf_eq_twist`), so a
lambda-preserving automorphism moves its rows exactly through the `nu_sq`-part, and the pair
is chosen to land them on `(1, 0)`. -/
theorem gRow_modelMove_of_pair {h : ℕ} {a b d e : ℤ_[2]} (hde : d * e = 1)
    (hd : d = a - sqPivotExp * b)
    (H : GRowPair h (e * (1 - sqPivotExp * b)) (-(e * b))) : GClearModelMove h a b := by
  obtain ⟨Ψ, hlam, hA, hB⟩ := H
  refine ⟨Ψ, (chiSq_preserving_iff_nuLam Ψ).mpr hlam, ?_, ?_⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [gClear_nuSqOf_eq_twist hde hd, toAdd_nuTwist, toAdd_ofAdd, hA, hlam (dsqSigma h),
      nuLam_sigma, toAdd_ofAdd]
    linear_combination hde
  · refine Multiplicative.toAdd.injective ?_
    rw [gClear_nuSqOf_eq_twist hde hd, toAdd_nuTwist, toAdd_ofAdd, hB, hlam (dsqX0 h),
      nuLam_x0, toAdd_ofAdd]
    ring

/-- **The converse bridge**: a model move with a chi-preserving automorphism realizes the row
pair at the corresponding coordinates.  So the pair target is exactly as strong as the model
move plus lambda-preservation, not stronger: the two sides of the bridge are a change of
coordinates on the same residual. -/
theorem gRow_pair_of_modelMove {h : ℕ} {a b d e : ℤ_[2]} (hde : d * e = 1)
    (hd : d = a - sqPivotExp * b) (H : GClearModelMove h a b) :
    GRowPair h (e * (1 - sqPivotExp * b)) (-(e * b)) := by
  obtain ⟨Ψ, hchi, hs, hx⟩ := H
  have hlam := (chiSq_preserving_iff_nuLam Ψ).mp hchi
  refine ⟨Ψ, hlam, ?_, ?_⟩
  · have h1 := congrArg toAdd hs
    rw [gClear_nuSqOf_eq_twist hde hd, toAdd_nuTwist, toAdd_ofAdd, hlam (dsqSigma h),
      nuLam_sigma, toAdd_ofAdd] at h1
    linear_combination e * h1
      - (toAdd (nuSq h (Ψ (dsqSigma h))) + e * b * sqPivotExp) * hde
  · have h2 := congrArg toAdd hx
    rw [gClear_nuSqOf_eq_twist hde hd, toAdd_nuTwist, toAdd_ofAdd, hlam (dsqX0 h),
      nuLam_x0, toAdd_ofAdd] at h2
    linear_combination e * h2 - (toAdd (nuSq h (Ψ (dsqX0 h))) + e * b) * hde

/-- **The translation ray in pair coordinates**: rows `(1 - c0 c, -c)`. -/
def GRowTranslate (h : ℕ) (c : ℤ_[2]) : Prop := GRowPair h (1 - sqPivotExp * c) (-c)

/-- **The scaling ray in pair coordinates**: rows `(e, 0)`. -/
def GRowScale (h : ℕ) (e : ℤ_[2]) : Prop := GRowPair h e 0

/-- The translation pair delivers wave 84's translation move. -/
theorem gRow_translate_of_pair {h : ℕ} {c : ℤ_[2]} (H : GRowTranslate h c) :
    GClearModelTranslate h c := by
  rw [GClearModelTranslate]
  refine gRow_modelMove_of_pair (d := 1) (e := 1) (mul_one 1) (by ring) ?_
  rw [show (1 : ℤ_[2]) * (1 - sqPivotExp * c) = 1 - sqPivotExp * c by ring,
    show -((1 : ℤ_[2]) * c) = -c by ring]
  exact H

/-- The scaling pair at `e` delivers wave 84's scaling move at `d = e⁻¹`. -/
theorem gRow_scale_of_pair {h : ℕ} {d e : ℤ_[2]} (hde : d * e = 1) (H : GRowScale h e) :
    GClearModelScale h d := by
  rw [GClearModelScale]
  refine gRow_modelMove_of_pair hde (by ring) ?_
  rw [show e * (1 - sqPivotExp * 0) = e by ring, show -(e * (0 : ℤ_[2])) = 0 by ring]
  exact H

/-- The ray pairs generate every model move on the unit locus, through wave 84's
`gClear_modelMove_of_ray`. -/
theorem gRow_modelMove_of_ray_pairs {h : ℕ} (htr : ∀ c : ℤ_[2], GRowTranslate h c)
    (hsc : ∀ e : ℤ_[2], IsUnit e → GRowScale h e) {a b : ℤ_[2]}
    (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b := by
  refine gClear_modelMove_of_ray (fun c => gRow_translate_of_pair (htr c)) (fun d hdu => ?_) hd
  obtain ⟨u, hu⟩ := hdu
  refine gRow_scale_of_pair (e := ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) ?_ (hsc _ ⟨u⁻¹, rfl⟩)
  rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end RowPair

/-! ## §2 The ansatz: pivot-twisted slots with one correction word each -/

section Frame

variable {h : ℕ}

/-- **The exponent row of the ansatz**: `(A - 1, B, 2B)` on the three core letters, `0` on
every handle letter.  The `x1`-exponent `2B` mirrors the forced row `nu(x1) = 2 nu(x0)`
(`toAdd_nu_dsqX1`): it is the unique choice whose degree-one part satisfies the abelianized
relation with no correction. -/
noncomputable def gRowExp (A B : ℤ_[2]) {h : ℕ} (i : Fin (sqRank h)) : ℤ_[2] :=
  if (i : ℕ) = 0 then A - 1 else if (i : ℕ) = 1 then B else if (i : ℕ) = 2 then 2 * B else 0

@[simp] theorem gRowExp_zero (A B : ℤ_[2]) : gRowExp A B (0 : Fin (sqRank h)) = A - 1 := by
  simp only [gRowExp, sqVal_zero]
  norm_num

@[simp] theorem gRowExp_one (A B : ℤ_[2]) : gRowExp A B (1 : Fin (sqRank h)) = B := by
  simp only [gRowExp, sqVal_one]
  norm_num

@[simp] theorem gRowExp_two (A B : ℤ_[2]) : gRowExp A B (2 : Fin (sqRank h)) = 2 * B := by
  simp only [gRowExp, sqVal_two]
  norm_num

@[simp] theorem gRowExp_handleU (A B : ℤ_[2]) (j : Fin h) :
    gRowExp A B (sqHandleIdxU j) = 0 := by
  simp only [gRowExp, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem gRowExp_handleV (A B : ℤ_[2]) (j : Fin h) :
    gRowExp A B (sqHandleIdxV j) = 0 := by
  simp only [gRowExp, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The row-move ansatz**: slot `i` is `gen_i * w^{e_i} * c_i`, with `w` the chi-trivial
pivot, `e = gRowExp A B` the exponent row, and one correction word `c i` per slot. -/
noncomputable def gRowMark (h : ℕ) (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  fun i => sqGen h i * zpowZtwo (isProP_DSq h) (sqPivot h) (gRowExp A B i) * c i

theorem gRowMark_apply (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type))
    (i : Fin (sqRank h)) :
    gRowMark h A B c i
      = sqGen h i * zpowZtwo (isProP_DSq h) (sqPivot h) (gRowExp A B i) * c i := rfl

theorem gRowMark_zero (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) :
    gRowMark h A B c 0
      = dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1) * c 0 := by
  rw [gRowMark_apply, gRowExp_zero]
  rfl

theorem gRowMark_one (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) :
    gRowMark h A B c 1
      = dsqX0 h * zpowZtwo (isProP_DSq h) (sqPivot h) B * c 1 := by
  rw [gRowMark_apply, gRowExp_one]
  rfl

theorem gRowMark_two (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) :
    gRowMark h A B c 2
      = dsqX1 h * zpowZtwo (isProP_DSq h) (sqPivot h) (2 * B) * c 2 := by
  rw [gRowMark_apply, gRowExp_two]
  rfl

theorem gRowMark_handleU (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) (j : Fin h) :
    gRowMark h A B c (sqHandleIdxU j) = sqGen h (sqHandleIdxU j) * c (sqHandleIdxU j) := by
  rw [gRowMark_apply, gRowExp_handleU, zpowZtwo_zero_exp, mul_one]

theorem gRowMark_handleV (A B : ℤ_[2]) (c : Fin (sqRank h) → (DSq h : Type)) (j : Fin h) :
    gRowMark h A B c (sqHandleIdxV j) = sqGen h (sqHandleIdxV j) * c (sqHandleIdxV j) := by
  rw [gRowMark_apply, gRowExp_handleV, zpowZtwo_zero_exp, mul_one]

/-- At the base point with bare corrections the ansatz is the standard frame. -/
theorem gRowMark_id : gRowMark h 1 0 (fun _ => 1) = sqGen h := by
  funext i
  rw [gRowMark_apply, mul_one]
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [gRowExp_zero, sub_self, zpowZtwo_zero_exp, mul_one]
  · rw [gRowExp_one, zpowZtwo_zero_exp, mul_one]
  · rw [gRowExp_two, mul_zero, zpowZtwo_zero_exp, mul_one]
  · rw [gRowExp_handleU, zpowZtwo_zero_exp, mul_one]
  · rw [gRowExp_handleV, zpowZtwo_zero_exp, mul_one]

end Frame

/-! ## §3 The word reduction: the rows are free, one identity is owed -/

section OfWord

variable {h : ℕ}

/-- **The row-move word reduction.**  Corrections with trivial `lambda`-rows and (at the two
core slots) trivial `nu_sq`-rows, a spanning frame, and the single word identity
`sqRelWord (gRowMark h A B c) = 1` produce the row pair at `(A, B)`.  The automorphism is the
frame form `sqAutOfMark`: no inverse words and no composition identities are owed. -/
theorem gRow_pair_of_word {A B : ℤ_[2]} {c : Fin (sqRank h) → (DSq h : Type)}
    (hlam : ∀ i, nuLam h (c i) = 1) (hnu0 : nuSq h (c 0) = 1) (hnu1 : nuSq h (c 1) = 1)
    (hindep : SqModTwoIndep (gRowMark h A B c))
    (hrel : sqRelWord (gRowMark h A B c) = 1) : GRowPair h A B := by
  have hsurj := sqLiftHom_surjective_of_modTwoIndep hrel hindep
  refine ⟨sqAutOfMark hrel hsurj, fun x => ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel hsurj)) = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel hsurj (sqGen h i)) = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, gRowMark_apply]
        refine Multiplicative.toAdd.injective ?_
        rw [map_mul, toAdd_mul, map_mul, toAdd_mul,
          toAdd_map_zpowZtwo (isProP_DSq h) (nuLam h) (sqPivot h) _, toAdd_nuLam_sqPivot,
          hlam i, toAdd_one]
        ring
    exact DFunLike.congr_fun hext x
  · show toAdd (nuSq h (sqAutOfMark hrel hsurj (sqGen h 0))) = A
    rw [sqAutOfMark_gen, gRowMark_zero, map_mul, toAdd_mul, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DSq h) (nuSq h) (sqPivot h) _, nuSq_sqPivot, nuSq_sigma, hnu0]
    simp only [toAdd_ofAdd, toAdd_one]
    ring
  · show toAdd (nuSq h (sqAutOfMark hrel hsurj (sqGen h 1))) = B
    rw [sqAutOfMark_gen, gRowMark_one, map_mul, toAdd_mul, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DSq h) (nuSq h) (sqPivot h) _, nuSq_sqPivot, nuSq_x0, hnu1]
    simp only [toAdd_ofAdd, toAdd_one]
    ring

end OfWord

/-! ## §4 Generation on the unit locus

If every slot of the frame lay in one index-two open normal subgroup `M`, the handle slots
and the `x1`-slot would strip (their pivot powers are trivial or even), and the two twisted
core slots would combine into `sigma * w^{A-1-B} * x0⁻¹` with `A - 1 - B` even, which is
exactly the unit condition.  Peeling the even power by normality puts `sigma * x0⁻¹` in `M`,
with it the pivot itself, and with the pivot both twisted slots strip completely.  Then `M`
swallows every generator, which no index-two open normal subgroup does. -/

section Generation

variable {h : ℕ}

/-- The intersection of the index-two open normal subgroups of `D_sq h`: the carrier in which
corrections cost nothing against generation. -/
noncomputable def gRowFrat (h : ℕ) : Subgroup (DSq h : Type) :=
  ⨅ M : OpenNormalSubgroup (DSq h : Type), ⨅ _ : M.toSubgroup.index = 2, M.toSubgroup

theorem gRow_mem_frat_iff {x : (DSq h : Type)} :
    x ∈ gRowFrat h ↔ ∀ M : OpenNormalSubgroup (DSq h : Type),
      M.toSubgroup.index = 2 → x ∈ M.toSubgroup := by
  simp [gRowFrat, Subgroup.mem_iInf]

/-- The second level of the two-central tower feeds the carrier: an index-two quotient kills
squares and commutators. -/
theorem gRow_lambdaTwo_le_frat : twoCentralSeries (DSq h : Type) 2 ≤ gRowFrat h := by
  intro x hx
  rw [gRow_mem_frat_iff]
  intro M hM
  have hle : twoCentralSeries (DSq h : Type) 2 ≤ M.toSubgroup := by
    rw [twoCentralSeries_succ (G := (DSq h : Type)) (k := 1) le_rfl]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) M.toOpenSubgroup.isClosed
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, -, rfl⟩
      exact sq_mem_of_index_two hM v
    · rw [Subgroup.commutator_le]
      intro g _ k _
      rw [commutatorElement_def]
      have hc := commP_mem_of_index_two (M := M.toSubgroup) hM g⁻¹ k⁻¹
      rwa [show commP g⁻¹ k⁻¹ = g * k * g⁻¹ * k⁻¹ by rw [commP]; group] at hc
  exact hle hx

private theorem gRow_strip {M : Subgroup (DSq h : Type)} {x y : (DSq h : Type)}
    (hxy : x * y ∈ M) (hy : y ∈ M) : x ∈ M := by
  have hp := M.mul_mem hxy (M.inv_mem hy)
  rwa [mul_inv_cancel_right] at hp

/-- **The unit locus is the even locus of `A - 1 - B`**: the parity bookkeeping both the
generation argument and the class-three rung consume. -/
theorem gRow_even_of_unit {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B)) :
    (2 : ℤ_[2]) ∣ A - 1 - B := by
  have hoddAB : IsUnit (A - B) := by
    refine isUnit_iff_not_two_dvd.mpr fun hdvd => ?_
    obtain ⟨q, hq⟩ := hdvd
    obtain ⟨r, hr⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
    exact (isUnit_iff_not_two_dvd.mp hAB) ⟨q - r * B, by linear_combination hq - B * hr⟩
  obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit hoddAB isUnit_one
  exact ⟨q, by linear_combination hq⟩

/-- **The ansatz spans `H_1` on the unit locus**, for any Frattini corrections. -/
theorem gRow_modTwoIndep {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B))
    {c : Fin (sqRank h) → (DSq h : Type)} (hc : ∀ i, c i ∈ gRowFrat h) :
    SqModTwoIndep (gRowMark h A B c) := by
  intro M hM
  by_contra hcon
  have hmem : ∀ i, gRowMark h A B c i ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hcon ⟨i, hni⟩
  have hcM : ∀ i, c i ∈ M.toSubgroup := fun i => (gRow_mem_frat_iff.mp (hc i)) M hM
  have heven : (2 : ℤ_[2]) ∣ A - 1 - B := gRow_even_of_unit hAB
  -- the `x1`-slot and the handle slots strip
  have hx1 : dsqX1 h ∈ M.toSubgroup := by
    have h2 := hmem 2
    rw [gRowMark_two] at h2
    exact gRow_strip (gRow_strip h2 (hcM 2))
      (zpowZtwo_mem_of_even (isProP_DSq h) hM (sqPivot h) ⟨B, rfl⟩)
  have hU : ∀ j : Fin h, sqGen h (sqHandleIdxU j) ∈ M.toSubgroup := by
    intro j
    have hj := hmem (sqHandleIdxU j)
    rw [gRowMark_handleU] at hj
    exact gRow_strip hj (hcM _)
  have hV : ∀ j : Fin h, sqGen h (sqHandleIdxV j) ∈ M.toSubgroup := by
    intro j
    have hj := hmem (sqHandleIdxV j)
    rw [gRowMark_handleV] at hj
    exact gRow_strip hj (hcM _)
  -- the two twisted slots, stripped of their corrections
  have hP : dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1) ∈ M.toSubgroup := by
    have h0 := hmem 0
    rw [gRowMark_zero] at h0
    exact gRow_strip h0 (hcM 0)
  have hQ : dsqX0 h * zpowZtwo (isProP_DSq h) (sqPivot h) B ∈ M.toSubgroup := by
    have h1 := hmem 1
    rw [gRowMark_one] at h1
    exact gRow_strip h1 (hcM 1)
  -- combine: `sigma * w^{A-1-B} * x0⁻¹` is in `M`
  have hsplit : zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1)
      = zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B)
        * zpowZtwo (isProP_DSq h) (sqPivot h) B := by
    rw [← zpowZtwo_add]
    congr 1
    ring
  have hR : dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B) * (dsqX0 h)⁻¹
      ∈ M.toSubgroup := by
    have hcomb := M.toSubgroup.mul_mem hP (M.toSubgroup.inv_mem hQ)
    have heq : dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1)
        * (dsqX0 h * zpowZtwo (isProP_DSq h) (sqPivot h) B)⁻¹
        = dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B) * (dsqX0 h)⁻¹ := by
      rw [hsplit]
      group
    rwa [heq] at hcomb
  -- the even pivot power peels off by normality, leaving `sigma * x0⁻¹`
  have hwe : zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B) ∈ M.toSubgroup :=
    zpowZtwo_mem_of_even (isProP_DSq h) hM (sqPivot h) heven
  have hconj : dsqX0 h * (zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B))⁻¹ * (dsqX0 h)⁻¹
      ∈ M.toSubgroup :=
    M.isNormal'.conj_mem _ (M.toSubgroup.inv_mem hwe) (dsqX0 h)
  have hT : dsqSigma h * (dsqX0 h)⁻¹ ∈ M.toSubgroup := by
    have hmul := M.toSubgroup.mul_mem hR hconj
    have heq : dsqSigma h * zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B) * (dsqX0 h)⁻¹ *
        (dsqX0 h * (zpowZtwo (isProP_DSq h) (sqPivot h) (A - 1 - B))⁻¹ * (dsqX0 h)⁻¹)
        = dsqSigma h * (dsqX0 h)⁻¹ := by
      group
    rwa [heq] at hmul
  -- the pivot itself is in `M`
  have hweven : (2 : ℤ_[2]) ∣ 1 - sqPivotExp := by
    obtain ⟨r, hr⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
    exact ⟨-r, by linear_combination -hr⟩
  have hzz : zpowZtwo (isProP_DSq h) (dsqX0 h) (1 - sqPivotExp)
      = dsqX0 h * (zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← zpowZtwo_add,
      show 1 - sqPivotExp + sqPivotExp = (1 : ℤ_[2]) by ring, zpowZtwo_one_exp]
  have hw : sqPivot h ∈ M.toSubgroup := by
    have hcomb := M.toSubgroup.mul_mem hT
      (zpowZtwo_mem_of_even (isProP_DSq h) hM (dsqX0 h) hweven)
    have heq : dsqSigma h * (dsqX0 h)⁻¹ * zpowZtwo (isProP_DSq h) (dsqX0 h) (1 - sqPivotExp)
        = sqPivot h := by
      rw [hzz, sqPivot, sqMixPivotElem]
      group
    rwa [heq] at hcomb
  -- both twisted slots strip completely, and `M` swallows every generator
  have hs : dsqSigma h ∈ M.toSubgroup :=
    gRow_strip hP (zpowZtwo_mem_of_mem (isProP_DSq h) hM hw (A - 1))
  have hx : dsqX0 h ∈ M.toSubgroup :=
    gRow_strip hQ (zpowZtwo_mem_of_mem (isProP_DSq h) hM hw B)
  obtain ⟨i, hi⟩ := exists_sqGen_notMem M hM
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact hi hs
  · exact hi hx
  · exact hi hx1
  · exact hi (hU j)
  · exact hi (hV j)

end Generation

/-! ## §5 The per-class solution sets -/

section Sets

variable {h : ℕ}

/-- The correction carrier: `lambda_2`, with exactly trivial `lambda`- and `nu_sq`-rows.  The
tower membership feeds generation (`gRow_lambdaTwo_le_frat`), the two kernels feed the rows. -/
noncomputable def gRowCorr (h : ℕ) : Subgroup (DSq h : Type) :=
  twoCentralSeries (DSq h : Type) 2 ⊓ (nuLam h).toMonoidHom.ker ⊓ (nuSq h).toMonoidHom.ker

theorem gRow_mem_corr {x : (DSq h : Type)} :
    x ∈ gRowCorr h ↔
      (x ∈ twoCentralSeries (DSq h : Type) 2 ∧ nuLam h x = 1) ∧ nuSq h x = 1 :=
  Iff.rfl

variable (h) in
/-- **The class-`k` solution set of the row-move ansatz at `(A, B)`**: correction tuples in
the carrier whose frame kills the relator to class `k` of the two-central tower.  Only the
last clause depends on `k`. -/
def gRowSet (A B : ℤ_[2]) (k : ℕ) : Set (Fin (sqRank h) → (DSq h : Type)) :=
  {c | (∀ i, c i ∈ gRowCorr h) ∧
    sqRelWord (gRowMark h A B c) ∈ twoCentralSeries (DSq h : Type) k}

theorem gRowSet_antitone {A B : ℤ_[2]} {k k' : ℕ} (hkk : k' ≤ k) :
    gRowSet h A B k ⊆ gRowSet h A B k' :=
  fun _ hc => ⟨hc.1, twoCentralSeries_antitone (G := (DSq h : Type)) hkk hc.2⟩

/-- The relator value of the ansatz varies continuously in the corrections. -/
theorem gRow_continuous (A B : ℤ_[2]) :
    Continuous fun c : Fin (sqRank h) → (DSq h : Type) => sqRelWord (gRowMark h A B c) := by
  have hW : Continuous fun c : Fin (sqRank h) → (DSq h : Type) =>
      sqWord (gRowMark h A B c 0) (gRowMark h A B c 1) (gRowMark h A B c 2) := by
    simp only [sqWord, conjP, commP, gRowMark_apply]
    fun_prop
  have hH : Continuous fun c : Fin (sqRank h) → (DSq h : Type) =>
      handleWord (fun j => gRowMark h A B c (sqHandleIdxU j))
        (fun j => gRowMark h A B c (sqHandleIdxV j)) := by
    simp only [handleWord, commP, gRowMark_apply]
    refine continuous_list_prod _ fun j _ => ?_
    fun_prop
  have hgoal : (fun c : Fin (sqRank h) → (DSq h : Type) => sqRelWord (gRowMark h A B c))
      = fun c => sqWord (gRowMark h A B c 0) (gRowMark h A B c 1) (gRowMark h A B c 2)
        * handleWord (fun j => gRowMark h A B c (sqHandleIdxU j))
            (fun j => gRowMark h A B c (sqHandleIdxV j)) := rfl
  rw [hgoal]
  exact hW.mul hH

theorem gRow_isClosed_corr :
    IsClosed ((gRowCorr h : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
  have h1 : IsClosed ((twoCentralSeries (DSq h : Type) 2 : Subgroup (DSq h : Type)) :
      Set (DSq h : Type)) := isClosed_twoCentralSeries _ 2
  have h2 : IsClosed {x : (DSq h : Type) | nuLam h x = 1} :=
    isClosed_eq (nuLam h).continuous_toFun continuous_const
  have h3 : IsClosed {x : (DSq h : Type) | nuSq h x = 1} :=
    isClosed_eq (nuSq h).continuous_toFun continuous_const
  have hset : ((gRowCorr h : Subgroup (DSq h : Type)) : Set (DSq h : Type))
      = (((twoCentralSeries (DSq h : Type) 2 : Subgroup (DSq h : Type)) :
          Set (DSq h : Type)) ∩ {x | nuLam h x = 1}) ∩ {x | nuSq h x = 1} := rfl
  rw [hset]
  exact (h1.inter h2).inter h3

/-- **The class-`k` solution set is closed** in the compact correction space. -/
theorem gRow_isClosed_set (A B : ℤ_[2]) (k : ℕ) : IsClosed (gRowSet h A B k) := by
  have h1 : IsClosed {c : Fin (sqRank h) → (DSq h : Type) | ∀ i, c i ∈ gRowCorr h} := by
    have hset : {c : Fin (sqRank h) → (DSq h : Type) | ∀ i, c i ∈ gRowCorr h}
        = ⋂ i, (fun c : Fin (sqRank h) → (DSq h : Type) => c i) ⁻¹'
            ((gRowCorr h : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
      ext c
      simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun i => (gRow_isClosed_corr (h := h)).preimage (continuous_apply i)
  have h2 : IsClosed {c : Fin (sqRank h) → (DSq h : Type) |
      sqRelWord (gRowMark h A B c) ∈ twoCentralSeries (DSq h : Type) k} :=
    (isClosed_twoCentralSeries (DSq h : Type) k).preimage (gRow_continuous A B)
  exact h1.inter h2

end Sets

/-! ## §5b The class-two commutator calculus

The generic identities of a group in which every `commP`-value is central of order two: the
exact laws of the class-three quotient.  They are stated with explicit centrality and
involution hypotheses and instantiated at `Q_3 = D_sq h / lambda_3` in section 6, where both
hypotheses are theorems.  All private: this is proof infrastructure. -/

section Class2Calculus

variable {G : Type*} [Group G]

private theorem gRow_cswap (a b : G) : b * a = a * b * commP b a := by
  rw [commP]
  group

private theorem gRow_cconj (a s : G) : conjP a s = a * commP a s := by
  rw [conjP, commP]
  group

private theorem gRow_cP_comm_inv (a b : G) : (commP a b)⁻¹ = commP b a := by
  rw [commP, commP]
  group

private theorem gRow_cmul_left (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (a b c : G) : commP (a * b) c = commP a c * commP b c := by
  have hexact : commP (a * b) c = b⁻¹ * (commP a c * b) * commP b c := by
    rw [commP, commP, commP]
    group
  rw [hexact, hcen a c b, inv_mul_cancel_left]

private theorem gRow_cmul_right (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (a b c : G) : commP a (b * c) = commP a c * commP a b := by
  have hexact : commP a (b * c) = commP a c * (c⁻¹ * (commP a b * c)) := by
    rw [commP, commP, commP]
    group
  rw [hexact, hcen a b c, inv_mul_cancel_left]

private theorem gRow_cinv_eq (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a b : G) :
    (commP a b)⁻¹ = commP a b := by
  have h := hc2 a b
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_left h

private theorem gRow_ccentral_right {z : G} (hz : ∀ w, z * w = w * z) (a : G) :
    commP a z = 1 := by
  rw [commP, mul_assoc, ← hz a]
  group

private theorem gRow_csq_right (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a b : G) : commP a (b ^ 2) = 1 := by
  rw [pow_two, gRow_cmul_right hcen a b b, ← pow_two, hc2]

private theorem gRow_csq_left (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a b : G) : commP (b ^ 2) a = 1 := by
  rw [pow_two, gRow_cmul_left hcen b b a, ← pow_two, hc2]

private theorem gRow_central_of_sq (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (b w : G) : b ^ 2 * w = w * b ^ 2 := by
  have h := gRow_cswap w (b ^ 2)
  rw [gRow_csq_left hcen hc2 w b, mul_one] at h
  exact h

private theorem gRow_cinv_right (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a b : G) : commP a b⁻¹ = commP a b := by
  have hexact : commP a b⁻¹ = b * (commP b a * b⁻¹) := by
    rw [commP, commP]
    group
  rw [hexact, hcen b a b⁻¹, mul_inv_cancel_left, ← gRow_cP_comm_inv, gRow_cinv_eq hc2]

private theorem gRow_cinv_left (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a b : G) : commP a⁻¹ b = commP a b := by
  have hexact : commP a⁻¹ b = a * (commP b a * a⁻¹) := by
    rw [commP, commP]
    group
  rw [hexact, hcen b a a⁻¹, mul_inv_cancel_left, ← gRow_cP_comm_inv, gRow_cinv_eq hc2]

private theorem gRow_commP_conjP_self (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (a s : G) : commP a (conjP a s) = 1 := by
  have hself : commP a a = 1 := by
    rw [commP]
    group
  rw [gRow_cconj, gRow_cmul_right hcen a a (commP a s),
    gRow_ccentral_right (hcen a s) a, hself, one_mul]

private theorem gRow_conjP_inv (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (a s : G) :
    (conjP a s)⁻¹ = commP a s * a⁻¹ := by
  rw [gRow_cconj, mul_inv_rev, gRow_cinv_eq hc2]

private theorem gRow_sq_expand (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (x p : G) : (x * p) ^ 2 = x ^ 2 * p ^ 2 * commP p x := by
  have h := gRow_cswap x p
  rw [pow_two, pow_two, pow_two]
  calc x * p * (x * p) = x * (p * x) * p := by group
    _ = x * (x * p * commP p x) * p := by rw [h]
    _ = x * x * p * (commP p x * p) := by group
    _ = x * x * p * (p * commP p x) := by rw [hcen p x p]
    _ = x * x * (p * p) * commP p x := by group

private theorem gRow_pow_four (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) {p : G} (hp4 : p ^ 4 = 1) (x : G) :
    (x * p) ^ 4 = x ^ 4 := by
  have h2 := gRow_sq_expand hcen x p
  have hk : ∀ w, p ^ 2 * commP p x * w = w * (p ^ 2 * commP p x) := by
    intro w
    rw [mul_assoc, hcen p x w, ← mul_assoc, gRow_central_of_sq hcen hc2 p w, mul_assoc]
  calc (x * p) ^ 4 = ((x * p) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    _ = (x ^ 2 * (p ^ 2 * commP p x)) ^ 2 := by rw [h2, mul_assoc]
    _ = (x ^ 2) ^ 2 * (p ^ 2 * commP p x) ^ 2 := Commute.mul_pow ((hk (x ^ 2)).symm) 2
    _ = x ^ 4 * (p ^ 2 * commP p x) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    _ = x ^ 4 := by
        have hsplit : (p ^ 2 * commP p x) ^ 2 = (p ^ 2) ^ 2 * commP p x ^ 2 :=
          Commute.mul_pow ((hcen p x (p ^ 2)).symm) 2
        rw [hsplit, hc2, mul_one, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, hp4, mul_one]

/-- **The base normal form**: in the class-two calculus, `sqWord s x y` is
`[x,s] * x^-4 * y^2`. -/
private theorem gRow_sqWord_base (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (s x y : G) :
    sqWord s x y = commP x s * ((x ^ 4)⁻¹ * y ^ 2) := by
  rw [sqWord, gRow_conjP_inv hc2 x s, gRow_commP_conjP_self hcen y s, mul_one]
  group

/-- **The twisted normal form**: dressing the three letters by `p * z` (central `z`),
`p`, `p^2` with `p^4 = 1` costs exactly the two commutators `[x,p]` and `[p,s]`. -/
private theorem gRow_sqWord_twist (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) {p z : G} (hz : ∀ w, z * w = w * z)
    (hp4 : p ^ 4 = 1) (s x y : G) :
    sqWord (s * (p * z)) (x * p) (y * p ^ 2)
      = commP x p * (commP p s * (commP x s * ((x ^ 4)⁻¹ * y ^ 2))) := by
  have hpp : commP p p = 1 := by
    rw [commP]
    group
  have hb : commP (x * p) (s * (p * z)) = commP x p * (commP x s * commP p s) := by
    rw [gRow_cmul_right hcen (x * p) s (p * z), gRow_cmul_right hcen (x * p) p z,
      gRow_ccentral_right hz (x * p), one_mul, gRow_cmul_left hcen x p p, hpp, mul_one,
      gRow_cmul_left hcen x p s]
  have hd : (y * p ^ 2) ^ 2 = y ^ 2 := by
    rw [gRow_sq_expand hcen y (p ^ 2), gRow_csq_left hcen hc2 y p, mul_one, ← pow_mul,
      show (2 * 2 : ℕ) = 4 from rfl, hp4, mul_one]
  have hfour : (x * p)⁻¹ * ((x * p) ^ 3)⁻¹ = (x ^ 4)⁻¹ := by
    have hgen : ∀ a : G, a⁻¹ * (a ^ 3)⁻¹ = (a ^ 4)⁻¹ := fun a => by group
    rw [hgen (x * p), gRow_pow_four hcen hc2 hp4 x]
  rw [sqWord, gRow_commP_conjP_self hcen (y * p ^ 2) (s * (p * z)), mul_one,
    gRow_conjP_inv hc2 (x * p) (s * (p * z)), hb, hd,
    mul_assoc (commP x p * (commP x s * commP p s)) (x * p)⁻¹ ((x * p) ^ 3)⁻¹, hfour,
    hcen x s (commP p s)]
  group

/-- **The defect at an odd pivot power dies**: with `p = (s * (x * ex^2)⁻¹) * e^2` the two
defect commutators collapse onto `[x,s]^2 = 1`. -/
private theorem gRow_defect_odd (hcen : ∀ u v w : G, commP u v * w = w * commP u v)
    (hc2 : ∀ u v : G, commP u v ^ 2 = 1) (s x e ex : G) :
    commP x (s * (x * ex ^ 2)⁻¹ * e ^ 2) * commP (s * (x * ex ^ 2)⁻¹ * e ^ 2) s = 1 := by
  have hselfinv : commP x (x * ex ^ 2) = 1 := by
    have hself : commP x x = 1 := by
      rw [commP]
      group
    rw [gRow_cmul_right hcen x x (ex ^ 2), gRow_csq_right hcen hc2 x ex, one_mul, hself]
  have hX : commP x (s * (x * ex ^ 2)⁻¹ * e ^ 2) = commP x s := by
    rw [gRow_cmul_right hcen x (s * (x * ex ^ 2)⁻¹) (e ^ 2), gRow_csq_right hcen hc2 x e,
      one_mul, gRow_cmul_right hcen x s ((x * ex ^ 2)⁻¹),
      gRow_cinv_right hcen hc2 x (x * ex ^ 2), hselfinv, one_mul]
  have hS : commP (s * (x * ex ^ 2)⁻¹ * e ^ 2) s = commP x s := by
    have hss : commP s s = 1 := by
      rw [commP]
      group
    rw [gRow_cmul_left hcen (s * (x * ex ^ 2)⁻¹) (e ^ 2) s, gRow_csq_left hcen hc2 s e,
      mul_one, gRow_cmul_left hcen s ((x * ex ^ 2)⁻¹) s, hss, one_mul,
      gRow_cinv_left hcen hc2 (x * ex ^ 2) s, gRow_cmul_left hcen x (ex ^ 2) s,
      gRow_csq_left hcen hc2 s ex, mul_one]
  rw [hX, hS, ← pow_two, hc2]

end Class2Calculus

/-! ## §6 The compactness assembly, and the free rungs -/

section Assembly

variable {h : ℕ}

/-- **The compactness core**: nested nonempty closed solution sets in a compact space meet. -/
theorem gRow_iInter_nonempty {A B : ℤ_[2]} (hne : ∀ k, (gRowSet h A B k).Nonempty) :
    (⋂ k, gRowSet h A B k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', gRowSet_antitone (le_max_left k k'),
      gRowSet_antitone (le_max_right k k')⟩
  · exact hne
  · exact fun k => (gRow_isClosed_set A B k).isCompact
  · exact fun k => gRow_isClosed_set A B k

/-- ⭐⭐⭐ **THE PER-CLASS CRITERION.**  If the row-move ansatz at `(A, B)` on the unit locus
can be solved to every class of the two-central tower, one finite quotient at a time, then it
can be solved outright and the row pair follows.  Nestedness, closedness, compactness of the
correction space and the tower separation are the whole argument: there is no inverse-limit
step to lose.  Contrapositively, if a row move is false it fails at a finite class, in a
finite 2-group. -/
theorem gRow_pair_of_forall_class {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B))
    (H : ∀ k, (gRowSet h A B k).Nonempty) : GRowPair h A B := by
  obtain ⟨c, hcmem⟩ := gRow_iInter_nonempty H
  have hmem : ∀ k, c ∈ gRowSet h A B k := Set.mem_iInter.mp hcmem
  obtain ⟨hcorr, -⟩ := hmem 0
  have hall : sqRelWord (gRowMark h A B c) ∈ ⨅ k, twoCentralSeries (DSq h : Type) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2
  rw [lim_iInf_twoCentralSeries h, Subgroup.mem_bot] at hall
  exact gRow_pair_of_word (fun i => (gRow_mem_corr.mp (hcorr i)).1.2)
    (gRow_mem_corr.mp (hcorr 0)).2 (gRow_mem_corr.mp (hcorr 1)).2
    (gRow_modTwoIndep hAB fun i => gRow_lambdaTwo_le_frat (gRow_mem_corr.mp (hcorr i)).1.1)
    hall

/-- Every `commP`-value lies in `lambda_2`. -/
theorem gRow_commP_mem_two (z w : (DSq h : Type)) :
    commP z w ∈ twoCentralSeries (DSq h : Type) 2 := by
  have hrw : commP z w = ⁅z⁻¹, w⁻¹⁆ := by
    rw [commP, commutatorElement_def]
    group
  rw [hrw]
  exact commutator_mem_twoCentralSeries_succ _ (Subgroup.mem_top z⁻¹) w⁻¹

/-- A `commP`-value with a `lambda_2`-argument lies in `lambda_3`. -/
theorem gRow_commP_mem_three {z : (DSq h : Type)}
    (hz : z ∈ twoCentralSeries (DSq h : Type) 2) (g : (DSq h : Type)) :
    commP z g ∈ twoCentralSeries (DSq h : Type) 3 := by
  have hrw : commP z g = ⁅z⁻¹, g⁻¹⁆ := by
    rw [commP, commutatorElement_def]
    group
  rw [hrw]
  exact commutator_mem_twoCentralSeries_succ _
    ((twoCentralSeries (DSq h : Type) 2).inv_mem hz) g⁻¹

private theorem gRow_levelMk_eq_one {k : ℕ} {x : (DSq h : Type)}
    (hx : x ∈ twoCentralSeries (DSq h : Type) k) : levelMk (DSq h : Type) k x = 1 :=
  (QuotientGroup.eq_one_iff x).mpr hx

private theorem gRow_mem_of_levelMk {k : ℕ} {x : (DSq h : Type)}
    (hx : levelMk (DSq h : Type) k x = 1) : x ∈ twoCentralSeries (DSq h : Type) k :=
  (QuotientGroup.eq_one_iff x).mp hx

private theorem gRow_map_commP {G' H' : Type*} [Group G'] [Group H'] (f : G' →* H')
    (x y : G') : f (commP x y) = commP (f x) (f y) := by
  rw [commP, commP, map_mul, map_mul, map_mul, map_inv, map_inv]

/-- ⭐ **CLASS TWO IS FREE, FOR EVERY FRAME.**  The relator word on any marking is a product
of squares, commutators, and a conjugate of a commutator, so it lies in `lambda_2` outright.
In particular the bare ansatz solves every rung `k <= 2` at every `(A, B)`. -/
theorem gRow_relWord_mem_two (m : Fin (sqRank h) → (DSq h : Type)) :
    sqRelWord m ∈ twoCentralSeries (DSq h : Type) 2 := by
  have hsq2 : ∀ z : (DSq h : Type), z ^ 2 ∈ twoCentralSeries (DSq h : Type) 2 := fun z =>
    sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top z)
  have hcm : ∀ z w : (DSq h : Type), commP z w ∈ twoCentralSeries (DSq h : Type) 2 :=
    gRow_commP_mem_two
  have hword : sqWord (m 0) (m 1) (m 2)
      = ((m 1)⁻¹ ^ 2) ^ 2
        * ((m 1) ^ 3 * commP (m 1)⁻¹ (m 0) * ((m 1) ^ 3)⁻¹)
        * (m 2) ^ 2 * commP (m 2) (conjP (m 2) (m 0)) := by
    simp only [sqWord, conjP, commP]
    group
  have hhandle : handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
      ∈ twoCentralSeries (DSq h : Type) 2 := by
    rw [handleWord]
    refine list_prod_mem fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact hcm _ _
  rw [sqRelWord, hword]
  exact mul_mem (mul_mem (mul_mem (mul_mem (hsq2 _)
    ((twoCentralSeries_normal _ 2).conj_mem _ (hcm _ _) _)) (hsq2 _)) (hcm _ _)) hhandle

/-- The rungs `k <= 2` are nonempty with bare corrections, at every `(A, B)`. -/
theorem gRow_nonempty_of_le_two {A B : ℤ_[2]} {k : ℕ} (hk : k ≤ 2) :
    (gRowSet h A B k).Nonempty :=
  ⟨fun _ => 1, fun _ => one_mem _,
    twoCentralSeries_antitone (G := (DSq h : Type)) hk (gRow_relWord_mem_two _)⟩

/-- ⭐⭐ **CLASS THREE IS FREE ON THE UNIT LOCUS, WITH THE BARE FRAME.**  In the class-three
quotient every commutator is central of order two, so the twisted word collapses onto the
standard relator times the two defect commutators `[x0, w^B] * [w^B, sigma]`.  At an even `B`
the pivot power is a square, hence class-three central, and both die; at an odd `B` the pivot
power is the pivot times a square, both defects read `[x0, sigma]`, and their product is a
commutator square.  Either way the defect dies, so the bare ansatz solves rung 3 everywhere
on the unit locus: the committed class-two balance (`PivotCoreMoves` docstring, prose only,
lower-central metric) is subsumed one rung up, in Lean, in the two-central metric. -/
theorem gRow_relWord_bare_mem_three {A B : ℤ_[2]} (hAB : (2 : ℤ_[2]) ∣ A - 1 - B) :
    sqRelWord (gRowMark h A B fun _ => 1) ∈ twoCentralSeries (DSq h : Type) 3 := by
  obtain ⟨t, ht⟩ := hAB
  have hA1 : A - 1 = B + 2 * t := by linear_combination ht
  -- the class-three quotient is a class-two calculus
  have hcen : ∀ a b w : levelQuot (DSq h : Type) 3, commP a b * w = w * commP a b := by
    intro a b w
    obtain ⟨a', rfl⟩ := levelMk_surjective (DSq h : Type) 3 a
    obtain ⟨b', rfl⟩ := levelMk_surjective (DSq h : Type) 3 b
    obtain ⟨w', rfl⟩ := levelMk_surjective (DSq h : Type) 3 w
    rw [← gRow_map_commP, ← map_mul, ← map_mul, gRow_cswap w' (commP a' b'), map_mul,
      gRow_levelMk_eq_one (gRow_commP_mem_three (gRow_commP_mem_two a' b') w'), mul_one]
  have hc2 : ∀ a b : levelQuot (DSq h : Type) 3, commP a b ^ 2 = 1 := by
    intro a b
    obtain ⟨a', rfl⟩ := levelMk_surjective (DSq h : Type) 3 a
    obtain ⟨b', rfl⟩ := levelMk_surjective (DSq h : Type) 3 b
    rw [← gRow_map_commP, ← map_pow]
    exact gRow_levelMk_eq_one
      (sq_mem_twoCentralSeries_succ _ (gRow_commP_mem_two a' b'))
  have hp4 : levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) (sqPivot h) B) ^ 4 = 1 := by
    rw [← map_pow]
    refine gRow_levelMk_eq_one ?_
    have h1 : zpowZtwo (isProP_DSq h) (sqPivot h) B ^ 2
        ∈ twoCentralSeries (DSq h : Type) 2 :=
      sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top _)
    have h2 := sq_mem_twoCentralSeries_succ _ h1
    rwa [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl] at h2
  -- the image of the standard relator
  have hrel0 : sqWord (levelMk (DSq h : Type) 3 (dsqSigma h))
      (levelMk (DSq h : Type) 3 (dsqX0 h)) (levelMk (DSq h : Type) 3 (dsqX1 h))
      * handleWord (fun j => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU j)))
        (fun j => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxV j))) = 1 := by
    have h1 : levelMk (DSq h : Type) 3 (sqRelWord (sqGen h)) = 1 := by
      rw [dsq_relation h, map_one]
    rw [map_sqRelWord] at h1
    exact h1
  -- membership through the level projection
  refine gRow_mem_of_levelMk ?_
  rw [sqRelWord]
  simp only [gRowMark_zero, gRowMark_one, gRowMark_two, gRowMark_handleU, gRowMark_handleV,
    mul_one]
  rw [hA1, zpowZtwo_add]
  simp only [zpowZtwo_two_mul]
  rw [map_mul, map_sqWord, map_handleWord]
  simp only [map_mul, map_pow]
  rw [gRow_sqWord_twist hcen hc2
    (fun w => gRow_central_of_sq hcen hc2
      (levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) (sqPivot h) t)) w) hp4,
    ← gRow_sqWord_base hcen hc2 (levelMk (DSq h : Type) 3 (dsqSigma h))
      (levelMk (DSq h : Type) 3 (dsqX0 h)) (levelMk (DSq h : Type) 3 (dsqX1 h))]
  have hassoc : ∀ q1 q2 q3 q4 : levelQuot (DSq h : Type) 3,
      q1 * (q2 * q3) * q4 = q1 * q2 * (q3 * q4) := by
    intro q1 q2 q3 q4
    group
  rw [hassoc, hrel0, mul_one]
  -- the defect: `[x0, w^B] * [w^B, sigma]` dies by parity
  by_cases hB : (2 : ℤ_[2]) ∣ B
  · obtain ⟨u2, hu2⟩ := hB
    rw [hu2, zpowZtwo_two_mul, map_pow, gRow_csq_right hcen hc2, gRow_csq_left hcen hc2,
      one_mul]
  · obtain ⟨r, hr⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hB) isUnit_one
    obtain ⟨r0, hr0⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
    have hwsplit : zpowZtwo (isProP_DSq h) (sqPivot h) B
        = sqPivot h * zpowZtwo (isProP_DSq h) (sqPivot h) r ^ 2 := by
      rw [show B = 1 + 2 * r by linear_combination hr, zpowZtwo_add, zpowZtwo_one_exp,
        zpowZtwo_two_mul]
    have hpivsplit : sqPivot h = dsqSigma h *
        (dsqX0 h * zpowZtwo (isProP_DSq h) (dsqX0 h) r0 ^ 2)⁻¹ := by
      rw [sqPivot, sqMixPivotElem]
      congr 2
      rw [show sqPivotExp = 1 + 2 * r0 by linear_combination hr0, zpowZtwo_add,
        zpowZtwo_one_exp, zpowZtwo_two_mul]
    rw [hwsplit, hpivsplit]
    simp only [map_mul, map_inv, map_pow]
    exact gRow_defect_odd hcen hc2 _ _ _ _

/-- The rungs `k <= 3` are nonempty with bare corrections, on the unit locus. -/
theorem gRow_nonempty_of_le_three {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B)) {k : ℕ}
    (hk : k ≤ 3) : (gRowSet h A B k).Nonempty :=
  ⟨fun _ => 1, fun _ => one_mem _,
    twoCentralSeries_antitone (G := (DSq h : Type)) hk
      (gRow_relWord_bare_mem_three (gRow_even_of_unit hAB))⟩

/-- ⭐ **The residue, exactly**: on the unit locus the row pair follows from class-`k`
solvability at `k >= 4` alone.  Classes at most three are theorems, so the first class that
can obstruct a row move is class four: the same threshold the `M6` ladder starts at.

[W86-HOUSE, as of `f0de6ad5`: everything through the colon is exact and is what this theorem
says; the clause after it is stale.  `Instances/MpcBuild.lean`'s `mpcBld_nonempty_four` solves
the `M6` ladder's class four, so that ladder starts at class FIVE and this one starts at class
four.  The two are one rung apart, not level.]

[W88-HOUSE, as of `ad8c2b62`: this theorem is still exactly true and is still the route, but
both numbers above have moved by one.  Wave 87's `GradedRowResidue.gRsd_nonempty_four` pays
class four here on the whole unit locus, so THIS ladder now starts at class five and the
sharp form is `gRsd_pair_of_forall_class_five`; `MpcFive.mpcFv_nonempty_five` puts the `M6`
ladder at class SIX.  Five against six, still one rung apart.] -/
theorem gRow_pair_of_forall_class_four {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B))
    (H : ∀ k, 4 ≤ k → (gRowSet h A B k).Nonempty) : GRowPair h A B := by
  refine gRow_pair_of_forall_class hAB fun k => ?_
  by_cases hk : 4 ≤ k
  · exact H k hk
  · exact gRow_nonempty_of_le_three hAB (by omega)

end Assembly

/-! ## §7 The composition through the committed chain -/

section Composition

variable {h : ℕ}

/-- Per-class solvability on the unit locus yields every model move. -/
theorem gRow_modelMove_of_forall_class
    (H : ∀ A B : ℤ_[2], IsUnit (A - sqPivotExp * B) → ∀ k, (gRowSet h A B k).Nonempty)
    {a b : ℤ_[2]} (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b := by
  obtain ⟨u, hu⟩ := hd
  have hde : (a - sqPivotExp * b) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hunit : IsUnit (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - sqPivotExp * b)
      - sqPivotExp * (-(((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * b))) := by
    rw [show ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - sqPivotExp * b)
        - sqPivotExp * (-(((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * b)) = ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) by ring]
    exact ⟨u⁻¹, rfl⟩
  exact gRow_modelMove_of_pair hde rfl (gRow_pair_of_forall_class hunit (H _ _ hunit))

/-- The translation ray from its own per-class ladder. -/
theorem gRow_translate_of_forall_class {c : ℤ_[2]}
    (H : ∀ k, (gRowSet h (1 - sqPivotExp * c) (-c) k).Nonempty) :
    GClearModelTranslate h c := by
  refine gRow_translate_of_pair (gRow_pair_of_forall_class ?_ H)
  rw [show (1 - sqPivotExp * c) - sqPivotExp * (-c) = (1 : ℤ_[2]) by ring]
  exact isUnit_one

/-- The scaling ray from its own per-class ladder. -/
theorem gRow_scale_of_forall_class {d e : ℤ_[2]} (hde : d * e = 1)
    (H : ∀ k, (gRowSet h e 0 k).Nonempty) : GClearModelScale h d := by
  refine gRow_scale_of_pair hde (gRow_pair_of_forall_class ?_ H)
  rw [show e - sqPivotExp * 0 = e by ring]
  exact ⟨⟨e, d, by linear_combination hde, hde⟩, rfl⟩

/-- ⭐⭐⭐ **The odd route's last item over the per-class ladder alone**: class-`k` solvability
of the row-move word on the unit locus, at every `k`, discharges the oriented clearing at
every unit-pivot marking, through wave 84's `gClear_clearing_of_model`. -/
theorem gRow_clearing_of_forall_class
    (H : ∀ A B : ℤ_[2], IsUnit (A - sqPivotExp * B) → ∀ k, (gRowSet h A B k).Nonempty) :
    SqNuOrientedClearAtUnitPivot h :=
  gClear_clearing_of_model fun _ _ hd => gRow_modelMove_of_forall_class H hd

/-- The model moves over the class-`k >= 4` rungs alone. -/
theorem gRow_modelMove_of_forall_class_four
    (H : ∀ A B : ℤ_[2], IsUnit (A - sqPivotExp * B) →
      ∀ k, 4 ≤ k → (gRowSet h A B k).Nonempty)
    {a b : ℤ_[2]} (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b := by
  obtain ⟨u, hu⟩ := hd
  have hde : (a - sqPivotExp * b) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hunit : IsUnit (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - sqPivotExp * b)
      - sqPivotExp * (-(((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * b))) := by
    rw [show ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - sqPivotExp * b)
        - sqPivotExp * (-(((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * b)) = ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) by ring]
    exact ⟨u⁻¹, rfl⟩
  exact gRow_modelMove_of_pair hde rfl (gRow_pair_of_forall_class_four hunit (H _ _ hunit))

/-- The translation ray over its class-`k >= 4` rungs alone. -/
theorem gRow_translate_of_forall_class_four {c : ℤ_[2]}
    (H : ∀ k, 4 ≤ k → (gRowSet h (1 - sqPivotExp * c) (-c) k).Nonempty) :
    GClearModelTranslate h c := by
  refine gRow_translate_of_pair (gRow_pair_of_forall_class_four ?_ H)
  rw [show (1 - sqPivotExp * c) - sqPivotExp * (-c) = (1 : ℤ_[2]) by ring]
  exact isUnit_one

/-- The scaling ray over its class-`k >= 4` rungs alone. -/
theorem gRow_scale_of_forall_class_four {d e : ℤ_[2]} (hde : d * e = 1)
    (H : ∀ k, 4 ≤ k → (gRowSet h e 0 k).Nonempty) : GClearModelScale h d := by
  refine gRow_scale_of_pair hde (gRow_pair_of_forall_class_four ?_ H)
  rw [show e - sqPivotExp * 0 = e by ring]
  exact ⟨⟨e, d, by linear_combination hde, hde⟩, rfl⟩

/-- ⭐⭐⭐ **The sharpest conditional form this lane leaves**: the odd route's last item over
the class-`k >= 4` rungs of the row-move word on the unit locus, and nothing else.  Classes
at most three are theorems. -/
theorem gRow_clearing_of_forall_class_four
    (H : ∀ A B : ℤ_[2], IsUnit (A - sqPivotExp * B) →
      ∀ k, 4 ≤ k → (gRowSet h A B k).Nonempty) :
    SqNuOrientedClearAtUnitPivot h :=
  gClear_clearing_of_model fun _ _ hd => gRow_modelMove_of_forall_class_four H hd

section DegreeZero

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The row pairs are theorems at `h = 0`**, on the whole unit locus, through the converse
bridge and the committed degree-one model moves (axioms B8 + B3c enter here and only here).
So the pair target is realized in full at the settled handle count: the coordinates this lane
chose do not overshoot the committed residual. -/
theorem gRow_pair_zero {A B : ℤ_[2]} (hAB : IsUnit (A - sqPivotExp * B)) : GRowPair 0 A B := by
  obtain ⟨u, hu⟩ := hAB
  set d : ℤ_[2] := ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hdd
  have hde : d * (A - sqPivotExp * B) = 1 := by
    rw [hdd, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hd1 : (A - sqPivotExp * B) * d = 1 := by
    rw [mul_comm]
    exact hde
  have H0 : GClearModelMove 0 (d + sqPivotExp * (-(B * d))) (-(B * d)) :=
    gClear_modelMove_zero (by
      rw [show d + sqPivotExp * (-(B * d)) - sqPivotExp * (-(B * d)) = d by ring]
      exact ⟨u⁻¹, rfl⟩)
  have hp := gRow_pair_of_modelMove (e := A - sqPivotExp * B) hde (by ring) H0
  have e1 : (A - sqPivotExp * B) * (1 - sqPivotExp * (-(B * d))) = A := by
    linear_combination sqPivotExp * B * hd1
  have e2 : -((A - sqPivotExp * B) * (-(B * d))) = B := by
    linear_combination B * hd1
  rw [e1, e2] at hp
  exact hp

end DegreeZero

end Composition

/-! ## §7b The seam: the ladder carries the odd-degree classification -/

section Seam

open ContCoh LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The seam over the ladder: per-class solvability implies `SqMarkedForwardSupply B h` at
every odd-degree `K`. -/
theorem gRow_supply_of_forall_class (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : ∀ A B' : ℤ_[2], IsUnit (A - sqPivotExp * B') → ∀ k, (gRowSet h A B' k).Nonempty) :
    SqMarkedForwardSupply B h :=
  gClear_supply_of_model B FF hdeg fun _ _ hd => gRow_modelMove_of_forall_class H hd

/-- The general theorem over the ladder: at every odd-degree `K`, what remains beyond the
per-class solvability is exactly the two record blocks. -/
theorem gRow_candidateEquiv_of_forall_class (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : ∀ A B' : ℤ_[2], IsUnit (A - sqPivotExp * B') → ∀ k, (gRowSet h A B' k).Nonempty) :
    ∃ G : GenAsmBranch K B, G.pres = .L h ∧
      ∀ F : GenAsmFieldInputs K B FF G.degree, GenAsmRowResidual G F.T →
        Nonempty (ContinuousMulEquiv
          ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  gClear_candidateEquiv_of_model B hdeg fun _ _ hd => gRow_modelMove_of_forall_class H hd

end Seam

/-! ## §8 Stress pins -/

section StressPins

/-- The ansatz at the base point with bare corrections is the standard frame, and its word
identity is the defining relation: the family is non-vacuous. -/
example (h : ℕ) : sqRelWord (gRowMark h 1 0 (fun _ => 1)) = 1 := by
  rw [gRowMark_id]
  exact dsq_relation h

/-- Full circle: the word route at the base point reproves the free pair `(1, 0)`. -/
example (h : ℕ) : GRowPair h 1 0 := by
  refine gRow_pair_of_word (c := fun _ => 1) (fun _ => map_one _) (map_one _) (map_one _)
    (gRow_modTwoIndep (by rw [mul_zero, sub_zero]; exact isUnit_one) fun _ => one_mem _) ?_
  rw [gRowMark_id]
  exact dsq_relation h

/-- The base point of each ray is free. -/
example (h : ℕ) : GRowTranslate h 0 ∧ GRowScale h 1 := by
  constructor
  · rw [GRowTranslate, mul_zero, sub_zero, neg_zero]
    exact gRow_pair_one_zero h
  · exact gRow_pair_one_zero h

/-- The free rungs: class 2 everywhere, class 3 on the unit locus. -/
example (h : ℕ) (A B : ℤ_[2]) : (gRowSet h A B 2).Nonempty :=
  gRow_nonempty_of_le_two le_rfl

/-- The class-three rung at the two rays. -/
example (h : ℕ) (c : ℤ_[2]) : (gRowSet h (1 - sqPivotExp * c) (-c) 3).Nonempty :=
  gRow_nonempty_of_le_three (by
    rw [show (1 - sqPivotExp * c) - sqPivotExp * (-c) = (1 : ℤ_[2]) by ring]
    exact isUnit_one) le_rfl

/-- The pair route lands on the committed model-move statement through the committed ray
decomposition. -/
example (h : ℕ) (htr : ∀ c : ℤ_[2], GRowTranslate h c)
    (hsc : ∀ e : ℤ_[2], IsUnit e → GRowScale h e) {a b : ℤ_[2]}
    (hd : IsUnit (a - sqPivotExp * b)) : GClearModelMove h a b :=
  gRow_modelMove_of_ray_pairs htr hsc hd

end StressPins

/-! ## §9 Axiom pins

Verified at generation time (`scripts/mirror.sh gen`):

* `GRowPair`, `gRow_pair_one_zero`, `gRow_modelMove_of_pair`, `GRowTranslate`, `GRowScale`,
  `gRow_translate_of_pair`, `gRow_scale_of_pair`, `gRow_modelMove_of_ray_pairs`, `gRowExp`,
  `gRowMark`, `gRowMark_id`, `gRow_pair_of_word`, `gRowFrat`, `gRow_lambdaTwo_le_frat`,
  `gRow_modTwoIndep`, `gRowCorr`, `gRowSet`, `gRowSet_antitone`, `gRow_continuous`,
  `gRow_isClosed_set`, `gRow_iInter_nonempty`, `gRow_pair_of_forall_class`,
  `gRow_commP_mem_two`, `gRow_commP_mem_three`, `gRow_relWord_mem_two`,
  `gRow_nonempty_of_le_two`, `gRow_even_of_unit`, `gRow_relWord_bare_mem_three`,
  `gRow_nonempty_of_le_three`, `gRow_pair_of_forall_class_four`,
  `gRow_modelMove_of_forall_class`, `gRow_translate_of_forall_class`,
  `gRow_scale_of_forall_class`, `gRow_clearing_of_forall_class`,
  `gRow_modelMove_of_forall_class_four`, `gRow_translate_of_forall_class_four`,
  `gRow_scale_of_forall_class_four`, `gRow_clearing_of_forall_class_four` print **std-3**.
* `gRow_pair_of_modelMove` prints **std-3**; `gRow_pair_zero` prints std-3 +
  {`dyadicOrientation` (B3c), `peripheralCyclotomicAction` (B8)}, the committed price of the
  `h = 0` arithmetic affine family and nothing else.
* `gRow_supply_of_forall_class`, `gRow_candidateEquiv_of_forall_class` print std-3 +
  {`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`}.
-/

section AxiomPins

#print axioms GRowPair
#print axioms gRow_pair_one_zero
#print axioms gRow_modelMove_of_pair
#print axioms gRow_pair_of_modelMove
#print axioms gRow_pair_zero
#print axioms GRowTranslate
#print axioms GRowScale
#print axioms gRow_translate_of_pair
#print axioms gRow_scale_of_pair
#print axioms gRow_modelMove_of_ray_pairs
#print axioms gRowExp
#print axioms gRowMark
#print axioms gRowMark_id
#print axioms gRow_pair_of_word
#print axioms gRowFrat
#print axioms gRow_lambdaTwo_le_frat
#print axioms gRow_modTwoIndep
#print axioms gRowCorr
#print axioms gRowSet
#print axioms gRowSet_antitone
#print axioms gRow_continuous
#print axioms gRow_isClosed_set
#print axioms gRow_iInter_nonempty
#print axioms gRow_pair_of_forall_class
#print axioms gRow_commP_mem_two
#print axioms gRow_commP_mem_three
#print axioms gRow_relWord_mem_two
#print axioms gRow_nonempty_of_le_two
#print axioms gRow_even_of_unit
#print axioms gRow_relWord_bare_mem_three
#print axioms gRow_nonempty_of_le_three
#print axioms gRow_pair_of_forall_class_four
#print axioms gRow_modelMove_of_forall_class
#print axioms gRow_translate_of_forall_class
#print axioms gRow_scale_of_forall_class
#print axioms gRow_clearing_of_forall_class
#print axioms gRow_modelMove_of_forall_class_four
#print axioms gRow_translate_of_forall_class_four
#print axioms gRow_scale_of_forall_class_four
#print axioms gRow_clearing_of_forall_class_four
#print axioms gRow_supply_of_forall_class
#print axioms gRow_candidateEquiv_of_forall_class

end AxiomPins

end SqCore

end Dyadic

end GQ2
