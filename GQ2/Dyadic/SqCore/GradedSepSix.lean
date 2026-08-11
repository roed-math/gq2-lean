/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedSeven
import GQ2.Dyadic.SqCore.GradedFiveSepZero

/-!
# W65-SIX: the class-six sigma separation is NOT forced

W64-SEP0H proved that the class-**five** sigma separation forces `0 < h`, with no gauge
hypothesis, by showing that the class-five response to the `a0 = a1` dressing is a
polynomial-coefficient combination of the nine class-two-to-four rows of the **undressed** core
word: at `h = 0` the relator *is* that word, so a relator-killing marking sets all nine rows to
`0` and the response is even.  Wave 65 asked the same question one class up, and named an
induction for it: the class-six response reads the class-five rows, which SEP0H proves even at
`h = 0`, so the induction has a base.

## ⭐⭐⭐ Headline: NO.  The induction step is false, and an explicit witness refutes it

⭐⭐⭐ `sepSix_not_bit_even`.  There is a marking of the **handle-free** `D_sq 0` into the
class-six test group that kills the relator and whose `a0 = a1` dressing has an **odd**
class-six coordinate.  So the class-six analogue of `sepZero_bit_even` is false, and

> ⭐⭐⭐ `sepSix_not_pos_of_bit_odd`.  The class-six analogue of `sepZero_pos_of_bit_odd` is
> **false**: a class-six sigma separation does *not* require a handle.

with ⭐⭐ `sepSix_not_bit_even_hom` the same at the hom level, through `sqLiftHom` and the new
`SqU7.isProP_two`: an honest continuous homomorphism on the handle-free `D_sq 0` separates at
class six.  ⭐ So **class five is sharp against class six**: the forcing holds at class five and
fails at class six, so it cannot be pushed up by one, and W64-SEP0H's item 5 ("it says nothing
about class six and above") is settled in the negative at class six.  ⚠ Not "the top class":
classes seven and up are deliberately unasked here, and item 4 below says so.

## ⭐ Why the mechanism dies, stated as the mechanism

At the witness every one of the twenty-one rows of the undressed core word is `0`, and the
class-six response is nevertheless odd (`sepSix_wit_relator` and `sepSix_wit_bit_odd`).  Any
identity of SEP0H's shape, "response `=` a combination of the rows of the undressed word `+ 2 *`
a witness", would force the response even exactly there.  ⭐ So no such identity exists, and
this is not a gap in the search for one: the class-six response is **not** in the ideal the
relator's own rows generate, not even modulo `2`.  That is the precise sense in which the
induction step fails, and it is what `sepSix_not_bit_even` says operationally.

⭐ The failure is exactly at class six and nowhere below.  `sepSix_wit_low_even` records that at
this same witness all twenty coordinates of class at most five of the dressed word are even, so
the witness satisfies SEP0H's conclusion at every lower class and violates it only at the top.

## ⚠⚠ What this does NOT do, and misreadings to refuse

1. ⚠ **It does not retract W64-SEP0H.**  The class-five statement is untouched and is used
   here: `sepSix_wit_five_even` checks that this very witness has even class-five coordinates,
   as `SqU6.selPar_sqWord_diagDress_high` demands of its `SqU6` shadow.  A report saying the
   class-five forcing was weakened is wrong.
2. ⚠ **It does not say the class-six bit is generically odd.**  The bit depends on the marking:
   `scripts/w65_six/extend_six.py` finds base markings for which every extension tested is even,
   and others for which about half are odd.  The claim proved is the existential one, which is
   all a refutation of forcing needs.  Do not quote a frequency.
3. ⚠ **It is not a block statement and not a gauge statement.**  No `blockRead`, no frame, no
   lattice; and no gauge hypothesis is assumed or needed, since the witness is exhibited.
4. ⚠ **It says nothing about class seven and above.**  Class six is the first class at which
   the forcing fails; whether some higher-class statement is again forced is untouched.
5. ⚠ **The class-six coordinate needs a new carrier and cannot be asked inside `SqU6`.**  The
   campaign's class-`N` test group is `U_{N+1}`, so `SqU6` is class five and every class-six
   commutator vanishes in it identically.  `GQ2/Dyadic/SqCore/GradedSeven.lean` supplies `SqU7`;
   a class-six statement written in `SqU6` would be vacuous, not false.

## PROVED versus MEASURED

**PROVED** (no `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`
tuples): the witness kills the relator, its class-six bit is odd, its twenty lower coordinates
are even, and the three refutations (tuple, marking, hom).

**MEASURED** (`scripts/w65_six/`, plain Python, exact integer arithmetic, no `sympy`): the
search that produced the witness, and the certification of the `SqU7` coordinate law against the
committed `SqU6` law one index down.  No measured claim is used in any proof; the witness is
re-checked by `decide` inside Lean.

## Naming

Everything new carries a `sepSix` prefix, except the one `SqU7`-namespaced statement,
`SqU7.not_selPar_sqWord_diagDress_e17`.  (`SqU7.isProP_two` is used here but declared in
`GradedSeven`.)  Nothing in the tree imports this file.
-/

namespace GQ2

namespace Dyadic

namespace SqCore

/-! ## 1 The class-six sigma dressing -/

section Dress

variable {G : Type*} [Group G] {h : ℕ}

/-- **The sigma-dressed tuple**, at any class: the marking with the sigma slot multiplied by `v`
on the right and every other slot untouched.  This is `GradedFive.sigFiveDress` with the `SqU6`
hypothesis dropped, and `sepSixDress_eq_sigFiveDress` pins it to the committed definition. -/
def sepSixDress (m : Fin (sqRank h) → G) (v : G) : Fin (sqRank h) → G :=
  fun i => if (i : ℕ) = 0 then m i * v else m i

variable {m : Fin (sqRank h) → G} {v : G}

@[simp] theorem sepSixDress_zero : sepSixDress m v 0 = m 0 * v := by
  simp only [sepSixDress, sqVal_zero]
  norm_num

theorem sepSixDress_ne {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) : sepSixDress m v i = m i :=
  if_neg hi

theorem sepSixDress_one : sepSixDress m v 1 = m 1 :=
  sepSixDress_ne (by rw [sqVal_one]; omega)

theorem sepSixDress_two : sepSixDress m v 2 = m 2 :=
  sepSixDress_ne (by rw [sqVal_two]; omega)

/-- ⭐ **The dressing is the committed one.**  At the class-five carrier `sepSixDress` is
`GradedFive.sigFiveDress`, definitionally, so no statement below is about a different
dressing. -/
theorem sepSixDress_eq_sigFiveDress {R : Type} [CommRing R]
    (m : Fin (sqRank h) → SqU6 R) (v : SqU6 R) : sepSixDress m v = sigFiveDress m v := rfl

end Dress

/-! ## 2 The witness, and what `decide` checks about it

The three slots were found by `scripts/w65_six/extend_six.py`.  `U_7` is block triangular in the
index `7`, so a triple killing the core word in `U_6` still kills its first fifteen rows after
any extension up column `7`; the search fixes such a triple, chooses the column-`7` entries of
the sigma and `x0` slots freely, and solves the six remaining cells for `x1`.  ⚠ Nothing about
that provenance is used below: the three slots are literals and every claim about them is
re-checked by `decide` on `ZMod 8` tuples. -/

section Witness

/-- The sigma slot of the class-six witness. -/
def sepSixWitS : SqU7 gr3R := ⟨7, 7, 1, 4, 3, 5, 7, 7, 0, 6, 0, 6, 1, 2, 5, 2, 1, 4, 1, 0, 7⟩

/-- The `x0` slot of the class-six witness. -/
def sepSixWitX : SqU7 gr3R := ⟨5, 7, 1, 6, 1, 5, 5, 7, 4, 2, 6, 6, 3, 5, 6, 3, 5, 5, 2, 5, 2⟩

/-- The `x1` slot of the class-six witness. -/
def sepSixWitY : SqU7 gr3R := ⟨6, 2, 2, 0, 2, 2, 2, 1, 1, 1, 0, 5, 0, 0, 1, 1, 6, 1, 3, 3, 1⟩

/-- The `a0 = a1` dressing of the witness core word, as a single element. -/
def sepSixDressed : SqU7 gr3R := sqWord (sepSixWitS * sepSixWitX) sepSixWitX sepSixWitY

theorem sepSixDressed_eq :
    sepSixDressed = sqWord (sepSixWitS * sepSixWitX) sepSixWitX sepSixWitY := rfl

set_option maxRecDepth 100000 in
/-- ⭐⭐ **The witness kills the core word**, so at `h = 0` it kills the relator: all twenty-one
rows of `sqWord` vanish over `gr3R`. -/
theorem sepSix_wit_relator : sqWord sepSixWitS sepSixWitX sepSixWitY = 1 := by decide

set_option maxRecDepth 100000 in
/-- The class-six coordinate of the dressing, on the nose. -/
theorem sepSix_wit_e17 : sepSixDressed.e17 = 3 := by decide

set_option maxRecDepth 100000 in
/-- ⭐⭐⭐ **The class-six bit is ODD** at a marking that kills the relator with no handle. -/
theorem sepSix_wit_bit_odd : selPar sepSixDressed.e17 = 1 := by decide

set_option maxRecDepth 200000 in
/-- ⭐ **The failure is exactly at class six.**  Every coordinate of class at most five of the
dressing is even, so this witness satisfies the conclusion of `SqU6.selPar_sqWord_diagDress_high`
at each lower class and violates it only at the top one. -/
theorem sepSix_wit_low_even :
    selPar sepSixDressed.e12 = 0 ∧ selPar sepSixDressed.e23 = 0 ∧
      selPar sepSixDressed.e34 = 0 ∧ selPar sepSixDressed.e45 = 0 ∧
      selPar sepSixDressed.e56 = 0 ∧ selPar sepSixDressed.e67 = 0 ∧
      selPar sepSixDressed.e13 = 0 ∧ selPar sepSixDressed.e24 = 0 ∧
      selPar sepSixDressed.e35 = 0 ∧ selPar sepSixDressed.e46 = 0 ∧
      selPar sepSixDressed.e57 = 0 ∧ selPar sepSixDressed.e14 = 0 ∧
      selPar sepSixDressed.e25 = 0 ∧ selPar sepSixDressed.e36 = 0 ∧
      selPar sepSixDressed.e47 = 0 ∧ selPar sepSixDressed.e15 = 0 ∧
      selPar sepSixDressed.e26 = 0 ∧ selPar sepSixDressed.e37 = 0 ∧
      selPar sepSixDressed.e16 = 0 ∧ selPar sepSixDressed.e27 = 0 := by decide

set_option maxRecDepth 100000 in
/-- ⚠ **No tension with W64-SEP0H.**  The two class-five coordinates of the dressing are even,
which is what the class-five theorem demands.  The class-five forcing is not weakened here. -/
theorem sepSix_wit_five_even :
    selPar sepSixDressed.e16 = 0 ∧ selPar sepSixDressed.e27 = 0 := by decide

end Witness

/-! ## 3 The refutations, at the tuple, marking and hom levels -/

section Refutation

/-- ⭐⭐⭐ **THE CLASS-SIX RESPONSE IS NOT IN THE ROW IDEAL.**  The exact class-six analogue of
`SqU6.selPar_sqWord_diagDress_o` is **false**.  Since the witness kills every row of the
undressed word, any identity expressing the class-six response as a combination of those rows
plus `2 *` anything would make the response even there; none does. -/
theorem SqU7.not_selPar_sqWord_diagDress_e17 :
    ¬ ∀ s x y : SqU7 gr3R, sqWord s x y = 1 → selPar (sqWord (s * x) x y).e17 = 0 := by
  intro hall
  have h : selPar sepSixDressed.e17 = 0 :=
    hall sepSixWitS sepSixWitX sepSixWitY sepSix_wit_relator
  rw [sepSix_wit_bit_odd] at h
  exact absurd h (by decide)

/-- The witness as a marking of the handle-free `D_sq 0`. -/
def sepSixMark : Fin (sqRank 0) → SqU7 gr3R :=
  fun i => if (i : ℕ) = 0 then sepSixWitS else if (i : ℕ) = 1 then sepSixWitX else sepSixWitY

@[simp] theorem sepSixMark_zero : sepSixMark 0 = sepSixWitS := by
  simp only [sepSixMark, sqVal_zero]
  norm_num

@[simp] theorem sepSixMark_one : sepSixMark 1 = sepSixWitX := by
  simp only [sepSixMark, sqVal_one]
  norm_num

@[simp] theorem sepSixMark_two : sepSixMark 2 = sepSixWitY := by
  simp only [sepSixMark, sqVal_two]
  norm_num

/-- The marking kills the relator, with no handle. -/
theorem sepSix_mark_relator : sqRelWord sepSixMark = 1 := by
  rw [sqRelWord_zero, sepSixMark_zero, sepSixMark_one, sepSixMark_two]
  exact sepSix_wit_relator

/-- The marking's `a0 = a1` dressing separates at class six. -/
theorem sepSix_mark_bit_odd :
    selPar (sqRelWord (sepSixDress sepSixMark (sepSixMark 1))).e17 = 1 := by
  rw [sqRelWord_zero, sepSixDress_zero, sepSixDress_one, sepSixDress_two, sepSixMark_zero,
    sepSixMark_one, sepSixMark_two]
  exact sepSix_wit_bit_odd

/-- ⭐⭐⭐ **The class-six analogue of `sepZero_bit_even` is FALSE.**  A handle-free marking over
`gr3R` can kill the relator and still have an odd class-six separation bit. -/
theorem sepSix_not_bit_even :
    ¬ ∀ m : Fin (sqRank 0) → SqU7 gr3R, sqRelWord m = 1 →
        selPar (sqRelWord (sepSixDress m (m 1))).e17 = 0 := by
  intro hall
  have h := hall sepSixMark sepSix_mark_relator
  rw [sepSix_mark_bit_odd] at h
  exact absurd h (by decide)

/-- ⭐⭐⭐ **THE FORCING FAILS AT CLASS SIX.**  The exact class-six analogue of
`sepZero_pos_of_bit_odd` is false: a class-six sigma separation does not require a handle.  ⚠
The class-five statement is untouched; see `sepSix_wit_five_even`. -/
theorem sepSix_not_pos_of_bit_odd :
    ¬ ∀ (h : ℕ) (m : Fin (sqRank h) → SqU7 gr3R), sqRelWord m = 1 →
        selPar (sqRelWord (sepSixDress m (m 1))).e17 = 1 → 0 < h := by
  intro hall
  exact absurd (hall 0 sepSixMark sepSix_mark_relator sepSix_mark_bit_odd) (lt_irrefl 0)

/-- The witness marking, classified as a continuous homomorphism on the handle-free `D_sq 0`
through the presentation's universal property and the new `SqU7.isProP_two`. -/
noncomputable def sepSixHom : ContinuousMonoidHom (DSq 0 : Type) (SqU7 gr3R) :=
  sqLiftHom 0 (SqU7.isProP_two gr3R_card) sepSixMark sepSix_mark_relator

theorem sepSixHom_gen (i : Fin (sqRank 0)) : sepSixHom (sqGen 0 i) = sepSixMark i :=
  sqLiftHom_gen _ _ _ _ i

/-- ⭐⭐ **The hom form.**  The class-six analogue of `sepZero_bit_even_hom` is false: an honest
continuous homomorphism from the handle-free `D_sq 0` into the class-six test group has an odd
class-six separation bit. -/
theorem sepSix_not_bit_even_hom :
    ¬ ∀ Phi : ContinuousMonoidHom (DSq 0 : Type) (SqU7 gr3R),
        selPar (sqRelWord (sepSixDress (fun i => Phi (sqGen 0 i)) (Phi (sqGen 0 1)))).e17 = 0 := by
  intro hall
  have h := hall sepSixHom
  rw [funext sepSixHom_gen, sepSixHom_gen, sepSix_mark_bit_odd] at h
  exact absurd h (by decide)

end Refutation

/-! ## 4 Axiom pins -/

section AxiomPins

#print axioms sepSix_wit_relator
#print axioms sepSix_wit_bit_odd
#print axioms sepSix_wit_low_even
#print axioms SqU7.not_selPar_sqWord_diagDress_e17
#print axioms sepSix_not_bit_even
#print axioms sepSix_not_pos_of_bit_odd
#print axioms sepSix_not_bit_even_hom

end AxiomPins

end SqCore

end Dyadic

end GQ2
