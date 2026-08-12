/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedLimit
import GQ2.Roe.Labute.Levelwise

/-!
# W68-BRIDGE: the class-three clearing supply, on the tower

Wave 67 reduced the `h ≥ 1` residual to the per-class family `SqClassClearingSupply h k`
(`SqCore/GradedLimit.lean`), discharged `k ≤ 2` by the trivial dressing, and left
`LimFinalResidual h`: the instances `k ≥ 3`.  This file discharges the first of them, `k = 3`,
for every `h`, directly on the tower.

## The route

Route (b) of the ticket: rerun the witness computation in the tower's own vocabulary rather
than transporting `GradedContain`'s binder witness through the selection family.  The
computation turns out to need no binder, no test carrier and no census.

Write `γₖ = twoCentralSeries G k` for `G = D_sq h`, and `Q₃ = levelQuot G 3`.  The committed
class-two calculus of `Roe/Labute/Levelwise.lean` says that in `Q₃` every square and every
commutator lands in the central exponent-two layer `Z₂`, so `commP` is bimultiplicative there.
Two consequences:

* `bridge_sqWord`: `sqWord a b c = commP a b * c ^ 2` in `Q₃`.  Both correction factors of the
  free identity die: `((b²)²)⁻¹` because `b²` already lies in `Z₂`, and `commP c (conjP c a)`
  because `conjP c a = c · commP c a` differs from `c` by a central factor.
* `bridge_comm_zpow_eq`: a bracket reads a `ℤ₂`-power through its exponent's **parity** only,
  so the exponent may be moved from one slot of the bracket to the other.

Hence the relator of a frame, read mod `γ₃`, is `commP m₀ m₁ · m₂² · ∏ commP m_U m_V`, and the
class-three obligation is one identity in the bracket group.  The undressed frame `sqArbBase`
fails it by exactly the Eichler twist: the two cleared handle letters are `w^{-ν'(u_j)}·u_j`
and `v_j·w^{-ν'(v_j)}`, so the `j`-th handle bracket picks up
`commP w^{ν'(u_j)} v_j · commP u_j w^{ν'(v_j)}`.

The fix.  Put the **same** dressing `A` on the `σ`-slot and on the `x₀`-slot and leave every
other slot alone.  Then `commP (σA) (x₀A) = commP σ x₀ · commP (σ·x₀) A`, and `σ·x₀` **is** the
pivot `w` modulo `γ₂` (`bridge_sigma_x0_eq_pivot`: `c₀ = sqPivotExp` is a unit, so
`x₀·x₀^{c₀} = x₀^{1+c₀}` is an even power).  Choosing

```text
  A = u_j^{ν'(v_j)} · v_j^{ν'(u_j)} · w^{-2·ν'(u_j)·ν'(v_j)}
```

makes `commP w A` equal to the handle's defect, and the two defects cancel because `Z₂` has
exponent two.  The third factor of `A` is a pure row correction: it is an even pivot power, so
it is invisible mod `γ₂`, and it is exactly what makes both rows of `A` vanish **on the nose**.

## The row-lifting verdict: NOT obstructed

The ticket's row-lifting question is whether a dressing prescribed mod `γₖ` with admissible
row data can be corrected inside its coset to exact rows; equivalently how large the joint
image of `(nuLam, ν')` on `ker (levelMk (DSq h) k) = γₖ` is.  Verdict: it is the **full square**
`2^{k-1}ℤ₂ × 2^{k-1}ℤ₂`, at every selected marking and every `k` (`bridge_row_image` proves the
containment, which is the direction a coset repair consumes).  Two elements witness it, and
they are row-independent by construction: `x₀` has `λ = 1` and `ν' = 0` exactly, the second by
selectedness, and the pivot `w = σ·x₀^{-c₀}` has `λ = 0` and `ν' = 1` exactly.  Their
`2^{k-1}`-st powers lie in `γₖ`, so both rows can be corrected independently without leaving
the coset.

This wave does not have to invoke the lemma, because `bridgeDress` is written with
`ℤ₂`-exponents whose rows cancel on the nose (`bridge_nuLam_dress`, `bridge_nu_dress`); no
coset correction is performed at all.  The verdict is recorded because the ticket asked for it
and because classes `k ≥ 4` will consume it.

## Contents

* **§1** the class-two calculus in `Q₃`, over the committed `Levelwise` API;
* **§2** the relator modulo `γ₃`: `bridge_sqWord`, `bridge_sqRelWord`;
* **§3** one handle factor, changed centrally (the list surgery);
* **§4** `γ₂`-shadows of `ℤ₂`-powers, and the pivot shadow of `σ·x₀`;
* **§5** the witness dressing `bridgeDress`, its exact rows, and the frame it builds;
* **§6** ⭐⭐ the two brackets and the cancellation: `bridge_relator_mem`;
* **§7** mod-2 independence of the dressed frame;
* **§8** ⭐⭐⭐ `sqClassThree_supply`, and the residual restated from class four;
* **§9** the row-lifting verdict for every class;
* **§10** what class four needs, and why it is not this argument;
* **§11** axiom pins.

Lane W68-BRIDGE.  New file; no edits to existing files.  Prefixes `bridge` / `sqClassThree` /
`bridgeFinal`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The class-two calculus in `Q₃`

`Levelwise.lean` commits `commP_mem_zLayer_two`, `sq_mem_zLayer_two`, bimultiplicativity of
`commP` in both slots, and the two `Z₂`-facts `zLayer_commute`, `zLayer_inv_self`, `zLayer_sq`.
This section adds only the consequences the computation quotes: commuting entries kill a
bracket, `Z₂`-factors are invisible in either slot, and the bracket is symmetric. -/

section ClassTwo

variable {Q : Type*} [Group Q]

/-- A bracket of an element against itself is trivial. -/
theorem bridge_comm_self (p : Q) : commP p p = 1 := by simp only [commP]; group

/-- **Commuting entries kill a bracket.** -/
theorem bridge_comm_of_commute {p q : Q} (hpq : p * q = q * p) : commP p q = 1 := by
  have hq : q⁻¹ * p * q = p := by
    rw [mul_assoc, hpq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hsplit : commP p q = p⁻¹ * (q⁻¹ * p * q) := by simp only [commP]; group
  rw [hsplit, hq, inv_mul_cancel]

/-- A central factor may be shuffled to the far right of a four-fold product.  This is the
shape the final assembly meets: `(A·z)·B·(C·z) = A·B·C·z²`. -/
theorem bridge_central_shuffle {z : Q} (hz : ∀ g : Q, g * z = z * g) (A B C : Q) :
    A * z * B * (C * z) = A * B * C * (z * z) := by
  calc A * z * B * (C * z) = A * (z * B) * (C * z) := by rw [mul_assoc A z B]
    _ = A * (B * z) * (C * z) := by rw [← hz B]
    _ = A * B * (z * C) * z := by group
    _ = A * B * (C * z) * z := by rw [← hz C]
    _ = A * B * C * (z * z) := by group

end ClassTwo

section LevelThree

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A `Z₂`-element is central, so it kills a bracket from the left. -/
theorem bridge_comm_zLayer_left {z : levelQuot G 3} (hz : z ∈ zLayer G 2) (q : levelQuot G 3) :
    commP z q = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq

/-- A `Z₂`-element is central, so it kills a bracket from the right. -/
theorem bridge_comm_zLayer_right {z : levelQuot G 3} (hz : z ∈ zLayer G 2) (q : levelQuot G 3) :
    commP q z = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq.symm

/-- **The bracket is symmetric in `Q₃`**: it equals its own inverse, `Z₂` having exponent two. -/
theorem bridge_comm_swap (p q : levelQuot G 3) : commP q p = commP p q := by
  have hsw : commP q p = (commP p q)⁻¹ := by simp only [commP]; group
  rw [hsw, zLayer_inv_self (commP_mem_zLayer_two p q)]

/-- Every bracket of `Q₃` is central. -/
theorem bridge_comm_central (p q t : levelQuot G 3) : t * commP p q = commP p q * t :=
  (zLayer_commute (commP_mem_zLayer_two p q) t).eq.symm

/-- A `Z₂`-factor on the left of the left slot is invisible. -/
theorem bridge_comm_z_mul_left {z : levelQuot G 3} (hz : z ∈ zLayer G 2)
    (p q : levelQuot G 3) : commP (z * p) q = commP p q := by
  rw [commP_mul_left_of_three, bridge_comm_zLayer_left hz, one_mul]

/-- A `Z₂`-factor on the right of the left slot is invisible. -/
theorem bridge_comm_mul_z_left {z : levelQuot G 3} (hz : z ∈ zLayer G 2)
    (p q : levelQuot G 3) : commP (p * z) q = commP p q := by
  rw [commP_mul_left_of_three, bridge_comm_zLayer_left hz, mul_one]

/-- A `Z₂`-factor on the left of the right slot is invisible. -/
theorem bridge_comm_z_mul_right {z : levelQuot G 3} (hz : z ∈ zLayer G 2)
    (p q : levelQuot G 3) : commP p (z * q) = commP p q := by
  rw [commP_mul_right_of_three, bridge_comm_zLayer_right hz, mul_one]

/-- A `Z₂`-factor on the right of the right slot is invisible. -/
theorem bridge_comm_mul_z_right {z : levelQuot G 3} (hz : z ∈ zLayer G 2)
    (p q : levelQuot G 3) : commP p (q * z) = commP p q := by
  rw [commP_mul_right_of_three, bridge_comm_zLayer_right hz, one_mul]

/-! ## §2 The relator modulo `γ₃` -/

/-- **The core word modulo `γ₃`**: `sqWord a b c = commP a b · c²`.  The fourth power dies
because `b²` is already central of order two, and the twisted commutator dies because
`conjP c a` differs from `c` by the central factor `commP c a`.  This is
`lim_sqRelWord_mem_twoCentralSeries_two` one class deeper: there the whole word died, here what
survives is exactly the bilinear part. -/
theorem bridge_sqWord (a b c : levelQuot G 3) : sqWord a b c = commP a b * c ^ 2 := by
  have hid : sqWord a b c = commP a b * ((b ^ 2) ^ 2)⁻¹ * c ^ 2 * commP c (conjP c a) := by
    simp only [sqWord, conjP, commP]
    group
  have hb : ((b ^ 2) ^ 2 : levelQuot G 3) = 1 := zLayer_sq G (sq_mem_zLayer_two b)
  have hconj : conjP c a = c * commP c a := by simp only [conjP, commP]; group
  have hcc : commP c (conjP c a) = 1 := by
    rw [hconj, commP_mul_right_of_three, bridge_comm_zLayer_right (commP_mem_zLayer_two c a),
      one_mul, bridge_comm_self]
  rw [hid, hb, inv_one, mul_one, hcc, mul_one]

/-- **The relator modulo `γ₃`**: the `σ`/`x₀` bracket, the `x₁`-square, and the handle
brackets.  Nothing else survives. -/
theorem bridge_sqRelWord {k : ℕ} (m : Fin (sqRank k) → levelQuot G 3) :
    sqRelWord m = commP (m 0) (m 1) * m 2 ^ 2 *
      handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) := by
  rw [sqRelWord, bridge_sqWord]

end LevelThree

/-! ## §3 One handle factor, changed centrally

The dressed frame differs from the standard generators at the `j`-th handle only, and the
bracket there changes by one central factor.  The list surgery is the `GradedLift` /
`GradedFiveForce` pattern, restated here because that helper is `private`. -/

section HandleSurgery

variable {Q : Type*} [Group Q]

/-- One entry of a product over `Fin n` picking up a central right factor passes it to the
whole product. -/
theorem bridge_prod_map_update_center (n : ℕ) :
    ∀ (F : Fin n → Q) (j : Fin n) (z : Q), (∀ g : Q, g * z = z * g) →
      ((List.finRange n).map fun k => if k = j then F k * z else F k).prod
        = ((List.finRange n).map F).prod * z := by
  induction n with
  | zero => exact fun F j z _ => j.elim0
  | succ n ih =>
    intro F j z hz
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    cases j using Fin.cases with
    | zero =>
      rw [if_pos rfl]
      have htail : (List.finRange n).map ((fun k => if k = 0 then F k * z else F k)
            ∘ Fin.succ) = (List.finRange n).map (F ∘ Fin.succ) := by
        refine List.map_congr_left fun k _ => ?_
        simp [Fin.succ_ne_zero]
      rw [htail, mul_assoc, ← hz ((List.finRange n).map (F ∘ Fin.succ)).prod, ← mul_assoc]
    | succ j' =>
      rw [if_neg (Fin.succ_ne_zero j').symm]
      have htail : (List.finRange n).map ((fun k => if k = Fin.succ j' then F k * z else F k)
            ∘ Fin.succ)
          = (List.finRange n).map fun k => if k = j' then (F ∘ Fin.succ) k * z
              else (F ∘ Fin.succ) k := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, Fin.succ_inj]
      rw [htail, ih (F ∘ Fin.succ) j' z hz, ← mul_assoc]

/-- **A handle word with one bracket changed by a central factor.** -/
theorem bridge_handleWord_update {n : ℕ} (u v u' v' : Fin n → Q) (j : Fin n) (z : Q)
    (hz : ∀ g : Q, g * z = z * g)
    (hne : ∀ i, i ≠ j → commP (u i) (v i) = commP (u' i) (v' i))
    (hj : commP (u j) (v j) = commP (u' j) (v' j) * z) :
    handleWord u v = handleWord u' v' * z := by
  have hmap : ((List.finRange n).map fun i => commP (u i) (v i))
      = ((List.finRange n).map fun i => if i = j then commP (u' i) (v' i) * z
          else commP (u' i) (v' i)) := by
    refine List.map_congr_left fun i _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij]
      subst hij
      exact hj
    · rw [if_neg hij]
      exact hne i hij
  rw [handleWord, hmap, bridge_prod_map_update_center n _ j z hz, handleWord]

end HandleSurgery

/-! ## §4 `γ₂`-shadows of `ℤ₂`-powers

Everything the computation needs to know about a `ℤ₂`-power, read mod `γ₂`, is its exponent's
parity: an even power is a square, an odd power is its own base times a square. -/

section Shadows

variable {h : ℕ}

/-- The image of a `γ₂`-element in `Q₃` lies in the central layer `Z₂`. -/
theorem bridge_mem_zLayer {v : (DSq h : Type)} (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 3 v ∈ zLayer (DSq h : Type) 2 :=
  ⟨v, hv, rfl⟩

/-- **An even `ℤ₂`-power is a square**, hence lies in `γ₂`. -/
theorem bridge_zpow_even (g : (DSq h : Type)) {k : ℤ_[2]} (hk : (2 : ℤ_[2]) ∣ k) :
    zpowZtwo (isProP_DSq h) g k ∈ twoCentralSeries (DSq h : Type) 2 := by
  obtain ⟨s, rfl⟩ := hk
  rw [zpowZtwo_two_mul]
  exact sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (Subgroup.mem_top _)

/-- **An odd `ℤ₂`-power is its own base modulo `γ₂`**: `g^{2q+1} = (g^q)²·g`. -/
theorem bridge_zpow_odd_eq (g : (DSq h : Type)) {k : ℤ_[2]} (hk : ¬ (2 : ℤ_[2]) ∣ k) :
    ∃ u ∈ twoCentralSeries (DSq h : Type) 2, zpowZtwo (isProP_DSq h) g k = u * g := by
  obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hk) isUnit_one
  have hsplit : k = 2 * q + 1 := by linear_combination hq
  refine ⟨zpowZtwo (isProP_DSq h) g q ^ 2,
    sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (Subgroup.mem_top _), ?_⟩
  rw [hsplit, zpowZtwo_add, zpowZtwo_one_exp, zpowZtwo_two_mul]

/-- ⭐ **A bracket reads a `ℤ₂`-power through its exponent's parity only**, so the exponent may
be moved from one slot of the bracket to the other.  This is what makes the core defect and the
handle defect the same element of `Z₂` (`bridge_defect_eq`). -/
theorem bridge_comm_zpow_eq (g t : (DSq h : Type)) (k : ℤ_[2]) :
    commP (levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) g k))
        (levelMk (DSq h : Type) 3 t)
      = commP (levelMk (DSq h : Type) 3 g)
          (levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) t k)) := by
  by_cases hk : (2 : ℤ_[2]) ∣ k
  · rw [bridge_comm_zLayer_left (bridge_mem_zLayer (bridge_zpow_even g hk)),
      bridge_comm_zLayer_right (bridge_mem_zLayer (bridge_zpow_even t hk))]
  · obtain ⟨u, hu, hug⟩ := bridge_zpow_odd_eq g hk
    obtain ⟨v, hv, hvt⟩ := bridge_zpow_odd_eq t hk
    rw [hug, hvt, map_mul, map_mul, bridge_comm_z_mul_left (bridge_mem_zLayer hu),
      bridge_comm_z_mul_right (bridge_mem_zLayer hv)]

/-- **`σ·x₀` is the pivot modulo `γ₂`**: `c₀ = sqPivotExp` is a unit, so `x₀·x₀^{c₀}` is the
even power `x₀^{1+c₀}`.  This is why dressing the `σ`- and `x₀`-slots by the same element
produces a defect read at the *pivot*, which is where the Eichler twist lives. -/
theorem bridge_sigma_x0_eq_pivot :
    ∃ u ∈ twoCentralSeries (DSq h : Type) 2, dsqSigma h * dsqX0 h = u * sqPivot h := by
  obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit isUnit_sqPivotExp isUnit_one
  have hdvd : (2 : ℤ_[2]) ∣ 1 + sqPivotExp := ⟨1 + q, by linear_combination hq⟩
  refine ⟨dsqSigma h * zpowZtwo (isProP_DSq h) (dsqX0 h) (1 + sqPivotExp) * (dsqSigma h)⁻¹,
    (twoCentralSeries_normal (DSq h : Type) 2).conj_mem _
      (bridge_zpow_even (dsqX0 h) hdvd) _, ?_⟩
  simp only [sqPivot, sqMixPivotElem]
  rw [zpowZtwo_add, zpowZtwo_one_exp]
  group

end Shadows

/-! ## §5 The witness dressing -/

section Witness

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- The `ν'`-row of the `j`-th handle's first letter. -/
noncomputable def bridgeRowU : ℤ_[2] := toAdd (nu' (sqGen h (sqHandleIdxU j)))

/-- The `ν'`-row of the `j`-th handle's second letter. -/
noncomputable def bridgeRowV : ℤ_[2] := toAdd (nu' (sqGen h (sqHandleIdxV j)))

/-- **The witness dressing** `u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{-2·ν'(u_j)·ν'(v_j)}`.  The first
two factors carry the mod-`γ₂` class that cancels the Eichler twist; the third is an even pivot
power, invisible mod `γ₂`, which is what makes both rows vanish exactly. -/
noncomputable def bridgeDress : (DSq h : Type) :=
  zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) (bridgeRowV nu' j) *
      zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) (bridgeRowU nu' j) *
    zpowZtwo (isProP_DSq h) (sqPivot h) (-(2 * bridgeRowU nu' j * bridgeRowV nu' j))

/-- The `u`-row, unfolded. -/
theorem bridgeRowU_def : bridgeRowU nu' j = toAdd (nu' (sqGen h (sqHandleIdxU j))) := rfl

/-- The `v`-row, unfolded. -/
theorem bridgeRowV_def : bridgeRowV nu' j = toAdd (nu' (sqGen h (sqHandleIdxV j))) := rfl

/-- **The witness dressing tuple**: the same element on the `σ`-slot and the `x₀`-slot, trivial
on every other slot. -/
noncomputable def bridgeTuple : Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = 0 then bridgeDress nu' j
    else if (i : ℕ) = 1 then bridgeDress nu' j else 1

/-- **The dressing is `λ`-trivial, exactly**: the two handle letters and the pivot all have
zero `λ`-row. -/
theorem bridge_nuLam_dress : nuLam h (bridgeDress nu' j) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  simp only [bridgeDress, map_mul, toAdd_mul, toAdd_map_zpowZtwo, toAdd_nuLam_sqPivot,
    nuLam_handleU, nuLam_handleV, toAdd_one, mul_zero, add_zero]

/-- **The dressing is `ν'`-trivial, exactly**: the two cross terms `ν'(u_j)·ν'(v_j)` cancel
against the even pivot power, whose `ν'`-row is `1` at a selected marking. -/
theorem bridge_nu_dress (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : nu' (bridgeDress nu' j) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  simp only [bridgeDress, map_mul, toAdd_mul, toAdd_map_zpowZtwo,
    toAdd_nu_sqPivot_selected nu' hsigma hx0, toAdd_one, bridgeRowU, bridgeRowV]
  ring

/-- Every slot of the tuple is `λ`-trivial. -/
theorem bridge_tuple_nuLam (i : Fin (sqRank h)) : nuLam h (bridgeTuple nu' j i) = 1 := by
  simp only [bridgeTuple]
  split_ifs
  · exact bridge_nuLam_dress nu' j
  · exact bridge_nuLam_dress nu' j
  · exact map_one _

/-- Every slot of the tuple is `ν'`-trivial. -/
theorem bridge_tuple_nu (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (i : Fin (sqRank h)) :
    nu' (bridgeTuple nu' j i) = 1 := by
  simp only [bridgeTuple]
  split_ifs
  · exact bridge_nu_dress nu' j hsigma hx0
  · exact bridge_nu_dress nu' j hsigma hx0
  · exact map_one _

/-- Away from the two core slots the tuple is trivial. -/
theorem bridge_tuple_of_ne {i : Fin (sqRank h)} (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) :
    bridgeTuple nu' j i = 1 := by
  simp only [bridgeTuple, if_neg h0, if_neg h1]

/-- The `σ`-slot of the dressed frame. -/
theorem bridge_frame_zero :
    sqArbFrame h nu' j (bridgeTuple nu' j) 0 = dsqSigma h * bridgeDress nu' j := by
  simp only [sqArbFrame, sqArbBase_zero, bridgeTuple, sqVal_zero, if_pos]

/-- The `x₀`-slot of the dressed frame. -/
theorem bridge_frame_one :
    sqArbFrame h nu' j (bridgeTuple nu' j) 1 = dsqX0 h * bridgeDress nu' j := by
  have hT : bridgeTuple nu' j 1 = bridgeDress nu' j := by
    simp only [bridgeTuple, sqVal_one]
    norm_num
  rw [sqArbFrame, sqArbBase_one, hT]

/-- The `x₁`-slot of the dressed frame is undressed. -/
theorem bridge_frame_two : sqArbFrame h nu' j (bridgeTuple nu' j) 2 = dsqX1 h := by
  rw [sqArbFrame, sqArbBase_two, bridge_tuple_of_ne nu' j (by rw [sqVal_two]; omega)
    (by rw [sqVal_two]; omega), mul_one]

/-- Every handle slot of the dressed frame is undressed. -/
theorem bridge_frame_handleU (j' : Fin h) :
    sqArbFrame h nu' j (bridgeTuple nu' j) (sqHandleIdxU j') =
      sqArbBase h nu' j (sqHandleIdxU j') := by
  rw [sqArbFrame, bridge_tuple_of_ne nu' j (by rw [sqHandleIdxU_val]; omega)
    (by rw [sqHandleIdxU_val]; omega), mul_one]

/-- Every handle slot of the dressed frame is undressed. -/
theorem bridge_frame_handleV (j' : Fin h) :
    sqArbFrame h nu' j (bridgeTuple nu' j) (sqHandleIdxV j') =
      sqArbBase h nu' j (sqHandleIdxV j') := by
  rw [sqArbFrame, bridge_tuple_of_ne nu' j (by rw [sqHandleIdxV_val]; omega)
    (by rw [sqHandleIdxV_val]; omega), mul_one]

end Witness

/-! ## §6 The two brackets

Both the core bracket and the `j`-th handle bracket miss their undressed values by a `Z₂`-shift.
The two shifts are the same element, so they cancel: `Z₂` has exponent two. -/

section Brackets

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The core bracket under a common dressing**: dressing the `σ`-slot and the `x₀`-slot by
the *same* element `a` shifts the bracket by `commP (s·x) a` and by nothing else, because the
`a`-`a` term is a self-bracket. -/
theorem bridge_comm_common_dress (s x a : levelQuot G 3) :
    commP (s * a) (x * a) = commP s x * commP (s * x) a := by
  rw [commP_mul_left_of_three, commP_mul_right_of_three s x a,
    commP_mul_right_of_three a x a, bridge_comm_self, one_mul, bridge_comm_swap x a,
    commP_mul_left_of_three s x a,
    (zLayer_commute (commP_mem_zLayer_two s a) (commP s x)).eq, mul_assoc]

/-- **The Eichler-twisted handle bracket**: the two pivot powers pulled off the handle letters
contribute the two mixed brackets and nothing else, their own bracket vanishing because powers
of one element commute. -/
theorem bridge_comm_eich (zu zv U V : levelQuot G 3) (hcomm : zu * zv = zv * zu) :
    commP (zu⁻¹ * U) (V * zv⁻¹) = commP U V * (commP zu V * commP U zv) := by
  have hzz : commP zu⁻¹ zv⁻¹ = 1 :=
    bridge_comm_of_commute (by rw [← mul_inv_rev, ← mul_inv_rev, hcomm])
  have hu' : commP zu⁻¹ V = commP zu V := by
    rw [commP_inv_left_of_three, zLayer_inv_self (commP_mem_zLayer_two zu V)]
  have hv' : commP U zv⁻¹ = commP U zv := by
    rw [commP_inv_right_of_three, zLayer_inv_self (commP_mem_zLayer_two U zv)]
  rw [commP_mul_left_of_three, commP_mul_right_of_three zu⁻¹ V zv⁻¹,
    commP_mul_right_of_three U V zv⁻¹, hzz, hu', hv', one_mul, ← mul_assoc,
    (zLayer_commute ((zLayer G 2).mul_mem (commP_mem_zLayer_two zu V)
      (commP_mem_zLayer_two U zv)) (commP U V)).eq]

end Brackets

section Cancellation

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The class-three defect of the witness**: the bracket of the pivot against the dressing.
Both the core bracket and the handle bracket miss their undressed values by exactly this. -/
noncomputable def bridgeDefect : levelQuot (DSq h : Type) 3 :=
  commP (levelMk (DSq h : Type) 3 (sqPivot h)) (levelMk (DSq h : Type) 3 (bridgeDress nu' j))

/-- The defect is central. -/
theorem bridge_defect_central (g : levelQuot (DSq h : Type) 3) :
    g * bridgeDefect nu' j = bridgeDefect nu' j * g :=
  bridge_comm_central _ _ g

/-- The defect has order dividing two, which is why the two copies cancel. -/
theorem bridge_defect_sq : bridgeDefect nu' j * bridgeDefect nu' j = 1 := by
  rw [← pow_two]
  exact zLayer_sq (DSq h : Type) (commP_mem_zLayer_two _ _)

/-- **The defect, read at the handle**: the even pivot factor of the dressing is invisible, and
the two remaining exponents move across the bracket by `bridge_comm_zpow_eq`. -/
theorem bridge_defect_eq :
    bridgeDefect nu' j
      = commP (levelMk (DSq h : Type) 3
            (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowU nu' j)))
          (levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxV j))) *
        commP (levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU j)))
          (levelMk (DSq h : Type) 3
            (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j))) := by
  have hdvd : (2 : ℤ_[2]) ∣ -(2 * bridgeRowU nu' j * bridgeRowV nu' j) :=
    ⟨-(bridgeRowU nu' j * bridgeRowV nu' j), by ring⟩
  rw [bridgeDefect, bridgeDress, map_mul, map_mul, commP_mul_right_of_three,
    bridge_comm_zLayer_right (bridge_mem_zLayer (bridge_zpow_even (sqPivot h) hdvd)),
    one_mul, commP_mul_right_of_three,
    ← bridge_comm_zpow_eq (sqPivot h) (sqGen h (sqHandleIdxV j)) (bridgeRowU nu' j),
    ← bridge_comm_zpow_eq (sqPivot h) (sqGen h (sqHandleIdxU j)) (bridgeRowV nu' j),
    bridge_comm_swap (levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU j)))
      (levelMk (DSq h : Type) 3
        (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j)))]

/-- **The core bracket of the dressed frame**, off by the defect. -/
theorem bridge_core_comm :
    commP (levelMk (DSq h : Type) 3 (dsqSigma h * bridgeDress nu' j))
        (levelMk (DSq h : Type) 3 (dsqX0 h * bridgeDress nu' j))
      = commP (levelMk (DSq h : Type) 3 (dsqSigma h))
          (levelMk (DSq h : Type) 3 (dsqX0 h)) * bridgeDefect nu' j := by
  obtain ⟨u, hu, hsx⟩ := bridge_sigma_x0_eq_pivot (h := h)
  rw [map_mul, map_mul, bridge_comm_common_dress, ← map_mul, hsx, map_mul,
    bridge_comm_z_mul_left (bridge_mem_zLayer hu), bridgeDefect]

/-- **The `j`-th handle bracket of the dressed frame**, off by the same defect. -/
theorem bridge_handle_comm :
    commP (levelMk (DSq h : Type) 3 (sqEichU h nu' j))
        (levelMk (DSq h : Type) 3 (sqEichV h nu' j))
      = commP (levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU j)))
          (levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxV j))) * bridgeDefect nu' j := by
  have hcomm : levelMk (DSq h : Type) 3
        (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowU nu' j)) *
      levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j))
      = levelMk (DSq h : Type) 3 (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j)) *
        levelMk (DSq h : Type) 3
          (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowU nu' j)) := by
    rw [← map_mul, ← map_mul, ← zpowZtwo_add, ← zpowZtwo_add, add_comm]
  rw [sqEichU, sqEichV, ← bridgeRowU_def, ← bridgeRowV_def, map_mul, map_mul, map_inv, map_inv,
    bridge_comm_eich _ _ _ _ hcomm, bridge_defect_eq]

/-- ⭐⭐ **The cancellation**: the dressed frame's relator dies to class three.  The core
bracket and the handle bracket each pick up the defect, and `Z₂` has exponent two. -/
theorem bridge_relator_mem :
    sqRelWord (sqArbFrame h nu' j (bridgeTuple nu' j)) ∈
      twoCentralSeries (DSq h : Type) 3 := by
  have hgen : sqRelWord (fun i => levelMk (DSq h : Type) 3 (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, dsq_relation, map_one]
  simp only [bridge_sqRelWord] at hgen
  have hhandle : handleWord
      (fun i => levelMk (DSq h : Type) 3 (sqArbBase h nu' j (sqHandleIdxU i)))
      (fun i => levelMk (DSq h : Type) 3 (sqArbBase h nu' j (sqHandleIdxV i)))
      = handleWord (fun i => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxU i)))
          (fun i => levelMk (DSq h : Type) 3 (sqGen h (sqHandleIdxV i))) *
        bridgeDefect nu' j := by
    refine bridge_handleWord_update _ _ _ _ j _ (bridge_defect_central nu' j) ?_ ?_
    · intro i hi
      simp only [sqArbBase_handleU_ne hi, sqArbBase_handleV_ne hi]
    · simp only [sqArbBase_handleU, sqArbBase_handleV]
      exact bridge_handle_comm nu' j
  rw [lim_mem_twoCentralSeries_iff_levelMk, map_sqRelWord]
  simp only [bridge_sqRelWord, bridge_frame_zero, bridge_frame_one, bridge_frame_two,
    bridge_frame_handleU, bridge_frame_handleV]
  rw [bridge_core_comm, hhandle, bridge_central_shuffle (bridge_defect_central nu' j),
    bridge_defect_sq, mul_one]
  exact hgen

/-! ## §7 Mod-2 independence of the dressed frame

The dressing is built out of the two handle letters and the pivot, so an index-two open normal
subgroup swallowing every slot swallows all of them, and then every standard generator. -/

/-- **The dressed frame is mod-2 independent**, at every marking and every handle.  Selectedness
is not needed: the argument only uses that `sqPivotExp` is a unit. -/
theorem bridge_modTwoIndep : SqModTwoIndep (sqArbFrame h nu' j (bridgeTuple nu' j)) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, sqArbFrame h nu' j (bridgeTuple nu' j) i ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hx1 : dsqX1 h ∈ M.toSubgroup := by
    have hs := hmem 2
    rwa [bridge_frame_two] at hs
  have h0 : dsqSigma h * bridgeDress nu' j ∈ M.toSubgroup := by
    have hs := hmem 0
    rwa [bridge_frame_zero] at hs
  have h1 : dsqX0 h * bridgeDress nu' j ∈ M.toSubgroup := by
    have hs := hmem 1
    rwa [bridge_frame_one] at hs
  have hsx : dsqSigma h * (dsqX0 h)⁻¹ ∈ M.toSubgroup := by
    have hprod := M.toSubgroup.mul_mem h0 (M.toSubgroup.inv_mem h1)
    have heq : dsqSigma h * bridgeDress nu' j * (dsqX0 h * bridgeDress nu' j)⁻¹
        = dsqSigma h * (dsqX0 h)⁻¹ := by group
    rwa [heq] at hprod
  have hiff : dsqSigma h ∈ M.toSubgroup ↔ dsqX0 h ∈ M.toSubgroup := by
    have hd := (mul_mem_iff_of_index_two hM (dsqSigma h) (dsqX0 h)⁻¹).mp hsx
    rwa [Subgroup.inv_mem_iff] at hd
  have hpiv : sqPivot h ∈ M.toSubgroup := by
    have hodd : ¬ (2 : ℤ_[2]) ∣ sqPivotExp := isUnit_iff_not_two_dvd.mp isUnit_sqPivotExp
    have hzp : zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp ∈ M.toSubgroup ↔
        dsqX0 h ∈ M.toSubgroup := zpowZtwo_mem_iff_of_odd (isProP_DSq h) hM _ hodd
    rw [sqPivot, sqMixPivotElem]
    refine (mul_mem_iff_of_index_two hM _ _).mpr ?_
    rw [Subgroup.inv_mem_iff, hzp]
    exact hiff
  have hzU : zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowU nu' j) ∈ M.toSubgroup :=
    zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _
  have hzV : zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j) ∈ M.toSubgroup :=
    zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _
  have hU : sqGen h (sqHandleIdxU j) ∈ M.toSubgroup := by
    have hslot := hmem (sqHandleIdxU j)
    rw [bridge_frame_handleU, sqArbBase_handleU, sqEichU, ← bridgeRowU_def] at hslot
    have hprod := M.toSubgroup.mul_mem hzU hslot
    rwa [mul_inv_cancel_left] at hprod
  have hV : sqGen h (sqHandleIdxV j) ∈ M.toSubgroup := by
    have hslot := hmem (sqHandleIdxV j)
    rw [bridge_frame_handleV, sqArbBase_handleV, sqEichV, ← bridgeRowV_def] at hslot
    have hprod := M.toSubgroup.mul_mem hslot hzV
    rwa [inv_mul_cancel_right] at hprod
  have hA : bridgeDress nu' j ∈ M.toSubgroup := by
    rw [bridgeDress]
    exact M.toSubgroup.mul_mem (M.toSubgroup.mul_mem
      (zpowZtwo_mem_of_mem (isProP_DSq h) hM hU _)
      (zpowZtwo_mem_of_mem (isProP_DSq h) hM hV _))
      (zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _)
  have hs : dsqSigma h ∈ M.toSubgroup := by
    have hprod := M.toSubgroup.mul_mem h0 (M.toSubgroup.inv_mem hA)
    rwa [mul_inv_cancel_right] at hprod
  have hgen : ∀ i, sqGen h i ∈ M.toSubgroup := by
    intro i
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · exact hs
    · exact hiff.mp hs
    · exact hx1
    · by_cases hjj : j' = j
      · subst hjj
        exact hU
      · have hslot := hmem (sqHandleIdxU j')
        rwa [bridge_frame_handleU, sqArbBase_handleU_ne hjj] at hslot
    · by_cases hjj : j' = j
      · subst hjj
        exact hV
      · have hslot := hmem (sqHandleIdxV j')
        rwa [bridge_frame_handleV, sqArbBase_handleV_ne hjj] at hslot
  obtain ⟨i, hi⟩ := exists_sqGen_notMem M hM
  exact hi (hgen i)

end Cancellation

/-! ## §8 The instance, and the residual restated -/

section Instance

/-- ⭐⭐⭐ **The class-three clearing supply, at every `h`, every selected marking and every
handle.**  This is the first nontrivial instance of the per-class family that wave 67 made the
whole `h ≥ 1` residual.  The witness is explicit and `h`-uniform: dress the `σ`- and
`x₀`-slots by `u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{-2ν'(u_j)ν'(v_j)}` and leave every other slot
alone. -/
theorem sqClassThree_supply (h : ℕ) : SqClassClearingSupply h 3 := by
  intro nu' j hsigma hx0
  exact ⟨bridgeTuple nu' j, bridge_tuple_nuLam nu' j, bridge_tuple_nu nu' j hsigma hx0,
    bridge_modTwoIndep nu' j, bridge_relator_mem nu' j⟩

/-- **The honest remainder after this wave**: the class-`k` clearing supply at every `k ≥ 4`. -/
def BridgeFinalResidual (h : ℕ) : Prop := ∀ k, 4 ≤ k → SqClassClearingSupply h k

/-- The remainder supplies every class: `k ≤ 2` by wave 67, `k = 3` by this wave. -/
theorem bridgeFinal_supply_of_residual {h : ℕ} (H : BridgeFinalResidual h) (k : ℕ) :
    SqClassClearingSupply h k := by
  rcases le_or_gt k 2 with hk | hk
  · exact sqClassClearingSupply_of_le_two hk
  · rcases eq_or_lt_of_le (show 3 ≤ k by omega) with hk3 | hk3
    · exact hk3 ▸ sqClassThree_supply h
    · exact H k (by omega)

/-- ⭐⭐⭐ **The residual now starts at class four**: `SqLamMarkTransitivity h` holds iff the
clearing problem is solvable at every class `k ≥ 4`. -/
theorem bridgeFinal_residual_iff {h : ℕ} :
    SqLamMarkTransitivity h ↔ BridgeFinalResidual h :=
  ⟨fun H k _ => sqClassClearingSupply_of_arbRelWord
      (sqArbRelWord_iff_lamMarkTransitivity.mpr H) k,
    fun H => limFinal_markTransitivity (bridgeFinal_supply_of_residual H)⟩

/-- **Wave 67's residual, with its first instance discharged.** -/
theorem bridgeFinal_limResidual_iff {h : ℕ} : LimFinalResidual h ↔ BridgeFinalResidual h :=
  ⟨fun H k hk => H k (by omega), fun H k hk => by
    rcases eq_or_lt_of_le hk with hk3 | hk3
    · exact hk3 ▸ sqClassThree_supply h
    · exact H k (by omega)⟩

end Instance

/-! ## §9 The row-lifting verdict

The ticket asked whether a dressing prescribed modulo `γₖ` can be corrected inside its coset to
*exact* rows, that is how large the joint image of `(nuLam, ν')` on `ker (levelMk (DSq h) k)` is.
It is large enough at every class and every selected marking, and the pivot alone witnesses it:
`w` has `λ(w) = 0` and `ν'(w) = 1` exactly, so its `2^m`-th powers sweep out `{0} × 2^m ℤ₂`
inside `γ_{m+1}`.  Since `λ` and `ν'` are independent modulo 2, that is exactly the correction
group a coset repair needs, so the row-lifting step is **not** an obstruction. -/

section RowLifting

/-- Every `2^m`-th `ℤ₂`-power lies in `γ_{m+1}`. -/
theorem bridge_zpow_pow_two_mem {h : ℕ} (g : (DSq h : Type)) (m : ℕ) (a : ℤ_[2]) :
    zpowZtwo (isProP_DSq h) g (2 ^ m * a) ∈ twoCentralSeries (DSq h : Type) (m + 1) := by
  have hcast : ((2 ^ m : ℕ) : ℤ_[2]) = 2 ^ m := by push_cast; ring
  have heq : zpowZtwo (isProP_DSq h) g a ^ (2 ^ m)
      = zpowZtwo (isProP_DSq h) g (2 ^ m * a) := by
    rw [← zpowZtwo_natCast (isProP_DSq h) (zpowZtwo (isProP_DSq h) g a) (2 ^ m),
      zpowZtwo_zpowZtwo, hcast, mul_comm]
  rw [← heq]
  exact pow_two_pow_mem_twoCentralSeries_succ (G := (DSq h : Type)) _ m

/-- ⭐ **The row-lifting verdict**: at every selected marking the joint image of
`(nuLam, ν')` on `γ_{m+1} = ker (levelMk (DSq h) (m+1))` contains the full square
`2^m ℤ₂ × 2^m ℤ₂`.  The two witnesses are independent by construction: `x₀` has
`λ = 1` and `ν' = 0` exactly (the second by selectedness), and the pivot `w = σ·x₀^{-c₀}` has
`λ = 0` and `ν' = 1` exactly.  So both rows of a dressing prescribed modulo `γₖ` can be
corrected independently inside its coset, and the row-lifting step of
`docs/dyadic/w67-limit-note.md` §4.2 is not an obstruction. -/
theorem bridge_row_image {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (m : ℕ) (a b : ℤ_[2]) :
    ∃ v ∈ twoCentralSeries (DSq h : Type) (m + 1),
      toAdd (nuLam h v) = 2 ^ m * a ∧ toAdd (nu' v) = 2 ^ m * b := by
  refine ⟨zpowZtwo (isProP_DSq h) (dsqX0 h) (2 ^ m * a) *
    zpowZtwo (isProP_DSq h) (sqPivot h) (2 ^ m * b),
    (twoCentralSeries (DSq h : Type) (m + 1)).mul_mem
      (bridge_zpow_pow_two_mem _ m a) (bridge_zpow_pow_two_mem _ m b), ?_, ?_⟩
  · rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo, toAdd_map_zpowZtwo, toAdd_nuLam_sqPivot,
      nuLam_x0, toAdd_ofAdd, mul_one, mul_zero, add_zero]
  · rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo, toAdd_map_zpowZtwo,
      toAdd_nu_sqPivot_selected nu' hsigma hx0, hx0, toAdd_ofAdd, mul_zero, mul_one, zero_add]

end RowLifting

/-! ## §10 What class four needs

Sections 1 to 6 use exactly two class-specific inputs about `Q₃`, both from `Levelwise`:
`commP` is bimultiplicative there, and `(b²)² = 1` there.  Neither is available at `Q₄`.  The
second is recorded here as an explicit equivalence, because it is the one the tree already
knows to be **false** for `D_sq h`: `GQ2.ContCoh.dsqSigma_pow_four_not_mem_twoCentralSeries_four`
says `σ⁴ ∉ γ₄`.  So the class-four relator identity must carry the `x₀`-slot's fourth power,
which the class-three identity `bridge_sqWord` does not see, and a class-four run cannot be the
present argument with `3` replaced by `4`.

When this section was written that refutation sat in
`Count/LowerTwoCentralJenningsDegreeThree.lean`, so combining it with `bridge_pow_four_iff`
would have needed the first `SqCore → Count` import, and the two-line derivation was left
uncommitted.  It is now hoisted to `SqCore/TwoCentralFacts.lean` (owner decision 5 of
`docs/dyadic/owner-items-2026-08-05.md`), under the same full name and with the same proof, in
a module that sits strictly below both layers.  So the derivation is available to any `SqCore`
module that adds that import: at `G = (DSq h : Type)`, contraposing `bridge_pow_four_iff`
against the refutation at `g = σ` gives `∃ b : levelQuot (DSq h : Type) 4, (b²)² ≠ 1`.  This
file deliberately does not take the import, so that the class-four development owns the step
rather than the class-three record. -/

section ClassFour

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The class-four fourth-power condition, isolated**: `(q²)² = 1` holds throughout `Q₄`
exactly when every fourth power of `G` has already died to class four.  `bridge_sqWord`'s proof
consumes the `Q₃` analogue of the left-hand side, so this is the hypothesis a class-four run
must supply or route around. -/
theorem bridge_pow_four_iff :
    (∀ q : levelQuot G 4, (q ^ 2) ^ 2 = 1) ↔ ∀ g : G, g ^ 4 ∈ twoCentralSeries G 4 := by
  have hpow : ∀ g : G, (levelMk G 4 g ^ 2) ^ 2 = levelMk G 4 (g ^ 4) := by
    intro g
    rw [map_pow, ← pow_mul]
  constructor
  · intro H g
    rw [lim_mem_twoCentralSeries_iff_levelMk, ← hpow g]
    exact H (levelMk G 4 g)
  · intro H q
    obtain ⟨g, rfl⟩ := levelMk_surjective G 4 q
    rw [hpow g, ← lim_mem_twoCentralSeries_iff_levelMk]
    exact H g

end ClassFour

/-! ## §11 Axiom pins -/

section AxiomPins

#print axioms bridge_comm_self
#print axioms bridge_comm_of_commute
#print axioms bridge_central_shuffle
#print axioms bridge_comm_zLayer_left
#print axioms bridge_comm_zLayer_right
#print axioms bridge_comm_swap
#print axioms bridge_comm_central
#print axioms bridge_comm_z_mul_left
#print axioms bridge_comm_mul_z_left
#print axioms bridge_comm_z_mul_right
#print axioms bridge_comm_mul_z_right
#print axioms bridge_sqWord
#print axioms bridge_sqRelWord
#print axioms bridge_prod_map_update_center
#print axioms bridge_handleWord_update
#print axioms bridge_mem_zLayer
#print axioms bridge_zpow_even
#print axioms bridge_zpow_odd_eq
#print axioms bridge_comm_zpow_eq
#print axioms bridge_sigma_x0_eq_pivot
#print axioms bridgeRowU
#print axioms bridgeRowV
#print axioms bridgeDress
#print axioms bridgeRowU_def
#print axioms bridgeRowV_def
#print axioms bridgeTuple
#print axioms bridge_nuLam_dress
#print axioms bridge_nu_dress
#print axioms bridge_tuple_nuLam
#print axioms bridge_tuple_nu
#print axioms bridge_tuple_of_ne
#print axioms bridge_frame_zero
#print axioms bridge_frame_one
#print axioms bridge_frame_two
#print axioms bridge_frame_handleU
#print axioms bridge_frame_handleV
#print axioms bridge_comm_common_dress
#print axioms bridge_comm_eich
#print axioms bridgeDefect
#print axioms bridge_defect_central
#print axioms bridge_defect_sq
#print axioms bridge_defect_eq
#print axioms bridge_core_comm
#print axioms bridge_handle_comm
#print axioms bridge_relator_mem
#print axioms bridge_modTwoIndep
#print axioms sqClassThree_supply
#print axioms BridgeFinalResidual
#print axioms bridgeFinal_supply_of_residual
#print axioms bridgeFinal_residual_iff
#print axioms bridgeFinal_limResidual_iff
#print axioms bridge_zpow_pow_two_mem
#print axioms bridge_row_image
#print axioms bridge_pow_four_iff

end AxiomPins

end SqCore

end Dyadic

end GQ2
