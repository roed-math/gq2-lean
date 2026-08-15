/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcCertificate
import GQ2.Dyadic.GaussZ.FinalDK

/-!
# W80-ROWDATA: the procyclic rows' arithmetic, and the determinant wiring

Two independent tickets, both bookkeeping against committed statements.

**A.** Wave 79 reduced each of the two procyclic quadratic rows to one named `Prop`,
`MpcRowData_sqrt{Ten,NegTen}`, which is `B.r = 1` together with three congruences of the
transported marking.  This module discharges what the tree can carry and names, exactly, what it
cannot.

**B.** `GaussZ/FinalDK.lean` carries the `K` clone of the (83)-evaluation bridge; what was owed
was the wiring of its output into the `determinant` field of `KSupply`.

Declaration prefix `mpcRow`, namespace `GQ2.Dyadic.Instances.MpcRow`.
-/

namespace GQ2.Dyadic.Instances.MpcRow

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.FieldUnimod GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Fields GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The level at the two procyclic fields is at most one

Wave 78 §2.3 argued `B.r = 1` at `ℚ₂(√10)` and `ℚ₂(√−10)` twice, and neither argument was
formalized.  The `≤` half is formalizable exactly as §3 of `FieldUnimodularity` does the `= 0`
case, and with the same witness the unramified row uses: the **scalar `2`**.

At a ramified quadratic `K = ℚ₂(√a)` the scalar `2` has two properties at once:

* `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}`, whose unit part is `1` **on the nose**, so `rec_K(2) ∈ ker χ_K`
  (`fieldUni_norm_twoUnit`, at every `K`);
* `2 = (a/2)⁻¹ · (√a)²` is a **square** of the uniformizer times a spectral unit, so
  `ν_ur(rec_K 2) = ofAdd(−2)`, of 2-adic valuation exactly `1`.

`nu_ker_chi_le` then puts `−2` in `2^{B.r} ℤ₂`, and `mpcCert_le_of_two_pow_eq` reads off
`B.r ≤ 1`.  Contrast `fieldUni_level_sqrtNegTwo`, where the witness has `ν`-value `−1` and the
same argument gives `B.r = 0`: the whole difference between the two pairs of ramified rows is
whether the field carries an element of odd valuation whose norm is a power of `2` on the nose.
-/

section Cofactor

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The coercion of a unit decomposition `x = u · π^n` down to `ℚ̄₂`. -/
theorem mpcRow_val_of_decomp {x u pi : (↥K)ˣ} {n : ℕ} (hx : x = u * pi ^ (n : ℤ)) :
    ((x : ↥K) : ℚ̄₂) = ((u : ↥K) : ℚ̄₂) * ((pi : ↥K) : ℚ̄₂) ^ n := by
  rw [hx, zpow_natCast]
  push_cast
  ring

/-- **The cofactor of a power decomposition is a spectral unit** when the norms match: if
`x = u · π^n` and `‖x‖ = ‖π‖^n`, then `‖u‖ = 1`.  This is how the two rows below avoid ever
naming the scalar `a/2`. -/
theorem mpcRow_norm_cofactor {x u pi : (↥K)ˣ} {n : ℕ} (hx : x = u * pi ^ (n : ℤ))
    (hpi : ((pi : ↥K) : ℚ̄₂) ≠ 0) (h : ‖((x : ↥K) : ℚ̄₂)‖ = ‖((pi : ↥K) : ℚ̄₂)‖ ^ n) :
    ‖((u : ↥K) : ℚ̄₂)‖ = 1 := by
  have hval := mpcRow_val_of_decomp hx
  rw [hval, norm_mul, norm_pow] at h
  have hne : ‖((pi : ↥K) : ℚ̄₂)‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hpi)
  field_simp at h
  exact h

end Cofactor

section LevelUpper

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {Rec : LocalReciprocity}

/-- **The level from one element of `ν`-valuation exactly one**: the `r ≤ 1` companion of
`fieldUni_level_eq_zero_of_decomp`, whose witness is a *square* of the uniformizer rather than
the uniformizer itself. -/
theorem mpcRow_level_le_one_of_decomp (B : MarkedRecip Rec K) (x u pi : (↥K)ˣ)
    (hchi : chiCycKAb K (B.recip x) = 1) (hx : x = u * pi ^ ((2 : ℕ) : ℤ))
    (hu : ‖((u : ↥K) : ℚ̄₂)‖ = 1) (hpi : ‖((pi : ↥K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : ↥K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((pi : ↥K) : ℚ̄₂)‖) :
    B.r ≤ 1 := by
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le _ hchi
  rw [B.nu_ur_recip_of_decomp x u pi ((2 : ℕ) : ℤ) hx hu hpi hmax] at hy
  refine mpcCert_le_of_two_pow_eq (γ := (-1 : ℤ_[2])) (y := y) isUnit_one.neg ?_
  rw [← hy, toAdd_ofAdd]
  push_cast
  ring

end LevelUpper

section QuadLevel

variable {Rec : LocalReciprocity} {a : ℚ_[2]}

/-- `‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ₂)‖`: the spectral norm extends the 2-adic one. -/
theorem mpcRow_norm_two_alg : ‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ_[2])‖ := by
  rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 by rw [map_ofNat]]
  exact GQ2.Dyadic.Fields.norm_algebraMap 2

/-- **`2` is a square of the uniformizer times a spectral unit** at a ramified quadratic field:
the decomposition witness of `mpcRow_level_le_one_of_decomp`. -/
def mpcRow_cofactor (ha : ¬ IsSquare a) : (↥(quadField a))ˣ :=
  fieldUni_twoUnit (quadField a) * ((fieldUni_rootUnit ha) ^ ((2 : ℕ) : ℤ))⁻¹

theorem mpcRow_two_decomp (ha : ¬ IsSquare a) :
    fieldUni_twoUnit (quadField a)
      = mpcRow_cofactor ha * (fieldUni_rootUnit ha) ^ ((2 : ℕ) : ℤ) :=
  (mul_inv_cancel_right _ _).symm

/-- `‖2/(√a)²‖ = 1` when `‖a‖ = ‖2‖`: the cofactor is spectral. -/
theorem mpcRow_norm_cofactor_eq_one (ha : ¬ IsSquare a) (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) :
    ‖((mpcRow_cofactor ha : ↥(quadField a)) : ℚ̄₂)‖ = 1 := by
  refine mpcRow_norm_cofactor (mpcRow_two_decomp ha) ?_ ?_
  · rw [fieldUni_rootUnit_val]
    intro h
    have := norm_sqrtIn_sq a
    rw [h, norm_zero, hna] at this
    rw [fieldUni_norm_two] at this
    norm_num at this
  · rw [fieldUni_twoUnit_val, fieldUni_rootUnit_val, mpcRow_norm_two_alg, ← hna]
    exact (norm_sqrtIn_sq a).symm

/-- **THE LEVEL AT A RAMIFIED QUADRATIC FIELD IS AT MOST ONE.**  The uniform statement behind
both procyclic rows: at `K = ℚ₂(√a)` with `v(a)` odd and `‖a‖ = ‖2‖`, the marked level satisfies
`B.r ≤ 1`.  (It is `0` exactly when the field also carries an element of *odd* valuation whose
norm is a power of `2` with unit part `1`; that is what separates `ℚ₂(√±2)` from `ℚ₂(√±10)`.) -/
theorem mpcRow_level_le_one_quadField (ha : ¬ IsSquare a) (hodd : Odd a.valuation)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (B : MarkedRecip Rec (quadField a)) : B.r ≤ 1 := by
  refine mpcRow_level_le_one_of_decomp B (fieldUni_twoUnit (quadField a)) (mpcRow_cofactor ha)
    (fieldUni_rootUnit ha) ?_ (mpcRow_two_decomp ha) (mpcRow_norm_cofactor_eq_one ha hna)
    (fieldUni_rootUnit_lt_one ha hna) (fieldUni_rootUnit_max ha hodd hna)
  rw [fieldUni_chi_recip_of_norm B _ 1 _ fieldUni_norm_twoUnit, inv_one]

end QuadLevel

/-! ### §1.1 The two rows -/

section Rows

variable {Rec : LocalReciprocity}

theorem mpcRow_valuation_ten_odd : Odd (10 : ℚ_[2]).valuation := by
  rw [valuation_ten]
  exact ⟨0, by ring⟩

theorem mpcRow_valuation_neg_ten_odd : Odd (-10 : ℚ_[2]).valuation := by
  rw [valuation_neg, valuation_ten]
  exact ⟨0, by ring⟩

theorem mpcRow_norm_ten : ‖(10 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ :=
  norm_eq_of_valuation_eq (by norm_num) (by norm_num) (by rw [valuation_ten, valuation_two])

theorem mpcRow_norm_neg_ten : ‖(-10 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ := by
  rw [norm_neg]
  exact mpcRow_norm_ten

/-- **`B.r ≤ 1` AT `ℚ₂(√10)`**, over the field's own bundle and nothing else. -/
theorem mpcRow_level_le_one_sqrtTen (B : MarkedRecip Rec KSqrtTen) : B.r ≤ 1 :=
  mpcRow_level_le_one_quadField not_isSquare_ten mpcRow_valuation_ten_odd mpcRow_norm_ten B

/-- **`B.r ≤ 1` AT `ℚ₂(√−10)`**, over the field's own bundle and nothing else. -/
theorem mpcRow_level_le_one_sqrtNegTen (B : MarkedRecip Rec KSqrtNegTen) : B.r ≤ 1 :=
  mpcRow_level_le_one_quadField not_isSquare_neg_ten mpcRow_valuation_neg_ten_odd
    mpcRow_norm_neg_ten B

end Rows

/-! ## §2 The marking is rigid modulo two, and the `D̄` congruence is not independent

Wave 79 §3 identified a reduction at the `ε = false` row and did not take it, reporting that it
needs "the image of a continuous marking is the closed subgroup generated by its values at the
marked generators", which the tree does not state.  **It is taken here, and the missing lemma is
not needed**: the sharp form of the argument runs on the *preimage* instead of the image, and
`MarkedCore.dm_topGen` (the marked generators topologically generate `D_M`, committed) is then
enough.  If `H` is a **closed** subgroup of the target containing the four generator values, its
preimage is a closed subgroup containing `Set.range (dmGen α h)`, hence contains the topological
closure of the generated subgroup, which is everything.

Applied at `H = 2ℤ₂` this says: **a surjective marking has an odd value at one of the four marked
generators.**  At an `.Mpc α 1 ε η 0` row three of the four are pinned by the level and the frame:

* `ν'(C̄₀)` is even because `χ_M(C̄₀) = 1` and the level is `1` (`MpcChiKerLevel`);
* `ν'(Ā) = −2^{α−1}·ν'(C̄₀)` is then even too (`nu_dmA_eq`, the frame's own relation);
* `ν'(B̄)` is even *exactly when* `p = 0`, i.e. on the `ε = false` row — and that is the `B̄`
  clause of `MpcMarkedData` at `r = 1`.

So on the `ε = false` row the `D̄` clause is a **consequence** of the other data, and
`MpcMarkedData 2 1 0` costs two congruences rather than three.  On the `ε = true` row the
argument gives nothing: there `ν'(B̄)` is odd by assumption, so surjectivity is already accounted
for and `ν'(D̄)` is unconstrained by it.  That asymmetry is real, not an artefact of the proof.
-/

section Rigidity

variable {α h : ℕ}

/-- `2ℤ₂`, as a subgroup of the marking's target. -/
def mpcRow_evenSub : Subgroup (Multiplicative ℤ_[2]) where
  carrier := {x | ∃ y : ℤ_[2], toAdd x = 2 * y}
  mul_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by rw [toAdd_mul, hu, hv]; ring⟩
  one_mem' := ⟨0, by rw [toAdd_one]; ring⟩
  inv_mem' := by
    rintro a ⟨u, hu⟩
    exact ⟨-u, by rw [toAdd_inv, hu]; ring⟩

theorem mpcRow_mem_evenSub_iff {x : Multiplicative ℤ_[2]} :
    x ∈ mpcRow_evenSub ↔ ∃ y : ℤ_[2], toAdd x = 2 * y := Iff.rfl

/-- `2ℤ₂` is closed: it is the continuous image of the compact `ℤ₂` under doubling, pulled back
along `toAdd`. -/
theorem mpcRow_isClosed_evenSub : IsClosed (mpcRow_evenSub : Set (Multiplicative ℤ_[2])) := by
  have hset : (mpcRow_evenSub : Set (Multiplicative ℤ_[2]))
      = Multiplicative.toAdd ⁻¹' (Set.range fun y : ℤ_[2] => 2 * y) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  rw [hset]
  exact IsClosed.preimage continuous_toAdd (isCompact_range (by fun_prop)).isClosed

/-- **Generation transport for the marked core.**  A *closed* subgroup of the target containing
every marked-generator value contains every value.  This replaces the image lemma wave 79 §3
reported missing: `dm_topGen` plus one preimage is all the argument needs. -/
theorem mpcRow_mem_of_gens (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    {H : Subgroup (Multiplicative ℤ_[2])} (hH : IsClosed (H : Set (Multiplicative ℤ_[2])))
    (hgen : ∀ i, nu' (dmGen α h i) ∈ H) (x : (DM α h : Type)) : nu' x ∈ H := by
  have hle : Subgroup.closure (Set.range (dmGen α h)) ≤ H.comap nu'.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hcl : IsClosed ((H.comap nu'.toMonoidHom : Subgroup (DM α h : Type)) :
      Set (DM α h : Type)) := hH.preimage nu'.continuous_toFun
  have hall := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [dm_topGen α h] at hall
  exact hall (Subgroup.mem_top x)

/-- Every 2-adic integer is even or odd. -/
theorem mpcRow_even_or_odd (z : ℤ_[2]) :
    (∃ y : ℤ_[2], z = 2 * y) ∨ ∃ w : ℤ_[2], z = 1 + 2 * w := by
  obtain ⟨m, y, hmy⟩ := MarkedPair.exists_intCast_congr 1 z
  rw [pow_one] at hmy
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine Or.inl ⟨y + (k : ℤ_[2]), ?_⟩
    rw [hk] at hmy
    push_cast at hmy
    linear_combination hmy
  · refine Or.inr ⟨y + (k : ℤ_[2]), ?_⟩
    rw [hk] at hmy
    push_cast at hmy
    linear_combination hmy

/-- No 2-adic integer is both even and odd. -/
theorem mpcRow_not_even_and_odd {z : ℤ_[2]} (he : ∃ y : ℤ_[2], z = 2 * y)
    (ho : ∃ w : ℤ_[2], z = 1 + 2 * w) : False := by
  obtain ⟨y, hy⟩ := he
  obtain ⟨w, hw⟩ := ho
  have hone : (1 : ℤ_[2]) * 2 ^ 0 = 2 ^ 1 * (y - w) := by
    rw [pow_zero, mul_one, pow_one]
    linear_combination hy - hw
  exact absurd (mpcCert_le_of_two_pow_eq isUnit_one hone) (by omega)

/-- **A surjective marking is odd at one of the four marked generators.**  The `H = 2ℤ₂` case of
`mpcRow_mem_of_gens`. -/
theorem mpcRow_exists_odd_gen (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hsurj : Function.Surjective nu') :
    ∃ i, ∃ w : ℤ_[2], toAdd (nu' (dmGen α h i)) = 1 + 2 * w := by
  by_contra hcon
  push Not at hcon
  have hgen : ∀ i, nu' (dmGen α h i) ∈ mpcRow_evenSub := by
    intro i
    rcases mpcRow_even_or_odd (toAdd (nu' (dmGen α h i))) with hev | hodd
    · exact hev
    · exact absurd hodd (by simpa using hcon i)
  obtain ⟨x, hx⟩ := hsurj (ofAdd (1 : ℤ_[2]))
  obtain ⟨y, hy⟩ := mpcRow_mem_of_gens nu' mpcRow_isClosed_evenSub hgen x
  rw [hx, toAdd_ofAdd] at hy
  exact mpcRow_not_even_and_odd ⟨y, hy⟩ ⟨0, by ring⟩

/-- **THE `D̄` CONGRUENCE, FOR FREE AT `p = 0`.**  At level one, a surjective marking whose `B̄`
value is even has an odd `D̄` value: the other three generators are even (the level pins `C̄₀`,
the frame relation pins `Ā`, the hypothesis pins `B̄`), so `mpcRow_exists_odd_gen` has only `D̄`
left.  This is wave 79 §3's identified-but-not-taken reduction, taken. -/
theorem mpcRow_dmD_odd_of_dmB_even {α : ℕ} (hα : 1 ≤ α)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hsurj : Function.Surjective nu') (hlev : MpcChiKerLevel α 1 nu')
    (hB : ∃ y : ℤ_[2], toAdd (nu' (dmB α 0)) = 2 * y) :
    ∃ w : ℤ_[2], toAdd (nu' (dmD α 0)) = 1 + 2 * w := by
  obtain ⟨yC, hC⟩ : ∃ y : ℤ_[2], toAdd (nu' (dmC α 0)) = 2 * y := by
    obtain ⟨y, hy⟩ := hlev (dmC α 0) (chiM_dmC α 0)
    exact ⟨y, by rw [hy, pow_one]⟩
  have hA : ∃ y : ℤ_[2], toAdd (nu' (dmA α 0)) = 2 * y := by
    refine ⟨-(2 : ℤ_[2]) ^ (α - 1) * yC, ?_⟩
    rw [nu_dmA_eq α 0 hα nu', hC]
    ring
  obtain ⟨i, hi⟩ := mpcRow_exists_odd_gen nu' hsurj
  rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
  · exact absurd hi (fun hodd => mpcRow_not_even_and_odd hA hodd)
  · exact absurd hi (fun hodd => mpcRow_not_even_and_odd hB hodd)
  · exact absurd hi (fun hodd => mpcRow_not_even_and_odd ⟨yC, hC⟩ hodd)
  · exact hi

end Rigidity

/-! ## §3 The surjectivity input, at a field

`mpcRow_dmD_odd_of_dmB_even` needs the transported marking to be onto `ℤ₂`.  That is not an
assumption at these fields: `ν_ur` is onto as soon as the field has a uniformizer
(`MarkedRecip.surjective_nu_ur_of_uniformizer`), and `√a` is one at both procyclic rows
(`fieldUni_rootUnit_lt_one`, `fieldUni_rootUnit_max`).  Descending to `G_K(2)` and pulling back
along the oriented equivalence keeps it onto, since both steps are surjections. -/

section Surjectivity

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] {Rec : LocalReciprocity}

/-- The transported marking is onto whenever `ν_ur` is. -/
theorem mpcRow_surjective_nuPullbackM (B : MarkedRecip Rec K) {α : ℕ}
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K)))
    (hsurj : Function.Surjective B.nu_ur) :
    Function.Surjective (fieldUni_nuPullbackM B e) := by
  intro w
  obtain ⟨gbar, hg⟩ := hsurj w
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨e.1.symm (maxProPMk 2 (GalK K) g), ?_⟩
  show nuUrKTwo B (e.1 (e.1.symm (maxProPMk 2 (GalK K) g))) = w
  rw [e.1.apply_symm_apply, nuUrKTwo_maxProPMk]
  exact hg

variable {a : ℚ_[2]}

/-- `ν_ur` is onto at a ramified quadratic field, `√a` being a uniformizer. -/
theorem mpcRow_surjective_nu_ur_quadField [CompactSpace (GalK (quadField a))]
    [TotallyDisconnectedSpace (GalK (quadField a))] (ha : ¬ IsSquare a) (hodd : Odd a.valuation)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (B : MarkedRecip Rec (quadField a)) :
    Function.Surjective B.nu_ur :=
  B.surjective_nu_ur_of_uniformizer (fieldUni_rootUnit ha) (fieldUni_rootUnit_lt_one ha hna)
    (fieldUni_rootUnit_max ha hodd hna)

end Surjectivity

/-! ## §4 The two rows: what the arithmetic still owes, named

Wave 79 left each procyclic field one `Prop` with four conjuncts (the level and three
congruences), all asserted **at wave 77's chosen oriented equivalence**, which is a `Classical`
choice about which nothing is known.  Three of the four can be restated as statements about the
bundle alone, with no equivalence in sight, and that is what this section does:

| conjunct | equivalence-free form | what it is |
| --- | --- | --- |
| `B.r = 1` | `MpcNoUnitKerChi` (plus §1's `B.r ≤ 1`) | `(2, ±10)₂ = −1` |
| `ν'(B̄) ≡ p` | `MpcLambdaOne B (−1) p` | `λ(−1) = p`, i.e. `(−2, ±10)₂` |
| `ν'(D̄) ≡ 1` | `MpcLambdaOne B (mUnit 2) 1` | `λ(5) = 1`, i.e. `(5, ±10)₂ = −1` |
| `ν'(C̄₀) = γ·2` | **none** | see below |

`MpcLambdaOne B u c` says every class of cyclotomic value `u` has `ν_ur`-value `≡ c (mod 2)`.
That is exactly the marked pair's `λ` at level one (`MarkedRecip.nuMod`/`λ`), and it is
well-posed for the same reason `λ` is: two classes with the same `χ` differ by a class in
`ker χ`, whose `ν` is `2`-divisible at level `1`.  It is also literally what
`FieldBranchSelector.Matches` calls `negOneVal` at `u = −1`.

**The pivot has no such form**, and that is a finding rather than an omission: `C̄₀` is one chosen
element of `ker χ_M`, so `ν'(C̄₀)` is not a function of `χ` at all.  What pins it is the *lower*
half of the level, `nu_ker_chi_ge`, together with a description of `ker χ_M` inside `D_M` that the
tree does not carry (§6 of the lane note spells out what is needed).  So the pivot stays as a
clause at the chosen equivalence, on both rows. -/

section RowInputs

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] {Rec : LocalReciprocity}

/-- **The level's one arithmetic input**, in the bundle's vocabulary: no class of `ker χ_K`
carries a unimodular `ν_ur`-value.  Wave 78 §2.3's `(2, ±10)₂ = −1` is exactly this: an element
of odd valuation whose norm is a power of `2` with unit part `1` would supply such a class. -/
def MpcNoUnitKerChi (B : MarkedRecip Rec K) : Prop :=
  ∀ g : GalKab K, chiCycKAb K g = 1 → ¬ IsUnit (toAdd (B.nu_ur g))

/-- **`λ(u) = c` at level one**: every class of cyclotomic value `u` has `ν_ur`-value congruent to
`c` modulo `2`.  This is the marked pair's `λ` with no marked pair built, and it is the
equivalence-free form of the two congruence clauses. -/
def MpcLambdaOne (B : MarkedRecip Rec K) (u : ℤ_[2]ˣ) (c : ℤ_[2]) : Prop :=
  ∀ g : GalKab K, chiCycKAb K g = u → ∃ y : ℤ_[2], toAdd (B.nu_ur g) = c + 2 * y

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **The level is not zero** once no `ker χ` class is unimodular: `nu_ker_chi_ge` at `y = 1`
would supply one. -/
theorem mpcRow_level_ne_zero {B : MarkedRecip Rec K} (h : MpcNoUnitKerChi B) : B.r ≠ 0 := by
  intro hr
  obtain ⟨g, hchi, hnu⟩ := B.nu_ker_chi_ge 1
  refine h g hchi ?_
  rw [hnu, hr, pow_zero, one_mul]
  exact isUnit_one

/-- **A `λ`-value transports to any marked generator with that cyclotomic value.**  The step that
makes the two congruence clauses independent of which oriented equivalence was chosen. -/
theorem mpcRow_congr_of_lambda {B : MarkedRecip Rec K} {α : ℕ}
    (e : OrientedContinuousMulEquiv (chiM α 0) (chiCycKTwo (K := K))) {u : ℤ_[2]ˣ} {c : ℤ_[2]}
    (h : MpcLambdaOne B u c) {x : (DM α 0 : Type)} (hx : chiM α 0 x = u) :
    ∃ y : ℤ_[2], toAdd (fieldUni_nuPullbackM B e x) = c + 2 * y := by
  obtain ⟨g, hg⟩ := maxProPMk_surjective (p := 2) (G := GalK K) (e.1 x)
  refine (h (toAbK K g) ?_).imp fun y hy => ?_
  · have hchi : chiCycKTwo (K := K) (e.1 x) = chiM α 0 x := e.2 x
    rw [← hg, chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at hchi
    exact hchi.trans hx
  · show toAdd (nuUrKTwo B (e.1 x)) = c + 2 * y
    rw [← hg, nuUrKTwo_maxProPMk]
    exact hy

end RowInputs

/-! ### §4.1 The `ε = false` row: two clauses, not three -/

section RowStatements

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`MpcRowData_sqrtTen` FROM THE LEVEL, ONE `λ`-VALUE AND THE PIVOT.**  The `D̄` congruence is
gone: at `p = 0` it follows from §2's rigidity.  So `ℚ₂(√10)`'s remaining input is
`λ(−1) = 0` plus the pivot plus `(2, 10)₂ = −1`, and no clause about `D̄`. -/
theorem mpcRow_rowData_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    (hlev : MpcNoUnitKerChi B) (hneg : MpcLambdaOne B (-1) 0)
    (hpivot : ∃ γ : ℤ_[2]ˣ,
      toAdd (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtTen B) (dmC 2 0))
        = (γ : ℤ_[2]) * 2 ^ 1) :
    MpcRowData_sqrtTen B := by
  have hr : B.r = 1 :=
    le_antisymm (mpcRow_level_le_one_sqrtTen B)
      (Nat.one_le_iff_ne_zero.2 (mpcRow_level_ne_zero hlev))
  refine ⟨hr, hpivot, ?_, ?_⟩
  · have hsurj : Function.Surjective (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtTen B)) :=
      mpcRow_surjective_nuPullbackM B _
        (mpcRow_surjective_nu_ur_quadField not_isSquare_ten mpcRow_valuation_ten_odd
          mpcRow_norm_ten B)
    obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda (fieldId_chosenEquivM_sqrtTen B) hneg
      (chiM_dmB 2 0)
    obtain ⟨w, hw⟩ := mpcRow_dmD_odd_of_dmB_even (α := 2) one_le_two _ hsurj
      (mpcCert_chiKerLevel_of_level B hr _) ⟨y, by rw [hy]; ring⟩
    exact ⟨w, by rw [hw, pow_one]⟩
  · obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda (fieldId_chosenEquivM_sqrtTen B) hneg
      (chiM_dmB 2 0)
    refine ⟨y, ?_⟩
    rw [hy, pow_one]
    norm_num [GQ2.Dyadic.p, GQ2.Dyadic.epsVal]

/-- **THE `sqrtTen` BRANCH DATUM over the reduced input.**  `mpcCert_genAsmBranch_sqrtTen` with
wave 79's `Prop` replaced by the three named arithmetic facts. -/
theorem mpcRow_genAsmBranch_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    (hlev : MpcNoUnitKerChi B) (hneg : MpcLambdaOne B (-1) 0)
    (hpivot : ∃ γ : ℤ_[2]ˣ,
      toAdd (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtTen B) (dmC 2 0))
        = (γ : ℤ_[2]) * 2 ^ 1) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0 :=
  mpcCert_genAsmBranch_sqrtTen B (mpcRow_rowData_sqrtTen B hlev hneg hpivot)

/-- **`MpcRowData_sqrtNegTen` FROM THE LEVEL, TWO `λ`-VALUES AND THE PIVOT.**  At `p = 1` the
rigidity argument gives nothing (`ν'(B̄)` is odd there, so it already accounts for surjectivity),
and the `D̄` congruence stays as its own arithmetic input `λ(5) = 1`. -/
theorem mpcRow_rowData_sqrtNegTen [T2Space (GalK KSqrtNegTen)] (B : MarkedRecip R KSqrtNegTen)
    (hlev : MpcNoUnitKerChi B) (hneg : MpcLambdaOne B (-1) 1)
    (hgen : MpcLambdaOne B (mUnit 2) 1)
    (hpivot : ∃ γ : ℤ_[2]ˣ,
      toAdd (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtNegTen B) (dmC 2 0))
        = (γ : ℤ_[2]) * 2 ^ 1) :
    MpcRowData_sqrtNegTen B := by
  have hr : B.r = 1 :=
    le_antisymm (mpcRow_level_le_one_sqrtNegTen B)
      (Nat.one_le_iff_ne_zero.2 (mpcRow_level_ne_zero hlev))
  refine ⟨hr, hpivot, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda (fieldId_chosenEquivM_sqrtNegTen B) hgen
      (chiM_dmD 2 0)
    exact ⟨y, by rw [hy, pow_one]⟩
  · obtain ⟨y, hy⟩ := mpcRow_congr_of_lambda (fieldId_chosenEquivM_sqrtNegTen B) hneg
      (chiM_dmB 2 0)
    refine ⟨y, ?_⟩
    rw [hy, pow_one]
    norm_num [GQ2.Dyadic.p, GQ2.Dyadic.epsVal]

/-- **THE `sqrtNegTen` BRANCH DATUM over the reduced input.** -/
theorem mpcRow_genAsmBranch_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip R KSqrtNegTen) (hlev : MpcNoUnitKerChi B) (hneg : MpcLambdaOne B (-1) 1)
    (hgen : MpcLambdaOne B (mUnit 2) 1)
    (hpivot : ∃ γ : ℤ_[2]ˣ,
      toAdd (fieldUni_nuPullbackM B (fieldId_chosenEquivM_sqrtNegTen B) (dmC 2 0))
        = (γ : ℤ_[2]) * 2 ^ 1) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 :=
  mpcCert_genAsmBranch_sqrtNegTen B (mpcRow_rowData_sqrtNegTen B hlev hneg hgen hpivot)

end RowStatements

/-! ## §5 The determinant binder, wired

`GaussZ/FinalDK.lean` §7's `affineDeterminant_galK` is the `K` clone of the (83)-evaluation
bridge, and its §8 `example` produces `KSupply.determinant`'s field type verbatim.  **Verified
here**: the two theorems below are that example promoted to named declarations, and then used to
*remove the field* from both records that carry it.  There is no statement gap; what was missing
was only that no declaration named the composite, so every consumer still had to supply
`determinant` as a binder.

The two record builders are the point of the ticket:

* `mpcRow_kSupply_of_counting`: a `KSupply` from `exactLifting` and `stokes` and **no**
  `determinant` argument;
* `mpcRow_genAsmRowResidual_of_counting`: a `GenAsmRowResidual` from `exactLifting`, `stokes`,
  `cand` and **no** `determinant` argument.

Both take `params : FieldParameters` with its two pins and `ramifiedData`, which is not a
weakening: `FieldParameters` carries the `f ∣ n` clause no lane has attached to a
`DyadicUnitFiltration`, and `ramifiedData` is AX3's field-side interface, which
`DyadicLocalInput` already carries as a constructor argument.  At the `GenAsmRowResidual` layer
the numerics pins vanish outright (`standardNumerics` makes them `rfl`), which is why the second
builder has two fewer hypotheses than the first.
-/

section DeterminantWiring

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **`KSupply.determinant`, as a named theorem.**  `GaussZ/FinalDK.lean` §8's acceptance
`example`, promoted: the field type of `KSupply.determinant` produced by the committed bridge.
Nothing is transported and nothing is re-proved; the point is that the composite now has a name,
so a `KSupply` can be built without the field. -/
theorem mpcRow_determinant_of_bridge (T : OrientedTameQuotientK B FF) {n : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (pro2 : ContinuousMonoidHom (GalK K) P)
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g))
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF) (hdeg : Module.finrank ℚ_[2] K = n)
    (hgu : ∀ m : ℕ, SN.gaussUnram m = (-1 : ℤ) ^ n * 2 ^ (n * m))
    (hgr : ∀ m : ℕ, SN.gaussRam m = (2 : ℤ) ^ (n * m))
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg) (rho : ContinuousMonoidHom ↥(GalKsub K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    AffineDeterminantCertificate (galKProfinite K) n (qOf K FF) P nuP SN
      T.tameFK pro2 (fun g => T.compatF_K pro2 nuP nu_compat g) (smulZmod2GalK K) :=
  affineDeterminant_galK K params params_n params_qK hdeg hgu hgr T.tameFK T.tameFK_surjective
    pro2 (fun g => T.compatF_K pro2 nuP nu_compat g) ramifiedData

/-- **THE SUPPLY PACKAGE WITHOUT ITS DETERMINANT BINDER.**  A `KSupply` from the two genuinely
unowned counting clauses (`exactLifting`, `stokes`) alone: ledger field 6 is discharged in place
by the committed bridge.  This is what "the `determinant` obligation is wired" means at the
record. -/
noncomputable def mpcRow_kSupply_of_counting (T : OrientedTameQuotientK B FF) {n : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n} (hdeg : Module.finrank ℚ_[2] K = n)
    (hhom : SN.homScalar = 2 ^ (n + 2)) (pro2 : ContinuousMonoidHom (GalK K) P)
    (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g))
    (exactLifting : ExactLiftingSemantics (galKProfinite K) n (qOf K FF) P nuP SN)
    (stokes : StokesDualityCertificate (galKProfinite K) n (qOf K FF) P nuP SN (smulZmod2GalK K))
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF)
    (hgu : ∀ m : ℕ, SN.gaussUnram m = (-1 : ℤ) ^ n * 2 ^ (n * m))
    (hgr : ∀ m : ℕ, SN.gaussRam m = (2 : ℤ) ^ (n * m))
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg) (rho : ContinuousMonoidHom ↥(GalKsub K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    KSupply T n P hP nuP SN where
  hdeg := hdeg
  hhom := hhom
  pro2 := pro2
  hpro2 := hpro2
  ker_pro2 := ker_pro2
  nu_compat := nu_compat
  exactLifting := exactLifting
  stokes := stokes
  determinant := mpcRow_determinant_of_bridge T pro2 nu_compat params params_n params_qK hdeg
    hgu hgr ramifiedData

/-- **THE ROW RESIDUAL WITHOUT ITS DETERMINANT BINDER.**  The same wiring at
`GeneralAssembly.GenAsmRowResidual`, where the numerics are `standardNumerics G.degree` and the
two Gauss pins are therefore `rfl` (`gaussUnram_standard`, `gaussRam_standard`).  So the general
row residual costs **three** blocks, not four: the two counting clauses and `cand`. -/
noncomputable def mpcRow_genAsmRowResidual_of_counting {G : GenAsmBranch K B}
    (T : OrientedTameQuotientK B FF)
    (exactLifting : ExactLiftingSemantics (galKProfinite K) G.degree (qOf K FF) G.core G.nuP
      (standardNumerics G.degree))
    (stokes : StokesDualityCertificate (galKProfinite K) G.degree (qOf K FF) G.core G.nuP
      (standardNumerics G.degree) (smulZmod2GalK K))
    (cand : WordCertificate G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
      (standardNumerics G.degree))
    (params : FieldParameters) (params_n : params.n = G.degree)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg) (rho : ContinuousMonoidHom ↥(GalKsub K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GenAsmRowResidual G T where
  exactLifting := exactLifting
  stokes := stokes
  determinant := mpcRow_determinant_of_bridge T G.pro2 G.realization.nu_compat params params_n
    params_qK G.hdeg (gaussUnram_standard G.degree) (gaussRam_standard G.degree) ramifiedData
  cand := cand

end DeterminantWiring

end

end GQ2.Dyadic.Instances.MpcRow
