import GQ2.LocalKummer
import GQ2.UnitFiltration

/-!
# The Kummer depth filtration on `H¹(G_k, 𝔽₂)`  (ticket P-15f6, brick i)

The image of the unit filtration `U^{(j)}(k)` (`GQ2/UnitFiltration.lean`) under the Kummer
class map, as a decreasing chain of additive subgroups of `H¹(G_k, 𝔽₂)` — the filtration whose
graded `Hom`-counts (P-15f5's engine) produce `DeepKummerData.card_fam`/`card_deepFam` for the
Lemma-6.17 dimension clause.

* `kummerDepth k π j` — classes `kummerClassK k a` of depth-`j` units; an `AddSubgroup` by the
  banked Kummer-class algebra (`kummerClassK_mul`/`_one`, 2-torsion of `H¹`);
* `kummerDepth_antitone` — decreasing in `j`;
* `kummerDepth_eq_bot` — the filtration dies at `j = 2e + 1` (`U^{(2e+1)} ⊆ (k^×)²` — the
  Local Square Theorem `sq_of_near_one` + `kummerClassK_sq`), the endpoint for the
  P-15f5 iteration;
* `kummerClassK_mem_deepClasses` / `coe_kummerDepth_deep` — stage `e + 1` **is** the deep
  classes: `(kummerDepth k π (e+1) : Set _) = LocalKummer.deepClasses k.fixingSubgroup`.
  (In particular `deepClasses` is an additive subgroup — the form P-15f2's orbit analysis and
  the `card_deepFam` count consume.)

The B13 inputs — the uniformizer `π ∈ k`, `‖2‖ = ‖π‖^e`, `‖π‖ < 1`, and value-group
discreteness `hπ_max` — enter only as **hypotheses** (the consumer pulls them from the
`GQ2.dyadicUnitFiltration` bundle), so this file is std-3 sorry-free and axiom-free.
-/

namespace GQ2

open ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section KummerFiltration

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- **The depth-`j` Kummer classes**: images under `kummerClassK` of the depth-`j` units
`U^{(j)}(k)`.  An additive subgroup by the Kummer-class algebra (`[ab] = [a] + [b]`,
`[1] = 0`, and `H¹(G_k, 𝔽₂)` is 2-torsion so negation is the identity). -/
def kummerDepth (j : ℕ) : AddSubgroup (H1 k.fixingSubgroup (ZMod 2)) where
  carrier := {ξ | ∃ a : (↥k)ˣ, a ∈ depthUnits k π j ∧ kummerClassK k a = ξ}
  zero_mem' := ⟨1, one_mem _, kummerClassK_one k⟩
  add_mem' := by
    rintro ξ η ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, kummerClassK_mul k a b⟩
  neg_mem' := by
    rintro ξ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (neg_eq_of_add_eq_zero_left (h1_add_self (kummerClassK k a))).symm⟩

/-- Membership in `kummerDepth` unfolded. -/
theorem mem_kummerDepth_iff {j : ℕ} {ξ : H1 k.fixingSubgroup (ZMod 2)} :
    ξ ∈ kummerDepth k π j ↔ ∃ a : (↥k)ˣ, a ∈ depthUnits k π j ∧ kummerClassK k a = ξ :=
  Iff.rfl

/-- The Kummer depth filtration is decreasing. -/
theorem kummerDepth_antitone (hπ1 : ‖π‖ ≤ 1) {i j : ℕ} (hij : i ≤ j) :
    kummerDepth k π j ≤ kummerDepth k π i := by
  rintro ξ ⟨a, ha, rfl⟩
  exact ⟨a, depthUnits_antitone k π hπ1 hij ha, rfl⟩

/-- Squares have trivial Kummer class (unit-of-a-square form): if `(a : ↥k) = w ^ 2` then
`[a] = 0` — package the root as a unit and apply `kummerClassK_mul_self`-style algebra. -/
theorem kummerClassK_eq_zero_of_sq (a : (↥k)ˣ) (w : ↥k) (hw : w ^ 2 = (a : ↥k)) :
    kummerClassK k a = 0 := by
  have hw0 : w ≠ 0 := by
    intro h0
    apply a.ne_zero
    rw [← hw, h0]
    ring
  have hau : a = Units.mk0 w hw0 * Units.mk0 w hw0 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, ← sq, hw]
  rw [hau]
  exact kummerClassK_mul_self k (Units.mk0 w hw0)

/-- **The filtration endpoint** (`U^{(2e+1)} ⊆ (k^×)²`, the Local Square Theorem): past depth
`2e` every Kummer class dies.  The P-15f5 iteration terminates here
(`card_equivHoms_of_subsingleton`). -/
theorem kummerDepth_eq_bot [FiniteDimensional ℚ_[2] k]
    (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {j : ℕ} (hj : 2 * e + 1 ≤ j) :
    kummerDepth k π j = ⊥ := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  rw [eq_bot_iff]
  rintro ξ ⟨a, ha, rfl⟩
  have h4 : ‖(4 : ℚ̄₂)‖ = ‖π‖ ^ (2 * e) := by
    rw [show (4 : ℚ̄₂) = 2 * 2 by norm_num, norm_mul, he, ← pow_add, two_mul]
  have hlt : ‖((a : ↥k) : ℚ̄₂) - 1‖ < ‖(4 : ℚ̄₂)‖ := by
    refine lt_of_le_of_lt (le_trans ha.2 (pow_le_pow_of_le_one (norm_nonneg π) hπ1.le hj)) ?_
    rw [h4]
    calc ‖π‖ ^ (2 * e + 1) = ‖π‖ ^ (2 * e) * ‖π‖ := by rw [pow_succ]
      _ < ‖π‖ ^ (2 * e) * 1 := by
          exact mul_lt_mul_of_pos_left hπ1 (pow_pos hπpos _)
      _ = ‖π‖ ^ (2 * e) := mul_one _
  obtain ⟨w, hw⟩ := sq_of_near_one k (a : ↥k) hlt
  rw [AddSubgroup.mem_bot]
  exact kummerClassK_eq_zero_of_sq k a w hw

/-- **Deep units give deep classes** (the converse of `LocalKummer.deepClass_eq_kummerClassK`):
the Kummer class of a unit with `‖a − 1‖ < ‖2‖` lies in `deepClasses`.  Witnesses: `A := a`,
`β := sqrtCl A`, `b := (A − 1)/2`. -/
theorem kummerClassK_mem_deepClasses (a : (↥k)ˣ)
    (ha : ‖((a : ↥k) : ℚ̄₂) - 1‖ < ‖(2 : ℚ̄₂)‖) :
    kummerClassK k a ∈ LocalKummer.deepClasses k.fixingSubgroup := by
  have hA0 : ((a : ↥k) : ℚ̄₂) ≠ 0 := unitCoe_ne_zero k a
  have hfix : ∀ g ∈ k.fixingSubgroup, g • ((a : ↥k) : ℚ̄₂) = ((a : ↥k) : ℚ̄₂) :=
    fun g hg => fixingSubgroup_smul k hg (a : ↥k)
  have h2pos : (0 : ℝ) < ‖(2 : ℚ̄₂)‖ := norm_pos_iff.mpr two_ne_zero
  refine ⟨((a : ↥k) : ℚ̄₂), GQ2.sqrtCl ((a : ↥k) : ℚ̄₂),
    ⟨hA0, hfix, (((a : ↥k) : ℚ̄₂) - 1) / 2, ?_, ?_, ?_⟩,
    GQ2.sqrtCl_sq _, GQ2.sqrtCl_ne_zero hA0, ?_⟩
  · -- the shift `b = (A − 1)/2` is `G_k`-fixed
    intro g hg
    have hgA := hfix g hg
    rw [AlgEquiv.smul_def] at hgA ⊢
    rw [map_div₀, map_sub, map_one, map_ofNat, hgA]
  · -- `A = 1 + 2 b`
    field_simp
    ring
  · -- `‖b‖ < 1`
    rw [norm_div, div_lt_one h2pos]
    exact ha
  · -- the restricted Kummer cocycle of `sqrtCl A` presents `kummerClassK k a`
    have hmem : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : ↥k) : ℚ̄₂))
          (n : Kummer.GaloisGroup ℚ_[2])) ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      (GQ2.kummerZ1On k.fixingSubgroup (GQ2.sqrtCl_sq _) (GQ2.sqrtCl_ne_zero hA0) hfix).2
    rw [H1ofFun_of_mem hmem]
    unfold GQ2.kummerClassK
    congr 1

/-- **Stage `e + 1` of the Kummer depth filtration is exactly the deep classes** — given the
B13 bundle data (uniformizer `π ∈ k`, discreteness `hπ_max`, `‖2‖ = ‖π‖^e`).  Forward:
`‖a − 1‖ ≤ ‖π‖^{e+1} < ‖π‖^e = ‖2‖` is deep; backward: a deep class is `kummerClassK` of a
unit with `‖a − 1‖ < ‖2‖` (`deepClass_eq_kummerClassK`), and discreteness upgrades the strict
bound to `≤ ‖π‖^{e+1}`.  In particular `deepClasses` is an additive subgroup. -/
theorem coe_kummerDepth_deep [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he_pos : 1 ≤ e) (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (kummerDepth k π (e + 1) : Set (H1 k.fixingSubgroup (ZMod 2)))
      = LocalKummer.deepClasses k.fixingSubgroup := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hπepos : (0 : ℝ) < ‖π‖ ^ e := pow_pos hπpos e
  have hstep : ‖π‖ ^ (e + 1) < ‖(2 : ℚ̄₂)‖ := by
    rw [he, pow_succ]
    calc ‖π‖ ^ e * ‖π‖ < ‖π‖ ^ e * 1 := mul_lt_mul_of_pos_left hπ1 hπepos
      _ = ‖π‖ ^ e := mul_one _
  ext ξ
  constructor
  · -- depth `e+1` ⟹ deep
    rintro ⟨a, ha, rfl⟩
    exact kummerClassK_mem_deepClasses k a (lt_of_le_of_lt ha.2 hstep)
  · -- deep ⟹ depth `e+1`, via the bridge + discreteness
    intro hξ
    obtain ⟨a, ha, rfl⟩ := LocalKummer.deepClass_eq_kummerClassK k hξ
    have h2lt1 : ‖(2 : ℚ̄₂)‖ < 1 := by
      rw [he]
      exact pow_lt_one₀ (norm_nonneg π) hπ1 (by omega)
    have hA1 : ‖((a : ↥k) : ℚ̄₂)‖ = 1 := by
      have hlt1 : ‖((a : ↥k) : ℚ̄₂) - 1‖ < 1 := ha.trans h2lt1
      rw [show ((a : ↥k) : ℚ̄₂) = (((a : ↥k) : ℚ̄₂) - 1) + 1 by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by rw [norm_one]; exact ne_of_lt hlt1),
        norm_one, max_eq_right hlt1.le]
    refine ⟨a, ⟨hA1, ?_⟩, rfl⟩
    -- discreteness: `‖A − 1‖ < ‖π‖^e ⟹ ‖A − 1‖ ≤ ‖π‖^{e+1}`
    have hy : ‖(((a : ↥k) : ℚ̄₂) - 1) / π ^ e‖ ≤ ‖π‖ := by
      refine hπmax _ ?_ ?_
      · exact div_mem (sub_mem (by exact_mod_cast (a : ↥k).2) (one_mem k))
          (pow_mem hπk e)
      · rw [norm_div, norm_pow, div_lt_one hπepos, ← he]
        exact ha
    have hπe0 : π ^ e ≠ 0 := pow_ne_zero e hπ0
    calc ‖((a : ↥k) : ℚ̄₂) - 1‖
        = ‖(((a : ↥k) : ℚ̄₂) - 1) / π ^ e‖ * ‖π‖ ^ e := by
          rw [norm_div, norm_pow, div_mul_cancel₀ _ (ne_of_gt hπepos)]
      _ ≤ ‖π‖ * ‖π‖ ^ e := mul_le_mul_of_nonneg_right hy (le_of_lt hπepos)
      _ = ‖π‖ ^ (e + 1) := by rw [pow_succ, mul_comm]

end KummerFiltration

end GQ2
