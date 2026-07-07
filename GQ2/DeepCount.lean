import GQ2.DeepDualityK

/-!
# The (H4) structural count  (ticket P-15f7, counting half)

The single remaining input of `hsharp`: `#(M ⧸ Deep) ≤ #E` for `M = H¹(G_k, 𝔽₂)`,
`Deep = deepClassesSubgroup = kummerDepth (e+1)`, `E = midClassesSubgroup = kummerDepth e`.
Everything derives from the EXISTING B13 bundle (`DyadicUnitFiltration`) — no clause
extension (derivability audit: `docs/p15f-handoff.md` §8, session 4).

This file (increment 1) provides the k-level foundations:

* `exists_sq_of_kummerClassK_eq_zero` — **the Kummer kernel**: class-zero units are squares
  (`B¹(G_k, 𝔽₂) = 0` since the action is trivial, so class-zero forces the cocycle to
  vanish, i.e. `G_k` fixes `sqrtCl a`, i.e. `sqrtCl a ∈ k`);
* `kummerClassK_mem_midClasses` / `coe_kummerDepth_mid` — stage `e` of the Kummer depth
  filtration IS the mid classes (the `≤`-mirror of `coe_kummerDepth_deep`; no discreteness
  upgrade needed since mid = `‖a−1‖ ≤ ‖2‖ = ‖π‖^e` on the nose);
* `norm_step_down` — the discreteness step (`x ∈ k`, `‖x‖ < ‖π‖^i ⟹ ‖x‖ ≤ ‖π‖^{i+1}`),
  extracted from `coe_kummerDepth_deep`;
* `norm_sq_sub_one` / `norm_sq_sub_one_le_succ_of_odd` — **square depths are even below
  `2e`**: `‖w² − 1‖ = ‖w − 1‖²` or `‖w² − 1‖ ≤ ‖4‖`, hence a square lying in `U_j` for odd
  `j ≤ 2e − 1` lies in `U_{j+1}` (the odd-level-fullness workhorse).

All std-3 sorry-free axiom-free.  Ticket: P-15f7 (`docs/tickets.md`); plan:
`docs/p15f-handoff.md` §8 session-4 update.
-/

namespace GQ2

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section KummerKernel

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- **The Kummer kernel** (converse of `kummerClassK_eq_zero_of_sq`): a unit of `k` with
vanishing Kummer class is a square in `k`.  `B¹(G_k, 𝔽₂) = 0` because the coefficient action
is trivial (`δ⁰m = g•m − m = 0`), so class-zero forces the COCYCLE to vanish pointwise:
`G_k` fixes `sqrtCl a`, hence `sqrtCl a ∈ ℚ̄₂^{G_k} = k` by the Galois correspondence. -/
theorem exists_sq_of_kummerClassK_eq_zero (a : (↥k)ˣ) (h : kummerClassK k a = 0) :
    ∃ w : ↥k, w ^ 2 = (a : ↥k) := by
  -- class-zero ⟹ the cocycle is a coboundary `δ⁰ m`
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp h
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨m, hm⟩ := hmem
  -- with the trivial action `δ⁰ m ≡ m − m = 0`, so the cocycle vanishes: `G_k` fixes the root
  have hfix : ∀ g ∈ k.fixingSubgroup,
      g • GQ2.sqrtCl ((a : ↥k) : ℚ̄₂) = GQ2.sqrtCl ((a : ↥k) : ℚ̄₂) := by
    intro g hg
    have happ := congrFun hm (⟨g, hg⟩ : k.fixingSubgroup)
    have hview : m - m = Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : ↥k) : ℚ̄₂))
        ((⟨g, hg⟩ : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) := happ
    rw [sub_self] at hview
    by_contra hne
    have h1 := hview.symm
    simp only [Kummer.kummerCocycleFun] at h1
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  have hmemk : ∀ s : ℚ̄₂, (∀ g ∈ k.fixingSubgroup, g • s = s) → s ∈ k := by
    intro s hsfix
    rw [← InfiniteGalois.fixedField_fixingSubgroup k]
    exact (IntermediateField.mem_fixedField_iff _ _).mpr hsfix
  refine ⟨⟨GQ2.sqrtCl ((a : ↥k) : ℚ̄₂), hmemk _ hfix⟩, ?_⟩
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact GQ2.sqrtCl_sq _

end KummerKernel

section MidStage

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- **Mid units give mid classes** — the `≤`-mirror of `kummerClassK_mem_deepClasses`.
Witnesses: `A := a`, `β := sqrtCl A`, `b := (A − 1)/2`. -/
theorem kummerClassK_mem_midClasses (a : (↥k)ˣ)
    (ha : ‖((a : ↥k) : ℚ̄₂) - 1‖ ≤ ‖(2 : ℚ̄₂)‖) :
    kummerClassK k a ∈ midClassesSubgroup k.fixingSubgroup := by
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
  · -- `‖b‖ ≤ 1`
    rw [norm_div, div_le_one h2pos]
    exact ha
  · -- the restricted Kummer cocycle of `sqrtCl A` presents `kummerClassK k a`
    have hmem : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : ↥k) : ℚ̄₂))
          (n : Kummer.GaloisGroup ℚ_[2])) ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      (GQ2.kummerZ1On k.fixingSubgroup (GQ2.sqrtCl_sq _) (GQ2.sqrtCl_ne_zero hA0) hfix).2
    rw [H1ofFun_of_mem hmem]
    unfold GQ2.kummerClassK
    congr 1

/-- **Stage `e` of the Kummer depth filtration is exactly the mid classes** — the `≤`-mirror
of `coe_kummerDepth_deep`.  Forward: `‖a − 1‖ ≤ ‖π‖^e = ‖2‖` is mid; backward: a mid class is
`kummerClassK` of a unit with `‖a − 1‖ ≤ ‖2‖` (`midClass_eq_kummerClassK`), and mid IS
depth-`e` on the nose (no discreteness upgrade). -/
theorem coe_kummerDepth_mid [FiniteDimensional ℚ_[2] k]
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (kummerDepth k π e : Set (H1 k.fixingSubgroup (ZMod 2)))
      = (midClassesSubgroup k.fixingSubgroup : Set (H1 k.fixingSubgroup (ZMod 2))) := by
  have h2lt1 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂) (2 : ℚ_[2])]
    exact Padic.norm_p_lt_one
  ext ξ
  constructor
  · -- depth `e` ⟹ mid
    rintro ⟨a, ha, rfl⟩
    exact kummerClassK_mem_midClasses k a (by rw [he]; exact ha.2)
  · -- mid ⟹ depth `e`, via the bridge
    intro hξ
    obtain ⟨a, ha, rfl⟩ := midClass_eq_kummerClassK k hξ
    have hA1 : ‖((a : ↥k) : ℚ̄₂)‖ = 1 := by
      have hlt1 : ‖((a : ↥k) : ℚ̄₂) - 1‖ < 1 := lt_of_le_of_lt ha h2lt1
      rw [show ((a : ↥k) : ℚ̄₂) = (((a : ↥k) : ℚ̄₂) - 1) + 1 by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by rw [norm_one]; exact ne_of_lt hlt1),
        norm_one, max_eq_right hlt1.le]
    exact ⟨a, ⟨hA1, by rw [← he]; exact ha⟩, rfl⟩

end MidStage

/-! ## The square-depth parity core

`w² − 1 = (w − 1)(w + 1)` with `w + 1 = (w − 1) + 2`: by the ultrametric, either
`‖w − 1‖ > ‖2‖` and `‖w² − 1‖ = ‖w − 1‖²` (an EVEN `π`-power), or `‖w² − 1‖ ≤ ‖4‖`
(past depth `2e`).  Consequence: no square sits at an odd depth `< 2e` — the injectivity
half of the odd-level class-gr fullness. -/

section SquareParity

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- **The discreteness step-down** (extracted from `coe_kummerDepth_deep`): a `k`-rational
element strictly below depth `i` is at depth `i + 1`. -/
theorem norm_step_down (hπk : π ∈ k) (hπ0 : π ≠ 0)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {x : ℚ̄₂} (hx : x ∈ k) {i : ℕ} (h : ‖x‖ < ‖π‖ ^ i) : ‖x‖ ≤ ‖π‖ ^ (i + 1) := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hπipos : (0 : ℝ) < ‖π‖ ^ i := pow_pos hπpos i
  have hy : ‖x / π ^ i‖ ≤ ‖π‖ := by
    refine hπmax _ (div_mem hx (pow_mem hπk i)) ?_
    rw [norm_div, norm_pow, div_lt_one hπipos]
    exact h
  have hπe0 : π ^ i ≠ 0 := pow_ne_zero i hπ0
  calc ‖x‖ = ‖x / π ^ i‖ * ‖π‖ ^ i := by
        rw [norm_div, norm_pow, div_mul_cancel₀ _ (ne_of_gt hπipos)]
    _ ≤ ‖π‖ * ‖π‖ ^ i := mul_le_mul_of_nonneg_right hy (le_of_lt hπipos)
    _ = ‖π‖ ^ (i + 1) := by rw [pow_succ, mul_comm]

/-- **The square-depth dichotomy**: `‖w² − 1‖ = ‖w − 1‖²` or `‖w² − 1‖ ≤ ‖4‖`. -/
theorem norm_sq_sub_one (w : ℚ̄₂) :
    ‖w ^ 2 - 1‖ = ‖w - 1‖ ^ 2 ∨ ‖w ^ 2 - 1‖ ≤ ‖(4 : ℚ̄₂)‖ := by
  have hfac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have hplus : w + 1 = (w - 1) + 2 := by ring
  rcases lt_trichotomy ‖w - 1‖ ‖(2 : ℚ̄₂)‖ with hlt | heq | hgt
  · -- `‖w−1‖ < ‖2‖`: `‖w+1‖ = ‖2‖`, so `‖w²−1‖ = ‖w−1‖·‖2‖ < ‖4‖`
    right
    have hp : ‖w + 1‖ = ‖(2 : ℚ̄₂)‖ := by
      rw [hplus, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt),
        max_eq_right hlt.le]
    rw [hfac, norm_mul, hp, show (4 : ℚ̄₂) = 2 * 2 by norm_num, norm_mul]
    exact mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _)
  · -- `‖w−1‖ = ‖2‖`: `‖w+1‖ ≤ ‖2‖`, so `‖w²−1‖ ≤ ‖4‖`
    right
    have hp : ‖w + 1‖ ≤ ‖(2 : ℚ̄₂)‖ := by
      rw [hplus]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (by rw [heq, max_self])
    rw [hfac, norm_mul, heq, show (4 : ℚ̄₂) = 2 * 2 by norm_num, norm_mul]
    exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  · -- `‖w−1‖ > ‖2‖`: `‖w+1‖ = ‖w−1‖`, so `‖w²−1‖ = ‖w−1‖²`
    left
    have hp : ‖w + 1‖ = ‖w - 1‖ := by
      rw [hplus, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hgt),
        max_eq_left hgt.le]
    rw [hfac, norm_mul, hp, sq]

/-- **No square at an odd depth `< 2e`**: if `w²` is within `‖π‖^j` of `1` for ODD
`j ≤ 2e − 1`, it is within `‖π‖^{j+1}` (the depth skips the odd level).  Even case of the
dichotomy: an even power cannot land at exactly an odd level (discreteness step-down on
`w − 1`); `≤ ‖4‖`-case: `‖4‖ = ‖π‖^{2e} ≤ ‖π‖^{j+1}`. -/
theorem norm_sq_sub_one_le_succ_of_odd (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {w : ↥k} {t : ℕ} (hj2e : 2 * t + 1 ≤ 2 * e - 1) (he_pos : 1 ≤ e)
    (h : ‖((w : ℚ̄₂)) ^ 2 - 1‖ ≤ ‖π‖ ^ (2 * t + 1)) :
    ‖((w : ℚ̄₂)) ^ 2 - 1‖ ≤ ‖π‖ ^ (2 * t + 2) := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  rcases norm_sq_sub_one ((w : ℚ̄₂)) with hcase | hcase
  · -- even case: `‖w²−1‖ = ‖w−1‖²`
    have hs : ‖(w : ℚ̄₂) - 1‖ ^ 2 ≤ ‖π‖ ^ (2 * t + 1) := by rw [← hcase]; exact h
    -- `‖w−1‖² ≤ ‖π‖^{2t+1} < ‖π‖^{2t}` forces `‖w−1‖ < ‖π‖^t`, then step-down
    have hlt : ‖(w : ℚ̄₂) - 1‖ < ‖π‖ ^ t := by
      have h1 : ‖(w : ℚ̄₂) - 1‖ ^ 2 < (‖π‖ ^ t) ^ 2 := by
        calc ‖(w : ℚ̄₂) - 1‖ ^ 2 ≤ ‖π‖ ^ (2 * t + 1) := hs
          _ < ‖π‖ ^ (2 * t) := by
              rw [pow_succ]
              calc ‖π‖ ^ (2 * t) * ‖π‖ < ‖π‖ ^ (2 * t) * 1 :=
                    mul_lt_mul_of_pos_left hπ1 (pow_pos hπpos _)
                _ = ‖π‖ ^ (2 * t) := mul_one _
          _ = (‖π‖ ^ t) ^ 2 := by rw [← pow_mul, mul_comm]
      exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt (pow_pos hπpos t)) h1
    have hstep : ‖(w : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ (t + 1) :=
      norm_step_down k π hπk hπ0 hπmax (sub_mem (w : ↥k).2 (one_mem k)) hlt
    rw [hcase]
    calc ‖(w : ℚ̄₂) - 1‖ ^ 2 ≤ (‖π‖ ^ (t + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hstep 2
      _ = ‖π‖ ^ (2 * t + 2) := by rw [← pow_mul]; ring_nf
  · -- past-`2e` case: `‖4‖ = ‖π‖^{2e} ≤ ‖π‖^{2t+2}`
    refine le_trans hcase ?_
    have h4 : ‖(4 : ℚ̄₂)‖ = ‖π‖ ^ (2 * e) := by
      rw [show (4 : ℚ̄₂) = 2 * 2 by norm_num, norm_mul, he, ← pow_add, two_mul]
    rw [h4]
    refine pow_le_pow_of_le_one (norm_nonneg π) hπ1.le ?_
    omega

end SquareParity

end GQ2
