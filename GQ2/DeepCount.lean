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

/-! ## The graded squaring `U_i/U_{i+1} → U_{2i}/U_{2i+1}` and the even-level collapse

Squaring doubles depth for `i ≤ e` (`w² − 1 = (w−1)(w+1)`, `‖w+1‖ ≤ max(‖w−1‖, ‖2‖)`).
The induced map of graded pieces is INJECTIVE for `i < e` (the square-parity dichotomy +
discreteness), and both grs have `2^f` elements (B13 `card_gr`), so it is SURJECTIVE — every
even-depth unit is a square times something deeper.  Consequence
(`kummerDepth_even_collapse`): the class-level filtration COLLAPSES at even levels
`0 < 2i < 2e`. -/

section GrSquaring

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- The strengthened square-depth dichotomy, retaining the base-side bound in the degenerate
branch: either `‖w − 1‖ ≤ ‖2‖` (the unit is mid-or-deeper) or `‖w² − 1‖ = ‖w − 1‖²`. -/
theorem norm_sq_sub_one' (w : ℚ̄₂) :
    ‖w - 1‖ ≤ ‖(2 : ℚ̄₂)‖ ∨ ‖w ^ 2 - 1‖ = ‖w - 1‖ ^ 2 := by
  rcases le_or_gt ‖w - 1‖ ‖(2 : ℚ̄₂)‖ with hle | hgt
  · exact Or.inl hle
  · right
    have hfac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    have hp : ‖w + 1‖ = ‖w - 1‖ := by
      rw [show w + 1 = (w - 1) + 2 by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hgt),
        max_eq_left hgt.le]
    rw [hfac, norm_mul, hp, sq]

/-- **Squaring doubles depth**: `u ∈ U_i ⟹ u² ∈ U_{2i}` for `i ≤ e`. -/
theorem sq_mem_depthUnits (hπle : ‖π‖ ≤ 1) {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {i : ℕ} (hie : i ≤ e) {u : (↥k)ˣ} (hu : u ∈ depthUnits k π i) :
    u ^ 2 ∈ depthUnits k π (2 * i) := by
  obtain ⟨hu1, hud⟩ := hu
  have hcast : (((u ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂) = (((u : ↥k) : ℚ̄₂)) ^ 2 := by
    rw [Units.val_pow_eq_pow_val]
    push_cast
    ring
  constructor
  · show ‖(((u ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
    rw [hcast, norm_pow, hu1, one_pow]
  · show ‖(((u ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ (2 * i)
    have hplus : ‖((u : ↥k) : ℚ̄₂) + 1‖ ≤ ‖π‖ ^ i := by
      rw [show ((u : ↥k) : ℚ̄₂) + 1 = (((u : ↥k) : ℚ̄₂) - 1) + 2 by ring]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hud ?_)
      rw [he]
      exact pow_le_pow_of_le_one (norm_nonneg π) hπle hie
    rw [hcast, show (((u : ↥k) : ℚ̄₂)) ^ 2 - 1
        = (((u : ↥k) : ℚ̄₂) - 1) * (((u : ↥k) : ℚ̄₂) + 1) by ring,
      norm_mul, two_mul, pow_add]
    exact mul_le_mul hud hplus (norm_nonneg _) (by positivity)

/-- **Squaring sends `U_{i+1}` into `U_{2i+1}`** (`i ≤ e`) — the well-definedness of the
graded squaring. -/
theorem sq_mem_depthUnits_succ (hπle : ‖π‖ ≤ 1) {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {i : ℕ} (hie : i ≤ e) {v : (↥k)ˣ} (hv : v ∈ depthUnits k π (i + 1)) :
    v ^ 2 ∈ depthUnits k π (2 * i + 1) := by
  obtain ⟨hv1, hvd⟩ := hv
  have hcast : (((v ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂) = (((v : ↥k) : ℚ̄₂)) ^ 2 := by
    rw [Units.val_pow_eq_pow_val]
    push_cast
    ring
  constructor
  · show ‖(((v ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
    rw [hcast, norm_pow, hv1, one_pow]
  · show ‖(((v ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ (2 * i + 1)
    have hplus : ‖((v : ↥k) : ℚ̄₂) + 1‖ ≤ ‖π‖ ^ min (i + 1) e := by
      rw [show ((v : ↥k) : ℚ̄₂) + 1 = (((v : ↥k) : ℚ̄₂) - 1) + 2 by ring]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
      · exact hvd.trans (pow_le_pow_of_le_one (norm_nonneg π) hπle (min_le_left _ _))
      · rw [he]
        exact pow_le_pow_of_le_one (norm_nonneg π) hπle (min_le_right _ _)
    rw [hcast, show (((v : ↥k) : ℚ̄₂)) ^ 2 - 1
        = (((v : ↥k) : ℚ̄₂) - 1) * (((v : ↥k) : ℚ̄₂) + 1) by ring, norm_mul]
    calc ‖((v : ↥k) : ℚ̄₂) - 1‖ * ‖((v : ↥k) : ℚ̄₂) + 1‖
        ≤ ‖π‖ ^ (i + 1) * ‖π‖ ^ min (i + 1) e :=
          mul_le_mul hvd hplus (norm_nonneg _) (by positivity)
      _ = ‖π‖ ^ (i + 1 + min (i + 1) e) := by rw [← pow_add]
      _ ≤ ‖π‖ ^ (2 * i + 1) :=
          pow_le_pow_of_le_one (norm_nonneg π) hπle (by omega)

/-- **A unit whose square is one level deeper than double is itself one level deeper**
(`i + 1 ≤ e`): the kernel-triviality core of the graded squaring, via the strengthened
dichotomy + the discreteness step-down. -/
theorem mem_depthUnits_succ_of_sq (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {i : ℕ} (hie : i + 1 ≤ e)
    {v : (↥k)ˣ} (hv : v ∈ depthUnits k π i)
    (hsq : ‖(((v : ↥k) : ℚ̄₂)) ^ 2 - 1‖ ≤ ‖π‖ ^ (2 * i + 1)) :
    v ∈ depthUnits k π (i + 1) := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  obtain ⟨hv1, hvd⟩ := hv
  refine ⟨hv1, ?_⟩
  rcases norm_sq_sub_one' ((v : ↥k) : ℚ̄₂) with hcase | hcase
  · -- `‖v−1‖ ≤ ‖2‖ = ‖π‖^e ≤ ‖π‖^{i+1}`
    refine hcase.trans ?_
    rw [he]
    exact pow_le_pow_of_le_one (norm_nonneg π) hπ1.le hie
  · -- `‖v−1‖² ≤ ‖π‖^{2i+1} < ‖π‖^{2i}` forces `‖v−1‖ < ‖π‖^i`, then step-down
    have hlt : ‖((v : ↥k) : ℚ̄₂) - 1‖ < ‖π‖ ^ i := by
      have h1 : ‖((v : ↥k) : ℚ̄₂) - 1‖ ^ 2 < (‖π‖ ^ i) ^ 2 := by
        calc ‖((v : ↥k) : ℚ̄₂) - 1‖ ^ 2 = ‖(((v : ↥k) : ℚ̄₂)) ^ 2 - 1‖ := hcase.symm
          _ ≤ ‖π‖ ^ (2 * i + 1) := hsq
          _ < ‖π‖ ^ (2 * i) := by
              rw [pow_succ]
              calc ‖π‖ ^ (2 * i) * ‖π‖ < ‖π‖ ^ (2 * i) * 1 :=
                    mul_lt_mul_of_pos_left hπ1 (pow_pos hπpos _)
                _ = ‖π‖ ^ (2 * i) := mul_one _
          _ = (‖π‖ ^ i) ^ 2 := by rw [← pow_mul, mul_comm]
      exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt (pow_pos hπpos i)) h1
    exact norm_step_down k π hπk hπ0 hπmax
      (sub_mem (((v : (↥k)ˣ) : ↥k)).2 (one_mem k)) hlt

variable {e : ℕ}

/-- The squaring homomorphism `U_i →* U_{2i}` on the subtype groups (`i ≤ e`). -/
noncomputable def sqHom (hπle : ‖π‖ ≤ 1) (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {i : ℕ} (hie : i ≤ e) :
    ↥(depthUnits k π i) →* ↥(depthUnits k π (2 * i)) where
  toFun u := ⟨(u : (↥k)ˣ) ^ 2, sq_mem_depthUnits k π hπle he hie u.2⟩
  map_one' := by
    apply Subtype.ext
    show ((1 : (↥k)ˣ)) ^ 2 = 1
    rw [one_pow]
  map_mul' u v := by
    apply Subtype.ext
    show ((u : (↥k)ˣ) * v) ^ 2 = ((u : (↥k)ˣ)) ^ 2 * ((v : (↥k)ˣ)) ^ 2
    rw [mul_pow]

/-- **The graded squaring** `U_i/U_{i+1} →* U_{2i}/U_{2i+1}` (`i ≤ e`). -/
noncomputable def grSq (hπle : ‖π‖ ≤ 1) (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {i : ℕ} (hie : i ≤ e) :
    (↥(depthUnits k π i) ⧸ (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) →*
      (↥(depthUnits k π (2 * i)) ⧸
        (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) :=
  QuotientGroup.map _ _ (sqHom k π hπle he hie) (by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact sq_mem_depthUnits_succ k π hπle he hie hv)

/-- **Injectivity of the graded squaring** for `i + 1 ≤ e`. -/
theorem grSq_injective (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {i : ℕ} (hie : i + 1 ≤ e) :
    Function.Injective (grSq k π hπ1.le he (Nat.le_of_succ_le hie)) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H v =>
    -- `grSq (mk v) = mk (sqHom v)` by definition of `QuotientGroup.map`
    have hq' : (QuotientGroup.mk (sqHom k π hπ1.le he (Nat.le_of_succ_le hie) v)
        : ↥(depthUnits k π (2 * i)) ⧸
          (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) = 1 := hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq'
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    -- `hq' : v² ∈ U_{2i+1}`; extract the norm bound and apply the kernel-triviality core
    have hcast : ((((v : (↥k)ˣ) ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂)
        = ((((v : (↥k)ˣ) : ↥k)) : ℚ̄₂) ^ 2 := by
      rw [Units.val_pow_eq_pow_val]
      push_cast
      ring
    refine mem_depthUnits_succ_of_sq k π hπk hπ0 hπ1 hπmax he hie v.2 ?_
    have hd : ‖((((v : (↥k)ˣ) ^ 2 : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ (2 * i + 1) := hq'.2
    rw [hcast] at hd
    exact hd

/-- **Surjectivity of the graded squaring** for `1 ≤ i`, `i + 1 ≤ e`: injective + both grs
have `2^f` elements (B13 `card_gr`, passed as hypotheses). -/
theorem grSq_surjective (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ} (hf_pos : 1 ≤ f)
    {i : ℕ} (hie : i + 1 ≤ e)
    (hcard_i : Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f)
    (hcard_2i : Nat.card (↥(depthUnits k π (2 * i)) ⧸
      (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) = 2 ^ f) :
    Function.Surjective (grSq k π hπ1.le he (Nat.le_of_succ_le hie)) := by
  haveI hfin1 : Finite (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) :=
    (Nat.card_pos_iff.mp (by rw [hcard_i]; positivity)).2
  haveI hfin2 : Finite (↥(depthUnits k π (2 * i)) ⧸
      (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) :=
    (Nat.card_pos_iff.mp (by rw [hcard_2i]; positivity)).2
  haveI := Fintype.ofFinite (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i))
  haveI := Fintype.ofFinite (↥(depthUnits k π (2 * i)) ⧸
      (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i)))
  have hcards : Fintype.card (↥(depthUnits k π i) ⧸
        (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i))
      = Fintype.card (↥(depthUnits k π (2 * i)) ⧸
        (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_i, hcard_2i]
  exact ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨grSq_injective k π hπk hπ0 hπ1 hπmax he hie, hcards⟩).2

/-- **The even-level collapse** (`0 < 2i < 2e`): the class-level Kummer filtration does not
move at even levels — every even-depth unit is a square times a one-deeper unit, and squares
have trivial class. -/
theorem kummerDepth_even_collapse (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ} (hf_pos : 1 ≤ f)
    {i : ℕ} (hie : i + 1 ≤ e)
    (hcard_i : Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f)
    (hcard_2i : Nat.card (↥(depthUnits k π (2 * i)) ⧸
      (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) = 2 ^ f) :
    kummerDepth k π (2 * i) ≤ kummerDepth k π (2 * i + 1) := by
  rintro ξ ⟨a, ha, rfl⟩
  -- hit `[a]` in the gr by the surjective graded squaring
  obtain ⟨wq, hwq⟩ := grSq_surjective k π hπk hπ0 hπ1 hπmax he hf_pos hie hcard_i hcard_2i
    (QuotientGroup.mk (⟨a, ha⟩ : ↥(depthUnits k π (2 * i))))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective wq
  -- unpack: `(sqHom w)⁻¹ · a ∈ U_{2i+1}`
  have hco : (QuotientGroup.mk (sqHom k π hπ1.le he (Nat.le_of_succ_le hie) w)
      : ↥(depthUnits k π (2 * i)) ⧸
        (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i)))
      = QuotientGroup.mk ⟨a, ha⟩ := hwq
  rw [QuotientGroup.eq] at hco
  rw [Subgroup.mem_subgroupOf] at hco
  -- `b := (w²)⁻¹ · a` is a depth-`2i+1` unit and `a = w² · b`
  set b : (↥k)ˣ := ((w : (↥k)ˣ) ^ 2)⁻¹ * a with hbdef
  have hb : b ∈ depthUnits k π (2 * i + 1) := hco
  have hdecomp : a = (w : (↥k)ˣ) ^ 2 * b := by
    rw [hbdef, mul_inv_cancel_left]
  rw [show kummerClassK k a = kummerClassK k ((w : (↥k)ˣ) ^ 2) + kummerClassK k b from by
    rw [← kummerClassK_mul, ← hdecomp]]
  rw [kummerClassK_eq_zero_of_sq k ((w : (↥k)ˣ) ^ 2) ((w : (↥k)ˣ) : ↥k)
    (by rw [Units.val_pow_eq_pow_val]), zero_add]
  exact ⟨b, hb, rfl⟩

end GrSquaring

/-! ## The class-graded comparison map and the odd-level count

`classGrMap : U_j/U_{j+1} → Dc_j/Dc_{j+1}`, `[u] ↦ [[u]]` — always surjective (depth-`j`
classes are classes of depth-`j` units by definition), and INJECTIVE at odd `j < 2e`:
a unit whose class drops a level is `b·w²` with `b` one deeper and `w²` a square in `U_j`
(the Kummer kernel), and squares skip odd levels (`norm_sq_sub_one_le_succ_of_odd`), so the
unit itself is one deeper.  Consequences: `#(Dc_j/Dc_{j+1}) ≤ 2^f` always, `= 2^f` at odd
`j < 2e`, and `= 1` at even `0 < j < 2e` (increment 2's collapse). -/

section ClassGr

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- The comparison map from the unit-graded piece to the class-graded piece. -/
noncomputable def classGrMap (j : ℕ) :
    (↥(depthUnits k π j) ⧸ (depthUnits k π (j + 1)).subgroupOf (depthUnits k π j)) →
      (↥(kummerDepth k π j) ⧸
        (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) :=
  fun q => Quotient.liftOn' q
    (fun u => QuotientAddGroup.mk
      ⟨kummerClassK k (u : (↥k)ˣ),
        (mem_kummerDepth_iff k π).mpr ⟨(u : (↥k)ˣ), u.2, rfl⟩⟩)
    (by
      intro u v huv
      rw [QuotientGroup.leftRel_apply] at huv
      rw [Subgroup.mem_subgroupOf] at huv
      refine QuotientAddGroup.eq.mpr ?_
      rw [AddSubgroup.mem_addSubgroupOf]
      have hgoal : -(kummerClassK k (u : (↥k)ˣ)) + kummerClassK k (v : (↥k)ˣ)
          ∈ kummerDepth k π (j + 1) := by
        refine (mem_kummerDepth_iff k π).mpr ⟨((u : (↥k)ˣ))⁻¹ * v, huv, ?_⟩
        rw [kummerClassK_mul, kummerClassK_inv,
          neg_eq_of_add_eq_zero_left (h1_add_self (kummerClassK k (u : (↥k)ˣ)))]
      exact hgoal)

/-- Computation rule (definitional). -/
theorem classGrMap_mk (j : ℕ) (u : ↥(depthUnits k π j)) :
    classGrMap k π j (QuotientGroup.mk u)
      = QuotientAddGroup.mk ⟨kummerClassK k (u : (↥k)ˣ),
          (mem_kummerDepth_iff k π).mpr ⟨(u : (↥k)ˣ), u.2, rfl⟩⟩ := rfl

/-- `classGrMap` is surjective (depth-`j` classes are classes of depth-`j` units). -/
theorem classGrMap_surjective (j : ℕ) : Function.Surjective (classGrMap k π j) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨a, ha, hax⟩ := x.2
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, congrArg QuotientAddGroup.mk (Subtype.ext hax)⟩

/-- **`classGrMap` is injective at odd `j ≤ 2e − 1`** — the odd-level fullness core. -/
theorem classGrMap_injective [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e)
    {t : ℕ} (hj2e : 2 * t + 1 ≤ 2 * e - 1) :
    Function.Injective (classGrMap k π (2 * t + 1)) := by
  intro q q'
  induction q using QuotientGroup.induction_on with
  | H u =>
    induction q' using QuotientGroup.induction_on with
    | H v =>
      intro hqq
      rw [classGrMap_mk, classGrMap_mk] at hqq
      have hqq' := QuotientAddGroup.eq.mp hqq
      rw [AddSubgroup.mem_addSubgroupOf] at hqq'
      -- re-view the membership with the subtype-coe reduced
      have hqq2 : -(kummerClassK k (u : (↥k)ˣ)) + kummerClassK k (v : (↥k)ˣ)
          ∈ kummerDepth k π (2 * t + 1 + 1) := hqq'
      obtain ⟨b, hb, hbeq⟩ := hqq2
      -- flip the sign (2-torsion): `[b] = [u] + [v]`
      have hbeq' : kummerClassK k b
          = kummerClassK k (u : (↥k)ˣ) + kummerClassK k (v : (↥k)ˣ) := by
        rw [hbeq, neg_eq_of_add_eq_zero_left (h1_add_self (kummerClassK k (u : (↥k)ˣ)))]
      -- `[u⁻¹·v·b⁻¹] = 0`, so it is a square
      have h0 : kummerClassK k ((u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) * b⁻¹) = 0 := by
        rw [kummerClassK_mul, kummerClassK_mul, kummerClassK_inv, kummerClassK_inv, hbeq']
        exact h1_add_self _
      obtain ⟨w, hw⟩ := exists_sq_of_kummerClassK_eq_zero k _ h0
      -- the square `w² = u⁻¹·v·b⁻¹` is a depth-`j` unit, hence depth-`j+1` (odd parity)
      have hc : (u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) * b⁻¹ ∈ depthUnits k π (2 * t + 1) :=
        mul_mem (mul_mem (inv_mem u.2) v.2)
          (inv_mem (depthUnits_antitone k π hπ1.le (Nat.le_succ _) hb))
      have hcoe : ((w : ℚ̄₂)) ^ 2
          = ((((u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) * b⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) := by
        rw [← SubmonoidClass.coe_pow, hw]
      have hwnorm : ‖((w : ℚ̄₂)) ^ 2 - 1‖ ≤ ‖π‖ ^ (2 * t + 1) := by
        rw [hcoe]
        exact hc.2
      have hpar := norm_sq_sub_one_le_succ_of_odd k π hπk hπ0 hπ1 hπmax he hj2e he_pos hwnorm
      have hcmem : (u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) * b⁻¹ ∈ depthUnits k π (2 * t + 2) := by
        refine ⟨hc.1, ?_⟩
        rw [← hcoe]
        exact hpar
      -- `u⁻¹·v = (u⁻¹·v·b⁻¹)·b ∈ U_{j+1}`
      have huv : (u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) ∈ depthUnits k π (2 * t + 1 + 1) := by
        rw [show (u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ)
            = ((u : (↥k)ˣ)⁻¹ * (v : (↥k)ˣ) * b⁻¹) * b by group]
        exact mul_mem hcmem hb
      rw [QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      exact huv

/-- The class-graded piece has at most `2^f` elements (surjectivity + the unit-gr count,
the latter a B13 hypothesis). -/
theorem card_classGr_le (j : ℕ) {f : ℕ}
    (hcard_j : Nat.card (↥(depthUnits k π j) ⧸
      (depthUnits k π (j + 1)).subgroupOf (depthUnits k π j)) = 2 ^ f) :
    Nat.card (↥(kummerDepth k π j) ⧸
      (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) ≤ 2 ^ f := by
  haveI : Finite (↥(depthUnits k π j) ⧸
      (depthUnits k π (j + 1)).subgroupOf (depthUnits k π j)) :=
    (Nat.card_pos_iff.mp (by rw [hcard_j]; positivity)).2
  rw [← hcard_j]
  exact Nat.card_le_card_of_surjective _ (classGrMap_surjective k π j)

/-- **The odd-level class-gr count**: `#(Dc_j/Dc_{j+1}) = 2^f` at odd `j ≤ 2e − 1`
(the comparison map is bijective). -/
theorem card_classGr_odd [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e)
    {t : ℕ} (hj2e : 2 * t + 1 ≤ 2 * e - 1) {f : ℕ}
    (hcard_j : Nat.card (↥(depthUnits k π (2 * t + 1)) ⧸
      (depthUnits k π (2 * t + 1 + 1)).subgroupOf (depthUnits k π (2 * t + 1))) = 2 ^ f) :
    Nat.card (↥(kummerDepth k π (2 * t + 1)) ⧸
      (kummerDepth k π (2 * t + 1 + 1)).addSubgroupOf (kummerDepth k π (2 * t + 1)))
      = 2 ^ f := by
  haveI : Finite (↥(depthUnits k π (2 * t + 1)) ⧸
      (depthUnits k π (2 * t + 1 + 1)).subgroupOf (depthUnits k π (2 * t + 1))) :=
    (Nat.card_pos_iff.mp (by rw [hcard_j]; positivity)).2
  rw [← hcard_j]
  exact Nat.card_eq_of_bijective _
    ⟨classGrMap_injective k π hπk hπ0 hπ1 hπmax he he_pos hj2e,
      classGrMap_surjective k π (2 * t + 1)⟩ |>.symm

/-- **The even-level class-gr count**: `#(Dc_{2i}/Dc_{2i+1}) = 1` for `0 < 2i < 2e`
(increment 2's collapse makes the quotient a subsingleton). -/
theorem card_classGr_even (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ} (hf_pos : 1 ≤ f)
    {i : ℕ} (hie : i + 1 ≤ e)
    (hcard_i : Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f)
    (hcard_2i : Nat.card (↥(depthUnits k π (2 * i)) ⧸
      (depthUnits k π (2 * i + 1)).subgroupOf (depthUnits k π (2 * i))) = 2 ^ f) :
    Nat.card (↥(kummerDepth k π (2 * i)) ⧸
      (kummerDepth k π (2 * i + 1)).addSubgroupOf (kummerDepth k π (2 * i))) = 1 := by
  have hcollapse := kummerDepth_even_collapse k π hπk hπ0 hπ1 hπmax he hf_pos hie
    hcard_i hcard_2i
  have hsub : Subsingleton (↥(kummerDepth k π (2 * i)) ⧸
      (kummerDepth k π (2 * i + 1)).addSubgroupOf (kummerDepth k π (2 * i))) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H b =>
        refine QuotientAddGroup.eq.mpr ?_
        rw [AddSubgroup.mem_addSubgroupOf]
        exact hcollapse (AddSubgroup.add_mem _ (AddSubgroup.neg_mem _ a.2) b.2)
  exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subsingleton.elim x y⟩, ⟨0⟩⟩

end ClassGr

/-! ## The tail survivor: `#Dc_{2e} ≥ 2`

The graded squaring at `i = e` kills `[−1] ≠ [1]` (`‖−1 − 1‖ = ‖2‖ = ‖π‖^e` exactly), so it
is NOT injective; on equal-card grs it is then not surjective, and any unit class outside
its range is a NONZERO element of `Dc_{2e}`: were it zero, the Kummer kernel would make the
unit a square `w²` with `w ∈ U_e` (the dichotomy), putting it back in the range. -/

section TailSurvivor

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- `−1` is a depth-`e` unit: `‖−1 − 1‖ = ‖2‖ = ‖π‖^e`. -/
theorem neg_one_mem_depthUnits {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (-1 : (↥k)ˣ) ∈ depthUnits k π e := by
  have hcast : (((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) = -1 := by
    rw [Units.val_neg, Units.val_one]
    push_cast
    ring
  constructor
  · show ‖(((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
    rw [hcast, norm_neg, norm_one]
  · show ‖(((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ e
    rw [hcast, show (-1 : ℚ̄₂) - 1 = -2 by ring, norm_neg, he]

/-- `−1` is NOT a depth-`(e+1)` unit (`‖π‖^e > ‖π‖^{e+1}`). -/
theorem neg_one_not_mem_depthUnits_succ (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (-1 : (↥k)ˣ) ∉ depthUnits k π (e + 1) := by
  intro h
  have hd := h.2
  have hcast : (((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) = -1 := by
    rw [Units.val_neg, Units.val_one]
    push_cast
    ring
  rw [hcast, show (-1 : ℚ̄₂) - 1 = -2 by ring, norm_neg, he] at hd
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have : ‖π‖ ^ (e + 1) < ‖π‖ ^ e := by
    rw [pow_succ]
    calc ‖π‖ ^ e * ‖π‖ < ‖π‖ ^ e * 1 := mul_lt_mul_of_pos_left hπ1 (pow_pos hπpos e)
      _ = ‖π‖ ^ e := mul_one _
  exact absurd hd (not_le.mpr this)

/-- **The tail survivor**: some depth-`2e` Kummer class is nonzero.  The graded squaring at
`i = e` has `[−1]` in its kernel but `[−1] ≠ [1]`, so it is not injective, hence (equal-card
grs) not surjective; a unit class `[a]` outside the range gives `kummerClassK a ≠ 0` — were
it zero, the Kummer kernel would write `a = w²` with `w ∈ U_e` (norm-one by taking norms;
depth-`e` by the dichotomy), and `[a] = grSq [w]`. -/
theorem exists_kummerDepth_ne_zero [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ}
    (hcard_e : Nat.card (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) = 2 ^ f)
    (hcard_2e : Nat.card (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) = 2 ^ f) :
    ∃ ξ ∈ kummerDepth k π (2 * e), ξ ≠ 0 := by
  haveI hfin1 : Finite (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) :=
    (Nat.card_pos_iff.mp (by rw [hcard_e]; positivity)).2
  haveI hfin2 : Finite (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) :=
    (Nat.card_pos_iff.mp (by rw [hcard_2e]; positivity)).2
  -- `grSq` at `i = e` is not injective: `[−1] ≠ [1]` squares to `1`
  have hker : grSq k π hπ1.le he (le_refl e)
      (QuotientGroup.mk ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩) = 1 := by
    have h1 : (QuotientGroup.mk (sqHom k π hπ1.le he (le_refl e)
        ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩)
        : ↥(depthUnits k π (2 * e)) ⧸
          (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hval : ((sqHom k π hπ1.le he (le_refl e)
          ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩
          : ↥(depthUnits k π (2 * e))) : (↥k)ˣ) = 1 := by
        show ((-1 : (↥k)ˣ)) ^ 2 = 1
        rw [neg_one_sq]
      rw [hval]
      exact one_mem _
    exact h1
  have hne : (QuotientGroup.mk (⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩
      : ↥(depthUnits k π e)) : ↥(depthUnits k π e) ⧸
        (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact neg_one_not_mem_depthUnits_succ k π hπ0 hπ1 he
  have hnotinj : ¬ Function.Injective (grSq k π hπ1.le he (le_refl e)) := by
    intro hinj
    exact hne ((injective_iff_map_eq_one _).mp hinj _ hker)
  -- not injective + equal finite cards ⟹ not surjective
  have hnotsurj : ¬ Function.Surjective (grSq k π hπ1.le he (le_refl e)) := by
    intro hsurj
    haveI := Fintype.ofFinite (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e))
    haveI := Fintype.ofFinite (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
    have hcards : Fintype.card (↥(depthUnits k π (2 * e)) ⧸
          (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
        = Fintype.card (↥(depthUnits k π e) ⧸
          (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_e, hcard_2e]
    exact hnotinj ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcards.symm⟩).1
  obtain ⟨yq, hyq⟩ := not_forall.mp hnotsurj
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective yq
  -- the survivor
  refine ⟨kummerClassK k (a : (↥k)ˣ),
    (mem_kummerDepth_iff k π).mpr ⟨(a : (↥k)ˣ), a.2, rfl⟩, ?_⟩
  intro h0
  obtain ⟨w, hw⟩ := exists_sq_of_kummerClassK_eq_zero k _ h0
  -- `w` is a norm-one unit
  have hw0 : w ≠ 0 := by
    intro hz
    have := unitCoe_ne_zero k (a : (↥k)ˣ)
    rw [← hw, hz] at this
    exact this (by push_cast; ring)
  have hwn1 : ‖(w : ℚ̄₂)‖ = 1 := by
    have hsq : ‖(w : ℚ̄₂)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← SubmonoidClass.coe_pow, hw]
      exact a.2.1
    nlinarith [norm_nonneg (w : ℚ̄₂), sq_nonneg (‖(w : ℚ̄₂)‖ - 1)]
  -- `w` has depth `e` (the dichotomy)
  have hwd : ‖(w : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ e := by
    rcases norm_sq_sub_one' ((w : ℚ̄₂)) with hcase | hcase
    · rw [he] at hcase
      exact hcase
    · have h2e : ‖(w : ℚ̄₂) - 1‖ ^ 2 ≤ (‖π‖ ^ e) ^ 2 := by
        calc ‖(w : ℚ̄₂) - 1‖ ^ 2 = ‖((w : ℚ̄₂)) ^ 2 - 1‖ := hcase.symm
          _ ≤ ‖π‖ ^ (2 * e) := by
              rw [← SubmonoidClass.coe_pow, hw]
              exact a.2.2
          _ = (‖π‖ ^ e) ^ 2 := by rw [← pow_mul, mul_comm]
      exact le_of_pow_le_pow_left₀ (by omega) (le_of_lt (pow_pos (norm_pos_iff.mpr hπ0) e)) h2e
  have hwmem : Units.mk0 w hw0 ∈ depthUnits k π e := ⟨hwn1, hwd⟩
  -- `grSq [w] = [a]` since `w² = a` on the nose — contradicting the escape
  refine hyq ⟨QuotientGroup.mk ⟨Units.mk0 w hw0, hwmem⟩, ?_⟩
  have hunit : (Units.mk0 w hw0) ^ 2 = (a : (↥k)ˣ) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hw
  have hval : (QuotientGroup.mk (sqHom k π hπ1.le he (le_refl e) ⟨Units.mk0 w hw0, hwmem⟩)
      : ↥(depthUnits k π (2 * e)) ⧸
        (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
      = QuotientGroup.mk a := by
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show (Units.mk0 w hw0) ^ 2 = (a : (↥k)ˣ)
    exact hunit
  exact hval

end TailSurvivor

/-! ## The head: `#(M ⧸ Dc_1) ≤ 2`

Two inputs: the level-`0` collapse `Dc_0 ≤ Dc_1` (the residue group `U⁰/U¹` has ODD order
`2^f − 1`, so squaring is bijective on it — `grSq` at `i = 0` is the squaring map of the
gr-group itself), and the `π`-parity decomposition (every `a ∈ k^×` is `u·π^m` with `u`
norm-one, by discreteness), which makes `M ⧸ Dc_1` generated by the single 2-torsion class
`mk [π]`. -/

section Head

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- **The ℕ-valuation** from discreteness: a nonzero integral `k`-element has norm an exact
power of `‖π‖`.  Take the least `m` with `‖π‖^{m+1} < ‖x‖`; then `x/π^m` is integral of norm
`> ‖π‖`, hence norm one by `hπ_max`. -/
theorem exists_nat_val (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {x : ℚ̄₂} (hx : x ∈ k) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖π‖ ^ m := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  -- the least `m` with `‖π‖^{m+1} < ‖x‖`
  have hex : ∃ m : ℕ, ‖π‖ ^ (m + 1) < ‖x‖ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hxpos hπ1
    exact ⟨m, lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg π) hπ1.le (Nat.le_succ m)) hm⟩
  classical
  refine ⟨Nat.find hex, ?_⟩
  have hfound : ‖π‖ ^ (Nat.find hex + 1) < ‖x‖ := Nat.find_spec hex
  have hupper : ‖x‖ ≤ ‖π‖ ^ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]
      exact hx1
    · have hnot := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [not_lt] at hnot
      have harith : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [harith] at hnot
      exact hnot
  -- `y := x / π^m` is integral (norm ≤ 1) with `‖y‖ > ‖π‖`, hence `‖y‖ = 1`
  have hπmpos : (0 : ℝ) < ‖π‖ ^ Nat.find hex := pow_pos hπpos _
  have hy1 : ‖x / π ^ Nat.find hex‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one hπmpos]
    exact hupper
  have hygt : ‖π‖ < ‖x / π ^ Nat.find hex‖ := by
    rw [norm_div, norm_pow, lt_div_iff₀ hπmpos, ← pow_succ']
    exact hfound
  have hyeq : ‖x / π ^ Nat.find hex‖ = 1 := by
    by_contra hne
    have hlt : ‖x / π ^ Nat.find hex‖ < 1 := lt_of_le_of_ne hy1 hne
    exact absurd (hπmax _ (div_mem hx (pow_mem hπk _)) hlt) (not_le.mpr hygt)
  calc ‖x‖ = ‖x / π ^ Nat.find hex‖ * ‖π‖ ^ Nat.find hex := by
        rw [norm_div, norm_pow, div_mul_cancel₀ _ (ne_of_gt hπmpos)]
    _ = ‖π‖ ^ Nat.find hex := by rw [hyeq, one_mul]

/-- **The level-`0` collapse** `Dc_0 ≤ Dc_1`: the residue group `U⁰/U¹` has odd order
`2^f − 1` (B13 `card_gr_zero`, as a hypothesis over the `depthUnits 0`-form), so squaring is
bijective on it and every norm-one unit is a square times a principal unit. -/
theorem kummerDepth_zero_collapse (hπle : ‖π‖ ≤ 1) {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1) :
    kummerDepth k π 0 ≤ kummerDepth k π 1 := by
  -- `grSq` at `i = 0` is the squaring map of the gr-group itself; injective by odd order
  have hcardpos : 0 < Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) := by
    rw [hcard_0]
    have : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf_pos
    omega
  haveI hfin : Finite (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) :=
    (Nat.card_pos_iff.mp hcardpos).2
  have hodd : Odd (Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0))) := by
    rw [hcard_0]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf_pos
    have heven : Even (2 ^ f) := by
      rcases f with _ | f'
      · omega
      · exact ⟨2 ^ f', by rw [pow_succ, mul_two]⟩
    rcases heven with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  -- the squaring map on the gr is injective (no 2-torsion in odd order), hence surjective
  have hinj : Function.Injective (grSq k π hπle he (Nat.zero_le e)) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H v =>
      -- `grSq (mk v) = (mk v)²` at `i = 0`
      have hq' : ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 = 1 := by
        have hval : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) v)
            : ↥(depthUnits k π (2 * 0)) ⧸
              (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0))) = 1 := hq
        have hmk : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) v)
            : ↥(depthUnits k π (2 * 0)) ⧸
              (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0)))
            = ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
              (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 := by
          have : (QuotientGroup.mk (v ^ 2) : ↥(depthUnits k π 0) ⧸
              (depthUnits k π 1).subgroupOf (depthUnits k π 0))
              = ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
                (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 := by
            rw [← QuotientGroup.mk_pow]
          exact this
        rw [← hmk]
        exact hval
      -- odd order kills the 2-torsion element `mk v`
      have hdvd2 : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hq'
      have hdvdcard : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ∣ Nat.card _ :=
        orderOf_dvd_natCard _
      have hone : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) = 1 := by
        have hd := Nat.dvd_gcd hdvd2 hdvdcard
        have hgcd : Nat.gcd 2 (Nat.card (↥(depthUnits k π 0) ⧸
            (depthUnits k π 1).subgroupOf (depthUnits k π 0))) = 1 := by
          rw [Nat.gcd_rec, Nat.odd_iff.mp hodd, Nat.gcd_one_left]
        rw [hgcd] at hd
        exact Nat.dvd_one.mp hd
      rw [← orderOf_eq_one_iff]
      exact hone
  have hsurj : Function.Surjective (grSq k π hπle he (Nat.zero_le e)) := by
    haveI := Fintype.ofFinite (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0))
    exact Finite.surjective_of_injective hinj
  -- consume exactly as in the even collapse
  rintro ξ ⟨a, ha, rfl⟩
  obtain ⟨wq, hwq⟩ := hsurj (QuotientGroup.mk (⟨a, ha⟩ : ↥(depthUnits k π 0)))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective wq
  have hco : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) w)
      : ↥(depthUnits k π (2 * 0)) ⧸
        (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0)))
      = QuotientGroup.mk ⟨a, ha⟩ := hwq
  rw [QuotientGroup.eq] at hco
  rw [Subgroup.mem_subgroupOf] at hco
  set b : (↥k)ˣ := ((w : (↥k)ˣ) ^ 2)⁻¹ * a with hbdef
  have hb : b ∈ depthUnits k π 1 := hco
  have hdecomp : a = (w : (↥k)ˣ) ^ 2 * b := by
    rw [hbdef, mul_inv_cancel_left]
  rw [show kummerClassK k a = kummerClassK k ((w : (↥k)ˣ) ^ 2) + kummerClassK k b from by
    rw [← kummerClassK_mul, ← hdecomp]]
  rw [kummerClassK_eq_zero_of_sq k ((w : (↥k)ˣ) ^ 2) ((w : (↥k)ˣ) : ↥k)
    (by rw [Units.val_pow_eq_pow_val]), zero_add]
  exact ⟨b, hb, rfl⟩

/-- `kummerClassK` of a power: `[a^m] = m • [a]`. -/
theorem kummerClassK_pow (a : (↥k)ˣ) (m : ℕ) :
    kummerClassK k (a ^ m) = m • kummerClassK k a := by
  induction m with
  | zero => rw [pow_zero, kummerClassK_one, zero_nsmul]
  | succ n ih => rw [pow_succ, kummerClassK_mul, ih, succ_nsmul]

/-- 2-torsion `nsmul` reduction: `m • ξ = (m % 2) • ξ`. -/
theorem nsmul_mod_two {G : Type*} [AddCommGroup G] (ξ : G) (hξ : ξ + ξ = 0) (m : ℕ) :
    m • ξ = (m % 2) • ξ := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [add_nsmul, mul_comm, mul_nsmul, two_nsmul, ← nsmul_add, hξ, smul_zero, zero_add]

/-- The uniformizer as a unit of `k`. -/
noncomputable def piUnit (hπk : π ∈ k) (hπ0 : π ≠ 0) : (↥k)ˣ :=
  Units.mk0 ⟨π, hπk⟩ (fun h => hπ0 (by simpa using congrArg Subtype.val h))

theorem piUnit_coe (hπk : π ∈ k) (hπ0 : π ≠ 0) :
    (((piUnit k π hπk hπ0 : ↥k)) : ℚ̄₂) = π := rfl

/-- **The head bound**: `M ⧸ Dc_1` is generated by the single 2-torsion class of the
uniformizer (`π`-parity via the ℕ-valuation, unit part into `Dc_1` by the level-`0`
collapse), so it has at most `2` elements. -/
theorem card_quot_kummerDepth_one_le_two [FiniteDimensional ℚ_[2] k]
    [Finite (H1 k.fixingSubgroup (ZMod 2))]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) ≤ 2 := by
  -- the classification: every element of the quotient is `0` or `mk [π₀]`
  have hkey : ∀ b : (↥k)ˣ, ‖((b : ↥k) : ℚ̄₂)‖ ≤ 1 →
      (QuotientAddGroup.mk (kummerClassK k b)
          : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) = 0
        ∨ (QuotientAddGroup.mk (kummerClassK k b)
          : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
          = QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) := by
    intro b hb1
    obtain ⟨m, hm⟩ := exists_nat_val k π hπk hπ0 hπ1 hπmax
      (by exact_mod_cast ((b : ↥k)).2) (unitCoe_ne_zero k b) hb1
    -- the norm-one part `u := b · π₀⁻ᵐ`
    have hval : (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)
        = (((b : ↥k) : ℚ̄₂)) * ((π : ℚ̄₂) ^ m)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      push_cast
      rfl
    have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
    have hu1 : ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1 := by
      rw [hval, norm_mul, norm_inv, norm_pow, hm]
      field_simp
    -- its class lies in `Dc_1` (level-`0` collapse)
    have humem : kummerClassK k (b * (piUnit k π hπk hπ0 ^ m)⁻¹)
        ∈ kummerDepth k π 1 := by
      refine kummerDepth_zero_collapse k π hπ1.le he hf_pos hcard_0 ?_
      refine (mem_kummerDepth_iff k π).mpr ⟨_, ⟨hu1, ?_⟩, rfl⟩
      rw [pow_zero]
      calc ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖
          ≤ max ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ ‖(1 : ℚ̄₂)‖ := by
            rw [show (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1
                = (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) + (-1) by ring]
            refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
            rw [norm_neg]
        _ = 1 := by rw [hu1, norm_one, max_self]
    -- decompose the class and reduce the multiplicity mod 2
    have hcls : kummerClassK k b
        = kummerClassK k (b * (piUnit k π hπk hπ0 ^ m)⁻¹)
          + m • kummerClassK k (piUnit k π hπk hπ0) := by
      rw [← kummerClassK_pow, ← kummerClassK_mul]
      congr 1
      group
    have hmk : (QuotientAddGroup.mk (kummerClassK k b)
        : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
        = QuotientAddGroup.mk ((m % 2) • kummerClassK k (piUnit k π hπk hπ0)) := by
      rw [hcls, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr humem,
        zero_add, nsmul_mod_two _ (h1_add_self _) m]
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · left
      rw [hmk, h0, zero_nsmul, QuotientAddGroup.mk_zero]
    · right
      rw [hmk, h1, one_nsmul]
  -- surjection from `Fin 2`
  set g : Fin 2 → H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1 :=
    fun i => if i = 0 then 0
      else QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) with hg
  have hg0 : g 0 = 0 := by rw [hg]; simp
  have hg1 : g 1 = QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) := by
    rw [hg]; simp
  have hsurj : Function.Surjective g := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H ξ =>
      obtain ⟨a, rfl⟩ := kummerClassK_surjective k ξ
      rcases le_or_gt ‖((a : ↥k) : ℚ̄₂)‖ 1 with hle | hgt
      · rcases hkey a hle with h | h
        · exact ⟨0, by rw [hg0]; exact h.symm⟩
        · exact ⟨1, by rw [hg1]; exact h.symm⟩
      · have hinv1 : ‖(((a⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ ≤ 1 := by
          rw [show (((a⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) = (((a : ↥k) : ℚ̄₂))⁻¹ from by
            rw [Units.val_inv_eq_inv_val]; push_cast; ring, norm_inv]
          exact inv_le_one_of_one_le₀ hgt.le
        have hswap : kummerClassK k a⁻¹ = kummerClassK k a := kummerClassK_inv k a
        rcases hkey a⁻¹ hinv1 with h | h
        · refine ⟨0, by rw [hg0]; rw [hswap] at h; exact h.symm⟩
        · refine ⟨1, by rw [hg1]; rw [hswap] at h; exact h.symm⟩
  calc Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
      ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective g hsurj
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]

end Head

/-! ## The assembly: `#(M ⧸ Dc_{e+1}) ≤ #Dc_e`

The paired descent: `R(s) : #(M⧸Dc_{e+1})·#Dc_{e+1+s} ≤ #Dc_e·#(M⧸Dc_{e−s})` holds at
`s = 0` with equality (double Lagrange), and each step trades the level `e−s−1` on the right
for the level `e+1+s` on the left — same-parity levels summing to `2e`, where the class-gr
counts compare (`= 2^f` odd / `= 1 ≤` even).  At `s = e−1` the head (`≤ 2`) and the tail
survivor (`≥ 2`) close the inequality. -/

section Assembly

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)
variable [Finite (H1 k.fixingSubgroup (ZMod 2))]

/-- Lagrange step-down for the class filtration:
`#Dc_j = #(Dc_j/Dc_{j+1}) · #Dc_{j+1}`. -/
theorem card_kummerDepth_step (hπ1 : ‖π‖ ≤ 1) (j : ℕ) :
    Nat.card ↥(kummerDepth k π j)
      = Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))
        * Nat.card ↥(kummerDepth k π (j + 1)) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))]
  congr 1
  exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
    (kummerDepth_antitone k π hπ1 (Nat.le_succ j))).toEquiv

/-- Lagrange step-up for the ambient quotients:
`#(M⧸Dc_{j+1}) = #(M⧸Dc_j) · #(Dc_j/Dc_{j+1})`. -/
theorem card_quot_kummerDepth_step (hπ1 : ‖π‖ ≤ 1) (j : ℕ) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) := by
  haveI : Nonempty ↥(kummerDepth k π (j + 1)) := ⟨⟨0, zero_mem _⟩⟩
  have h1 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
        * Nat.card ↥(kummerDepth k π (j + 1)) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card ↥(kummerDepth k π j) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 := card_kummerDepth_step k π hπ1 j
  have h4 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
        * Nat.card ↥(kummerDepth k π (j + 1))
      = (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)))
        * Nat.card ↥(kummerDepth k π (j + 1)) := by
    rw [← h1, h2, h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h4

/-- **The paired level comparison**: for `1 ≤ j ≤ e − 1`, the class-gr at `j` is at most the
class-gr at `2e − j` (same parity: odd levels are both `2^f`, even levels collapse to `1`). -/
theorem card_classGr_pair_le [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f)
    {j : ℕ} (hj1 : 1 ≤ j) (hje : j ≤ e - 1) :
    Nat.card (↥(kummerDepth k π j) ⧸
        (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))
      ≤ Nat.card (↥(kummerDepth k π (2 * e - j)) ⧸
        (kummerDepth k π (2 * e - j + 1)).addSubgroupOf (kummerDepth k π (2 * e - j))) := by
  haveI : Nonempty (↥(kummerDepth k π (2 * e - j)) ⧸
      (kummerDepth k π (2 * e - j + 1)).addSubgroupOf (kummerDepth k π (2 * e - j))) :=
    ⟨0⟩
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨t, ht⟩
  · -- even level: the left side collapses to `1`
    have hji : j = 2 * i := by omega
    have hi1 : 1 ≤ i := by omega
    have hie : i + 1 ≤ e := by omega
    have hLHS : Nat.card (↥(kummerDepth k π j) ⧸
        (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) = 1 := by
      rw [hji]
      exact card_classGr_even k π hπk hπ0 hπ1 hπmax he hf_pos hie
        (hcard_gr i hi1) (hcard_gr (2 * i) (by omega))
    rw [hLHS]
    exact Nat.card_pos
  · -- odd level: both sides are `2^f`
    subst ht
    rw [show 2 * e - (2 * t + 1) = 2 * (e - t - 1) + 1 from by omega]
    rw [card_classGr_odd k π hπk hπ0 hπ1 hπmax he he_pos (by omega)
        (hcard_gr (2 * t + 1) (by omega)),
      card_classGr_odd k π hπk hπ0 hπ1 hπmax he he_pos (by omega)
        (hcard_gr (2 * (e - t - 1) + 1) (by omega))]

/-- **THE STRUCTURAL COUNT** — the single remaining input of (H4)'s sharpness:
`#(M ⧸ Dc_{e+1}) ≤ #Dc_e`, by the paired descent between the double-Lagrange identity at
`s = 0` and the head/tail comparison at `s = e − 1`. -/
theorem card_quot_deep_le_card_mid [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
      ≤ Nat.card ↥(kummerDepth k π e) := by
  have hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1 := by
    rw [depthUnits_zero]
    exact hcard_zero
  -- the paired descent
  have hR : ∀ s : ℕ, s ≤ e - 1 →
      Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1 + s))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s)) := by
    intro s
    induction s with
    | zero =>
      intro _
      show Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π e)
      have h1 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
        (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
      have h2 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π e)
            * Nat.card ↥(kummerDepth k π e) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
      refine le_of_eq ?_
      rw [h1, h2, mul_comm]
    | succ s ih =>
      intro hs
      have hR_s := ih (by omega)
      -- step the two sides
      have hAstep := card_kummerDepth_step k π hπ1.le (e + 1 + s)
      have hidx : e - s - 1 + 1 = e - s := by omega
      have hBstep : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s - 1))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        rw [← hidx]
        exact card_quot_kummerDepth_step k π hπ1.le (e - s - 1)
      -- the paired comparison at `j := e − s − 1`
      have hidx2 : 2 * e - (e - s - 1) = e + 1 + s := by omega
      have hpair : Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
            (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
          ≤ Nat.card (↥(kummerDepth k π (e + 1 + s)) ⧸
            (kummerDepth k π (e + 1 + s + 1)).addSubgroupOf (kummerDepth k π (e + 1 + s))) := by
        have := card_classGr_pair_le k π hπk hπ0 hπ1 hπmax he he_pos hf_pos hcard_gr
          (j := e - s - 1) (by omega) (by omega)
        rw [hidx2] at this
        exact this
      have hg'pos : 0 < Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
          (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        haveI : Nonempty (↥(kummerDepth k π (e - s - 1)) ⧸
            (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := ⟨0⟩
        exact Nat.card_pos
      -- the multiplicative bookkeeping, then cancel the small gr
      have hchain : (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
            * Nat.card ↥(kummerDepth k π (e + 1 + (s + 1))))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
          ≤ (Nat.card ↥(kummerDepth k π e)
            * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - (s + 1))))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        have hidx3 : e + 1 + (s + 1) = e + 1 + s + 1 := by omega
        have hidx4 : e - (s + 1) = e - s - 1 := by omega
        rw [hidx3, hidx4]
        calc (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s + 1)))
              * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
                (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
            ≤ (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s + 1)))
              * Nat.card (↥(kummerDepth k π (e + 1 + s)) ⧸
                (kummerDepth k π (e + 1 + s + 1)).addSubgroupOf (kummerDepth k π (e + 1 + s))) := by
              exact Nat.mul_le_mul_left _ hpair
          _ = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s)) := by
              rw [hAstep]
              ring
          _ ≤ Nat.card ↥(kummerDepth k π e)
              * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s)) := hR_s
          _ = (Nat.card ↥(kummerDepth k π e)
              * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s - 1)))
              * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
                (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
              rw [hBstep]
              ring
      exact Nat.le_of_mul_le_mul_right hchain hg'pos
  -- endpoint at `s = e − 1`
  have hend := hR (e - 1) (le_refl _)
  have hidx1 : e + 1 + (e - 1) = 2 * e := by omega
  have hidx2 : e - (e - 1) = 1 := by omega
  rw [hidx1, hidx2] at hend
  -- head and tail
  have hhead := card_quot_kummerDepth_one_le_two k π hπk hπ0 hπ1 hπmax he hf_pos hcard_0
  have htail : 2 ≤ Nat.card ↥(kummerDepth k π (2 * e)) := by
    obtain ⟨ξ, hξ, hne⟩ := exists_kummerDepth_ne_zero k π hπk hπ0 hπ1 hπmax he
      (hcard_gr e he_pos) (hcard_gr (2 * e) (by omega))
    haveI : Nontrivial ↥(kummerDepth k π (2 * e)) :=
      ⟨⟨⟨ξ, hξ⟩, 0, fun h => hne (by simpa using congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hchain : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
        * Nat.card ↥(kummerDepth k π (2 * e))
      ≤ Nat.card ↥(kummerDepth k π e) * Nat.card ↥(kummerDepth k π (2 * e)) := by
    calc Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (2 * e))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) := hend
      _ ≤ Nat.card ↥(kummerDepth k π e) * 2 := Nat.mul_le_mul_left _ hhead
      _ ≤ Nat.card ↥(kummerDepth k π e) * Nat.card ↥(kummerDepth k π (2 * e)) :=
          Nat.mul_le_mul_left _ htail
  exact Nat.le_of_mul_le_mul_right hchain (by omega)

end Assembly

/-! ## The `ker ρ ↔ G_k` transport of `H¹`

`hker` is a POINTWISE identification, so the types `H1 ↥(ker ρ)` and `H1 k.fixingSubgroup`
differ as terms and an `Eq`-rewrite dies on dependent motives.  Instead: with trivial
coefficients the transport is plain COCYCLE PRECOMPOSITION along the identity inclusions
`kerToFixing`/`fixingToKer` (the `conjAct`-machinery pattern: `Quotient.out`-based maps with
`H1ofFun`-computation rules — the `B¹ = 0` argument makes the representative exact). -/

section KerTransport

variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C) (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The identity inclusion `↥k.fixingSubgroup → ↥(ker ρ)` (inverse of `kerToFixing`). -/
def fixingToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n : ↥k.fixingSubgroup) : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  ⟨(n : Kummer.GaloisGroup ℚ_[2]), (hker n.1).mpr n.2⟩

theorem fixingToKer_mul (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n m : ↥k.fixingSubgroup) :
    fixingToKer ρ k hker (n * m) = fixingToKer ρ k hker n * fixingToKer ρ k hker m :=
  Subtype.ext rfl

theorem continuous_fixingToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    Continuous (fixingToKer ρ k hker) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- Precomposition with `fixingToKer` carries `Z¹(ker ρ)` to `Z¹(G_k)`. -/
theorem comp_fixingToKer_mem_Z1 (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    (fun n => f (fixingToKer ρ k hker n)) ∈ Z1 k.fixingSubgroup (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_fixingToKer ρ k hker), fun n m => ?_⟩
  show f (fixingToKer ρ k hker (n * m))
    = f (fixingToKer ρ k hker n) + n • f (fixingToKer ρ k hker m)
  have htriv : ∀ (a : ↥(k.fixingSubgroup)) (z : ZMod 2), a • z = z := fun _ _ => rfl
  have htriv' : ∀ (a : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (z : ZMod 2),
      a • z = z := fun _ _ => rfl
  rw [fixingToKer_mul, hcoc, htriv, htriv']

/-- Precomposition with `kerToFixing` carries `Z¹(G_k)` to `Z¹(ker ρ)`. -/
theorem comp_kerToFixing_mem_Z1 (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(k.fixingSubgroup) → ZMod 2}
    (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    (fun n => f (kerToFixing ρ k hker n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_kerToFixing ρ k hker), fun n m => ?_⟩
  show f (kerToFixing ρ k hker (n * m))
    = f (kerToFixing ρ k hker n) + n • f (kerToFixing ρ k hker m)
  have htriv : ∀ (a : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (z : ZMod 2),
      a • z = z := fun _ _ => rfl
  have htriv' : ∀ (a : ↥(k.fixingSubgroup)) (z : ZMod 2), a • z = z := fun _ _ => rfl
  rw [kerToFixing_mul, hcoc, htriv, htriv']

/-- Transport `H¹(ker ρ) → H¹(G_k)` (cocycle precomposition with `fixingToKer`). -/
noncomputable def h1KerToFix (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    H1 k.fixingSubgroup (ZMod 2) :=
  H1ofFun k.fixingSubgroup (fun n => (Quotient.out ξ).1 (fixingToKer ρ k hker n))

/-- Transport `H¹(G_k) → H¹(ker ρ)` (cocycle precomposition with `kerToFixing`). -/
noncomputable def h1FixToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (η : H1 k.fixingSubgroup (ZMod 2)) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
    (fun n => (Quotient.out η).1 (kerToFixing ρ k hker n))

/-- Computation rule for `h1KerToFix` (the `B¹ = 0` argument: the canonical representative of
an `H1ofFun`-class is the function itself). -/
theorem h1KerToFix_h1ofFun (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f)
      = H1ofFun k.fixingSubgroup (fun n => f (fixingToKer ρ k hker n)) := by
  set ξ := H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f with hξ
  have hout : (Quotient.out ξ
      : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))).1 = f := by
    have h1 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) (Quotient.out ξ)
        = H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⟨f, hf⟩ := by
      have hoe : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) (Quotient.out ξ)
          = ξ := Quotient.out_eq ξ
      rw [hoe, hξ, H1ofFun_of_mem hf]
    have hz0 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)
        (Quotient.out ξ - ⟨f, hf⟩) = 0 := by
      rw [map_sub, h1, sub_self]
    have hdiff := (QuotientAddGroup.eq_zero_iff _).mp hz0
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff
    obtain ⟨w₀, hw₀⟩ := hdiff
    funext n
    have hn := congrFun hw₀ n
    have hz : (Quotient.out ξ - ⟨f, hf⟩ :
        ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))).1 n = 0 := by
      rw [← hn]
      show n • w₀ - w₀ = 0
      rw [show n • w₀ = w₀ from rfl, sub_self]
    have : (Quotient.out ξ).1 n - f n = 0 := hz
    exact sub_eq_zero.mp this
  unfold h1KerToFix
  rw [hout]

/-- Computation rule for `h1FixToKer`. -/
theorem h1FixToKer_h1ofFun (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(k.fixingSubgroup) → ZMod 2}
    (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup f)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => f (kerToFixing ρ k hker n)) := by
  set η := H1ofFun k.fixingSubgroup f with hη
  have hout : (Quotient.out η : ↥(Z1 k.fixingSubgroup (ZMod 2))).1 = f := by
    have h1 : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η)
        = H1mk k.fixingSubgroup (ZMod 2) ⟨f, hf⟩ := by
      have hoe : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η) = η := Quotient.out_eq η
      rw [hoe, hη, H1ofFun_of_mem hf]
    have hz0 : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η - ⟨f, hf⟩) = 0 := by
      rw [map_sub, h1, sub_self]
    have hdiff := (QuotientAddGroup.eq_zero_iff _).mp hz0
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff
    obtain ⟨w₀, hw₀⟩ := hdiff
    funext n
    have hn := congrFun hw₀ n
    have hz : (Quotient.out η - ⟨f, hf⟩ : ↥(Z1 k.fixingSubgroup (ZMod 2))).1 n = 0 := by
      rw [← hn]
      show n • w₀ - w₀ = 0
      rw [show n • w₀ = w₀ from rfl, sub_self]
    have : (Quotient.out η).1 n - f n = 0 := hz
    exact sub_eq_zero.mp this
  unfold h1FixToKer
  rw [hout]

/-- The round trip `ker → fix → ker` is the identity. -/
theorem h1FixToKer_h1KerToFix (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) = ξ := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a
        : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) a.1
      from (H1ofFun_of_mem a.2).symm]
    rw [h1KerToFix_h1ofFun ρ k hker a.2,
      h1FixToKer_h1ofFun ρ k hker (comp_fixingToKer_mem_Z1 ρ k hker a.2)]
    exact congrArg _ (funext fun n => congrArg a.1 (Subtype.ext rfl))

/-- The round trip `fix → ker → fix` is the identity. -/
theorem h1KerToFix_h1FixToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (η : H1 k.fixingSubgroup (ZMod 2)) :
    h1KerToFix ρ k hker (h1FixToKer ρ k hker η) = η := by
  induction η using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a : H1 k.fixingSubgroup (ZMod 2))
      = H1ofFun k.fixingSubgroup a.1 from (H1ofFun_of_mem a.2).symm]
    rw [h1FixToKer_h1ofFun ρ k hker a.2,
      h1KerToFix_h1ofFun ρ k hker (comp_kerToFixing_mem_Z1 ρ k hker a.2)]
    exact congrArg _ (funext fun n => congrArg a.1 (Subtype.ext rfl))

/-- `h1KerToFix` is additive. -/
theorem h1KerToFix_add (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker (ξ + η) = h1KerToFix ρ k hker ξ + h1KerToFix ρ k hker η := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    induction η using QuotientAddGroup.induction_on with
    | H b =>
      show h1KerToFix ρ k hker (H1mk _ _ a + H1mk _ _ b)
        = h1KerToFix ρ k hker (H1mk _ _ a) + h1KerToFix ρ k hker (H1mk _ _ b)
      rw [← map_add, ← H1ofFun_of_mem (a + b).2, ← H1ofFun_of_mem a.2,
        ← H1ofFun_of_mem b.2, h1KerToFix_h1ofFun ρ k hker (a + b).2,
        h1KerToFix_h1ofFun ρ k hker a.2, h1KerToFix_h1ofFun ρ k hker b.2]
      exact GQ2.DeepPart.H1ofFun_add (comp_fixingToKer_mem_Z1 ρ k hker a.2)
        (comp_fixingToKer_mem_Z1 ρ k hker b.2)

/-- **The transport equivalence** `H¹(ker ρ) ≃+ H¹(G_k)`. -/
noncomputable def h1KerFixEquiv (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ≃+
      H1 k.fixingSubgroup (ZMod 2) where
  toFun := h1KerToFix ρ k hker
  invFun := h1FixToKer ρ k hker
  left_inv := h1FixToKer_h1KerToFix ρ k hker
  right_inv := h1KerToFix_h1FixToKer ρ k hker
  map_add' := h1KerToFix_add ρ k hker

/-- `h1KerToFix` carries deep classes to deep classes, and conversely (the `(A, β)`-data
transports verbatim; memberships move along `hker`). -/
theorem h1KerToFix_mem_deep_iff (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker ξ ∈ LocalKummer.deepClasses k.fixingSubgroup
      ↔ ξ ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    have hZ1 : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2))
        = h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup
            (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))) := by
          rw [h1FixToKer_h1ofFun ρ k hker hZ1]
          exact congrArg _ (funext fun n => rfl)
      _ = h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) := by rw [heq]
      _ = ξ := h1FixToKer_h1KerToFix ρ k hker ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    show H1ofFun k.fixingSubgroup
        (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      = h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
    rw [h1KerToFix_h1ofFun ρ k hker hZ1]
    exact congrArg _ (funext fun n => rfl)

/-- The mid-classes version of the transport. -/
theorem h1KerToFix_mem_mid_iff (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker ξ ∈ midClassesSubgroup k.fixingSubgroup
      ↔ ξ ∈ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    have hZ1 : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2))
        = h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup
            (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))) := by
          rw [h1FixToKer_h1ofFun ρ k hker hZ1]
          exact congrArg _ (funext fun n => rfl)
      _ = h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) := by rw [heq]
      _ = ξ := h1FixToKer_h1KerToFix ρ k hker ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    show H1ofFun k.fixingSubgroup
        (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      = h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
    rw [h1KerToFix_h1ofFun ρ k hker hZ1]
    exact congrArg _ (funext fun n => rfl)

/-- **The transported structural count**, in `ker ρ`-vocabulary:
`#(H¹(ker ρ) ⧸ Deep) ≤ #E`. -/
theorem card_quot_deep_le_card_mid_ker [FiniteDimensional ℚ_[2] k]
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (π : ℚ̄₂) (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      ≤ Nat.card ↥(midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) := by
  haveI hfinFix : Finite (H1 k.fixingSubgroup (ZMod 2)) :=
    Finite.of_equiv _ (h1KerFixEquiv ρ k hker).toEquiv
  have hcount := card_quot_deep_le_card_mid k π hπk hπ0 hπ1 hπmax he he_pos hf_pos
    hcard_zero hcard_gr
  -- (a) the ambient cards agree
  have ha : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    Nat.card_congr (h1KerFixEquiv ρ k hker).toEquiv
  -- (b) the deep subgroups agree (through `coe_kummerDepth_deep`)
  have hb : Nat.card ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card ↥(kummerDepth k π (e + 1)) := by
    refine Nat.card_congr ((h1KerFixEquiv ρ k hker).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFix ρ k hker ξ)
      exact hset.mpr ((h1KerToFix_mem_deep_iff ρ k hker ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFix ρ k hker ξ)
      exact (h1KerToFix_mem_deep_iff ρ k hker ξ).mp (hset.mp hη)
  -- (c) the mid subgroups agree (through `coe_kummerDepth_mid`)
  have hc : Nat.card ↥(midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card ↥(kummerDepth k π e) := by
    refine Nat.card_congr ((h1KerFixEquiv ρ k hker).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he) (h1KerToFix ρ k hker ξ)
      exact hset.mpr ((h1KerToFix_mem_mid_iff ρ k hker ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he) (h1KerToFix ρ k hker ξ)
      exact (h1KerToFix_mem_mid_iff ρ k hker ξ).mp (hset.mp hη)
  -- the quotient cards agree by Lagrange + cancellation
  haveI : Nonempty ↥(kummerDepth k π (e + 1)) := ⟨⟨0, zero_mem _⟩⟩
  have hL1 : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
        * Nat.card ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hL2 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
        * Nat.card ↥(kummerDepth k π (e + 1))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hq : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1)) := by
    have hmm : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
          deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
          * Nat.card ↥(kummerDepth k π (e + 1))
        = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1)) := by
      rw [← hb, hL1, ha, ← hL2, hb]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmm
  rw [hq, hc]
  exact hcount

end KerTransport

end GQ2
