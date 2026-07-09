import GQ2.UnitFiltration

/-!
# B13-1 — the topology layer for the unit-filtration discharge

This is the **B13-1 deliverable** of the `dyadicUnitFiltration` axiom-discharge initiative
(board `docs/b13-tickets.md`, plan `docs/b13-proof-plan.md`, §4-B13-1).  It supplies the compact
unit ball of a finite extension `k/ℚ₂` and the finite quotient `O/2O` that drives the
uniformizer pigeonhole (B13-2).

The one non-trivial output is `exists_pow_sub_dyadic`: for `x` with `‖x‖ ≤ 1`, two of the powers
`x⁰, x¹, …` are congruent mod the radius-`‖2‖` ball — the finite-quotient pigeonhole that B13-2
turns into the value-group gap `‖x‖ⁱ ≤ ‖2‖`.

**Route note (B13-0 recon).**  Mathlib's `IsUltrametricDist.closedBall_openAddSubgroup` gives the
closed ball directly as a bundled `OpenAddSubgroup`, so `unitBall`/`dyadicBall` are one term each;
`↥k` is proper (`FiniteDimensional.proper`), so the unit ball is compact and `O/2O` is finite
(`AddSubgroup.quotient_finite_of_isOpen`).  The unit-ball `Subring` and the residue field live
downstream in B13-3.
-/

namespace GQ2

open IsUltrametricDist Metric

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The closed **unit ball** `O = {x ∈ k : ‖x‖ ≤ 1}` of `k`, as a bundled open additive subgroup
(the ball is clopen in the ultrametric topology). -/
noncomputable def unitBall : OpenAddSubgroup ↥k := closedBall_openAddSubgroup ↥k (r := 1) one_pos

/-- The radius-`‖2‖` ball `2O = {x ∈ k : ‖x‖ ≤ ‖2‖}`, as a bundled open additive subgroup. -/
noncomputable def dyadicBall : OpenAddSubgroup ↥k :=
  closedBall_openAddSubgroup ↥k (r := ‖(2 : ℚ̄₂)‖) (norm_pos_iff.mpr two_ne_zero)

@[simp] theorem mem_unitBall {x : ↥k} : x ∈ (unitBall k).toAddSubgroup ↔ ‖x‖ ≤ 1 :=
  mem_closedBall_zero_iff

@[simp] theorem mem_dyadicBall {x : ↥k} :
    x ∈ (dyadicBall k).toAddSubgroup ↔ ‖x‖ ≤ ‖(2 : ℚ̄₂)‖ := mem_closedBall_zero_iff

/-- Powers of a norm-`≤ 1` element stay in the unit ball. -/
theorem unitBall_pow_mem {x : ↥k} (hx : ‖x‖ ≤ 1) (i : ℕ) : x ^ i ∈ (unitBall k).toAddSubgroup := by
  rw [mem_unitBall, norm_pow]; exact pow_le_one₀ (norm_nonneg x) hx

variable [FiniteDimensional ℚ_[2] k]

/-- The unit ball is compact: a closed ball in the proper space `↥k` (finite-dimensional over the
locally compact `ℚ₂`). -/
instance : CompactSpace ↥(unitBall k).toAddSubgroup := by
  refine isCompact_iff_compactSpace.mp ?_
  have hp := FiniteDimensional.proper ℚ_[2] ↥k
  have hc : ((unitBall k).toAddSubgroup : Set ↥k) = closedBall 0 1 := rfl
  rw [hc]; exact isCompact_closedBall 0 1

/-- The quotient `O/2O` is finite: `2O` is an open subgroup of the compact group `O`. -/
instance : Finite (↥(unitBall k).toAddSubgroup ⧸
    (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) :=
  AddSubgroup.quotient_finite_of_isOpen _
    (continuous_subtype_val.isOpen_preimage _ (dyadicBall k).isOpen)

/-- **The uniformizer pigeonhole** (B13-1's deliverable for B13-2): for any `x` with `‖x‖ ≤ 1`, two
of the powers `x⁰, x¹, …` are congruent modulo the radius-`‖2‖` ball, i.e. their difference has
norm `≤ ‖2‖`.  (B13-2 factors `xⁱ − xʲ = xⁱ(1 − xʲ⁻ⁱ)` and, when `‖x‖ < 1`, reads off the value-group
gap `‖x‖ⁱ ≤ ‖2‖`.) -/
theorem exists_pow_sub_dyadic {x : ↥k} (hx : ‖x‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖x ^ i - x ^ j‖ ≤ ‖(2 : ℚ̄₂)‖ := by
  classical
  haveI : Fintype (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) := Fintype.ofFinite _
  let g : ℕ → ↥(unitBall k).toAddSubgroup := fun i => ⟨x ^ i, unitBall_pow_mem k hx i⟩
  set N := Fintype.card (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) with hN
  let f : Fin (N + 1) → (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) :=
    fun i => QuotientAddGroup.mk (g i)
  have hlt : Fintype.card (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup)
      < Fintype.card (Fin (N + 1)) := by rw [Fintype.card_fin]; omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have hsub : g a.val - g b.val ∈
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp hfab
  rw [AddSubgroup.mem_addSubgroupOf] at hsub
  have hval : ((g a.val - g b.val : ↥(unitBall k).toAddSubgroup) : ↥k) = x ^ a.val - x ^ b.val := by
    simp [g]
  rw [hval, mem_dyadicBall] at hsub
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact ⟨a.val, b.val, h, hsub⟩
  · exact ⟨b.val, a.val, h, by rwa [norm_sub_rev] at hsub⟩

end GQ2
