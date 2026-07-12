/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.EvensKahn

/-!
# The unit filtration of a finite dyadic field  (supporting definitions for B13)

The norm-one unit subgroup and the depth filtration `U^{(i)} = 1 + 𝔭_k^i` of a finite
extension `k/ℚ₂` inside `ℚ̄₂`, in the repo's spectral-norm vocabulary (the `IsDeepUnit`
idiom): depth is measured against a uniformizer `π` by `‖u − 1‖ ≤ ‖π‖^i` — no valuation
ring, residue field, or ramification bookkeeping is introduced.

The structure `DyadicUnitFiltration` bundles the **B13 axiom content**: existence of a
uniformizer (discreteness of the value group), the normalization `‖2‖ = ‖π‖^e`, and the
residue counts of the graded pieces of the filtration — **Serre, *Local Fields* [7],
Ch. IV §2, Proposition 6** (verified verbatim against the cited source; the audit copy is
not vendored):
`U^{(0)}/U^{(1)} ≅ k̄^×` (order `2^f − 1`) and `U^{(i)}/U^{(i+1)} ≅ k̄⁺` (order `2^f`) for
`i ≥ 1`.  The axiom `GQ2.dyadicUnitFiltration` asserting an instance for every finite `k`
lives in `GQ2/Foundations/Axioms.lean` (T-19 placement); everything in this file is a plain
definition or a proved lemma.

The proposal's (F2) clause (the inertia twist `θ_g = (g•π)/π` acting on `gr_j` by `θ_g^j`)
turned out to be **derivable** and is therefore NOT a field: `g•(1+a) = 1 + θ_g^i·g(a/π^i)·π^i`
is exact `ℚ̄₂`-algebra, and `θ_g^e = g(u)/u ≡ 1 (mod 𝔪)` for inertial `g` follows from the
`he` normalization with `u = π^e/2`.  See `docs/p15f1-axiom-proposal.md` and the B13 entry of
`docs/literature-axioms.md`.

Ticket: P-15f1.
-/

namespace GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The **norm-one units** of `k` — the arithmetic unit group `O_k^×` of the field `k`, cut
out of `(↥k)ˣ` (which is all of `k ∖ {0}`) by the spectral norm. -/
def normUnits : Subgroup (↥k)ˣ where
  carrier := {u | ‖((u : ↥k) : ℚ̄₂)‖ = 1}
  one_mem' := by simp
  mul_mem' := by intro u v hu hv; simp_all [norm_mul]
  inv_mem' := by intro u hu; simp_all [norm_inv]

/-- Membership in `normUnits` unfolded. -/
theorem mem_normUnits (u : (↥k)ˣ) :
    u ∈ normUnits k ↔ ‖((u : ↥k) : ℚ̄₂)‖ = 1 := Iff.rfl

variable (π : ℚ̄₂)

/-- The **depth-`i` unit subgroup** `U^{(i)} = 1 + 𝔭_k^i` relative to a uniformizer `π`:
norm-one units with `‖u − 1‖ ≤ ‖π‖^i`.  (At `i = 0` this is all of `normUnits k` —
`depthUnits_zero`; no hypothesis on `π` is needed for the subgroup property.) -/
def depthUnits (i : ℕ) : Subgroup (↥k)ˣ where
  carrier := {u | ‖((u : ↥k) : ℚ̄₂)‖ = 1 ∧ ‖((u : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ i}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have hcast : (((u * v : (↥k)ˣ) : ↥k) : ℚ̄₂)
        = ((u : ↥k) : ℚ̄₂) * ((v : ↥k) : ℚ̄₂) := by
      rw [Units.val_mul]
      push_cast
      ring
    constructor
    · show ‖(((u * v : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
      rw [hcast, norm_mul, hu.1, hv.1, mul_one]
    · show ‖(((u * v : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ i
      have hsplit : (((u * v : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1
          = ((u : ↥k) : ℚ̄₂) * (((v : ↥k) : ℚ̄₂) - 1) + (((u : ↥k) : ℚ̄₂) - 1) := by
        rw [hcast]; ring
      rw [hsplit]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ hu.2)
      rw [norm_mul, hu.1, one_mul]
      exact hv.2
  inv_mem' := by
    intro u hu
    have h1 : ((u⁻¹ : (↥k)ˣ) : ↥k) = ((u : ↥k))⁻¹ := Units.val_inv_eq_inv_val u
    have hcast : (((u⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) = (((u : ↥k) : ℚ̄₂))⁻¹ := by
      rw [h1]
      push_cast
      ring
    constructor
    · show ‖(((u⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
      rw [hcast, norm_inv, hu.1, inv_one]
    · show ‖(((u⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ i
      have hne : ((u : ↥k) : ℚ̄₂) ≠ 0 := by
        intro h0
        have h2 : ‖((u : ↥k) : ℚ̄₂)‖ = 1 := hu.1
        rw [h0, norm_zero] at h2
        exact one_ne_zero h2.symm
      have hsplit : (((u⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1
          = (((u : ↥k) : ℚ̄₂))⁻¹ * (1 - ((u : ↥k) : ℚ̄₂)) := by
        rw [hcast]
        field_simp
      rw [hsplit, norm_mul, norm_inv, hu.1, inv_one, one_mul, norm_sub_rev]
      exact hu.2

/-- Membership in `depthUnits` unfolded. -/
theorem mem_depthUnits (i : ℕ) (u : (↥k)ˣ) :
    u ∈ depthUnits k π i
      ↔ ‖((u : ↥k) : ℚ̄₂)‖ = 1 ∧ ‖((u : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ i := Iff.rfl

/-- At depth `0` the filtration is the full norm-one unit group (`‖u − 1‖ ≤ 1` is automatic
by the ultrametric inequality). -/
theorem depthUnits_zero : depthUnits k π 0 = normUnits k := by
  ext u
  rw [mem_depthUnits, mem_normUnits, pow_zero]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hsplit : ((u : ↥k) : ℚ̄₂) - 1 = ((u : ↥k) : ℚ̄₂) + (-1) := by ring
  rw [hsplit]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_of_eq h) ?_)
  rw [norm_neg, norm_one]

/-- The depth filtration is decreasing (for `‖π‖ ≤ 1`). -/
theorem depthUnits_antitone (hπ : ‖π‖ ≤ 1) {i j : ℕ} (hij : i ≤ j) :
    depthUnits k π j ≤ depthUnits k π i := by
  intro u hu
  exact ⟨hu.1, le_trans hu.2 (pow_le_pow_of_le_one (norm_nonneg π) hπ hij)⟩

/-- **The B13 bundle** — the unit-filtration data of a finite dyadic field: a uniformizer
(value-group discreteness), the `‖2‖ = ‖π‖^e` normalization, and the residue counts of the
graded pieces (Serre LF [7], Ch. IV §2, Prop. 6).  Asserted for every finite `k` by the axiom
`GQ2.dyadicUnitFiltration` (`GQ2/Foundations/Axioms.lean`); see the docstring there for the
full citation/deviation record. -/
structure DyadicUnitFiltration : Type where
  /-- A uniformizer: an element of `k` of maximal norm `< 1`. -/
  π : ℚ̄₂
  hπ_mem : π ∈ k
  hπ_ne : π ≠ 0
  hπ_lt : ‖π‖ < 1
  /-- Discreteness: `π` attains the maximal norm below `1` (so `‖π‖` generates the value
  group of `k`). -/
  hπ_max : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖
  /-- The absolute ramification index: `v_k(2) = e`. -/
  e : ℕ
  he_pos : 1 ≤ e
  he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e
  /-- The residue degree: `#k̄ = 2^f`. -/
  f : ℕ
  hf_pos : 1 ≤ f
  /-- Serre LF IV §2 Prop. 6(a): `U^{(0)}/U^{(1)} ≅ k̄^×`, of order `2^f − 1`. -/
  card_gr_zero :
    Nat.card (↥(normUnits k) ⧸ (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1
  /-- Serre LF IV §2 Prop. 6(b): `U^{(i)}/U^{(i+1)} ≅ k̄⁺`, of order `2^f`, for every
  `i ≥ 1`. -/
  card_gr : ∀ i : ℕ, 1 ≤ i →
    Nat.card (↥(depthUnits k π i) ⧸ (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i))
      = 2 ^ f

end GQ2
